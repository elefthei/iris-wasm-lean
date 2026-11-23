"""Compare bounded Wasm programs on the executable Lean semantics and a live wasm3."""

import argparse
from collections import Counter
from hashlib import sha256
from itertools import islice
import json
from pathlib import Path
import random
import shlex
import sys

from core3 import (FAULTS, HARNESS, HARNESS_REV, ROOT, SCALARS, Wasm3Client, _Process, concrete,
                   dump_line, matches_scalar, offline_lake, pinned_policy, scalar_nan_result,
                   signext_directory, unique_fields, verify_checkout, verify_profile)
from parity_model import abi, module_bytes, sized_body
from parity_scalar import scalar_ops
from parity_stateful import stateful_ops


def targets():
    ops = (*scalar_ops(), *stateful_ops())
    if len({op.name for op in ops}) != len(ops):
        raise ValueError('duplicate runtime target name')
    return ops


def edges(t):
    width = SCALARS[t]
    sign = 1 << (width - 1)
    if t.startswith('i'):
        return (0, 1, 2, sign - 1, sign, sign + 1, 2 * sign - 1, width - 1, width, width + 1)
    frac = 23 if width == 32 else 52
    inf = sign - (1 << frac)
    one = ((1 << (width - frac - 2)) - 1) << frac  # biased exponent for 1.0
    magnitudes = (0, 1, (1 << frac) - 1, 1 << frac, one - 1, one, one + 1,
                  one + (1 << (frac - 1)), inf - 1, inf, inf + 1, inf + (1 << (frac - 1)))
    return tuple(x | s for x in magnitudes for s in (0, sign))


def operands(op, count, seed):
    rng = random.Random(f'runtime:{seed}:{op.name}')
    pools = [edges(t) for t in op.params]
    for i in range(count):
        args = []
        for j, (t, pool) in enumerate(zip(op.params, pools)):
            if i % 4 == 0:
                n = pool[(i // 4 + j) % len(pool)]
            elif i % 4 == 1:
                n = rng.choice(pool)
            else:
                n = rng.getrandbits(SCALARS[t])
            args.append({'type': abi(t), 'value': str(n)})
        yield args


def agrees(op, args, lean, oracle):
    if lean['kind'] == oracle['kind'] == 'trap':
        return True  # the Lean trap boundary does not carry a diagnostic string
    if lean['kind'] != 'return' or oracle['kind'] != 'return':
        return False
    if len(lean['values']) != 1 or len(oracle['values']) != 1:
        return False
    left, right = (concrete(r['values'][0]) for r in (lean, oracle))
    if left[0] != abi(op.result) or right[0] != abi(op.result):
        return False
    if op.nan_choices:
        dst, field = op.name.split('.', 1)
        converting = field in ('promote_f32', 'demote_f64')
        action = {'field': op.name if converting else field,
                  'args': [{'type': t, 'value': a['value']} for t, a in zip(op.params, args)]}
        pattern = scalar_nan_result(action, 'conversions' if converting else dst)
        if pattern is not None:
            return all(matches_scalar(dst, pattern['value'], n) for n in (left[1], right[1]))
    return left == right


def lean_observations(raw, count):
    rows = json.loads(raw, object_pairs_hook=unique_fields)
    if not isinstance(rows, list) or len(rows) != count:
        raise ValueError('Lean returned a partial or surplus batch')
    for i, row in enumerate(rows, 1):
        if not isinstance(row, list) or len(row) != 2 or type(row[0]) is not int or row[0] != i:
            raise ValueError(f'expected ordered Lean batch ordinal {i}')
        obs = row[1]
        if obs == {'kind': 'trap'}:
            yield obs
        elif isinstance(obs, dict) and obs.get('kind') == 'error' and isinstance(obs.get('diagnostic'), str):
            yield obs
        elif isinstance(obs, dict) and set(obs) == {'kind', 'values'} and obs['kind'] == 'return':
            if not isinstance(obs['values'], list):
                raise ValueError('invalid Lean return')
            for v in obs['values']:
                t, n = concrete(v)
                if t not in ('i32', 'i64') or v['value'] != str(n):
                    raise ValueError(f'invalid Lean ABI value: {v!r}')
            yield obs
        else:
            raise ValueError(f'invalid Lean observation at {i}: {obs!r}')


def run_target(op, args, folder, lean, requests, records, counts):
    folder.mkdir()
    data = module_bytes(op)
    digest = sha256(data).hexdigest()
    (folder / 'module.wasm').write_bytes(data)
    body = sized_body(op)
    if not data.endswith(body):
        raise ValueError('tested body must be the last code entry in the oracle module')
    trials = operands(op, args.cases, args.seed)
    with (folder / 'oracle.raw').open('wb') as raw, Wasm3Client(args.wasm3, timeout=args.timeout, record=raw.write) as oracle:
        oracle.request({'type': 'reset'})
        loaded = oracle.request({'type': 'module', 'name': 'test', 'bytes': data.hex()})
        if loaded['kind'] != 'ok':
            raise ValueError(f'wasm3 did not load {op.name}: {loaded}')
        for offset in range(0, args.cases, 256):
            batch = list(islice(trials, 256))
            req = {'body': list(data[-len(body):]), 'memory64': op.memory64,
                   'params': [abi(t) for t in op.params], 'result': abi(op.result),
                   'trials': [[v['value'] for v in xs] for xs in batch]}
            line = (json.dumps(req, separators=(',', ':')) + '\n').encode()
            requests.write(line)
            try:
                observations = list(lean_observations(lean.exchange(line), len(batch)))
            except FAULTS as err:
                # Once framing is lost, a late reply could be attributed to the next target.
                raise RuntimeError(f'{op.name}: invalid Lean batch starting at {offset + 1}: {err}') from err
            for j, xs in enumerate(batch):
                actual = observations[j]
                other = oracle.request({'type': 'invoke', 'module': 'test', 'field': 'run', 'args': xs})
                verdict = None if actual['kind'] == 'error' else agrees(op, xs, actual, other)
                row = {'id': ['runtime', args.seed, op.name, offset + j + 1], 'module_sha256': digest,
                       'args': xs, 'lean': actual, 'oracle': other, 'agrees': verdict}
                dump_line(records, row)
                counts[verdict] += 1
                if verdict is not True and counts[verdict] == 1:
                    print('First disagreement:' if verdict is False else 'First incomplete observation:',
                          json.dumps(row), file=sys.stderr, flush=True)


def run(args, ops):
    root = args.out_dir
    if root is None:
        root = signext_directory('fuzz-runtime-')
    else:
        root.mkdir(parents=True)
        print(f'Evidence: {root}', flush=True)
    cmd = ['python3', '-B', 'tools/parity_runtime.py', '--cases', str(args.cases), '--seed', str(args.seed),
           '--wasm3', str(args.wasm3), '--skip-features', args.skip_features, '--timeout', str(args.timeout)]
    if args.target:
        cmd += ['--target', args.target]
    (root / 'replay.txt').write_text(shlex.join(cmd) + '\n')
    print(f'Replay: {shlex.join(cmd)}', flush=True)
    args.wasm3 = args.wasm3.resolve()
    verify_checkout(HARNESS, HARNESS_REV)
    verify_profile(args, pinned_policy(), root)
    offline_lake('--log-level=error', 'build', 'WasmTest.FuzzRuntime')
    counts = Counter()
    failures = 0
    with ((root / 'cases.jsonl').open('w') as records, (root / 'errors.jsonl').open('w') as errors,
          (root / 'lean-inputs.jsonl').open('wb') as requests, (root / 'lean-outputs.raw').open('wb') as replies,
          _Process(['lake', '--no-cache', 'env', 'lean', '--run', str(ROOT / 'WasmTest/FuzzRuntime.lean')],
                   b'\n', args.timeout, replies.write) as lean):
        for index, op in enumerate(ops):
            try:
                run_target(op, args, root / f'{index:03d}-{op.name}', lean, requests, records, counts)
            except FAULTS as e:
                failures += 1
                dump_line(errors, {'target': op.name, 'diagnostic': str(e)})
                print(f'{op.name}: incomplete: {e}', file=sys.stderr, flush=True)
                if lean.p.poll() is not None:
                    raise ValueError('Lean observer exited before campaign finished') from e
    total = len(ops) * args.cases
    print(f'{counts[True]}/{total} matched; {counts[False]} disagreed; '
          f'{total-counts[True]-counts[False]} missing. {len(ops)} runtime targets. Evidence: {root}')
    return not failures and counts[True] == total


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--cases', type=int, default=257)
    p.add_argument('--seed', type=int, required=True)
    p.add_argument('--skip-features', required=True, choices=('atomics', 'none'))
    p.add_argument('--wasm3', type=Path, default=Path('/usr/bin/wasm3'))
    p.add_argument('--timeout', type=int, default=30)
    p.add_argument('--out-dir', type=Path)
    p.add_argument('--target', help='replay just one named runtime target')
    args = p.parse_args()
    if min(args.cases, args.timeout) < 1:
        p.error('--timeout and --cases must be positive')
    ops = [op for op in targets() if args.target is None or args.target == op.name]
    if not ops:
        p.error('unknown target')
    return not run(args, ops)


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (*FAULTS, RuntimeError) as err:
        sys.exit(f'runtime campaign incomplete: {err}')
