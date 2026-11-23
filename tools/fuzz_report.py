"""Publish the sign-extension and shared-runtime parity campaigns on one static page."""

import argparse
from collections import defaultdict
from dataclasses import dataclass, field
from datetime import datetime, timezone
from functools import lru_cache
from hashlib import sha256
from html import escape
import json
import os
from pathlib import Path
import re

from core3 import FIXTURE_REV, HARNESS_REV, SIGNEXT, compare_pair, concrete, signext_fuzz_batches, unique_fields
from parity_runtime import agrees, module_bytes, operands, targets


DETAIL_LIMIT = 20


def observation(value, lane, runtime):
    if isinstance(value, dict):
        if value.get('kind') == 'error':
            raise ValueError(f'{lane} error: {value.get("diagnostic", "no diagnostic")}')
        if not runtime and value in ({'kind': 'exception'}, {'kind': 'exhaustion'}):
            return
        if runtime and lane == 'lean' and value == {'kind': 'trap'}:
            return
        if (set(value) == {'kind', 'diagnostic'} and value['kind'] == 'trap'
                and isinstance(value['diagnostic'], str) and value['diagnostic']):
            return
        if set(value) == {'kind', 'values'} and value['kind'] == 'return' and isinstance(value['values'], list):
            for item in value['values']:
                t, bits = concrete(item)
                if runtime and t in ('i32', 'i64', 'f32', 'f64') and item['value'] != str(bits):
                    raise ValueError(f'{lane}: expected unsigned decimal result bits')
            return
    raise ValueError(f'{lane}: missing or invalid engine observation')


@dataclass
class Suite:
    counts: dict
    details: list = field(default_factory=list)
    problems: list = field(default_factory=list)
    traps: int = 0
    nan_choices: int = 0

    def problem(self, message):
        if len(self.problems) < DETAIL_LIMIT:
            self.problems.append(message[:500])
        elif len(self.problems) == DETAIL_LIMIT:
            self.problems.append('Further evidence problems omitted; see the raw artifact.')


def counterexample(name, ordinal, row):
    fields = [('Input', 'args'), ('Expected', 'expected'), ('Lean', 'lean'), ('wasm3', 'oracle'),
              ('Module SHA-256', 'module_sha256'), ('Function index', 'function_index'),
              ('Body byte range [start, end)', 'byte_range')]
    items = ''.join(f'<dt>{label}</dt><dd><code>{escape(json.dumps(row[key])[:1000])}</code></dd>'
                    for label, key in fields if key in row)
    return f'<details><summary>{escape(name)} · case {ordinal}</summary><dl>{items}</dl></details>'


def collect(evidence, campaign, seed, cases, names, check):
    suite = Suite({name: [cases, 0, 0, cases] for name in names})
    runtime = campaign == 'runtime'
    # Retain verdicts, not raw rows. For disagreements keep a file offset until
    # duplicates have been invalidated, then read back only the displayed examples.
    seen = {}
    try:
        with (evidence / 'cases.jsonl').open('rb') as rows:
            for line, raw in enumerate(rows, 1):
                try:
                    row = json.loads(raw, object_pairs_hook=unique_fields)
                    tag, recorded_seed, name, ordinal = row['id']
                    if (not isinstance(row['id'], list) or tag != campaign
                            or type(recorded_seed) is not int or recorded_seed != seed
                            or not isinstance(name, str) or type(ordinal) is not int):
                        raise ValueError('unexpected campaign, seed or case ID')
                    key = name, ordinal
                    if key in seen:
                        seen[key] = None
                        raise ValueError(f'duplicate case ID: {key}')
                    seen[key] = None
                    for lane in ('lean', 'oracle'):
                        observation(row[lane], lane, runtime)
                    group, verdict = check(name, ordinal, row)
                    if row['agrees'] is not verdict:
                        raise ValueError('recorded verdict contradicts observations')
                    if not verdict:
                        kind, offset = 'disagreement', rows.tell() - len(raw)
                    elif row['lean']['kind'] == 'trap':
                        kind, offset = 'trap', None
                    elif runtime and row['lean']['values'] != row['oracle']['values']:
                        kind, offset = 'nan', None
                    else:
                        kind, offset = 'exact', None
                    seen[key] = group, kind, offset
                except (ValueError, KeyError, TypeError, RecursionError) as err:
                    suite.problem(f'cases.jsonl line {line}: {err}')
            for (_, ordinal), result in seen.items():
                if result is None:
                    continue
                group, kind, offset = result
                bucket = suite.counts[group]
                bucket[3] -= 1
                bucket[1 if offset is None else 2] += 1
                suite.traps += kind == 'trap'
                suite.nan_choices += kind == 'nan'
                if offset is not None and len(suite.details) < DETAIL_LIMIT:
                    rows.seek(offset)
                    suite.details.append(counterexample(group, ordinal, json.loads(rows.readline())))
    except OSError as err:
        suite.problem(f'Cannot read cases.jsonl: {err.strerror}')
    if runtime:
        try:
            with (evidence / 'errors.jsonl').open('rb') as errors:
                for raw in errors:
                    error = json.loads(raw, object_pairs_hook=unique_fields)
                    suite.problem(f'{error["target"]}: {error["diagnostic"]}')
        except FileNotFoundError:
            pass
        except (OSError, ValueError, TypeError, KeyError, RecursionError) as err:
            suite.problem(f'Cannot read errors.jsonl: {err}')
    return suite


def signext_suite(evidence, seed, cases):
    planned, names = {}, []
    for width, (_, exports) in SIGNEXT.items():
        names.extend(f'{width}.{export.field}' for export in exports)
        for _, batch, commands in signext_fuzz_batches(width, exports, cases, seed):
            for export in batch:
                for ordinal in export.ordinals:
                    planned[width, ordinal] = export, commands[ordinal]

    def check(width, ordinal, row):
        export, command = planned[width, ordinal]
        pinned = {'module': f'{width}.0.wasm', 'module_sha256': SIGNEXT[width][0],
                  'revision': FIXTURE_REV, 'function_index': export.index,
                  'byte_range': [export.start, export.start + 6], 'export': export.field,
                  'args': command['action']['args'], 'expected': command['expected']}
        if any(row[k] != v for k, v in pinned.items()):
            raise ValueError('case differs from pinned export or generated input/expectation')
        return f'{width}.{export.field}', compare_pair(command, row['lean'], row['oracle'], allow_choices=False)

    return collect(evidence, 'fuzz-signext', seed, cases, names, check)


def runtime_suite(evidence, seed, cases, ops):
    by_name = {op.name: op for op in ops}
    digests = {op.name: sha256(module_bytes(op)).hexdigest() for op in ops}

    @lru_cache(maxsize=2)
    def inputs(name):
        # The runner groups rows by target, but identity does not depend on row order.
        return list(operands(by_name[name], cases, seed))

    def check(name, ordinal, row):
        if name not in by_name or not 1 <= ordinal <= cases:
            raise ValueError(f'unknown runtime target or ordinal: {(name, ordinal)}')
        args = inputs(name)[ordinal - 1]
        if row['module_sha256'] != digests[name] or row['args'] != args:
            raise ValueError('case differs from generated runtime module or operands')
        op = by_name[name]
        lean, oracle = row['lean'], row['oracle']
        return name, agrees(op, args, lean, oracle)

    return collect(evidence, 'runtime', seed, cases, by_name, check)


def total(counts):
    return [sum(col) for col in zip(*counts.values())]


def table(caption, heading, counts):
    def cells(values):
        return ''.join(f'<td>{v}</td>' for v in values)
    rows = ''.join(f'<tr><th scope="row">{escape(name)}</th>{cells(values)}</tr>'
                   for name, values in counts.items())
    return (f'<div class="scroll"><table><caption>{escape(caption)}</caption><thead><tr><th>{heading}</th>'
            '<th>Planned</th><th>Matched</th><th>Disagreements</th><th>Missing</th></tr></thead>'
            f'<tbody>{rows}</tbody><tfoot><tr><th>Total</th>{cells(total(counts))}</tr></tfoot></table></div>')


def findings(suite):
    result = ''
    if suite.problems:
        result += '<h3>Evidence problems</h3><ul>' + ''.join(f'<li>{escape(msg)}</li>' for msg in suite.problems) + '</ul>'
    if suite.details:
        result += (f'<h3>Disagreement details</h3><p>Showing {len(suite.details)} of {total(suite.counts)[2]}. '
                   'Full rows and streams are in the raw CI evidence.</p>' + ''.join(suite.details))
    return result


def report(evidence, site, seed, cases, outcome, *, runtime_evidence, runtime_outcome):
    ops = targets()
    signext = signext_suite(evidence, seed, cases)
    runtime = runtime_suite(runtime_evidence, seed, cases, ops)
    families = defaultdict(dict)
    for op in ops:
        families[op.family][op.name] = runtime.counts[op.name]
    family_counts = {family: total(counts) for family, counts in families.items()}
    drilldown = ''.join(f'<details><summary>{escape(family)} ({len(counts)} targets)</summary>'
                        f'{table(family, "Target", counts)}</details>' for family, counts in families.items())
    ok = all(runner == 'success' and suite.counts and not suite.problems and total(suite.counts)[0] == total(suite.counts)[1]
             for suite, runner in ((signext, outcome), (runtime, runtime_outcome)))
    status = 'All cases matched' if ok else 'Disagreement observed' if signext.details or runtime.details else 'Run incomplete or failed'
    planned, matched, mismatched, missing = total({'pinned': total(signext.counts), 'runtime': total(runtime.counts)})
    run = ''
    artifact = 'See the raw CI evidence artifact for both cases.jsonl files, diagnostics and replay inputs.'
    repo, run_id = os.getenv('GITHUB_REPOSITORY', ''), os.getenv('GITHUB_RUN_ID', '')
    if re.fullmatch(r'[\w.-]+/[\w.-]+', repo, re.ASCII) and re.fullmatch(r'[0-9]+', run_id):
        url = f'https://github.com/{escape(repo)}/actions/runs/{run_id}'
        run = f' · <a href="{url}">Actions run {run_id}</a>'
        artifact_id = os.getenv('RAW_ARTIFACT_ID', '')
        href = f'{url}/artifacts/{artifact_id}' if re.fullmatch('[0-9]+', artifact_id) else f'{url}#artifacts'
        artifact = f'<a href="{href}">Raw CI evidence artifact</a>: complete rows, diagnostics and replay inputs.'
    sha = escape(os.getenv('GITHUB_SHA') or 'unavailable')
    now = datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%M:%S UTC')
    hashes = ''.join(f'<li>{w}.0.wasm: <code>{digest}</code></li>' for w, (digest, _) in SIGNEXT.items())
    page = f'''<!doctype html>
<html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>WebAssembly runtime parity report</title><style>
:root {{color-scheme:light dark;font:100%/1.6 system-ui}} body {{max-width:66rem;margin:auto;padding:1.5rem}}
h1,h2,h3 {{line-height:1.2}} .scroll {{overflow-x:auto}} table {{border-collapse:collapse;width:100%}}
th,td {{text-align:right;padding:.45rem;border-bottom:1px solid #888}} th:first-child {{text-align:left}}
code,li,dd {{overflow-wrap:anywhere}} pre {{white-space:pre-wrap}} dd {{margin:0 0 .6rem 1rem}}
</style><main><h1>WebAssembly runtime parity</h1><p>{now}{run}<br>Commit: <code>{sha}</code><br>Seed: <code>{seed}</code> · {cases} cases per target</p>
<h2>{status}</h2><p><strong>{matched:,} matched · {mismatched:,} disagreed · {missing:,} missing</strong> across {planned:,} planned comparisons.</p>
<p><a href="#runtime">Runtime families ({len(ops)} targets)</a> · <a href="#pinned">Pinned exports ({len(signext.counts)} targets)</a> · <a href="#replay">Replay</a></p>
<p>Missing means no verified pair: this includes absent, duplicate, invalid and infrastructure-error rows. A failed or skipped runner cannot pass, even with matching rows. {artifact}</p>
<h2 id="pinned">Pinned sign-extension exports</h2><p>Runner outcome: <strong>{escape(outcome)}</strong>. Lean’s decoded fixture body and the live wasm3 export must both return the expected integer bits. The generator computes those bits from the input and extension width, without either engine or a fixture assertion.</p>
{table("Sign-extension case inventory", "Export", signext.counts)}{findings(signext)}
<h2 id="runtime">Shared executable instruction families</h2><p>Runner outcome: <strong>{escape(runtime_outcome)}</strong>. These comparisons have two engines, not a third expected answer. Return types and raw bits must match except for spec-permitted quiet NaN choices on eligible operations. Traps compare by kind, not diagnostic text.</p>
<p>Matched cases include {runtime.nan_choices} with different permitted NaN bits and {runtime.traps} paired traps.</p>
{table("Runtime case inventory by family", "Family", family_counts)}<h3>Cases by target</h3>{drilldown}{findings(runtime)}
<h2>Coverage limits</h2><p>Counts cover bounded, well-typed programs and the listed inputs, not exhaustive behavior or whole-module conformance. Host calls, arbitrary modules, malformed binaries and resource stress are outside this campaign. SIMD lacks execution in the pinned wasm3; Core 3 features without executable Lean semantics are not compared. Unsupported features are outside the planned counts, not matches or missing cases.</p>
<h2 id="replay">Replay both campaigns</h2><p>At the reported commit, with pinned fixtures and the wasm3 build installed, use a fresh runtime output directory:</p>
<pre><code>python3 -B tools/core3.py fuzz-signext --seed {seed} --cases {cases} --skip-features none --wasm3 .lake/core3/wasm3/build/wasm3 --keep-going
python3 -B tools/parity_runtime.py --seed {seed} --cases {cases} --skip-features none --wasm3 .lake/core3/wasm3/build/wasm3 --out-dir runtime-replay</code></pre>
<p>To replay one runtime target, add <code>--target NAME</code> from the target table.</p>
<h2>Pinned inputs</h2><p>Fixture revision: <code>{FIXTURE_REV}</code><br>wasm3 revision: <code>{HARNESS_REV}</code></p><ul>{hashes}</ul></main></html>'''
    site.mkdir(parents=True, exist_ok=False)
    (site / 'index.html').write_text(page, encoding='utf-8')
    return ok


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--seed', required=True, type=int)
    parser.add_argument('--cases', required=True, type=int)
    parser.add_argument('--outcome', required=True)
    parser.add_argument('--runtime-evidence', required=True, type=Path)
    parser.add_argument('--runtime-outcome', required=True)
    parser.add_argument('evidence', type=Path)
    parser.add_argument('site', type=Path)
    args = parser.parse_args()
    if args.cases < 1:
        parser.error('--cases must be positive')
    raise SystemExit(not report(**vars(args)))
