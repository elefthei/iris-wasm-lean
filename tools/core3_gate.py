"""Check the pinned SpecTec inventory, project axioms and independent kernel replay."""

import csv
import json
import os
from pathlib import Path
import re
import subprocess
import sys

from core3 import ROOT, CACHE, SPEC, SPEC_REV, verify_checkout


INVENTORY = ROOT / "WasmTest/Core3/rules.tsv"
RESULTS = CACHE / "results/proof"
COLUMNS = "id syntax decoder declarative implementation correctness witness".split()
CLAIMS = ["Wasm.t_progress", "Wasm.t_preservation", "Wasm.b_e_type_checker_reflects_typing",
          "Wasm.CoreTypes.validateGroups_iff", "Wasm.CoreTypes.Composite.matches_iff", "Wasm.CoreTypes.External.matches_iff",
          "Wasm.validateModule_iff", "IrisWasm.be_fundamental", "IrisWasm.instantiation_wasm_spec",
          "IrisWasm.Examples.lse_adequacy"] + ["IrisWasm.Denotational." + name for name in
          ("round_next_iff", "round_done_iff", "denote_tau_iff", "denote_host_iff", "denote_steps_iff",
           "exact_config_iff", "exact_result_iff", "runRound_next", "runCut_sound")]


def required_ids():
    """Pin-relative production ordinals distinguish e.g. both binary 'if' alternatives."""
    ids = {}
    for src in sorted((SPEC / "specification/wasm-3.0").glob("[1-5].*.spectec")):
        # Remove inactive SpecTec commentary without shifting its source locations.
        text = re.sub(r'\(;.*?;\)|;;[^\n]*', lambda m: '\n' * m[0].count('\n'),
                      src.read_text(), flags=re.S)
        header = re.compile(r'^(rule|grammar|syntax|def|relation|var)\s+([^\s:(]+).*$', re.M)
        declarations = list(header.finditer(text))
        for i, m in enumerate(declarations):
            family, name = m.groups()
            if family != 'rule' and not (family == 'grammar' and src.name.startswith('5.')
                                         or family == 'syntax' and name.startswith('instr/')):
                continue
            start = m.start()
            body = text[start:declarations[i+1].start() if i+1 < len(declarations) else len(text)]
            alternatives = [a.start() for a in re.finditer(r'^[ \t]*\|[ \t]+(?!\.\.\.)\S', body, re.M)]
            points = alternatives if family != 'rule' and alternatives else [0]
            for ordinal, pos in enumerate(points, 1):
                key = family + '/' + name + (f'#{ordinal}' if len(points) > 1 else '')
                if key in ids:
                    raise ValueError(f'duplicate normative key: {key}')
                ids[key] = f'{src.name}:{text.count(chr(10), 0, start+pos)+1}'
    if not ids or 'rule/Step/call_ref-hostfunc-res' not in ids:
        raise ValueError('missing normative instruction source')
    return ids


def coverage():
    required = required_ids()
    seen, decls = set(), set()
    with INVENTORY.open() as stream:
        rows = csv.DictReader(stream, delimiter='\t')
        if rows.fieldnames != COLUMNS:
            raise ValueError(f'{INVENTORY}: expected fields {COLUMNS}')
        for row in rows:
            key = row['id']
            if key not in required or key in seen:
                raise ValueError(f'{INVENTORY}:{rows.line_num}: unexpected or repeated {key}')
            for col in COLUMNS[1:]:
                symbol = row[col]
                if not symbol or not re.fullmatch(r'[A-Za-z_][\w\'.]*(?:\.[\w\']+)*', symbol):
                    raise ValueError(f'{INVENTORY}:{rows.line_num}: invalid {col} declaration')
                decls.add(symbol)
            seen.add(key)
    missing = {k: v for k, v in required.items() if k not in seen}
    (RESULTS / 'uncovered.json').write_text(json.dumps(missing, indent=2) + '\n')
    print(f'Normative coverage: {len(seen)}/{len(required)} IDs mapped; {len(missing)} missing', flush=True)
    return decls, not missing


def project_sources():
    return sorted(p for lib in ('Wasm', 'IrisWasm', 'WasmTest') for p in
                  [ROOT / (lib + '.lean'), *(ROOT / lib).rglob('*.lean')] if p.is_file())


def checked(label, args, *, source=None, env=None):
    with (RESULTS / (label + '.log')).open('w') as log:
        p = subprocess.run(args, input=source, stdout=log, stderr=subprocess.STDOUT, text=True,
                           cwd=ROOT, env=env)
    if p.returncode:
        print(f'{label}: failed ({p.returncode}); see {log.name}', file=sys.stderr, flush=True)
    return p.returncode == 0


def main():
    verify_checkout(SPEC, SPEC_REV)
    RESULTS.mkdir(parents=True, exist_ok=True)
    decls, ok = coverage()
    files = project_sources()
    modules = ['.'.join(f.relative_to(ROOT).with_suffix('').parts) for f in files]
    findings = []
    for f in files:
        for i, line in enumerate(f.read_text().splitlines(), 1):
            if re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by)\b|@\[\s*extern\b', line):
                findings.append(f'{f.relative_to(ROOT)}:{i}: {line}')
    (RESULTS / 'source-scan.log').write_text('\n'.join(findings))
    ok &= not findings
    # The public results must be reachable through this import alone.
    ok &= checked('claims', ['lake', 'env', 'lean', '--stdin'], source='import IrisWasm\n' +
                  ''.join('#print axioms ' + decl + '\n' for decl in CLAIMS))
    imports = ''.join('import ' + m + '\n' for m in modules)
    src = 'import Lean\n' + imports + ''.join('#check ' + d + '\n' for d in sorted(decls)) + '''
open Lean in
run_cmd do
  let env ← getEnv
  let roots : List Name := MODULES
  let selected := env.header.moduleNames.map fun n => roots.contains n
  for (n, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    unless selected[idx.toNat]! do continue
    for a in ← collectAxioms n do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
        logError m!"{n} depends on {a}"
'''.replace('MODULES', '[' + ','.join('`' + m for m in modules) + ']')
    ok &= checked('axioms', ['lake', 'env', 'lean', '--stdin'], source=src)
    for m in modules:
        # Default leanchecker treats a module name as a prefix and replays all matches concurrently.
        flags = ['--fresh'] if any(other.startswith(m + '.') for other in modules) else []
        ok &= checked('replay-' + m, ['lake', 'env', 'leanchecker', *flags, m],
                      env={**os.environ, 'LEAN_NUM_THREADS': '1'} if flags else None)
    return 0 if ok else 1


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        sys.exit(f'core3 proof gate: {error}')
