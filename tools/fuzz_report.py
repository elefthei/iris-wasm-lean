"""Publish a static report from a single fuzz-signext run's live observations."""

import argparse
from datetime import datetime, timezone
from html import escape
import json
import os
from pathlib import Path
import re

from core3 import FIXTURE_REV, HARNESS_REV, SIGNEXT, compare_pair, concrete, signext_fuzz_batches, unique_fields


def observation(value):
    if isinstance(value, dict):
        if value in ({'kind': 'exception'}, {'kind': 'exhaustion'}):
            return
        if set(value) == {'kind', 'diagnostic'} and value['kind'] == 'trap' and isinstance(value['diagnostic'], str):
            return
        if set(value) == {'kind', 'values'} and value['kind'] == 'return' and isinstance(value['values'], list):
            for item in value['values']:
                concrete(item)
            return
    raise ValueError('missing or invalid engine observation')


def report(evidence, site, seed, cases, outcome):
    planned = {}
    counts = {}
    for width, (_, exports) in SIGNEXT.items():
        for export in exports:
            counts[width, export.field] = [cases, 0, 0, cases]
        for _, batch, commands in signext_fuzz_batches(width, exports, cases, seed):
            for export in batch:
                for ordinal in export.ordinals:
                    planned[width, ordinal] = export, commands[ordinal]

    seen, verified, errors = set(), {}, []
    try:
        with (evidence / 'cases.jsonl').open('rb') as rows:
            for line, raw in enumerate(rows, 1):
                try:
                    row = json.loads(raw, object_pairs_hook=unique_fields)
                    campaign, recorded_seed, width, ordinal = row['id']
                    if (campaign != 'fuzz-signext' or type(recorded_seed) is not int or recorded_seed != seed
                            or type(ordinal) is not int or (width, ordinal) not in planned):
                        raise ValueError('unexpected campaign, seed or case ID')
                    key = width, ordinal
                    if key in seen:
                        verified.pop(key, None)
                        raise ValueError('duplicate case ID')
                    seen.add(key)
                    export, command = planned[key]
                    pinned = {'module': f'{width}.0.wasm', 'module_sha256': SIGNEXT[width][0],
                              'revision': FIXTURE_REV, 'function_index': export.index,
                              'byte_range': [export.start, export.start + 6], 'export': export.field,
                              'args': command['action']['args'], 'expected': command['expected']}
                    if any(row[k] != v for k, v in pinned.items()):
                        raise ValueError('case differs from pinned export or generated input/expectation')
                    observation(row['lean'])
                    observation(row['oracle'])
                    agrees = compare_pair(command, row['lean'], row['oracle'], allow_choices=False)
                    if row['agrees'] is not agrees:
                        raise ValueError('recorded verdict contradicts observations')
                    verified[key] = agrees, row
                except (ValueError, KeyError, TypeError, RecursionError) as err:
                    errors.append(f'cases.jsonl line {line}: {err}')
    except OSError as err:
        errors.append(f'Cannot read cases.jsonl: {err.strerror}')

    mismatches = []
    for (width, ordinal), (agrees, row) in verified.items():
        bucket = counts[width, row['export']]
        bucket[1 if agrees else 2] += 1
        bucket[3] -= 1
        if not agrees:
            mismatches.append(f'<h3>{width}.{escape(row["export"])} · case {ordinal}</h3><dl>' + ''.join(
                f'<dt>{label}</dt><dd><code>{escape(json.dumps(row[k], ensure_ascii=True))}</code></dd>'
                for label, k in [('Input', 'args'), ('Expected', 'expected'), ('Lean', 'lean'), ('wasm3', 'oracle'),
                                 ('Function index', 'function_index'), ('Body byte range [start, end)', 'byte_range')]) + '</dl>')
    totals = list(map(sum, zip(*counts.values())))
    ok = not errors and outcome == 'success' and totals[1] == totals[0]
    status = 'All cases matched' if ok else 'Disagreement observed' if mismatches else 'Run incomplete or failed'
    def cells(values):
        return ''.join(f'<td>{v}</td>' for v in values)
    table = ''.join(f'<tr><th scope="row">{escape(w)}.{escape(e)}</th>{cells(values)}</tr>'
                    for (w, e), values in counts.items())
    run = ''
    repo, run_id = os.getenv('GITHUB_REPOSITORY', ''), os.getenv('GITHUB_RUN_ID', '')
    if re.fullmatch(r'[\w.-]+/[\w.-]+', repo, re.ASCII) and re.fullmatch(r'[0-9]+', run_id):
        run = f' · <a href="https://github.com/{escape(repo)}/actions/runs/{run_id}">Actions run {run_id}</a>'
    sha = escape(os.getenv('GITHUB_SHA') or 'unavailable')
    now = datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%M:%S UTC')
    notes = ''.join(f'<li>{escape(msg)}</li>' for msg in errors)
    hashes = ''.join(f'<li>{w}.0.wasm: <code>{digest}</code></li>' for w, (digest, _) in SIGNEXT.items())
    page = f'''<!doctype html>
<html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Sign-extension parity report</title><style>
:root {{color-scheme:light dark;font:100%/1.6 system-ui}} body {{max-width:66rem;margin:auto;padding:1.5rem}}
h1,h2,h3 {{line-height:1.2}} .scroll {{overflow-x:auto}} table {{border-collapse:collapse;width:100%}}
th,td {{text-align:right;padding:.45rem;border-bottom:1px solid #888}} th:first-child {{text-align:left}}
code,li,dd {{overflow-wrap:anywhere}} pre {{white-space:pre-wrap}} dd {{margin:0 0 .6rem 1rem}}
</style><main><h1>Sign-extension parity</h1><p>{now}{run}<br>Commit: <code>{sha}</code><br>Seed: <code>{seed}</code></p>
<h2>{status}</h2><p>Runner outcome: <strong>{escape(outcome)}</strong>. Each case compares Lean’s isolated function body and a live wasm3 export against the generated expected integer bits. This is not whole-module conformance.</p>
<div class="scroll"><table><caption>Case inventory by export</caption><thead><tr><th>Export</th><th>Planned</th><th>Matched</th><th>Disagreements</th><th>Missing</th></tr></thead><tbody>{table}</tbody><tfoot><tr><th>Total</th>{cells(totals)}</tr></tfoot></table></div>
<p>Missing means no verified pair of observations, not an engine disagreement.</p>
{('<h2>Evidence problems</h2><ul>' + notes + '</ul>') if notes else ''}
{('<h2>Disagreement details</h2>' + ''.join(mismatches)) if mismatches else ''}
<h2>Reproduce this campaign</h2><p>From the package root at the reported commit, with the pinned fixtures and wasm3 build installed:</p>
<pre><code>python3 -B tools/core3.py fuzz-signext --seed {seed} --cases {cases} --skip-features none --wasm3 .lake/core3/wasm3/build/wasm3 --keep-going</code></pre>
<h2>Pinned inputs</h2><p>Fixture revision: <code>{FIXTURE_REV}</code><br>wasm3 revision: <code>{HARNESS_REV}</code></p><ul>{hashes}</ul></main></html>'''
    site.mkdir(parents=True, exist_ok=False)
    (site / 'index.html').write_text(page, encoding='utf-8')
    return ok


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--seed', required=True, type=int)
    parser.add_argument('--cases', required=True, type=int)
    parser.add_argument('--outcome', required=True)
    parser.add_argument('evidence', type=Path)
    parser.add_argument('site', type=Path)
    args = parser.parse_args()
    if args.cases < 1:
        parser.error('--cases must be positive')
    raise SystemExit(not report(**vars(args)))
