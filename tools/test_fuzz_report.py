from hashlib import sha256
import json
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest
from unittest.mock import patch

from core3 import FIXTURE_REV, SIGNEXT, signext_fuzz_batches
from fuzz_report import report
from parity_runtime import module_bytes, operands
from parity_scalar import scalar_ops


# Exercise real generators/NaN rules with a small inventory: two families,
# several targets and edge operands at ordinal 1 (+0 / -0 for f32.div).
OPS = tuple(op for op in scalar_ops() if op.name in ('i32.add', 'i32.sub', 'f32.div'))


def returned(t, bits):
    return {'kind': 'return', 'values': [{'type': t, 'value': str(bits)}]}


def runtime_sample():
    rows = []
    for op in OPS:
        left, right = {'i32.add': (1, 1), 'i32.sub': (0xffffffff, 0xffffffff),
                       'f32.div': (0x7fc00000, 0xffc00000)}[op.name]
        rows.append({'id': ['runtime', 42, op.name, 1], 'args': next(operands(op, 1, 42)),
                     'module_sha256': sha256(module_bytes(op)).hexdigest(),
                     'lean': returned('i32', left), 'oracle': returned('i32', right), 'agrees': True})
    return rows


def sample():
    rows = []
    for width, (digest, exports) in SIGNEXT.items():
        for _, batch, commands in signext_fuzz_batches(width, exports, 1, 42):
            for e in batch:
                i, = e.ordinals
                cmd = commands[i]
                reply = {'kind': 'return', 'values': cmd['expected']}
                rows.append({'id': ['fuzz-signext', 42, width, i], 'export': e.field,
                             'module': f'{width}.0.wasm', 'module_sha256': digest,
                             'revision': FIXTURE_REV, 'function_index': e.index,
                             'byte_range': [e.start, e.start + 6], 'args': cmd['action']['args'],
                             'expected': cmd['expected'], 'lean': reply, 'oracle': reply, 'agrees': True})
    return rows


class ReportTests(unittest.TestCase):
    def render(self, rows, runtime_rows, *, outcome='success', runtime_outcome='success',
               tail='', runtime_tail='', errors=''):
        with TemporaryDirectory() as tmp, patch('fuzz_report.targets', return_value=OPS), patch.dict(
                'os.environ', {'GITHUB_SHA': '<script>bad</script>', 'GITHUB_REPOSITORY': 'example/wasm',
                               'GITHUB_RUN_ID': '123', 'RAW_ARTIFACT_ID': '456'}):
            root = Path(tmp)
            for dirname, data, suffix in [('signext', rows, tail), ('runtime', runtime_rows, runtime_tail)]:
                if data is not None:
                    path = root / dirname
                    path.mkdir()
                    (path / 'cases.jsonl').write_text(''.join(json.dumps(r) + '\n' for r in data) + suffix)
            if errors:
                (root / 'runtime/errors.jsonl').write_text(errors)
            ok = report(root / 'signext', root / 'site', 42, 1, outcome,
                        runtime_evidence=root / 'runtime', runtime_outcome=runtime_outcome)
            self.assertEqual([p.name for p in (root / 'site').iterdir()], ['index.html'])
            return ok, (root / 'site/index.html').read_text()

    def test_complete(self):
        ok, page = self.render(sample(), list(reversed(runtime_sample())))
        self.assertTrue(ok)
        self.assertIn('All cases matched', page)
        self.assertIn('<th>Total</th><td>5</td><td>5</td><td>0</td><td>0</td>', page)
        self.assertIn('<th>Total</th><td>3</td><td>3</td><td>0</td><td>0</td>', page)
        self.assertIn('integer arithmetic</th><td>2</td><td>2</td>', page)
        self.assertIn('i32.add</th><td>1</td><td>1</td>', page)
        self.assertIn('1 with different permitted NaN bits', page)
        self.assertIn('https://github.com/example/wasm/actions/runs/123/artifacts/456', page)
        self.assertIn('tools/parity_runtime.py --seed 42 --cases 1', page)
        self.assertIn('https://github.com/example/wasm/actions/runs/123', page)
        self.assertIn('--seed 42 --cases 1', page)
        self.assertIn('&lt;script&gt;', page)

    def test_disagreement(self):
        rows = sample()
        rows[0].update(oracle={'kind': 'trap', 'diagnostic': '<script>oops</script>'}, agrees=False)
        ok, page = self.render(rows, runtime_sample(), outcome='failure')
        self.assertFalse(ok)
        self.assertIn('Disagreement observed', page)
        self.assertIn('<th>Total</th><td>5</td><td>4</td><td>1</td><td>0</td>', page)
        self.assertIn('i32.extend8_s · case 1', page)
        self.assertIn('&lt;script&gt;oops', page)
        self.assertNotIn('<script>', page)

    def test_same_wrong_bits_fail_signext(self):
        rows = sample()
        wrong = returned('i32', int(rows[0]['expected'][0]['value']) ^ 1)
        rows[0].update(lean=wrong, oracle=wrong, agrees=False)
        ok, page = self.render(rows, runtime_sample())
        self.assertFalse(ok)
        self.assertIn('Disagreement observed', page)
        self.assertIn('<dt>Expected</dt>', page)

    def test_incomplete(self):
        rows = sample()
        for label, data, kwargs in [
            ('setup failure', None, {}), ('missing case', rows[:-1], {}),
            ('duplicate', rows + rows[:1], {}), ('truncated extra row', rows, {'tail': '{'}),
            ('failed runner', rows, {'outcome': 'failure'}),
            ('stale seed', [{**rows[0], 'id': ['fuzz-signext', 41, 'i32', 1]}, *rows[1:]], {}),
            ('wrong export', [{**rows[0], 'export': 'extend32_s'}, *rows[1:]], {}),
            ('invalid observation', [{**rows[0], 'oracle': {}}, *rows[1:]], {}),
            ('false verdict', [{**rows[0], 'agrees': False}, *rows[1:]], {}),
        ]:
            with self.subTest(label):
                ok, page = self.render(data, runtime_sample(), **kwargs)
                self.assertFalse(ok)
                self.assertIn('Run incomplete or failed', page)
                self.assertNotIn('Disagreement details', page)

    def test_runtime_disagreement(self):
        for label, value in [('wrong bits', returned('i32', 2)), ('wrong type', returned('i64', 1)),
                             ('trap', {'kind': 'trap', 'diagnostic': '<script>oops</script>'})]:
            with self.subTest(label):
                rows = runtime_sample()
                row = next(r for r in rows if r['id'][2] == 'i32.add')
                row.update(oracle=value, agrees=False)
                ok, page = self.render(sample(), rows, runtime_outcome='failure')
                self.assertFalse(ok)
                self.assertIn('Disagreement observed', page)
                self.assertIn('i32.add · case 1', page)
                self.assertIn('<th>Total</th><td>3</td><td>2</td><td>1</td><td>0</td>', page)
                self.assertIn(row['module_sha256'], page)
                self.assertNotIn('<script>', page)

    def test_trap_matches_kind_not_diagnostic(self):
        rows = runtime_sample()
        rows[0].update(lean={'kind': 'trap'}, oracle={'kind': 'trap', 'diagnostic': 'oracle detail'})
        ok, page = self.render(sample(), rows)
        self.assertTrue(ok)
        self.assertIn('1 paired traps', page)

    def test_runtime_incomplete(self):
        rows = runtime_sample()
        first, *rest = rows
        bad = [
            ('missing file', None, {}), ('missing row', rest, {}), ('duplicate', rows + [first], {}),
            ('truncated', rows, {'runtime_tail': '{'}), ('runner failed', rows, {'runtime_outcome': 'failure'}),
            ('target error', rows, {'errors': '{"target":"i32.add","diagnostic":"load failed"}\n'}),
        ]
        for label, changed in [
            ('stale seed', {'id': ['runtime', 41, first['id'][2], 1]}),
            ('other campaign', {'id': ['fuzz-signext', 42, first['id'][2], 1]}),
            ('other target', {'id': ['runtime', 42, 'unknown', 1]}),
            ('surplus ordinal', {'id': ['runtime', 42, first['id'][2], 2]}),
            ('boolean ordinal', {'id': ['runtime', 42, first['id'][2], True]}),
            ('unexpected operands', {'args': []}), ('stale module', {'module_sha256': '0' * 64}),
            ('wrong verdict', {'agrees': False}), ('untyped verdict', {'agrees': 1}),
            ('malformed bits', {'lean': returned('i32', 'nan:canonical')}),
            ('missing return', {'lean': {'kind': 'return'}}), ('missing trap detail', {'oracle': {'kind': 'trap'}}),
            ('Lean error', {'lean': {'kind': 'error', 'diagnostic': 'no cut'}, 'agrees': None}),
            ('oracle error', {'oracle': {'kind': 'error', 'diagnostic': 'unavailable'}, 'agrees': False}),
        ]:
            bad.append((label, [{**first, **changed}, *rest], {}))
        for label, data, kwargs in bad:
            with self.subTest(label):
                ok, page = self.render(sample(), data, **kwargs)
                self.assertFalse(ok)
                self.assertIn('Run incomplete or failed', page)
                self.assertNotIn('Disagreement details', page)
                if label in ('duplicate', 'Lean error', 'oracle error', 'stale module'):
                    self.assertIn('<th>Total</th><td>3</td><td>2</td><td>0</td><td>1</td>', page)

    def test_bounded_examples_and_duplicate_disagreement(self):
        rows = runtime_sample()
        for row in rows:
            row.update(oracle=returned('i32', 31), agrees=False)
        with patch('fuzz_report.DETAIL_LIMIT', 1):
            ok, page = self.render(sample(), [*rows, rows[0]])
        self.assertFalse(ok)
        self.assertIn('Showing 1 of 2', page)
        self.assertIn('<th>Total</th><td>3</td><td>0</td><td>2</td><td>1</td>', page)
        self.assertNotIn(f"{rows[0]['id'][2]} · case 1", page)
