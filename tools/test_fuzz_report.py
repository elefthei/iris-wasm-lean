import json
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest
from unittest.mock import patch

from core3 import FIXTURE_REV, SIGNEXT, signext_fuzz_batches
from fuzz_report import report


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
    def render(self, rows, *, outcome='success', tail=''):
        with TemporaryDirectory() as tmp, patch.dict('os.environ', {'GITHUB_SHA': '<script>bad</script>',
                'GITHUB_REPOSITORY': 'example/wasm', 'GITHUB_RUN_ID': '123'}):
            root = Path(tmp)
            if rows is not None:
                (root / 'cases.jsonl').write_text(''.join(json.dumps(r) + '\n' for r in rows) + tail)
            ok = report(root, root / 'site', 42, 1, outcome)
            self.assertEqual([p.name for p in (root / 'site').iterdir()], ['index.html'])
            return ok, (root / 'site/index.html').read_text()

    def test_complete(self):
        ok, page = self.render(sample())
        self.assertTrue(ok)
        self.assertIn('All cases matched', page)
        self.assertIn('<th>Total</th><td>5</td><td>5</td><td>0</td><td>0</td>', page)
        self.assertIn('https://github.com/example/wasm/actions/runs/123', page)
        self.assertIn('--seed 42 --cases 1', page)
        self.assertIn('&lt;script&gt;', page)

    def test_disagreement(self):
        rows = sample()
        rows[0].update(oracle={'kind': 'trap', 'diagnostic': '<script>oops</script>'}, agrees=False)
        ok, page = self.render(rows, outcome='failure')
        self.assertFalse(ok)
        self.assertIn('Disagreement observed', page)
        self.assertIn('<th>Total</th><td>5</td><td>4</td><td>1</td><td>0</td>', page)
        self.assertIn('i32.extend8_s · case 1', page)
        self.assertIn('&lt;script&gt;oops', page)
        self.assertNotIn('<script>', page)

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
                ok, page = self.render(data, **kwargs)
                self.assertFalse(ok)
                self.assertIn('Run incomplete or failed', page)
                self.assertNotIn('Disagreement details', page)
