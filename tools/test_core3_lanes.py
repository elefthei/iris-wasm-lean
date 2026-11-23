import json
from collections import Counter
from hashlib import sha256
from io import StringIO
from pathlib import Path
from tempfile import TemporaryDirectory
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from core3 import OracleHistory, ROOT, feature_witness, policy_reason, request_for, run_script, wire_reason


class LaneTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.policy = json.loads((ROOT / 'WasmTest/Core3/wasm3-exclusions.json').read_bytes())

    def test_negative_module_request_has_no_expected_answer(self):
        with TemporaryDirectory() as d:
            directory = Path(d)
            (directory / 'bad.wasm').write_bytes(b'not Wasm')
            for assertion, phase in [('assert_malformed', 'decode'), ('assert_invalid', 'validate'),
                                     ('assert_unlinkable', 'module'), ('assert_uninstantiable', 'module')]:
                req, frontend = request_for({'type': assertion, 'line': 7, 'filename': 'bad.wasm',
                                             'module_type': 'binary', 'text': 'an expected diagnostic'},
                                            directory, directory)
                self.assertIsNone(frontend)
                self.assertEqual(req, {'type': phase, 'bytes': b'not Wasm'.hex()})
            with self.assertRaises(ValueError):
                request_for({'type': 'assert_malformed', 'module_type': 'text', 'filename': 'missing.wat'},
                            directory, directory)

    def setUp(self):
        self.history = OracleHistory()
        self.modules = {}

    def module(self, n, *, imports=(), writes=False, initializes=False):
        data = f"module {n}".encode()
        self.modules[n] = f"{n}.wasm", sha256(data).hexdigest(), {
            "imports": set(imports), "writes": writes, "initializes": initializes, "reason": None}

    def publish(self, n, req, *, success=True, issue=None, assertion=None):
        selected, inherited = self.history.select(req, n, self.modules)
        self.history.advance({"type": assertion or req["type"]}, req, n, selected,
                             success=success, issue=issue or inherited)
        return selected

    def test_only_ordinary_success_rebinds_default_definition_instance_or_registry(self):
        h = self.history
        self.module(1)
        self.publish(1, {"type": "module", "name": "m"})
        self.publish(2, {"type": "register", "as": "r"})
        self.module(3)
        self.publish(3, {"type": "module_definition", "name": "d"})
        for n, (op, success, assertion) in enumerate([
                ("module", False, None), ("module_definition", False, None),
                ("module", True, "assert_unlinkable"), ("module", False, "assert_uninstantiable")], 4):
            self.module(n)
            self.publish(n, {"type": op, "name": "m"}, success=success, assertion=assertion)
        self.assertEqual(h.instances, {None: 1, "m": 1})
        self.assertEqual(h.definitions, {None: 3, "m": 1, "d": 3})
        self.assertEqual(h.registry, {"r": 1})
        selected = self.publish(8, {"type": "module_instance", "instance": "i"})
        self.assertEqual((selected["source"], selected["bytes_sha256"]), (3, self.modules[3][1]))
        self.assertEqual(h.route({"type": "module_instance"}, 8, selected),
                         {"type": "module_instance", "module": "cmd3", "instance": "cmd8"})
        self.publish(9, {"type": "module_instance", "module": "m"}, success=False)
        self.publish(10, {"type": "register", "as": "r"}, success=False)
        self.assertEqual((h.instances[None], h.definitions[None], h.registry["r"]), (8, 3, 1))
        action = {"type": "get", "field": "g"}
        selected, issue = h.select(action, 11, self.modules)
        self.assertIsNone(issue)
        self.assertEqual(h.route(action, 11, selected), {**action, "module": "cmd8"})

    def test_excluded_instance_shadows_only_its_binding_and_aliases(self):
        h = self.history
        self.module(1)
        self.publish(1, {"type": "module", "name": "good"})
        self.publish(2, {"type": "register", "as": "old"})
        self.module(3)
        excluded = ("excluded", "no SIMD")
        self.publish(3, {"type": "module", "name": "other"}, issue=excluded)
        self.publish(4, {"type": "register", "as": "new"})
        self.module(5, imports=["new", "old"])
        selected, issue = h.select({"type": "module"}, 5, self.modules)
        self.assertEqual((selected["imports"], issue), ({"new": 3, "old": 1}, excluded))
        self.assertEqual(h.select({"type": "get"}, 6, self.modules)[1], excluded)
        self.assertIsNone(h.select({"type": "get", "module": "good"}, 6, self.modules)[1])
        self.assertTrue(h.registration_problem("second-name", 1))
        self.assertIsNone(h.registration_problem("old", 1))

    def test_failed_start_and_mismatched_writes_block_aliases_not_siblings(self):
        for op in ("module", "invoke"):
            with self.subTest(op=op):
                h = self.history = OracleHistory()
                self.module(1, writes=True)
                self.publish(1, {"type": "module_definition"})
                self.publish(2, {"type": "module_instance", "instance": "first"})
                self.publish(3, {"type": "module_instance", "instance": "second"})
                self.publish(4, {"type": "register", "name": "first", "as": "r"})
                self.module(5, imports=["r"], initializes=True, writes=True)
                start = self.publish(5, {"type": "module", "name": "alias"})
                get = {"type": "get", "module": "alias"}
                if op == "module":
                    selected = start
                else:
                    selected, _ = h.select({"type": "invoke", "module": "first"}, 6, self.modules)
                cause = ("blocked", "unpaired write before trap")
                if op == "module":
                    h.effects(op, 6, {"lean": selected}, self.modules, {"lean": {"kind": "unlinkable"}}, cause)
                    self.assertIsNone(h.select(get, 7, self.modules)[1])
                traps = {lane: {"kind": "trap", "diagnostic": "unreachable"} for lane in ("lean", "oracle")}
                h.effects(op, 6, dict.fromkeys(traps, selected), self.modules, traps, None)
                self.assertIsNone(h.select(get, 7, self.modules)[1])
                h.effects(op, 6, {"lean": selected}, self.modules, {"lean": {"kind": "trap"}}, cause)
                self.assertEqual(h.select(get, 7, self.modules)[1], cause)
                self.assertEqual(h.select({**get, "module": "first"}, 8, self.modules)[1], cause)
                self.assertIsNone(h.select({**get, "module": "second"}, 8, self.modules)[1])

    def test_taint_follows_references_written_by_an_earlier_paired_call(self):
        h = self.history
        for n in (1, 2, 3):
            self.module(n, writes=True)
            self.publish(n, {"type": "module", "name": str(n)})
        for n in (1, 2):
            self.publish(n + 3, {"type": "register", "name": str(n), "as": str(n)})
        self.module(6, imports=["1", "2"], writes=True)
        self.publish(6, {"type": "module", "name": "bridge"})
        write, _ = h.select({"type": "invoke", "module": "bridge"}, 7, self.modules)
        result = {"kind": "return", "values": []}
        h.effects("invoke", 7, dict.fromkeys(("lean", "oracle"), write), self.modules,
                  dict.fromkeys(("lean", "oracle"), result), None)
        left, _ = h.select({"type": "invoke", "module": "1"}, 8, self.modules)
        cause = ("excluded", "mutation skipped on oracle")
        h.effects("invoke", 8, {"lean": left}, self.modules, {"lean": result}, cause)
        self.assertEqual(h.select({"type": "get", "module": "2"}, 9, self.modules)[1], cause)
        self.assertIsNone(h.select({"type": "get", "module": "3"}, 9, self.modules)[1])

    def test_unavailable_sessions_never_produce_a_pair_or_sent_request(self):
        with TemporaryDirectory() as d:
            root = Path(d)
            data = bytes.fromhex("0061736d01000000")
            (root / "empty.wasm").write_bytes(data)
            rel = Path("empty.json")
            script = ("witnesses", "rev", rel, root / rel,
                      [{"type": "module", "line": 1, "filename": "empty.wasm"}])
            args = SimpleNamespace(lean=root / "absent", wasm3=root / "absent", timeout=1)
            records, mismatches, errors = StringIO(), StringIO(), []
            with patch("core3.RESULTS", root):
                run_script(script, args, self.policy, None, False, records, mismatches, Counter(), errors)
            row = json.loads(records.getvalue())
            self.assertNotIn("agrees", row)
            self.assertEqual(len(row["infrastructure"]), 2)
            self.assertEqual(row["bytes_sha256"], sha256(data).hexdigest())
            replay = json.loads((root / "sessions/witnesses/empty/requests.jsonl").read_bytes())
            self.assertEqual(replay["request"]["bytes"], data.hex())
            self.assertEqual((replay["sent_overrides"], replay["sessions_reset"]), ({}, []))
            self.assertEqual((mismatches.getvalue(), errors), ("", []))

    def test_witness_labels_require_an_actual_action(self):
        script = Path('multi-memory/memory_copy1.json')
        self.assertIsNone(feature_witness(script, {'type': 'module'}))
        self.assertIsNone(feature_witness(script, {'type': 'assert_invalid'}))
        self.assertEqual(feature_witness(script, {'action': {'type': 'invoke', 'field': 'copy'}}), 'multi-memory')

    def test_high_memory_exclusion_is_specific(self):
        rel = Path('witnesses.json')
        self.assertTrue(policy_reason(self.policy, 'witnesses', rel,
                                      {'type': 'module_instance', 'instance': 'wide_instance'}, None))
        self.assertIsNone(policy_reason(self.policy, 'witnesses', rel,
                                        {'type': 'module_instance', 'instance': 'second'}, None))
        self.assertIsNone(wire_reason(self.policy, {'type': 'invoke', 'args': [], 'field': ''}, 'I7'))
        self.assertTrue(wire_reason(self.policy, {'type': 'invoke', 'args': [], 'field': '\x00a'}, 'I7'))
