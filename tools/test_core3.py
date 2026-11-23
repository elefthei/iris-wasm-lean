import unittest

from core3 import (FIXTURE_REV, SIGNEXT, SPEC_REV, check_request, compare_pair, expected_command,
                   matches_expected, parse_oracle, parse_signext_rows, signext_fuzz_batches,
                   unwire_name, wire_name, wire_reason, wire_reply)


def value(t, n):
    return {"type": t, "value": str(n)}


def returned(*values):
    return {"kind": "return", "values": list(values)}


def expects(*values):
    return {"type": "assert_return", "expected": list(values)}


class ComparisonTests(unittest.TestCase):
    def test_signed_zero_disagrees(self):
        for t, negative_zero in [("f32", 1 << 31), ("f64", 1 << 63)]:
            positive, negative = returned(value(t, 0)), returned(value(t, negative_zero))
            self.assertFalse(compare_pair({"type": "action"}, positive, negative))
            self.assertFalse(compare_pair(expects(*positive["values"]), positive, negative))

    def test_arithmetic_nan_rejects_signaling_and_infinity(self):
        for t, inf, quiet in [("f32", 0x7f800000, 1 << 22), ("f64", 0x7ff0000000000000, 1 << 51)]:
            expected = expects(value(t, "nan:arithmetic"))
            canonical = returned(value(t, inf | quiet))
            arithmetic = returned(value(t, inf | quiet | 0x123))
            self.assertTrue(matches_expected(expected, arithmetic))
            self.assertFalse(compare_pair(expected, canonical, arithmetic))  # no operation evidence
            for n in (inf, inf | 1, quiet):
                self.assertFalse(matches_expected(expected, returned(value(t, n))))
            self.assertFalse(matches_expected(expects(value(t, "nan:canonical")), arithmetic))
            self.assertFalse(matches_expected(expects(value(t, inf | quiet | 0x124)), arithmetic))

    def test_scalar_choice_needs_actual_operands_and_module(self):
        # f32.wast:51 `add(-0, -nan)` permits either sign, not arbitrary payloads.
        digest = "b4d93174c7a944c6e5c8b3a6dbf9d958573886aa5b8359ecffeaad6630115a11"
        zero = value("f32", 1 << 31)
        pos, neg = value("f32", 0x7fc00000), value("f32", 0xffc00000)
        quiet, signaling = value("f32", 0x7fc00001), value("f32", 0x7f800001)
        for base in [expects(value("f32", "nan:arithmetic")), {"type": "action", "expected": []}]:
            def predicate(arg, module=digest):
                cmd = {**base, "line": 51, "action": {"type": "invoke", "field": "add", "args": [zero, arg]}}
                return expected_command(cmd, SPEC_REV, "f32.json", module_sha256=module)
            self.assertTrue(compare_pair(predicate(neg), returned(pos), returned(neg)))
            self.assertFalse(compare_pair(predicate(neg), returned(pos), returned(quiet)))
            self.assertTrue(compare_pair(predicate(signaling), returned(pos), returned(quiet)))
            self.assertFalse(compare_pair(predicate(signaling), returned(pos), returned(quiet), allow_choices=False))
            self.assertFalse(compare_pair(predicate(zero), returned(pos), returned(neg)))
            self.assertFalse(compare_pair(predicate(neg, "different module"), returned(pos), returned(neg)))
            self.assertFalse(compare_pair(predicate(neg), returned(pos, zero), returned(neg, neg)))

    def test_negated_literal_nan_has_one_sign(self):
        def vec(n):
            return {"type": "v128", "lane_type": "f64", "value": [str(n), "13830554455654793216"]}
        cmd = {**expects(vec("nan:canonical")), "line": 5297,
               "action": {"type": "invoke", "field": "f64x2_neg_canon", "args": []}}
        pred = expected_command(cmd, SPEC_REV, "simd/simd_f64x2_arith.json", module_sha256=
                                "8fe6609d066a3d4a168ad7452322a0a331b9fc17b36adc8d021c188f94c0a85e")
        pos, neg = returned(vec(0x7ff8000000000000)), returned(vec(0xfff8000000000000))
        self.assertTrue(compare_pair(pred, neg, neg))
        self.assertFalse(compare_pair(pred, pos, neg))
        self.assertFalse(compare_pair(pred, pos, pos))

    def test_identical_unexpected_traps_fail(self):
        trap = {"kind": "trap", "diagnostic": "unreachable"}
        for command in [expects(), {"type": "action"}, {"type": "assert_trap", "text": "integer overflow"}]:
            self.assertFalse(matches_expected(command, trap))
            self.assertFalse(compare_pair(command, trap, trap))
        self.assertFalse(compare_pair({"type": "assert_trap", "text": "out of bounds"},
                                     {"kind": "trap", "diagnostic": "out of bounds memory access"},
                                     {"kind": "trap", "diagnostic": "out of bounds table access"}))
        unknown = {"kind": "trap", "diagnostic": "out of bounds host buffer"}
        self.assertFalse(compare_pair({"type": "assert_trap", "text": "out of bounds"}, unknown, unknown))
        for text, diagnostic in [
            ("undefined element", "undefined element -1"), ("unreachable", "unreachable executed"),
            ("cast failure", "cast failure, expected (ref $t) but got (ref i31)"),
            ("indirect call type mismatch", "indirect call type mismatch, expected $t but got $u"),
        ]:
            self.assertTrue(compare_pair({"type": "assert_trap", "text": text},
                                         {"kind": "trap", "diagnostic": diagnostic},
                                         {"kind": "trap", "diagnostic": text}))

    def test_vectors_lane_shapes_and_either_are_whole_results(self):
        def vector(lane, *xs):
            return {"type": "v128", "lane_type": lane, "value": list(map(str, xs))}
        mask = vector("f32", "nan:arithmetic", 0, 0, 0)
        chosen = returned(vector("i64", 0xffc00001, 0))
        other = vector("i32", -1, 1, 2, 3)
        alternatives = [mask, other]
        for command in [expects({"type": "either", "values": alternatives}),
                        {"type": "assert_return", "either": alternatives}]:
            self.assertTrue(matches_expected(command, chosen))
            self.assertTrue(matches_expected(command, returned(other)))
            self.assertFalse(compare_pair(command, chosen, returned(other)))  # fixed profile not established
            self.assertFalse(matches_expected(command, returned(vector("i32", 0xffc00001, 1, 0, 0))))
            self.assertFalse(matches_expected(command, returned()))
        self.assertTrue(compare_pair({"type": "action"}, chosen, returned(vector("i32", 0xffc00001, 0, 0, 0))))

    def test_references_use_kind_and_identity_relations_not_addresses(self):
        expected = expects({"type": "eqref"}, {"type": "arrayref"})
        a, b = value("arrayref", 0), value("arrayref", 83)
        self.assertTrue(compare_pair(expected, returned(a, a), returned(b, b)))
        self.assertFalse(compare_pair(expected, returned(a, a), returned(b, value("arrayref", 84))))
        self.assertFalse(compare_pair(expects({"type": "arrayref"}), returned(a), returned(b),
                                      prior_refs=[(value("arrayref", 3), b)]))
        for wrong in [value("externref", 0), value("funcref", 0), value("arrayref", "null")]:
            self.assertFalse(matches_expected(expected, returned(wrong, a)))
        self.assertTrue(matches_expected(expects({"type": "refnull"}), returned(value("funcref", "null"))))
        self.assertFalse(matches_expected(expects(value("externref", 1)), returned(value("externref", 2))))
        self.assertFalse(matches_expected(expects(value("anyref", 0)), returned(a)))  # gc/extern:56 ref.host 0
        self.assertTrue(matches_expected(expects(value("anyref", 0)), returned(value("anyref", 0))))
        self.assertFalse(compare_pair({"type": "action"}, returned(a), returned(value("arrayref", 84)),
                                      prior_refs=[(a, b)]))
        self.assertFalse(compare_pair(expects({"type": "either", "values": [{"type": "arrayref"}, {"type": "structref"}]}),
                                      returned(a), returned(value("structref", 83)), prior_refs=[(a, b)]))
        for abstract in [value("eqref", 1), value("i31ref", 1 << 31)]:
            with self.assertRaises(ValueError):
                matches_expected({"type": "action"}, returned(abstract))

    def test_grow_then_size_uses_each_sessions_observed_result(self):
        trials = [
            ("memory_grow64", 50, 105, 1 << 48, "9d189d2f2ed27c25be2fc8cbed0338ffe9bb652c6825c343920207271aff102b"),
            ("table_grow64", 23, 46, (1 << 64) - 1, "5639ddab7a69b555767b241b8da24915614a78d69e19c9925c9a7bd971562185"),
        ]
        for name, target, line, grown, digest in trials:
            script = f"memory64/{name}.json"
            old, fail, new = (value("i64", n) for n in [1, -1, grown])
            def pred(n, field, args, either, prev):
                cmd = {**expects({"type": "either", "values": either}), "line": n,
                       "action": {"type": "invoke", "field": field, "args": args}}
                return expected_command(cmd, SPEC_REV, script, previous=prev, module_sha256=digest)
            def row(ordinal, line, left, right):
                return {"id": ["deployed", script, ordinal, line], "bytes_sha256": digest,
                        "dependencies": {lane: {"target": target} for lane in ("lean", "oracle")},
                        "lean": returned(left), "lean_passed": True, "oracle": returned(right), "oracle_passed": True}
            initial = row(target + 2, line - 1, old, old)
            grow = pred(line, "grow", [value("i64", grown - 1)], [fail, old], initial)
            self.assertTrue(compare_pair(grow, returned(old), returned(fail)))
            previous = row(target + 3, line, old, fail)
            size = pred(line + 3, "size", [], [old, new], previous)
            self.assertTrue(compare_pair(size, returned(new), returned(old)))
            self.assertFalse(compare_pair(size, returned(old), returned(old)))
            self.assertFalse(compare_pair(size, returned(new), returned(new)))
            self.assertFalse(compare_pair(pred(line + 3, "size", [], [old, new], None), returned(old), returned(old)))
            previous["dependencies"]["oracle"]["target"] -= 1
            self.assertFalse(compare_pair(pred(line + 3, "size", [], [old, new], previous), returned(new), returned(old)))

    def test_historical_funcref_payload_is_not_a_heap_address(self):
        cmd = {**expects(value("funcref", 0)), "line": 1254, "action": {"field": "meet-funcref-1"}}
        result = returned(value("funcref", 701))
        known = expected_command(cmd, FIXTURE_REV, "core/br_table.json")
        self.assertTrue(matches_expected(known, result))
        self.assertFalse(matches_expected(known, returned(value("funcref", "null"))))
        for revision, script in [(SPEC_REV, "core/br_table.json"), (FIXTURE_REV, "other/br_table.json")]:
            with self.assertRaises(ValueError):
                matches_expected(expected_command(cmd, revision, script), result)

    def test_rejection_requires_precise_lean_phase(self):
        invalid = {"type": "assert_invalid"}
        self.assertTrue(compare_pair(invalid, {"kind": "invalid"}, {"kind": "rejected"}))
        self.assertFalse(compare_pair(invalid, {"kind": "malformed"}, {"kind": "rejected"}))
        self.assertFalse(compare_pair({"type": "assert_exception"}, {"kind": "exception", "handle": 4},
                                     {"kind": "trap", "diagnostic": "uncaught exception"}))


class SignextFuzzTests(unittest.TestCase):
    def test_seed_replays_across_partial_batches(self):
        exports = SIGNEXT["i64"][1]

        def collect(seed, count):
            by_export = {e.field: [] for e in exports}
            for _, _, cases in signext_fuzz_batches("i64", exports, count, seed):
                for c in cases.values():
                    action = c["action"]
                    by_export[action["field"]].append(action["args"][0])
            return by_export

        run = collect(17, 35)
        self.assertEqual(run, collect(17, 35))
        self.assertNotEqual(run, collect(18, 35))
        longer = collect(17, 40)
        for e in exports:
            self.assertEqual(len(run[e.field]), 35)
            self.assertEqual(run[e.field], longer[e.field][:35])

    def test_expected_bits_and_sign_boundaries(self):
        for width, (_, exports) in SIGNEXT.items():
            size = {"i32": 4, "i64": 8}[width]
            for _, batch, cases in signext_fuzz_batches(width, exports, 32, 0):
                for e in batch:
                    kept = {"extend8_s": 1, "extend16_s": 2, "extend32_s": 4}[e.field]
                    seen = set()
                    for i in e.ordinals:
                        c = cases[i]
                        n = int(c["action"]["args"][0]["value"])
                        low = n.to_bytes(size, "little")[:kept]
                        signed = int.from_bytes(low, "little", signed=True)
                        seen.add(signed)
                        want = int.from_bytes(signed.to_bytes(size, "little", signed=True), "little")
                        self.assertEqual(c["expected"], [value(width, want)])
                    sign = 1 << (8 * kept - 1)
                    self.assertTrue({sign - 1, -sign, -sign + 1, -1, 0, 1} <= seen)


class WireTests(unittest.TestCase):
    def test_signext_rows_require_each_ordered_ordinal(self):
        first = '[226,{"type":"i64","value":"18446744073709518848"}]\n'
        last = '[233,{"type":"i64","value":"32768"}]\n'
        self.assertEqual(parse_signext_rows(first + last, [226, 233])[233], value("i64", 32768))
        for raw in (first, first + first, last + first, first + last + "\n", first + last + last,
                    first + last.replace("32768", "-1"), first + last.replace("32768", "032768"),
                    first + last.replace('"value":', '"value":"0","value":')):
            with self.subTest(raw=raw), self.assertRaises(ValueError):
                parse_signext_rows(raw, [226, 233])

    def test_requests_never_deliver_the_expected_answer_to_an_engine(self):
        invoke = {"type": "invoke", "field": "add", "args": [value("i32", 1), value("i32", 1)]}
        self.assertEqual(check_request(invoke), "invoke")
        for invalid in [{**invoke, "expected": [value("i32", 2)]}, {**invoke, "args": ["1", "1"]},
                        {"type": "module", "bytes": "0"}, {"type": "decode", "bytes": "00 ff"}]:
            with self.assertRaises(ValueError):
                check_request(invalid)

    def test_unencodable_reference_does_not_disable_the_oracle_session(self):
        policy = {"wire": {"values": "no native reference token"}}
        invoke = {"type": "invoke", "field": "f", "args": [value("funcref", 1)]}
        self.assertEqual(wire_reason(policy, invoke, "I0"), policy["wire"]["values"])
        self.assertIsNone(wire_reason(policy, {**invoke, "args": [value("funcref", "null")]}, "I0"))
        with self.assertRaises(ValueError):
            wire_reason(policy, {**invoke, "args": [value("funcref", "corrupt")]}, "I0")

    def test_eager_link_or_start_failure_is_not_validation_evidence(self):
        for message, kind in [("unknown import", "unlinkable"), ("data segment out of bounds", "trap"),
                              ("[trap] unreachable", "trap")]:
            observation = parse_oracle(f"Error: {message} ()", loading=True)
            self.assertEqual(observation["kind"], kind)
            self.assertFalse(compare_pair({"type": "assert_invalid"}, {"kind": "invalid"}, observation))

    def test_utf8_tokens(self):
        for name in ["", "add", "$I1", "say hello\n", "λ😀\\x00"]:
            self.assertEqual(unwire_name(wire_name(name)), name)
        self.assertEqual(wire_name("λ"), r"\xce\xbb")
        for token in [r"\xff", r"\xa", r"\x00\x41"]:
            with self.assertRaises(ValueError):
                unwire_name(token)

    def test_lossless_framing(self):
        for response in [returned(), returned(value("i32", 2), value("f32", 1 << 31)),
                         returned(value("externref", "null")), {"kind": "trap", "diagnostic": "unreachable"},
                         {"kind": "exhaustion"}]:
            self.assertEqual(parse_oracle(wire_reply(response) + "\n"), response)
        self.assertEqual(parse_oracle("Error: [trap] uncaught exception ()"), {"kind": "exception"})
        for bad in ["", "Result: 1", "Result: 1.5:f32", "Result: 4294967296:i32", "Result: null:i32",
                    "Result: <Empty Stack>\nError: unknown ()", "Error: memory allocation failed ()"]:
            with self.assertRaises(ValueError):
                parse_oracle(bad)
        with self.assertRaises(ValueError):
            parse_oracle("Error: memory allocation failed ()", loading=True)


if __name__ == "__main__":
    unittest.main()
