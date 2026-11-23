import unittest

from parity_scalar import scalar_ops


class ScalarCatalogTest(unittest.TestCase):
    def test_opcode_inventory_and_abi(self):
        ops = list(scalar_ops())
        codes = [bytes([n]) for n in range(0x41, 0xc5)] + [bytes([0xfc, n]) for n in range(8)]
        self.assertEqual(len(ops), len(codes))
        self.assertEqual(len({op.name for op in ops}), len(codes))
        for op, code in zip(ops, codes):
            with self.subTest(op=op.name):
                if op.name.endswith(".const"):
                    # ABI input masks the literal bits with XOR.
                    self.assertEqual(op.body[:3], b"\x20\x00" + code)
                    self.assertEqual(op.params, (op.result,))
                    self.assertEqual(op.body[-1], 0x73 if op.result == "i32" else 0x85)
                    continue
                prefix = b"".join(bytes([0x20, i]) + {"f32": b"\xbe", "f64": b"\xbf"}.get(t, b"")
                                  for i, t in enumerate(op.params))
                suffix = {"f32": b"\xbc", "f64": b"\xbd"}.get(op.result, b"")
                self.assertEqual(op.body, prefix + code + suffix)

    def test_cross_width_and_nan_policy(self):
        ops = {op.name: op for op in scalar_ops()}
        for name, params, result in (
            ("i64.eqz", ("i64",), "i32"), ("f32.le", ("f32", "f32"), "i32"),
            ("i32.trunc_sat_f64_u", ("f64",), "i32"), ("f64.convert_i64_s", ("i64",), "f64"),
            ("i64.extend32_s", ("i64",), "i64"), ("f32.demote_f64", ("f64",), "f32"),
        ):
            self.assertEqual((ops[name].params, ops[name].result), (params, result))
        names = "ceil floor trunc nearest sqrt add sub mul div min max".split()
        self.assertEqual({op.name for op in ops.values() if op.nan_choices},
                         {f"{t}.{n}" for t in ("f32", "f64") for n in names}
                         | {"f32.demote_f64", "f64.promote_f32"})
