import unittest

from parity_stateful import stateful_ops


class StatefulCatalogTest(unittest.TestCase):
    def test_instruction_inventory(self):
        control = set("unreachable nop drop select block loop if br br_if br_table return call call_indirect "
                      "local.get local.set local.tee global.get global.set".split())
        types = ("i32", "i64", "f32", "f64")
        packed = [(t, n) for t in types[:2] for n in (8, 16, 32) if n < int(t[1:])]
        # Independent opcode inventory in the order of the scalar memory instructions, 0x28..0x40.
        memory = ([f"{t}.load" for t in types] + [f"{t}.load{n}_{sx}" for t, n in packed for sx in "su"]
                  + [f"{t}.store" for t in types] + [f"{t}.store{n}" for t, n in packed]
                  + ["memory.size", "memory.grow"])
        ops = list(stateful_ops())
        catalog = {op.name: op for op in ops}
        self.assertEqual(len(catalog), len(ops))
        expected = set(control)
        for suffix, width, index in (("", 32, 0), (".memory32.1", 32, 1),
                                     (".memory64.0", 64, 0), (".memory64.1", 64, 1)):
            for code, name in enumerate(memory, 0x28):
                expected.add(name + suffix)
                op = catalog[name + suffix]
                with self.subTest(op=op.name):
                    self.assertEqual(op.memory64, width == 64)
                    self.assertEqual(op.params[0], f"i{width}")
                    if code < 0x3f:
                        self.assertEqual(op.params[1], name[:3])
                        # The operation under test has offset 3; setup/readback use offset 0.
                        self.assertTrue(any(bytes((code, align | 64, 1, 3) if index else (code, align, 3))
                                            in op.body for align in range(4)))
                    else:
                        self.assertIn(bytes((code, index)), op.body)
        self.assertEqual(set(catalog), expected)
        self.assertFalse(any(op.nan_choices for op in ops))  # float memory traffic preserves bits

    def test_independent_memory_readback(self):
        ops = {op.name: op for op in stateful_ops()}
        body = ops["i64.store8.memory64.1"].body
        # Seed the whole word; store one byte; overwrite memory 0; read all 8 bytes of memory 1.
        prior = -1
        for instruction in ("37 43 01 00", "3c 40 01 03", "37 03 00", "29 43 01 00"):
            prior = body.index(bytes.fromhex(instruction), prior + 1)
        self.assertTrue(ops["f32.load"].body.endswith(bytes.fromhex("2a 02 03 bc")))
        self.assertIn(bytes.fromhex("be 38 42 01 03"), ops["f32.store.memory32.1"].body)
