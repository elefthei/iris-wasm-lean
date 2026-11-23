import unittest

from parity_model import Op
from parity_runtime import agrees, lean_observations, operands


def i32(bits):
    return {'type': 'i32', 'value': str(bits)}


def result(bits):
    return {'kind': 'return', 'values': [i32(bits)]}


class RuntimeParityTests(unittest.TestCase):
    def test_nan_choices_depend_on_operation_and_operands(self):
        op = Op('f32.sqrt', 'float arithmetic', ('f32',), 'f32', b'', nan_choices=True)
        qnan = 0x7fc00000
        # sqrt(-1) permits either sign of a canonical NaN, but not an arbitrary payload.
        self.assertTrue(agrees(op, [i32(0xbf800000)], result(qnan), result(qnan | 1 << 31)))
        self.assertFalse(agrees(op, [i32(0xbf800000)], result(qnan), result(qnan + 2)))
        self.assertTrue(agrees(op, [i32(qnan + 1)], result(qnan), result(qnan + 2)))
        self.assertFalse(agrees(op, [i32(qnan + 1)], result(0x7f800001), result(0x7f800001)))
        self.assertFalse(agrees(op, [i32(0x3f800000)], result(qnan), result(qnan | 1 << 31)))
        exact = Op('f32.abs', 'float arithmetic', ('f32',), 'f32', b'')
        self.assertFalse(agrees(exact, [i32(qnan + 1)], result(qnan), result(qnan + 1)))

    def test_trap_is_not_an_observation_failure(self):
        op = Op('unreachable', 'control', (), 'i32', b'\0')
        trap = {'kind': 'trap', 'diagnostic': 'unreachable'}
        self.assertTrue(agrees(op, [], {'kind': 'trap'}, trap))
        self.assertFalse(agrees(op, [], {'kind': 'error', 'diagnostic': 'no executable leaf'}, trap))
        self.assertFalse(agrees(op, [], result(0), trap))

    def test_replay_and_batch_framing(self):
        op = Op('i32.add', 'integer arithmetic', ('i32', 'i32'), 'i32', b'')
        xs = list(operands(op, 7, 29))
        self.assertEqual(xs, list(operands(op, 8, 29))[:7])
        self.assertNotEqual(xs, list(operands(op, 7, 30)))
        for raw in ('[[1,{"kind":"trap"}]]', '[[1,{"kind":"trap"}],[1,{"kind":"trap"}]]'):
            with self.assertRaises(ValueError):
                list(lean_observations(raw, 2))
