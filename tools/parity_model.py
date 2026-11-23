"""Binary layout shared by the runtime parity targets and the Lean observer fixture."""

from dataclasses import dataclass


@dataclass(frozen=True)
class Op:
    name: str
    family: str
    params: tuple[str, ...]
    result: str
    body: bytes
    nan_choices: bool = False
    memory64: bool = False


def abi(t):
    return {'i32': 'i32', 'i64': 'i64', 'f32': 'i32', 'f64': 'i64'}[t]


def uleb(n):
    if n < 0:
        raise ValueError('negative unsigned LEB')
    out = bytearray()
    while n >= 128:
        out.append(0x80 | (n & 127))
        n >>= 7
    out.append(n)
    return bytes(out)


def get(i):
    return b'\x20' + uleb(i)


def sized(data):
    return uleb(len(data)) + data


def sized_body(op):
    return sized(b'\x00' + op.body + b'\x0b')


def module_bytes(op):
    # Type/function 0 is the helper (x => x + 1); type/function 1 is the test export.
    types = {'i32': 0x7f, 'i64': 0x7e}
    signature = b'\x60' + sized(bytes(types[abi(t)] for t in op.params)) + bytes((1, types[abi(op.result)]))
    mem = bytes((5 if op.memory64 else 1, 1, 1))  # min = max = one page
    sections = (
        (1, b'\x02\x60\x01\x7f\x01\x7f' + signature),
        (3, b'\x02\x00\x01'),                   # function type indices
        (4, b'\x01\x70\x01\x01\x01'),           # one funcref table, one slot
        (5, b'\x02' + mem + mem),                 # distinct memories at indices 0 and 1
        (6, b'\x01\x7f\x01\x41\x00\x0b'),       # mutable i32 global initialized to zero
        (7, b'\x01\x03run\x00\x01'),
        (9, b'\x01\x00\x41\x00\x0b\x01\x00'),   # table[0] = function 0
        (10, b'\x02' + sized(bytes.fromhex('00 20 00 41 01 6a 0b')) + sized_body(op)),
    )
    return b'\0asm\x01\0\0\0' + b''.join(bytes([i]) + sized(data) for i, data in sections)
