"""Bounded control, variable and memory bodies for the fixed parity module."""

from parity_model import Op, abi, get
from parity_scalar import TO_BITS, TO_FLOAT


# In binary order from 0x28; the second column is the natural alignment exponent.
_ACCESSES = (
    ("i32.load", 2), ("i64.load", 3), ("f32.load", 2), ("f64.load", 3),
    ("i32.load8_s", 0), ("i32.load8_u", 0), ("i32.load16_s", 1), ("i32.load16_u", 1),
    ("i64.load8_s", 0), ("i64.load8_u", 0), ("i64.load16_s", 1), ("i64.load16_u", 1),
    ("i64.load32_s", 2), ("i64.load32_u", 2),
    ("i32.store", 2), ("i64.store", 3), ("f32.store", 2), ("f64.store", 3),
    ("i32.store8", 0), ("i32.store16", 1), ("i64.store8", 0), ("i64.store16", 1),
    ("i64.store32", 2),
)


def _access(opcode, index, align, offset):
    # Omit the index for memory 0; bit 6 introduces an explicit index for memory 1.
    return bytes((opcode, align | 64, index, offset) if index else (opcode, align, offset))


def _memory_ops(addr, index):
    wide = addr == "i64"
    suffix = f".memory{addr[1:]}.{index}" if wide or index else ""
    const, add, mask = (b"\x42", b"\x7c", b"\x83") if wide else (b"\x41", b"\x6a", b"\x71")
    # Base in 0..15. Independent addressing for setup/readback checks the target's offset 3.
    base = get(0)
    setup = base + const + b"\x0f" + mask + b"\x21\x00"
    at = base + const + b"\x03" + add
    for code, (name, align) in enumerate(_ACCESSES, 0x28):
        t = name.split(".")[0]
        bits = abi(t)
        i64 = bits == "i64"
        word_store, word_load, word_align = (0x37, 0x29, 3) if i64 else (0x36, 0x28, 2)
        value = get(1)
        complement = value + (b"\x42\x7f\x85" if i64 else b"\x41\x7f\x73")  # ~value
        store = _access(word_store, index, word_align, 0)
        # Write the other memory last so an implementation that aliases both memories cannot pass.
        other = at + complement + _access(word_store, 1 - index, word_align, 0)
        target = _access(code, index, align, 3)
        if code < 0x36:
            body = setup + at + value + store + other + base + target + TO_BITS.get(t, b"")
            yield Op(name + suffix, "memory load", (addr, t), t, body, memory64=wide)
        else:
            # A full-width readback exposes a packed store that overwrites neighboring bytes.
            body = (setup + at + complement + store + base + value + TO_FLOAT.get(t, b"") + target
                    + other + at + _access(word_load, index, word_align, 0))
            yield Op(name + suffix, "memory store", (addr, t), bits, body, memory64=wide)

    yield Op("memory.size" + suffix, "memory size/grow", (addr,), addr,
             base + bytes((0x3f, index)) + add, memory64=wide)
    # With min=max=1, delta 0 returns the size and delta 1 returns -1; neither changes state.
    yield Op("memory.grow" + suffix, "memory size/grow", (addr,), addr,
             base + const + b"\x01" + mask + bytes((0x40, index)), memory64=wide)


def stateful_ops():
    a, b, c = (get(i) for i in range(3))
    low2 = b"\x41\x03\x71"  # i32.const 3; i32.and
    inc = b"\x41\x01\x6a"
    xor1 = b"\x41\x01\x73"
    block = b"\x02\x7f"  # block (result i32)
    end = b"\x0b"

    for name, family, argc, body in (
        ("unreachable", "control", 2, a + low2 + b"\x04\x7f\x00\x05" + b + end),
        ("nop", "control", 2, a + b"\x01" + b + b"\x73"),
        ("drop", "parametric", 2, a + b + b"\x1a"),
        ("select", "parametric", 3, a + b + c + low2 + b"\x1b"),
        # Type 0 consumes/produces one i32. Preserve the operand underneath the block argument.
        ("block", "control", 2, a + b + b"\x02\x00" + inc + end + b"\x73"),
        # Carry a countdown through the type-0 loop label, incrementing local 1 exactly 1..4 times.
        ("loop", "control", 2, a + low2 + inc + b"\x03\x00\x41\x01\x6b\x22\x00"
         + b + inc + b"\x21\x01" + a + b"\x0d\x00" + end + b"\x1a" + b),
        ("if", "control", 2, a + low2 + b"\x04\x7f" + b + b"\x05" + b + xor1 + end),
        ("br", "control", 1, block * 2 + a + b"\x0c\x01" + end + xor1 + end),
        ("br_if", "control", 2, block + a + b + low2 + b"\x0d\x00" + xor1 + end),
        # The two table entries and default exit at different depths, with distinguishable results.
        ("br_table", "control", 2, block * 3 + a + b + low2 + b"\x0e\x02\x00\x01\x02"
         + end + xor1 + end + b"\x41\x02\x73" + end),
        ("return", "control", 1, block + b"\x41\x09" + a + b"\x0f" + end + xor1),
        ("call", "call", 2, a + b + b"\x10\x00\x73"),
        # Slot 0 invokes the real helper; slot 1 is the ordinary out-of-table Wasm trap.
        ("call_indirect", "call", 2, a + b + b"\x41\x01\x71\x11\x00\x00"),
        ("local.get", "local variable", 2, b),
        ("local.set", "local variable", 2, a + b + b"\x73\x21\x00" + a),
        ("local.tee", "local variable", 2, b + b"\x22\x00" + a + b"\x6a"),
        ("global.get", "global variable", 2, a + b"\x24\x00" + b + b"\x23\x00\x73"),
        ("global.set", "global variable", 2, a + b"\x24\x00" + b + b"\x24\x00\x23\x00"),
    ):
        yield Op(name, family, ("i32",) * argc, "i32", body)

    for addr in ("i32", "i64"):
        for index in (0, 1):
            yield from _memory_ops(addr, index)
