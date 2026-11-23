"""Scalar numeric bodies, in WebAssembly binary opcode order."""

from parity_model import Op, abi, get


TO_FLOAT = {"f32": b"\xbe", "f64": b"\xbf"}
TO_BITS = {"f32": b"\xbc", "f64": b"\xbd"}


def scalar_ops():
    # XOR exposes every literal bit at the ABI, including the sign and NaN payload.
    for code, (t, literal) in enumerate((
        ("i32", b"\xaf\x7f"), ("i64", b"\x81\x80\x80\x80\x10"),
        ("f32", bytes.fromhex("2143c5ff")), ("f64", bytes.fromhex("21436587a9cbf8ff")),
    ), 0x41):
        bits = abi(t)
        xor = b"\x73" if bits == "i32" else b"\x85"
        body = get(0) + bytes([code]) + literal + TO_BITS.get(t, b"") + xor
        yield Op(f"{t}.const", "scalar constant", (bits,), bits, body)

    def operation(code, t, name, family, params, result, nan=False):
        args = b"".join(get(i) + TO_FLOAT.get(p, b"") for i, p in enumerate(params))
        return Op(f"{t}.{name}", family, params, result,
                  args + code + TO_BITS.get(result, b""), nan_choices=nan)

    groups = (
        (0x45, "i32", "integer comparison", "eqz eq ne lt_s lt_u gt_s gt_u le_s le_u ge_s ge_u", 1, "i32"),
        (0x50, "i64", "integer comparison", "eqz eq ne lt_s lt_u gt_s gt_u le_s le_u ge_s ge_u", 1, "i32"),
        (0x5b, "f32", "float comparison", "eq ne lt gt le ge", 0, "i32"),
        (0x61, "f64", "float comparison", "eq ne lt gt le ge", 0, "i32"),
    )
    ints = "clz ctz popcnt add sub mul div_s div_u rem_s rem_u and or xor shl shr_s shr_u rotl rotr"
    floats = "abs neg ceil floor trunc nearest sqrt add sub mul div min max copysign"
    for start, t, family, names, unary_count, result in (*groups,
        (0x67, "i32", "integer arithmetic", ints, 3, "i32"),
        (0x79, "i64", "integer arithmetic", ints, 3, "i64"),
        (0x8b, "f32", "float arithmetic", floats, 7, "f32"),
        (0x99, "f64", "float arithmetic", floats, 7, "f64"),
    ):
        for i, name in enumerate(names.split()):
            params = (t,) if i < unary_count else (t, t)
            choices = family == "float arithmetic" and name not in ("abs", "neg", "copysign")
            yield operation(bytes([start + i]), t, name, family, params, result, choices)

    for start, dst, src, names in (
        (0xa7, "i32", "i64", "wrap_i64"),
        (0xa8, "i32", "f32", "trunc_f32_s trunc_f32_u"),
        (0xaa, "i32", "f64", "trunc_f64_s trunc_f64_u"),
        (0xac, "i64", "i32", "extend_i32_s extend_i32_u"),
        (0xae, "i64", "f32", "trunc_f32_s trunc_f32_u"),
        (0xb0, "i64", "f64", "trunc_f64_s trunc_f64_u"),
        (0xb2, "f32", "i32", "convert_i32_s convert_i32_u"),
        (0xb4, "f32", "i64", "convert_i64_s convert_i64_u"),
        (0xb6, "f32", "f64", "demote_f64"),
        (0xb7, "f64", "i32", "convert_i32_s convert_i32_u"),
        (0xb9, "f64", "i64", "convert_i64_s convert_i64_u"),
        (0xbb, "f64", "f32", "promote_f32"),
        (0xbc, "i32", "f32", "reinterpret_f32"),
        (0xbd, "i64", "f64", "reinterpret_f64"),
        (0xbe, "f32", "i32", "reinterpret_i32"),
        (0xbf, "f64", "i64", "reinterpret_i64"),
        (0xc0, "i32", "i32", "extend8_s extend16_s"),
        (0xc2, "i64", "i64", "extend8_s extend16_s extend32_s"),
    ):
        for code, name in enumerate(names.split(), start):
            family = "sign extension" if code >= 0xc0 else "scalar conversion"
            yield operation(bytes([code]), dst, name, family, (src,), dst, code in (0xb6, 0xbb))

    for sub in range(8):
        dst = ("i32", "i64")[sub // 4]
        src = ("f32", "f64")[sub // 2 % 2]
        sign = ("s", "u")[sub % 2]
        yield operation(bytes([0xfc, sub]), dst, f"trunc_sat_{src}_{sign}",
                        "saturating conversion", (src,), dst)
