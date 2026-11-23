"""Prepare and exercise the pinned WebAssembly Core 3 conformance suites."""

import argparse
from collections import Counter
from contextlib import ExitStack
from fnmatch import fnmatchcase
from hashlib import sha256
import json
import os
from pathlib import Path
import random
import re
import select
import shlex
import shutil
import subprocess
import sys
from tempfile import TemporaryDirectory, mkdtemp
import time
from typing import NamedTuple


ROOT = Path(__file__).resolve().parents[1]
CACHE = ROOT / ".lake/core3"
SPEC = CACHE / "spec"
HARNESS = CACHE / "wasm3"
FIXTURES = HARNESS / "test/.spec-wg-3.0"
DEPLOYED = CACHE / "deployed/core"
SPEC_REV = "6fca707686ed4f36a1e30ec2ae7d3dd32b276704"
HARNESS_REV = "28ecb9af6d2040e474a70f7cb7f43666740141fb"
FIXTURE_REV = "d2b8c296df2e209acbdd0d901d14dd7085acd178"
CONVERTER_VERSION = "1.256.0"


def output(*args):
    return subprocess.check_output(args, text=True).strip()


def run(*args, **kwargs):
    subprocess.run(args, check=True, **kwargs)


def verify_checkout(path, rev):
    if (Path(output("git", "-C", path, "rev-parse", "--show-toplevel")) != path
            or output("git", "-C", path, "rev-parse", "HEAD") != rev):
        raise ValueError(f"{path}: expected independent checkout at {rev}")
    run("git", "-C", path, "diff", "--quiet", rev, "--")
    # These directories are immutable inputs, not build trees. Even ignored extra fixtures
    # would enter recursive discovery without changing HEAD or `git diff`.
    inputs = {SPEC_REV: ("test/core", "specification/wasm-3.0"), FIXTURE_REV: ("core",)}.get(rev)
    if inputs:
        extra = subprocess.check_output(["git", "-C", path, "ls-files", "--others", "-z", "--", *inputs])
        if extra:
            first = os.fsdecode(extra.split(b"\0", 1)[0])
            raise ValueError(f"{path}: untracked corpus input {first!r}")


def checkout(path, repo, rev):
    if path.exists():
        verify_checkout(path, rev)
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    with TemporaryDirectory(dir=path.parent) as tmp:
        tree = Path(tmp) / "tree"
        run("git", "init", "--quiet", tree)
        run("git", "-C", tree, "remote", "add", "origin", f"https://github.com/{repo}.git")
        run("git", "-C", tree, "fetch", "--depth=1", "origin", rev)
        run("git", "-C", tree, "checkout", "--quiet", "--detach", rev)
        verify_checkout(tree, rev)
        tree.rename(path)


def converter():
    tools = CACHE / "tools"
    local = tools / "bin/wasm-tools"
    expected = f"wasm-tools {CONVERTER_VERSION}"
    for exe in (shutil.which("wasm-tools"), local):
        if exe and Path(exe).is_file() and output(exe, "--version") == expected:
            return exe
    run("cargo", "install", "--locked", "--root", tools, "--version", CONVERTER_VERSION, "wasm-tools")
    if output(local, "--version") != expected:
        raise ValueError(f"{local}: expected {expected}")
    return local


def prepare():
    checkout(SPEC, "WebAssembly/spec", SPEC_REV)
    prepare_historical_source()
    checkout(HARNESS, "wasm3/wasm3", HARNESS_REV)
    checkout(FIXTURES, "wasm3/wasm-core-testsuite", FIXTURE_REV)
    if not any((FIXTURES / "core").rglob("*.json")):
        raise ValueError(f"empty converted suite at {FIXTURES}")
    run("make", "-C", SPEC / "interpreter")
    if not Path("/usr/bin/wasm3").is_file():
        import os
        build = HARNESS / "build"
        run("cmake", "-S", HARNESS, "-B", build, "-DBUILD_WASI=simple",
            "-DCMAKE_C_FLAGS=-Dd_m3HasTypedRefs=1", env={**os.environ, "CC": "clang"})
        run("cmake", "--build", build)
    convert_sources(converter())


def convert_sources(tool):
    core = SPEC / "test/core"
    sources = sorted(core.rglob("*.wast"))
    if not sources:
        raise ValueError(f"empty source suite at {core}")
    expected = set()
    failures = []
    for source in sources:
        directory = DEPLOYED / source.relative_to(core).with_suffix("")
        directory.mkdir(parents=True, exist_ok=True)
        script = directory / (source.stem + ".json")
        argv = [str(tool), "json-from-wast", "--wasm-dir", str(directory), "-o", str(script), str(source)]
        try:
            run(*argv, stderr=subprocess.PIPE)
        except subprocess.CalledProcessError as exc:
            script.unlink(missing_ok=True)
            diagnostic = exc.stderr.decode(errors="replace")
            sys.stderr.write(diagnostic)
            record = {"source": str(source.relative_to(core)), "sha256": sha256(source.read_bytes()).hexdigest(),
                      "revision": SPEC_REV, "wasm-tools": CONVERTER_VERSION, "argv": argv,
                      "exit": exc.returncode, "stderr": diagnostic}
            if record["source"] == "gc/type-subtyping.wast" and "type-subtyping.wast:958:32" in diagnostic:
                record["finding"] = ("The second supertype is syntactic: 1.2-syntax.types.spectec:120 and "
                                     "5.2-binary.types.spectec:Bsubtype admit a list. Subtype_ok imposes "
                                     "length <= 1 during validation (2.1-validation.types.spectec:149–156).")
            failures.append(record)
        expected.add(script)
    actual = set(DEPLOYED.rglob("*.json"))
    RESULTS.mkdir(parents=True, exist_ok=True)
    with (RESULTS / "conversion-failures.jsonl").open("w") as out:
        for finding in failures:
            dump_line(out, finding)
    if failures:
        raise ValueError(f"{len(failures)}/{len(sources)} source conversions failed: "
                         + ", ".join(f["source"] for f in failures))
    if actual != expected:
        raise ValueError(f"script inventory mismatch: {sorted(actual ^ expected)}")
    print(f"Prepared {len(expected)} deployed scripts; historical fixtures at {FIXTURES}")


SCALARS = {"i32": 32, "i64": 64, "f32": 32, "f64": 64}
LANES = {**SCALARS, "i8": 8, "i16": 16}
NULL_TYPES = {"refnull", "nullref", "nullfuncref", "nullexternref", "nullexnref"}
EQ_TYPES = {"i31ref", "structref", "arrayref"}
REF_TYPES = EQ_TYPES | {"externref", "funcref", "exnref", "anyref", "eqref"}
WIRE_REFS = {"externref", "funcref", "exnref"}
PROMPT = b"wasm3> "


def integer(value, signed=False):
    if type(value) not in (str, int) or not re.fullmatch(
            r"-?[0-9]+" if signed else r"[0-9]+", str(value)):
        raise ValueError(f"not a decimal integer: {value!r}")
    return int(value)


def bits(value, width):
    n = integer(value, signed=True)
    if not -(1 << (width - 1)) <= n < 1 << width:
        raise ValueError(f"value outside {width} bits: {value}")
    return n % (1 << width)


def vector_lanes(value):
    lane, lanes = value["lane_type"], value["value"]
    if lane not in LANES or not isinstance(lanes, list) or len(lanes) != 128 // LANES[lane]:
        raise ValueError(f"invalid v128 lanes: {value!r}")
    return lane, lanes


def concrete(value):
    """Canonical, lossless single-session key; a reference's handle is local."""
    if not isinstance(value, dict) or "type" not in value or "value" not in value:
        raise ValueError(f"incomplete typed value: {value!r}")
    if set(value) != ({"type", "lane_type", "value"} if value["type"] == "v128" else {"type", "value"}):
        raise ValueError(f"unexpected typed value fields: {value!r}")
    t, v = value["type"], value["value"]
    if t in SCALARS:
        return t, bits(v, SCALARS[t])
    if t == "v128":
        lane, lanes = vector_lanes(value)
        w = LANES[lane]
        return t, sum(bits(x, w) << (i * w) for i, x in enumerate(lanes))
    if t in REF_TYPES | NULL_TYPES and v == "null":
        return "refnull", None  # Core has only REF.NULL_ADDR
    if t in REF_TYPES - {"eqref"}:
        n = integer(v)
        if t == "i31ref" and n >= 1 << 31:
            raise ValueError(f"i31 payload exceeds 31 bits: {n}")
        return t, n
    raise ValueError(f"invalid concrete typed value: {value!r}")


def matches_scalar(t, pattern, actual):
    if pattern in ("nan:canonical", "nan:arithmetic"):
        if t not in ("f32", "f64"):
            raise ValueError(f"NaN pattern on {t}")
        canonical = 0x7fc00000 if t == "f32" else 0x7ff8000000000000
        magnitude = actual & ((1 << (LANES[t] - 1)) - 1)
        return (magnitude == canonical if pattern == "nan:canonical"
                else magnitude & canonical == canonical)
    return bits(pattern, LANES[t]) == actual


def matches_value(expected, value):
    if not isinstance(expected, dict) or "type" not in expected:
        raise ValueError(f"not a result pattern: {expected!r}")
    t = expected["type"]
    u, actual = concrete(value)
    fields = ({"type", "values"} if t == "either" else {"type", "lane_type", "value"} if t == "v128"
              else {"type"} if t in REF_TYPES | NULL_TYPES and "value" not in expected else {"type", "value"})
    if expected.keys() != fields:
        raise ValueError(f"unknown or missing pattern fields: {expected!r}")
    if t == "either":
        alternatives = expected["values"]
        if not isinstance(alternatives, list) or not alternatives:
            raise ValueError("expected nonempty 'either' alternatives")
        # An unknown alternative is bad fixture data even if another one matches.
        matched = False
        for p in alternatives:
            matched |= matches_value(p, value)
        return matched
    if t in SCALARS:
        return t == u and matches_scalar(t, expected["value"], actual)
    if t == "v128":
        lane, lanes = vector_lanes(expected)
        w = LANES[lane]
        return u == t and all(matches_scalar(lane, p, actual >> (i * w) & ((1 << w) - 1))
                              for i, p in enumerate(lanes))
    if t not in REF_TYPES | NULL_TYPES:
        raise ValueError(f"unknown expected value type {t}")
    if t in NULL_TYPES and expected.get("value", "null") != "null":
        raise ValueError(f"invalid null pattern: {expected!r}")
    if t in NULL_TYPES or expected.get("value") == "null":
        return u == "refnull"
    if "value" in expected:
        if t not in {"anyref", "externref"}:
            raise ValueError(f"no script identity literal for {t}")
        # (ref.host N) isn't an array/struct at session-local address N.
        return (u, actual) == (t, integer(expected["value"]))
    return t == u or (t in {"eqref", "anyref"} and u in EQ_TYPES)


TRAP_CLASSES = {
    "unreachable", "integer overflow", "integer divide by zero", "invalid conversion to integer",
    "out of bounds memory access", "out of bounds table access", "out of bounds array access",
    "undefined element", "uninitialized element", "indirect call type mismatch", "cast failure",
    "null reference", "null exception reference", "null function reference", "null structure reference",
    "null array reference", "null i31 reference",
}


def trap_class(message):
    # The reference interpreter adds an index or a dynamic type to these classes.
    if message == "unreachable executed":
        return "unreachable"
    message = re.sub(r"^(uninitialized element|undefined element) -?[0-9]+$", r"\1", message)
    return re.sub(r"^(indirect call type mismatch|cast failure), expected .+ but got .+$", r"\1", message)


# Byte identities of the pure scalar wrappers in the two pinned corpora. Export
# names alone are not evidence: even float_exprs reuses names for different code.
NAN_WRAPPERS = {
    "b4d93174c7a944c6e5c8b3a6dbf9d958573886aa5b8359ecffeaad6630115a11": "f32",
    "70ab4cf9db7d315ad1217f0b9d81df3cec9cbf43f51cd4f1acccdc54ff9c2c56": "f64",
    "1026f248eddb09365cfc0911b4a783e33faa33a33964a8a881cd8802d89dcd7a": "float_misc",
    "6aa9e500948684fdcbd3877042b1d72b3dc5c1a070afd27c1ea1b1916a5ac196": "conversions",
    "682a471eb483a41f6ff9da9b8111efb852ed12f9009fce89446193c7d2a05204": "add_zero",
    "32a47ac340f88ce1eec84fb609656aad6e1c306c134da3dc51b27fc5680f941a": "zero_sub",
    "880ee4b1b4c4fc2de44393ae2d7b4dcc2d367946f33f3f09e8d59fcd55515ba3": "sub_zero",
    "0afef02bac793f23ae9bc13a6a37e1b94d89c335f87fd1c2453fd0f931aea865": "mul_zero",
    "45d3aacaf24a9366589bfda0180ca86b7356a9536846d0fcf2d5233f2ee1caf5": "mul_one",
    "680df7c124ab2c8821de1b5d0e95d6c025be290821bd80ab26fc1c792b25e53a": "zero_div",
    "87fb2bae14c587d08de53a621f499fc2867515c324e30679d3e3e8e34ad587e6": "div_one",
    "d0991ed8df78eb0b269abf34896d282ce809996d2f063b4e0691db7d2c8576d8": "div_neg1",
    "9083798211bf1efcf28d81364df27767eb655ecf3562f583b25c47908be49cf3": "neg0_sub",
    "7e3efbc4be7dd0d229936016dffb4b8153f22438c2d5a47ffe94aa2719dc4980": "neg1_mul",
    "bf8cd56a6ca0823a7bfc93694996a2b2de86d9e0e0c6adca6bc5fc05fd31dfe2": "sub_self",
    "f2809fe9f3f37c2a13336d85897679c55753a3fafaf4fe7c5974075d1ab4fdf2": "div_self",
    "176ad8175f3706200dd201d5b0f52490f8e669a1d477fc2c0680d9a774fc4fdf": "div_0",
    "bb5281a9f27b0a5f4f3ab5306f518e8635e69185eccabbcd353f449176107fbf": "div_neg0",
    "74998f29087485f60bb73fa6ec5d000fcbcd0e159f8331dbb1e663e76679d69c": "promote_demote",
    "ad6d5bf8529c1eeff925b02e2b0b63e3f9d499826ffa42d1b28010bb9a2e8743": "add_neg",
    "df95bc180a360abe7ca5078043a4320f2afa83bd75c5cbb1e520992a765f10cc": "mul_sqrts",
    "88878dd5b122d178e7d17f48490aaf5a1186ff542b178ff25a937e263f243b6d": "div_sqrts",
}


def scalar_nan_result(action, wrapper):
    """For the identified body and operands, return its Core nans_N set, or no witness."""
    field, args = action["field"], action["args"]
    binary = {"add", "sub", "mul", "div", "min", "max"}
    if wrapper in {"f32", "f64"}:
        t = out = wrapper
        op = field
        if op not in binary | {"ceil", "floor", "nearest", "sqrt", "trunc"}:
            return None
    elif wrapper == "float_misc" and field == "f64.sqrt":
        t = out = "f64"
        op = "sqrt"
    elif wrapper == "conversions" and field in {"f32.demote_f64", "f64.promote_f32"}:
        out, t, op = field[:3], field[-3:], "convert"
    elif wrapper == "promote_demote" and field == "no_fold_promote_demote":
        t = out = "f32"
        op = "convert"
    elif field[:3] in {"f32", "f64"} and field[3:] == ".no_fold_" + wrapper:
        t = out = field[:3]
        op = wrapper
    else:
        return None
    if len(args) != 1 + (op in binary | {"mul_sqrts", "div_sqrts"}) or any(a["type"] != t for a in args):
        return None
    width = SCALARS[t]
    sign = 1 << (width - 1)
    inf = 0x7f800000 if t == "f32" else 0x7ff0000000000000
    canonical = inf | ((1 << 22) if t == "f32" else (1 << 51))
    xs = [concrete(a)[1] for a in args]
    mag = [x & (sign - 1) for x in xs]
    nan = any(m > inf for m in mag)
    # Invalid arithmetic without NaN inputs produces canonical NaNs only.
    if op in {"sqrt", "mul_sqrts", "div_sqrts"}:
        nan |= any(x > sign for x in xs)
    if op in {"mul", "mul_sqrts"}:
        nan |= 0 in mag and inf in mag
    elif op in {"div", "div_sqrts"}:
        nan |= mag[0] == mag[1] and mag[0] in {0, inf}
    elif op in {"add", "sub"}:
        nan |= mag == [inf, inf] and ((xs[0] == xs[1]) == (op == "sub"))
    elif op in {"mul_zero", "sub_self", "div_self", "add_neg"}:
        nan |= mag[0] == inf
    if op in {"zero_div", "div_0", "div_neg0", "div_self"}:
        nan |= mag[0] == 0
    if nan:
        return {"type": out, "value": "nan:arithmetic" if any(m > inf and m != canonical for m in mag)
                else "nan:canonical"}
    return None


# The deployed scripts, unlike wg-3.0, query the same object just before and
# after this optional grow. A second independent `either` would lose that fact.
GROW_TRIALS = {
    "memory64/memory_grow64.json": ("9d189d2f2ed27c25be2fc8cbed0338ffe9bb652c6825c343920207271aff102b",
                                    50, 105, 1 << 48),
    "memory64/table_grow64.json": ("5639ddab7a69b555767b241b8da24915614a78d69e19c9925c9a7bd971562185",
                                   23, 46, (1 << 64) - 1),
}


def grow_results(command, script, previous, digest):
    expected_digest, target, line, grown = GROW_TRIALS[script]
    growing = command["line"] == line
    if not growing and command["line"] != line + 3:
        return None
    field = "grow" if growing else "size"
    args = command["action"]["args"]
    if (digest != expected_digest or "module" in command["action"] or command["action"]["field"] != field or
            [concrete(a) for a in args] != ([("i64", grown - 1)] if growing else [])):
        raise ValueError(f"growth witness does not match {script}:{command['line']}")
    old, fail = {"type": "i64", "value": "1"}, {"type": "i64", "value": "-1"}
    results = {}
    prior_id = ["deployed", script, target + (2 if growing else 3), line - 1 if growing else line]
    for lane in ("lean", "oracle"):
        if not (previous and previous["id"] == prior_id and previous.get("bytes_sha256") == digest and
                previous.get("dependencies", {}).get(lane, {}).get("target") == target and
                previous.get(lane + "_passed")):
            continue
        obs = previous[lane]
        if obs["kind"] != "return" or len(obs["values"]) != 1:
            continue
        key = concrete(obs["values"][0])
        if growing and key == ("i64", 1):
            results[lane] = {"type": "either", "values": [old, fail]}
        elif not growing and key in {("i64", 1), ("i64", (1 << 64) - 1)}:
            results[lane] = {"type": "i64", "value": str(grown)} if key[1] == 1 else old
    return results


def expected_command(command, revision, script, *, previous=None, module_sha256=None):
    """Keep the source assertion; attach replayable tighter predicates only with evidence."""
    if "core_result" in command:
        raise ValueError("reserved field in script command: core_result")
    if command["type"] not in {"action", "assert_return"} or revision not in {FIXTURE_REV, SPEC_REV}:
        return command
    script = Path(script)
    action = command["action"]
    if action.get("type") == "invoke":
        if revision == SPEC_REV and str(script) in GROW_TRIALS and command["type"] == "assert_return":
            results = grow_results(command, str(script), previous, module_sha256)
            if results is not None:
                return {**command, "core_result": results}
        if module_sha256 in NAN_WRAPPERS:
            pattern = scalar_nan_result(action, NAN_WRAPPERS[module_sha256])
            if pattern:
                return {**command, "core_result": dict.fromkeys(("lean", "oracle"), pattern)}
        # simd_f64x2_arith.wast:5286–5287 negates a literal; unlike arithmetic
        # it flips the sign and preserves the payload, even on a NaN.
        if (action["field"] == "f64x2_neg_canon" and action["args"] == [] and module_sha256 in {
                "8fe6609d066a3d4a168ad7452322a0a331b9fc17b36adc8d021c188f94c0a85e",
                "a0b4fff73199fae7bc841ce14fc36387cdaa0d60725a1905449fdf47b1db286d"}):
            pattern = {"type": "v128", "lane_type": "f64", "value": [str(0xfff8000000000000), str(0xbff0000000000000)]}
            return {**command, "core_result": dict.fromkeys(("lean", "oracle"), pattern)}
    if (revision != FIXTURE_REV or command["type"] != "assert_return" or
            script.parent not in {Path("."), Path("core")}):
        return command
    # WebAssembly/spec@9d36019973201a19f9c9ebb0f10828b2fe2374aa/test/core:
    # br_table.wast:1253-1264 and select.wast:279 explicitly say `(ref.func)`,
    # not `(ref.func 0)`. The historical converter wrote the dummy payload "0".
    line = command["line"]
    if script.name == "br_table.json" and 1253 <= line <= 1264:
        field = f"meet-funcref-{1 + (line - 1253) // 3}"
    elif script.name == "select.json" and line == 279:
        field = "join-funcnull"
    else:
        return command
    if command["action"]["field"] != field or command.get("expected") != [{"type": "funcref", "value": "0"}]:
        raise ValueError(f"historical fixture drift at {script}:{line}")
    return {**command, "expected": [{"type": "funcref"}]}


def expected_values(command):
    # wast2json uses command-level `either` for a single result; wasm-tools
    # uses an `either` node inside `expected`. Neither permits mixing lanes.
    if "either" in command:
        if "expected" in command:
            raise ValueError("assert_return cannot specify both either and expected")
        return [{"type": "either", "values": command["either"]}]
    if not isinstance(command["expected"], list):
        raise ValueError("assert_return expected must be a list")
    return command["expected"]


def matches_expected(command, observation, *, lane=None):
    """Verdict for one engine, independent of the other engine's answer."""
    t, k = command["type"], observation["kind"]
    if k == "return":
        if not isinstance(observation["values"], list):
            raise ValueError("return values must be a list")
        if "core_result" in command:
            # A grow result in one engine never predicts the other engine's state.
            allowed = command["core_result"].get(lane)
            if allowed is None or len(observation["values"]) != 1 or not matches_value(allowed, observation["values"][0]):
                return False
        if t == "action":
            # Historical WABT sometimes writes expected:[] even on a plain
            # invoke. Script Action demands a normal return, not an assertion.
            for value in observation["values"]:
                concrete(value)
    if t == "assert_return":
        expected = expected_values(command)
        return (k == "return" and len(expected) == len(observation["values"])
                and all(matches_value(p, v) for p, v in zip(expected, observation["values"])))
    if t in {"assert_trap", "assert_uninstantiable"}:
        # AssertTrap checks a diagnostic prefix in the pinned script interpreter.
        if k != "trap":
            return False
        actual = trap_class(observation["diagnostic"])
        return actual in TRAP_CLASSES and actual.startswith(trap_class(command["text"]))
    expected_kinds = {"action": "return", "module": "ok", "module_instance": "ok",
                      "module_definition": "ok", "register": "ok", "assert_malformed": "malformed",
                      "assert_invalid": "invalid", "assert_unlinkable": "unlinkable",
                      "assert_exhaustion": "exhaustion", "assert_exception": "exception"}
    if t not in expected_kinds:
        raise ValueError(f"unknown script command: {t}")
    return k == expected_kinds[t]


def compare_pair(command, lean, oracle, *, prior_refs=(), allow_choices=True):
    """Both verdicts and direct equality, modulo permitted patterns and handle renaming.

    prior_refs contains corresponding pairs of concrete typed reference values
    already observed in these two sessions, never process addresses to equate.
    Set allow_choices=False when the chosen implementation fixes the result.
    """
    if not matches_expected(command, lean, lane="lean"):
        return False
    if oracle["kind"] == "rejected":
        return command["type"] in {"assert_malformed", "assert_invalid", "assert_unlinkable"}
    if not matches_expected(command, oracle, lane="oracle") or lean["kind"] != oracle["kind"]:
        return False
    if lean["kind"] == "trap":
        return trap_class(lean["diagnostic"]) == trap_class(oracle["diagnostic"])
    if lean["kind"] != "return":
        return True
    left, right = lean["values"], oracle["values"]
    if len(left) != len(right):
        return False
    forward, reverse = {}, {}

    def same_ref(a, b):
        if a[0] != b[0] or a[0] not in REF_TYPES | {"refnull"}:
            return False
        if a[0] in {"anyref", "externref", "i31ref"}:
            return a == b  # script host identities / i31 payloads, not heap addresses
        return forward.setdefault(a, b) == b and reverse.setdefault(b, a) == a

    for a, b in prior_refs:
        if not same_ref(concrete(a), concrete(b)):
            return False
    for a, b in zip(left, right):
        ka, kb = concrete(a), concrete(b)
        if ka[0] in REF_TYPES | {"refnull"} or kb[0] in REF_TYPES | {"refnull"}:
            if not same_ref(ka, kb):
                return False
        elif ka != kb and not (allow_choices and "core_result" in command):
            return False
    return True


class _Process:
    """One session. A timeout, EOF mid-frame or crash never restarts the engine."""

    def __init__(self, argv, delimiter, timeout, record):
        self.argv, self.delimiter, self.timeout = argv, delimiter, timeout
        self.record = record  # optional binary transcript sink, called before parsing
        self.last_raw = b""

    def __enter__(self):
        self.p = subprocess.Popen(self.argv, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                  stderr=subprocess.STDOUT if self.delimiter == PROMPT else None,
                                  bufsize=0)
        os.set_blocking(self.p.stdin.fileno(), False)
        if self.delimiter == PROMPT:
            try:
                self.exchange(b"")
            except BaseException:
                self.__exit__(*sys.exc_info())
                raise
        return self

    def __exit__(self, exc_type, exc, tb):
        self.p.stdin.close()
        try:
            if exc_type is not None:
                self.p.kill()
            status = self.p.wait(timeout=self.timeout)
            if exc_type is None and status:
                raise ValueError(f"{self.argv} exited with status {status}")
            if exc_type is None and self.p.stdout.read():
                raise ValueError(f"{self.argv}: unsolicited trailing output")
        finally:
            if self.p.poll() is None:
                self.p.kill()
                self.p.wait()
            self.p.stdout.close()

    def exchange(self, command):
        deadline = time.monotonic() + self.timeout
        pending = memoryview(command)
        while pending:
            _, ready, _ = select.select([], [self.p.stdin], [], max(0, deadline - time.monotonic()))
            if not ready or time.monotonic() >= deadline:
                raise TimeoutError(f"{self.argv}: timed out writing request")
            n = os.write(self.p.stdin.fileno(), pending)
            pending = pending[n:]
        buf = bytearray()
        while True:
            ready, _, _ = select.select([self.p.stdout], [], [], max(0, deadline - time.monotonic()))
            if not ready or time.monotonic() >= deadline:
                raise TimeoutError(f"{self.argv}: timed out waiting for response")
            chunk = os.read(self.p.stdout.fileno(), 65536)
            if not chunk:
                raise ValueError(f"{self.argv}: EOF before {self.delimiter!r}, tail {buf[-256:]!r}")
            if self.record is not None:
                self.record(chunk)
            start = max(0, len(buf) - len(self.delimiter) + 1)
            buf.extend(chunk)
            end = buf.find(self.delimiter, start)
            if end != -1:
                self.last_raw = bytes(buf)
                if end + len(self.delimiter) != len(buf):
                    raise ValueError(f"{self.argv}: trailing output in response {buf[-256:]!r}")
                return self.last_raw[:end].decode("utf-8")


RETURN_KINDS = {
    "reset": {"ok"}, "register": {"ok"}, "decode": {"ok", "malformed"},
    "validate": {"ok", "malformed", "invalid"}, "module_definition": {"ok", "malformed", "invalid"},
    "module": {"ok", "malformed", "invalid", "unlinkable", "trap", "exception", "exhaustion", "stuck"},
    "module_instance": {"ok", "unlinkable", "trap", "exception", "exhaustion", "stuck"},
    "get": {"return"}, "invoke": {"return", "trap", "exception", "exhaustion", "stuck"},
}


def check_request(request):
    t = request["type"]
    required, optional = {
        "reset": ((), ()), "decode": (("bytes",), ()), "validate": (("bytes",), ()),
        "module": (("bytes",), ("name",)), "module_definition": (("bytes",), ("name",)),
        "module_instance": ((), ("module", "instance")), "register": (("as",), ("name",)),
        "get": (("field",), ("module",)), "invoke": (("field", "args"), ("module",)),
    }[t]
    keys = set(request) - {"type"}
    if set(required) - keys or keys - set(required) - set(optional):
        raise ValueError(f"invalid fields on {t} request: {keys}")
    for key in keys - {"args"}:
        if not isinstance(request[key], str):
            raise ValueError(f"{t}.{key} must be a string")
    if "bytes" in keys:
        data = request["bytes"]
        if len(data) % 2 or not re.fullmatch(r"[0-9a-fA-F]*", data):
            raise ValueError("bytes must be a hex string of whole bytes")
    if "args" in keys:
        if not isinstance(request["args"], list):
            raise ValueError("args must be a typed-value list")
        for v in request["args"]:
            concrete(v)
    return t


def unique_fields(pairs):
    obj = dict(pairs)
    if len(obj) != len(pairs):
        raise ValueError("duplicate JSON response key")
    return obj


class LeanClient(_Process):
    def __init__(self, executable, *, timeout=30, record=None):
        super().__init__([executable, "--json-repl"], b"\n", timeout, record)

    def request(self, request):
        t = check_request(request)
        raw = self.exchange(json.dumps(request, ensure_ascii=True, allow_nan=False).encode() + b"\n")
        reply = json.loads(raw, object_pairs_hook=unique_fields)
        if not isinstance(reply, dict) or reply.get("kind") not in RETURN_KINDS[t]:
            raise ValueError(f"invalid {t} response from Lean: {raw}")
        k = reply["kind"]
        fields = {"kind", "diagnostic"}
        if k == "return":
            fields.add("values")
        elif k == "exception":
            fields.add("handle")
        elif k == "ok" and t in {"module", "module_instance"}:
            fields.add("functions")
        if reply.keys() - fields:
            raise ValueError(f"unexpected fields on {k} response: {raw}")
        if k == "return":
            if not isinstance(reply.get("values"), list) or (t == "get" and len(reply["values"]) != 1):
                raise ValueError(f"invalid {t} result list: {raw}")
            for v in reply["values"]:
                concrete(v)
        if k == "exception":
            integer(reply["handle"])
        if k == "trap" or "diagnostic" in reply:
            message = reply.get("diagnostic")
            if not isinstance(message, str) or not message:
                raise ValueError(f"missing {k} diagnostic: {raw}")
        return reply


def wire_name(s):
    if "\0" in s:
        raise ValueError("NUL in name cannot be represented in wasm3's C string protocol")
    if not s:
        return r"\x00"
    if all(33 <= ord(c) < 127 and c != "\\" for c in s):
        return s
    return "".join(f"\\x{b:02x}" for b in s.encode("utf-8"))


def unwire_name(s):
    if s == r"\x00":
        return ""
    if "\\" not in s:
        return s
    if not re.fullmatch(r"(?:\\x[0-9a-fA-F]{2})+", s):
        raise ValueError(f"invalid upstream UTF-8 escape: {s!r}")
    name = bytes.fromhex(s.replace("\\x", "")).decode("utf-8")
    if "\0" in name:
        raise ValueError("embedded NUL cannot be represented by wasm3")
    return name


class UnrepresentableValue(ValueError):
    """A valid suite value with no native REPL encoding."""


def wire_value(value, *, argument=False):
    t, v = concrete(value)
    if value["type"] in WIRE_REFS and not (argument and value["type"] == "exnref"):
        if argument and v is not None and (t == "funcref" or v >= (1 << 64) - 1):
            # wasm3's text arguments are N+1 words, not a lookup of a script's
            # function index. Never manufacture a native function reference.
            raise UnrepresentableValue(f"reference argument not representable in wasm3: {value!r}")
        return ("null" if t == "refnull" else str(v))
    if t in SCALARS:
        return str(v)
    raise UnrepresentableValue(f"no upstream {'argument' if argument else 'result'} encoding for {value!r}")


def parse_oracle(text, *, loading=False):
    """Parse a literal prompt-delimited reply; never use an expected result."""
    text = text.rstrip("\r\n")
    if not text and loading:
        return {"kind": "ok"}
    err = re.fullmatch(r"Error: ([^\r\n]+?) \(([^\r\n]*)\)", text)
    if err:
        error = err[1]
        if (error in {"[trap] out of gas", "memory guards could not be installed"}
                or re.search(r"allocat|out of memory|limit(?:ation)? exceeded|resource limit", error, re.I)):
            raise ValueError(f"wasm3 resource failure: {text}")
        if error == "[trap] stack overflow":
            return {"kind": "exhaustion"}
        if error == "[trap] uncaught exception":
            return {"kind": "exception"}  # native text protocol exposes no address here
        if error.startswith("[trap] "):
            return {"kind": "trap", "diagnostic": error[7:]}
        # The native loader runs init/start even in a validation trial. These
        # named link/init errors are not evidence of malformed or invalid code.
        if loading and error in {"unknown import", "incompatible import type", "missing imported function",
                                "function lookup failed", "tag lookup failed", "global lookup failed"}:
            return {"kind": "unlinkable", "diagnostic": error}
        if loading and error in {"data segment out of bounds", "out of bounds table access"}:
            diagnostic = "out of bounds memory access" if error == "data segment out of bounds" else error
            return {"kind": "trap", "diagnostic": diagnostic}
        if loading and error != "file too big":
            return {"kind": "rejected", "diagnostic": error}
        raise ValueError(f"wasm3 REPL error: {text}")
    if loading or not text.startswith("Result: "):
        raise ValueError(f"unexpected wasm3 response: {text!r}")
    values = []
    payload = text.removeprefix("Result: ")
    if payload != "<Empty Stack>":
        for item in payload.split(", "):
            m = re.fullmatch(r"(null|[0-9]+):(i32|i64|f32|f64|funcref|externref|exnref)", item)
            if not m:
                raise ValueError(f"unrepresentable wasm3 result: {item!r}")
            value = {"type": m[2], "value": m[1]}
            concrete(value)
            values.append(value)
    return {"kind": "return", "values": values}


class Wasm3Client(_Process):
    """Live spec REPL. Always address a successfully loaded instance explicitly."""

    def __init__(self, executable, *, timeout=30, record=None):
        super().__init__([executable, "--spec-repl"], PROMPT, timeout, record)
        self.instances, self.definitions = {}, {}
        self.last = None
        self.count = 0

    def command(self, *tokens, payload=None):
        if any(not t or re.search(r"[\0 \t\r\n]", t) for t in tokens):
            raise ValueError(f"unrepresentable wasm3 tokens: {tokens!r}")
        line = " ".join(tokens).encode("utf-8") + b"\n"
        # Pinned C repl: char cmd_buff[2048], char *argv[32] incl. terminator.
        if len(line) > 2047 or len(tokens) > 31:
            raise ValueError("command exceeds pinned wasm3 text protocol limits")
        return self.exchange(line if payload is None else line + payload + b"\n")

    def ack(self, *tokens):
        raw = self.command(*tokens)
        if raw:
            raise ValueError(f"wasm3 {tokens[0]} failed: {raw}")

    def instance(self, name):
        target = self.last if name is None else self.instances.get(name)
        if target is None:
            raise ValueError(f"unknown wasm3 script instance: {name!r}")
        return target

    def load(self, data, name=None):
        reply = parse_oracle(self.command(":load-hex", str(len(data)), payload=data.hex().encode()),
                             loading=True)
        if reply["kind"] == "ok":
            handle = f"I{self.count}"
            raw = self.last_raw
            self.ack(":name", handle)
            self.last_raw = raw  # :name is bookkeeping, not the module's observation
            self.count += 1
            self.last = handle
            if name is not None:
                self.instances[name] = handle
        return reply

    def request(self, request):
        t = check_request(request)
        if t == "reset":
            self.ack(":init")
            self.instances.clear()
            self.definitions.clear()
            self.last, self.count = None, 0
        elif t in {"module_definition", "module"}:
            data = bytes.fromhex(request["bytes"])
            # A definition has no spec-REPL verdict; a failed ordinary load
            # must not replace the last successful definition or its name.
            reply = self.load(data, request.get("name")) if t == "module" else None
            if reply is not None and reply["kind"] != "ok":
                return reply
            self.definitions[None] = data
            if "name" in request:
                self.definitions[request["name"]] = data
            return reply
        elif t in {"decode", "validate"}:
            data = bytes.fromhex(request["bytes"])
            # The oracle only exposes acceptance/rejection, even in a fresh
            # process. Never mutate this script's registry by attempting a load.
            with Wasm3Client(self.argv[0], timeout=self.timeout, record=self.record) as trial:
                reply = parse_oracle(trial.command(":load-hex", str(len(data)),
                                                   payload=data.hex().encode()), loading=True)
                self.last_raw = trial.last_raw
            return reply
        elif t == "module_instance":
            return self.load(self.definitions[request.get("module")], request.get("instance"))
        elif t == "register":
            name = request["as"]  # upstream :register does not unescape its arguments
            if len(name.encode("utf-8")) >= 32:
                raise ValueError("registration would be truncated by wasm3")
            self.ack(":register", name, self.instance(request.get("name")))
        elif t in {"invoke", "get"}:
            target, field = self.instance(request.get("module")), wire_name(request["field"])
            if t == "invoke":
                args = [wire_value(v, argument=True) for v in request["args"]]
                return parse_oracle(self.command(":invoke-in", target, field, *args))
            reply = parse_oracle(self.command(":get-global-in", target, field))
            if reply["kind"] != "return" or len(reply["values"]) != 1:
                raise ValueError(f"invalid wasm3 get-global response: {reply}")
            return reply
        else:
            raise ValueError(f"unknown wasm3 request: {t}")
        return {"kind": "ok"}


def wire_reply(reply):
    k = reply["kind"]
    if k == "ok":
        return ""
    if k == "return":
        values = [f"{wire_value(v)}:{v['type']}" for v in reply["values"]]
        return "Result: " + (", ".join(values) or "<Empty Stack>")
    if k == "stuck":
        raise ValueError("Lean reached a stuck configuration")
    if k not in {"malformed", "invalid", "unlinkable", "trap", "exhaustion", "exception"}:
        raise ValueError(f"invalid Lean observation: {k!r}")
    message = {"exhaustion": "stack overflow", "exception": "uncaught exception"}.get(
        k, reply.get("diagnostic", k))
    if any(c in message for c in ("\r", "\n", "\0", "wasm3> ")):
        raise ValueError(f"diagnostic not representable in text REPL: {message!r}")
    prefix = "[trap] " if k in {"trap", "exhaustion", "exception"} else ""
    return f"Error: {prefix}{message} ()"


def spec_repl(executable):
    with LeanClient(executable) as lean:
        lean.request({"type": "reset"})
        # Unlike a register, a :name is private to the script. Bind fresh
        # instance IDs at load time so :name never reinstantiates the module.
        names, registrations, functions = {}, {}, {}
        latest = None

        def resolve(name):
            return names[name] if name in names else registrations[name]

        while True:
            sys.stdout.write("wasm3> ")
            sys.stdout.flush()
            line = sys.stdin.readline()
            if not line:
                return
            if not line.endswith("\n"):
                raise ValueError("unterminated spec REPL command")
            if "\0" in line:
                raise ValueError("NUL in text protocol command")
            words = re.findall(r"[^ \r\n\t]+", line)
            if not words:
                continue
            op, *args = words
            if op == ":exit" and not args:
                return
            if op == ":version" and not args:
                print("IrisWasm Lean Core 3 spec REPL; tail-call, typed-refs, multi-memory")
                continue
            if op == ":init" and not args:
                reply = lean.request({"type": "reset"})
                names.clear()
                registrations.clear()
                functions.clear()
                latest = None
            elif op == ":load-hex" and len(args) == 1:
                size = integer(args[0])
                data = sys.stdin.readline()
                if (not data.endswith("\n") or len(data) != size * 2 + 1
                        or not re.fullmatch(r"[0-9a-fA-F]*\n", data)):
                    raise ValueError(f"expected one hex line of {size} bytes")
                ident = f"I{len(functions)}"
                reply = lean.request({"type": "module", "bytes": data[:-1], "name": ident})
                if reply["kind"] == "ok":
                    signatures = reply.get("functions")
                    if not isinstance(signatures, dict) or not all(
                            isinstance(ts, list) and all(isinstance(t, str) for t in ts)
                            for ts in signatures.values()):
                        raise ValueError("Lean module response missing exported function signatures")
                    functions[ident], latest = signatures, ident
            elif op == ":name" and len(args) == 1 and latest is not None:
                names[args[0]] = latest
                continue
            elif op == ":register" and len(args) in (1, 2):
                ident = latest if len(args) == 1 else resolve(args[1])
                if ident is None:
                    raise ValueError("no instance to register")
                reply = lean.request({"type": "register", "as": args[0], "name": ident})
                registrations[args[0]] = ident
            elif op in {":invoke", ":invoke-in", ":get-global", ":get-global-in"}:
                ident = resolve(unwire_name(args.pop(0))) if op.endswith("-in") else latest
                field = unwire_name(args.pop(0))
                if ident is None:
                    raise ValueError("no loaded instance")
                if op.startswith(":invoke"):
                    params = functions[ident][field]
                    if len(args) != len(params):
                        raise ValueError(f"{field!r}: expected {len(params)} arguments")
                    typed = [{"type": t, "value": a} for t, a in zip(params, args)]
                    for v in typed:
                        v["value"] = wire_value(v, argument=True)
                    request = {"type": "invoke", "args": typed}
                else:
                    if args:
                        raise ValueError("unexpected arguments to get-global")
                    request = {"type": "get"}
                reply = lean.request({**request, "module": ident, "field": field})
            else:
                raise ValueError(f"invalid spec REPL command: {line!r}")
            message = wire_reply(reply)
            if message:
                print(message)


HISTORICAL_SPEC = "9d36019973201a19f9c9ebb0f10828b2fe2374aa"
RESULTS = CACHE / "results"
REFERENCE = SPEC / "interpreter/wasm"
FAULTS = (OSError, LookupError, TypeError, ValueError, subprocess.SubprocessError)


def prepare_historical_source():
    # Keep HEAD at the publication. The old source is for mismatch diagnostics only.
    ref = HISTORICAL_SPEC + "^{commit}"
    if subprocess.run(["git", "-C", SPEC, "cat-file", "-e", ref],
                      stderr=subprocess.DEVNULL).returncode:
        run("git", "-C", SPEC, "fetch", "--depth=1", "--no-tags",
            "https://github.com/WebAssembly/spec.git", HISTORICAL_SPEC)
    if output("git", "-C", SPEC, "rev-parse", ref) != HISTORICAL_SPEC:
        raise ValueError("missing pinned historical fixture source")
    verify_checkout(SPEC, SPEC_REV)


def dump_line(out, obj):
    out.write(json.dumps(obj, ensure_ascii=True, allow_nan=False, separators=(",", ":")) + "\n")


class SignextExport(NamedTuple):
    field: str
    index: int
    start: int  # six-byte sized body, including local groups and end
    opcode: int
    ordinals: range
    first_line: int


# wasm-tools dump 1.256.0: type index 1, no imports, start or mutable store.
# Only these module hashes justify isolating calls from their script history.
SIGNEXT = {
    "i32": ("bf5287e4e9a57efc97e1b0c6169503ee01beab6a54c93b6f87a06139410e6b6a", (
        SignextExport("extend8_s", 18, 0x1a7, 0xc0, range(217, 224), 270),
        SignextExport("extend16_s", 19, 0x1ad, 0xc1, range(224, 231), 278))),
    "i64": ("7c1de383fb3eef51b3f99c680045870439377707c2732a23d664779ed08f7a64", (
        SignextExport("extend8_s", 18, 0x1c0, 0xc2, range(217, 224), 271),
        SignextExport("extend16_s", 19, 0x1c6, 0xc3, range(224, 231), 279),
        SignextExport("extend32_s", 20, 0x1cc, 0xc4, range(231, 241), 287))),
}


def signext_inputs():
    if FIXTURE_REV != "d2b8c296df2e209acbdd0d901d14dd7085acd178":
        raise ValueError("re-establish sign-extension body windows and command IDs for the new revision")
    verify_checkout(HARNESS, HARNESS_REV)
    verify_checkout(FIXTURES, FIXTURE_REV)
    for width, (digest, exports) in SIGNEXT.items():
        path = FIXTURES / "core" / f"{width}.json"
        commands = json.loads(path.read_bytes(), object_pairs_hook=unique_fields)["commands"]
        first = commands[0]
        if first["type"] != "module" or first["filename"] != f"{width}.0.wasm":
            raise ValueError(f"{path}: wrong initial module")
        module = path.with_name(first["filename"]).read_bytes()
        if sha256(module).hexdigest() != digest:
            raise ValueError(f"{first['filename']}: wrong SHA-256")

        fields = {e.field for e in exports}
        cases = {i: c for i, c in enumerate(commands, 1) if c.get("action", {}).get("field") in fields}
        if set(cases) != {i for e in exports for i in e.ordinals}:
            raise ValueError(f"{path}: wrong sign-extension command IDs")
        for e in exports:
            if module[e.start:e.start + 6] != bytes((5, 0, 0x20, 0, e.opcode, 0x0b)):
                raise ValueError(f"{path}: wrong body for {e.field} at {e.start:#x}")
            for line, i in enumerate(e.ordinals, e.first_line):
                c = cases[i]
                a = c["action"]
                if (c["line"] != line or c["type"] != "assert_return" or a["type"] != "invoke"
                        or a["field"] != e.field or "module" in a or len(a["args"]) != 1
                        or len(c["expected"]) != 1 or concrete(a["args"][0])[0] != width
                        or concrete(c["expected"][0])[0] != width):
                    raise ValueError(f"{path}:{i}: expected {width} → {width} call to {e.field} at line {line}")
        yield width, module, exports, cases


def suite_inventory(errors):
    """Use source-relative script names in both corpora (the generated layouts differ)."""
    scripts = []
    for corpus, base, rev in [("converted", FIXTURES / "core", FIXTURE_REV),
                              ("deployed", DEPLOYED, SPEC_REV)]:
        paths = sorted(base.rglob("*.json"))
        if not paths:
            errors.append(f"empty {corpus} corpus: {base}")
        if corpus == "deployed":
            sources = sorted((SPEC / "test/core").rglob("*.wast"))
            expected = {base / p.relative_to(SPEC / "test/core").with_suffix("") /
                        (p.stem + ".json") for p in sources}
            if not sources:
                errors.append("empty deployed source inventory")
            for path in sorted(expected ^ set(paths)):
                errors.append(f"conversion inventory: {path} {'missing' if path in expected else 'unexpected'}")
            paths = [path for path in paths if path in expected]
        for path in paths:
            rel = path.relative_to(base)
            if corpus == "deployed":
                rel = rel.parent.with_suffix(".json")
            try:
                commands = json.loads(path.read_bytes(), object_pairs_hook=unique_fields)["commands"]
                if not isinstance(commands, list) or not commands or not all(
                        isinstance(c, dict) and type(c.get("line")) is int and
                        isinstance(c.get("type"), str) for c in commands):
                    raise ValueError("empty or invalid command list")
                scripts.append((corpus, rev, rel, path, commands))
            except FAULTS as e:
                errors.append(f"{path}: {e}")
    return scripts


def offline_printer():
    for exe in (shutil.which("wasm-tools"), CACHE / "tools/bin/wasm-tools"):
        if exe and Path(exe).is_file() and output(exe, "--version") == "wasm-tools " + CONVERTER_VERSION:
            return exe
    raise ValueError("missing pinned wasm-tools; run prepare")


def request_for(command, directory, tmp):
    """Only the script dispatcher sees expected answers, never either execution process."""
    t = command["type"]
    if "action" in command:
        if t not in {"action", "assert_return", "assert_trap", "assert_exception", "assert_exhaustion"}:
            raise ValueError(f"unknown action assertion: {t}")
        req = command["action"]
        if req["type"] not in ("invoke", "get"):
            raise ValueError(f"unknown action: {req['type']}")
    elif t in {"module_instance", "register"}:
        req = {k: v for k, v in command.items() if k != "line"}
    else:
        op = {"module": "module", "module_definition": "module_definition", "assert_invalid": "validate",
              "assert_malformed": "decode", "assert_unlinkable": "module",
              "assert_uninstantiable": "module"}[t]
        path = (directory / command["filename"]).resolve()
        if not path.is_relative_to(directory) or not path.is_file():
            raise ValueError(f"missing or out-of-tree fixture: {path}")
        if command.get("module_type", "binary") == "text":
            dest = tmp / "assembled.wasm"
            dest.unlink(missing_ok=True)
            result = subprocess.run([REFERENCE, "-d", "-u", path, "-o", dest],
                                    capture_output=True, timeout=30)
            if result.returncode:
                diagnostic = result.stderr.decode("utf-8", "replace").strip()
                error = re.search(r": (?:custom annotation )?syntax error: (.*)$", diagnostic)
                if result.returncode == 1 and t == "assert_malformed" and error:
                    return None, {"diagnostic": diagnostic, "passed": error[1].startswith(command["text"]),
                                  "wat_sha256": sha256(path.read_bytes()).hexdigest()}
                raise ValueError(f"text assembler exited {result.returncode}: {diagnostic}")
            path = dest
        elif command.get("module_type", "binary") != "binary":
            raise ValueError(f"unknown module type: {command['module_type']}")
        req = {"type": op, "bytes": path.read_bytes().hex()}
        if "name" in command:
            req["name"] = command["name"]
    check_request(req)
    return req, None


WAT_TOKEN = re.compile(r'\(;.*?;\)|;;[^\n]*|"(?:\\.|[^"\\])*"|[()]|[^\s()"]+', re.S)


def wat_name(literal):
    if not literal.startswith('"') or not literal.endswith('"'):
        raise ValueError(f"expected quoted import name: {literal}")
    data = bytearray()
    for match in re.finditer(r'\\(?:[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}|.)|[^\\]+', literal[1:-1]):
        chunk = match[0]
        if chunk.startswith("\\u{"):
            data.extend(chr(int(chunk[3:-1], 16)).encode())
        elif len(chunk) == 3 and chunk[0] == "\\":
            data.append(int(chunk[1:], 16))
        elif chunk.startswith("\\"):
            data.extend({"n": b"\n", "r": b"\r", "t": b"\t", '"': b'"', "'": b"'", "\\": b"\\"}[chunk[1]])
        else:
            data.extend(chunk.encode())
    return data.decode()


def module_facts(printer, data, policy):
    """Disassemble only for feature selection and import dependencies, not verdicts."""
    proc = subprocess.run([printer, "print", "-"], input=data, capture_output=True, timeout=30)
    if proc.returncode:
        raise ValueError(f"cannot inspect module features: {proc.stderr.decode(errors='replace')}")
    toks = [s for s in WAT_TOKEN.findall(proc.stdout.decode()) if not s.startswith(("(;", ";;"))]
    imports = {wat_name(toks[i+2]) for i in range(len(toks) - 2) if toks[i:i+2] == ["(", "import"]}
    atoms = {t for t in toks if t and t[0] not in '"$()'}
    reason = next((entry["reason"] for entry in policy["features"]
                   if any(re.fullmatch(entry["token"], t) for t in atoms)), None)
    # Inspect the printer's memory type, not bytes in a data segment or a quoted name.
    for i in range(len(toks) - 3):
        if toks[i:i+2] == ["(", "memory"]:
            j = i + 2 + int(toks[i+2].startswith("$"))
            if j+1 < len(toks) and toks[j] == "i64" and toks[j+1].isdigit() and int(toks[j+1]) > 65536:
                reason = policy["memory64_cap"]
    initializes = bool(atoms & {"start", "data", "elem"})
    # A skipped call in a closed module consisting of pure functions (e.g. names.wast)
    # cannot invalidate the other actions. Imports/indirect calls can mutate shared objects.
    writes = bool(imports) or any(re.fullmatch(
        r"(?:return_)?call_(?:ref|indirect)|.+\.store.*|global\.set|(?:memory|table)\.(?:set|copy|fill|init|grow)"
        r"|(?:data|elem)\.drop|(?:array|struct)\.(?:set|fill|copy|init_.*)", a) for a in atoms)
    return {"imports": imports, "reason": reason, "initializes": initializes, "writes": writes}


def policy_reason(policy, corpus, rel, request, filename):
    for entry in policy["commands"]:
        if (str(rel) == entry["script"]
                and entry.get("corpus", corpus) == corpus
                and ("instances" not in entry or request.get("instance") in entry["instances"])
                and ("files" not in entry or filename in entry["files"])
                and ("fields" not in entry or any(fnmatchcase(request.get("field", ""), f) for f in entry["fields"]))
                and ("args" not in entry or request.get("args") == entry["args"])):
            return entry["reason"]
    return None


def wire_reason(policy, req, handle):
    t = req["type"]
    if t == "register":
        name = req["as"]
        if not name or len(name.encode()) >= 32 or re.search(r"[\0 \t\r\n]", name):
            return policy["wire"]["registration"]
    if t in {"invoke", "get"}:
        field = req["field"]
        if "\0" in field:
            return policy["wire"]["name"]
        try:
            args = [wire_value(v, argument=True) for v in req.get("args", [])]
        except UnrepresentableValue:
            return policy["wire"]["values"]
        tokens = [":invoke-in" if t == "invoke" else ":get-global-in", handle, wire_name(field), *args]
        if len(tokens) > 31 or len(" ".join(tokens).encode()) + 1 > 2047:
            return policy["wire"]["length"]
    return None


class OracleHistory:
    """One lane's script bindings. Engine-private names are always explicit."""

    def __init__(self):
        self.definitions, self.instances, self.registry = {}, {}, {}
        self.sources, self.roots = {}, {}
        self.unavailable, self.unregistered = {}, {}
        self.shared, self.tainted = {}, {}
        self.native_names = {}

    def select(self, req, ordinal, modules):
        op = req["type"]
        source, target, imports, roots, issue = ordinal, None, {}, set(), None
        if op == "module_instance":
            source = target = self.definitions[req.get("module")]
        elif op in {"invoke", "get", "register"}:
            target = self.instances[req.get("name" if op == "register" else "module")]
            source = self.sources[target]
            roots.update(self.roots[target])
            issue = self.unavailable.get(target)
        if op in {"module", "module_instance"}:
            facts = modules[source][2]
            names = facts["imports"] if facts is not None else self.registry.keys() | {"spectest"}
            for name in sorted(names):
                provider = self.registry.get(name, "spectest" if name == "spectest" else None)
                imports[name] = provider
                if provider is not None:
                    roots.update(self.roots.get(provider, {provider}))
                issue = issue or self.unregistered.get(name) or self.unavailable.get(provider)
        issue = issue or next((self.tainted[r] for r in sorted(roots, key=str) if r in self.tainted), None)
        return {"source": source, "target": target, "imports": imports,
                "roots": sorted(roots, key=str), "bytes_sha256": modules[source][1]}, issue

    @staticmethod
    def route(req, ordinal, selection):
        op = req["type"]
        if op in {"module", "module_definition"}:
            return {**req, "name": f"cmd{ordinal}"}
        if op == "module_instance":
            return {**req, "module": f"cmd{selection['target']}", "instance": f"cmd{ordinal}"}
        if op in {"invoke", "get", "register"}:
            return {**req, "name" if op == "register" else "module": f"cmd{selection['target']}"}
        return req

    def registration_problem(self, name, target):
        # Pinned :register sets the module's sole C name; lookup is newest-load first.
        old = self.native_names.get(target)
        if old is not None and old != name and self.registry.get(old) == target:
            return f"native registration would remove the live alias {old!r}"
        if any(i > target and n == name for i, n in self.native_names.items()):
            return f"native registration would resolve {name!r} to a newer instance"
        return None

    def advance(self, command, req, ordinal, selection, *, success, issue=None):
        # A skipped oracle operation may shadow the old *script* binding, but
        # never supplies an engine instance or a successful observation.
        if not success:
            return
        t = command["type"]
        if t in {"module", "module_definition"}:
            self.definitions[None] = self.definitions[req.get("name")] = ordinal
        if t in {"module", "module_instance"}:
            key = req.get("instance" if t == "module_instance" else "name")
            self.instances[None] = self.instances[key] = ordinal
            self.sources[ordinal] = selection["source"]
            self.roots[ordinal] = set(selection["roots"]) | {ordinal}
            if issue:
                self.unavailable[ordinal] = issue
        elif t == "register":
            self.registry[req["as"]] = selection["target"]
            if issue:
                self.unregistered[req["as"]] = issue
            else:
                self.unregistered.pop(req["as"], None)
                self.native_names[selection["target"]] = req["as"]

    def effects(self, op, ordinal, selections, modules, observations, issue):
        # A trapped start/call may already have written. A link or validation
        # failure cannot. Cross-instance references can outlive the writer.
        roots = set()
        for lane, selection in selections.items():
            obs = observations.get(lane)
            if obs is None or obs["kind"] in {"malformed", "invalid", "unlinkable"}:
                continue
            facts = modules[selection["source"]][2]
            if ((op == "invoke" and (facts is None or facts["writes"])) or
                    (op in {"module", "module_instance"} and (facts is None or facts["initializes"]))):
                roots.update(selection["roots"])
                if op != "invoke":
                    roots.add(ordinal)
        if not roots:
            return
        group = roots.union(*(self.shared.get(r, ()) for r in roots))
        self.shared.update(dict.fromkeys(group, group))
        cause = next((self.tainted[r] for r in sorted(group, key=str) if r in self.tainted), issue)
        if cause:
            self.tainted.update(dict.fromkeys(group, cause))


def feature_witness(rel, command):
    # Accept only the fixed script sites that exercise each required behavior.
    field = command.get("action", {}).get("field")
    line = command.get("line")
    if rel == Path("i32.json"):
        return {(37, "assert_return"): "scalar-add", (64, "assert_trap"): "division-trap",
                (444, "assert_invalid"): "validation"}.get((line, command["type"]))
    if rel == Path("binary.json") and command.get("text") == "magic header not detected":
        return "bad-magic"
    if field is None:
        return None
    args = command["action"].get("args", [])
    if field == "simple-throw-catch" and args != [{"type": "i32", "value": "0"}]:
        return None
    if field in {"even", "odd"} and args == [{"type": "i64", "value": "0"}]:
        return None
    if rel == Path("bulk-memory/memory_copy.json") and line != 57:
        return None
    for family, script, exports in [
        ("bulk-memory", "bulk-memory/memory_copy.json", {"test"}),
        ("multi-memory", "multi-memory/memory_copy1.json", {"copy"}),
        ("memory64", "memory64/address64.json", {"8u_good1", "16u_good1"}),
        ("table64", "memory64/table_get64.json", {"get-externref", "get-funcref"}),
        ("tail-call", "return_call.json", {"even", "odd"}),
        ("exceptions", "exceptions/try_table.json", {"simple-throw-catch"}),
    ]:
        if str(rel) == script and field in exports:
            return family
    return None


def run_script(script, args, policy, printer, oracle_ok, records, mismatches, families, errors):
    corpus, rev, rel, path, commands = script
    folder = RESULTS / "sessions" / corpus / rel.with_suffix("")
    failed, recorded, previous = False, 0, None
    histories = {lane: OracleHistory() for lane in ("lean", "oracle")}
    oracle = histories["oracle"]
    modules, inspection_errors = {}, {}
    prior_refs, ref_pairs = [], set()
    clients, dead, logs = {}, {}, {}
    try:
        folder.mkdir(parents=True, exist_ok=True)
        with ExitStack() as stack:
            tmp = Path(stack.enter_context(TemporaryDirectory()))
            replay = stack.enter_context((folder / "requests.jsonl").open("w"))
            for lane, cls, executable in [("lean", LeanClient, args.lean), ("oracle", Wasm3Client, args.wasm3)]:
                logs[lane] = stack.enter_context((folder / f"{lane}.raw").open("wb", buffering=0))
                try:
                    if lane == "oracle" and not oracle_ok:
                        raise ValueError("oracle capability profile not verified")
                    client = stack.enter_context(cls(executable, timeout=args.timeout, record=logs[lane].write))
                    client.request({"type": "reset"})
                    clients[lane] = client
                except FAULTS as e:
                    dead[lane] = str(e)
            for ordinal, command in enumerate(commands, 1):
                t = command["type"]
                row = {"id": [corpus, str(rel), ordinal, command["line"]], "type": t}
                row_errors, selections, sent = [], {}, {}
                row["dependencies"] = selections
                req, predicate, issue = None, command, None
                start = {lane: log.tell() for lane, log in logs.items()}
                try:
                    req, frontend = request_for(command, path.parent, tmp)
                    if frontend:
                        row["frontend"] = frontend
                        row["oracle_excluded"] = policy["wire"]["text"]
                        if not frontend["passed"]:
                            row["disagreement"] = "frontend diagnostic"
                    else:
                        op = req["type"]
                        if "bytes" in req:
                            data = bytes.fromhex(req["bytes"])
                            facts = None
                            if op != "decode" and "oracle" not in dead:
                                try:
                                    if printer is None:
                                        raise ValueError("pinned feature inspector unavailable")
                                    facts = module_facts(printer, data, policy)
                                except FAULTS as e:
                                    inspection_errors[ordinal] = str(e)
                            modules[ordinal] = command.get("filename"), sha256(data).hexdigest(), facts
                            row["bytes_sha256"] = modules[ordinal][1]
                        for lane, h in histories.items():
                            if lane in dead:
                                row_errors.append(f"{lane}: {dead[lane]}")
                                continue
                            try:
                                selected, unavailable = h.select(req, ordinal, modules)
                            except KeyError as e:
                                problem = f"no successful binding for {op} target {e} at command {ordinal}"
                                row_errors.append(f"{lane}: {problem}")
                                if op == "register" and req["as"] not in h.registry:
                                    h.unregistered[req["as"]] = ("blocked", problem)
                                continue
                            selections[lane] = selected
                            filename, digest, facts = modules[selected["source"]]
                            row.setdefault("bytes_sha256", digest)
                            outgoing = h.route(req, ordinal, selected)
                            client = clients[lane]
                            if lane == "oracle":
                                issue = unavailable
                                if selected["source"] in inspection_errors:
                                    issue = ("blocked", inspection_errors[selected["source"]])
                                if not issue and "lean" not in dead and selected != selections.get("lean"):
                                    issue = ("blocked", "lanes resolve different script bindings or imports")
                                if not issue:
                                    reason = policy_reason(policy, corpus, rel, req, filename) or (facts and facts["reason"])
                                    if not reason:
                                        handle = client.instance(outgoing["module"]) if op in {"invoke", "get"} else ""
                                        reason = wire_reason(policy, req, handle)
                                    if not reason and op == "register":
                                        problem = h.registration_problem(req["as"], selected["target"])
                                        if problem:
                                            issue = ("blocked", problem)
                                    if reason:
                                        issue = ("excluded", reason)
                                if t == "module_definition" and not issue:
                                    issue = ("excluded", policy["wire"]["definition"])
                                if issue:
                                    if issue[0] == "excluded":
                                        row["oracle_excluded"] = issue[1]
                                    else:
                                        row_errors.append(f"oracle: {issue[1]}")
                                    # Cache definition bytes, not an instance or a native verdict.
                                    retain = row.get("lean", {}).get("kind") == "ok" or "lean" in dead
                                    if not retain or t not in {"module", "module_definition"}:
                                        shadow = selections.get("lean", selected)
                                        h.advance(command, req, ordinal, shadow, success=retain, issue=issue)
                                        continue
                                    outgoing = {**outgoing, "type": "module_definition"}
                            # Replay merges overrides over `request`, keeping the bytes only once.
                            sent[lane] = {k: v for k, v in outgoing.items() if v != req.get(k)}
                            try:
                                obs = client.request(outgoing)
                                if lane == "oracle" and outgoing["type"] == "module_definition":
                                    if obs is not None:
                                        raise ValueError("unexpected native definition-only observation")
                                    shadow = selections.get("lean", selected)
                                    h.advance(command, req, ordinal, shadow, success=True, issue=issue)
                                    continue
                                if obs is None:
                                    raise ValueError(f"missing native {op} response")
                            except FAULTS as e:
                                problem = f"command {ordinal}: {e}"
                                row_errors.append(f"{lane}: {problem}")
                                # An isolated oracle validation trial cannot damage the live script session.
                                if lane != "oracle" or op not in {"decode", "validate"}:
                                    dead[lane] = problem
                                    client.p.kill()
                                continue
                            row[lane] = obs
                            h.advance(command, req, ordinal, selected, success=obs["kind"] == "ok")
                        prior = previous
                        if prior and str(rel) in GROW_TRIALS:
                            # Equal module bytes are not evidence about the same memory/table instance.
                            prior = {**prior, **{lane + "_passed": False for lane, s in selections.items()
                                     if prior.get("dependencies", {}).get(lane, {}).get("target") != s["target"]}}
                        predicate = expected_command(command, rev, rel, previous=prior,
                                                     module_sha256=row.get("bytes_sha256"))
                        for lane in selections:
                            if lane not in row:
                                continue
                            obs = row[lane]
                            passed = (t in {"assert_malformed", "assert_invalid", "assert_unlinkable"}
                                      if lane == "oracle" and obs["kind"] == "rejected"
                                      else matches_expected(predicate, obs, lane=lane))
                            row[lane + "_passed"] = passed
                            if not passed:
                                row["disagreement"] = f"{lane} did not satisfy the script assertion"
                        if "lean" in row and "oracle" in row:
                            row["agrees"] = compare_pair(predicate, row["lean"], row["oracle"], prior_refs=prior_refs)
                            if not row["agrees"]:
                                row["disagreement"] = "direct comparison or expected verdict"
                            elif row["lean"]["kind"] == "return":
                                for a, b in zip(row["lean"]["values"], row["oracle"]["values"]):
                                    key = concrete(a), concrete(b)
                                    if key[0][0] in REF_TYPES and key[0][0] == key[1][0] and key not in ref_pairs:
                                        ref_pairs.add(key)
                                        prior_refs.append((a, b))
                except FAULTS as e:
                    row_errors.append(f"driver: {e}")
                    if req is None and t not in {"assert_malformed", "assert_invalid"}:
                        # An unreadable decode/validation trial has no live script effects.
                        # For an unknown stateful input there is no reproducible prefix.
                        for lane in clients:
                            dead.setdefault(lane, f"request construction failed at command {ordinal}")
                if req is not None:
                    cause = None
                    if (op in {"module", "module_instance"} and row.get("oracle", {}).get("kind") == "rejected"):
                        cause = ("blocked", f"oracle did not identify the rejection phase at command {ordinal}")
                    elif not row.get("agrees") and ("lean" not in dead or "disagreement" in row):
                        kind, reason = issue or ("blocked", "mutation lacks an agreeing paired observation")
                        cause = (kind, f"depends on command {ordinal}: {reason}")
                    oracle.effects(req["type"], ordinal, selections, modules, row, cause)
                entry = {"id": row["id"], "command": command, "request": req, "sent_overrides": sent}
                if ordinal == 1:
                    entry["sessions_reset"] = list(clients)
                dump_line(replay, {**entry, "oracle_excluded": row.get("oracle_excluded"), "errors": row_errors})
                row["raw"] = {lane: {"file": str((folder / f"{lane}.raw").relative_to(RESULTS)),
                                     "start": start[lane], "end": log.tell()} for lane, log in logs.items()}
                if row_errors:
                    row["infrastructure"] = row_errors
                if "disagreement" in row:
                    failed = True
                    dump_line(mismatches, {**row, "predicate": predicate,
                        "prefix": str((folder / "requests.jsonl").relative_to(RESULTS)),
                        "through": ordinal, "oracle_profile": "oracle.json",
                        "reference_diagnostic": str((folder / "reference.log").relative_to(RESULTS))})
                if row.get("agrees") and (family := feature_witness(rel, command)):
                    families[(corpus, family)] += 1
                dump_line(records, row)
                previous, recorded = row, ordinal
    except FAULTS as e:
        errors.append(f"{corpus}/{rel}: closing or opening session: {e}")
        for n, command in enumerate(commands[recorded:], recorded + 1):
            dump_line(records, {"id": [corpus, str(rel), n, command["line"]], "type": command["type"],
                                "infrastructure": [f"session unavailable: {e}"]})
    if failed:
        try:
            diagnose_source(corpus, rel, folder, args.timeout)
        except FAULTS as e:
            errors.append(f"{corpus}/{rel}: reference diagnosis: {e}")


def diagnose_source(corpus, rel, folder, timeout):
    with TemporaryDirectory() as tmp, (folder / "reference.log").open("wb") as log:
        if corpus == "converted":
            source = Path(tmp) / rel.with_suffix(".wast").name
            source.write_bytes(subprocess.check_output(
                ["git", "-C", SPEC, "show", f"{HISTORICAL_SPEC}:test/core/{rel.with_suffix('.wast')}"]))
        elif corpus == "witnesses":
            source = ROOT / "WasmTest/Core3/witnesses.wast"
        else:
            source = SPEC / "test/core" / rel.with_suffix(".wast")
        # Keep a reference diagnostic on a deliberately >4GiB sparse case from exhausting the workstation.
        argv = ["prlimit", "--as=2147483648", "--", REFERENCE, source]
        result = subprocess.run(argv, stdout=log, stderr=subprocess.STDOUT, timeout=timeout)
        log.write(f"\nexit: {result.returncode}\n".encode())
        if result.returncode < 0 or result.returncode > 1:
            raise ValueError(f"reference tool failed with status {result.returncode}")


def pinned_policy():
    policy = json.loads((ROOT / "WasmTest/Core3/wasm3-exclusions.json").read_bytes())
    if policy["harness"] != HARNESS_REV or policy["corpora"] != {"converted": FIXTURE_REV, "deployed": SPEC_REV}:
        raise ValueError("exclusion policy not pinned to this build and both corpora")
    return policy


def verify_profile(args, policy, out_dir):
    profile = policy["profiles"][args.skip_features]
    (out_dir / "oracle.json").unlink(missing_ok=True)
    with (out_dir / "oracle-version.raw").open("wb") as log, Wasm3Client(
            args.wasm3, timeout=args.timeout, record=log.write) as oracle:
        version = oracle.command(":version")
    info = {"path": str(args.wasm3), "version": version, "sha256": sha256(args.wasm3.read_bytes()).hexdigest(),
            "argv": [str(args.wasm3), "--spec-repl"], "skip_features": args.skip_features,
            "harness": HARNESS_REV, "corpora": policy["corpora"]}
    (out_dir / "oracle.json").write_text(json.dumps(info, indent=2) + "\n")
    lines = version.splitlines()
    features = set(lines[-1].split(", ")[2:]) if lines and lines[-1].startswith("Build: ") else set()
    if (not lines or not lines[0].startswith("Wasm3 " + profile["version"] + " on ")
            or features != set(profile["features"])
            or ("sha256" in profile and profile["sha256"] != info["sha256"])
            or (profile.get("source_build") and args.wasm3 != (HARNESS / "build/wasm3").resolve())):
        raise ValueError(f"oracle differs from pinned {args.skip_features} profile: {info}")


def upstream_gate(label, exe, skip, scripts, timeout):
    cwd = HARNESS / "test"
    # The runner downloads mutable fixtures if this path is absent; never invoke it in that state.
    if not (FIXTURES / "core").is_dir() or not scripts:
        raise ValueError("missing prepared core scripts for the upstream gate")
    scriptlog = cwd / "spec-test.log"
    scriptlog.unlink(missing_ok=True)
    argv = [sys.executable, "run-spec-test.py", "--exec", shlex.join([str(s) for s in exe]),
            "--spec=wg-3.0", "--skip-features=" + skip, "--format=raw", "--no-relax-nan",
            "--timeout", str(timeout), *(str(p.relative_to(cwd)) for p in sorted(scripts))]
    with (RESULTS / f"{label}-upstream.stdout").open("wb") as log:
        result = subprocess.run(argv, cwd=cwd, stdout=log, stderr=subprocess.STDOUT)
    archive = RESULTS / f"{label}-upstream.log"
    if not scriptlog.exists():
        raise ValueError(f"{label} upstream runner exited {result.returncode} without a log")
    shutil.copyfile(scriptlog, archive)
    warnings = [s for s in archive.read_text(errors="replace").splitlines() if s.startswith("Warning:")]
    unexpected = [s for s in warnings if "Skipped " in s and not any(x in s for x in
                  ("(blacklisted)", " of a text module)", "('module_definition' not implemented)",
                   "('module_instance' not implemented)"))]
    with (RESULTS / f"{label}-upstream.json").open("w") as out:
        dump_line(out, {"argv": argv, "exit": result.returncode, "warnings": warnings, "unexpected_skips": unexpected})
    if result.returncode or unexpected:
        raise ValueError(f"{label} upstream exit={result.returncode}, unexpected skips={len(unexpected)}; see {archive}")


def command_counts():
    counts, groups, suites, exclusions = {}, {}, {}, {}
    with (RESULTS / "commands.jsonl").open() as rows, (RESULTS / "inventory.jsonl").open() as inventory:
        for line in inventory:
            entry = json.loads(line)
            row = json.loads(next(rows, "null"))
            if not row or row["id"] != entry["id"] or row["type"] != entry["type"]:
                raise ValueError(f"command inventory lost ordering or a command at {entry['id']}")
            corpus, script, _, _ = row["id"]
            path = Path(script)
            group = path.parts[0] if len(path.parts) > 1 else path.stem
            if not any(k in row for k in ("lean", "frontend", "infrastructure")):
                raise ValueError(f"unaccounted Lean command: {row['id']}")
            for counter in (counts.setdefault(corpus, Counter()), groups.setdefault(corpus + "/" + group, Counter()),
                            suites.setdefault(corpus + "/" + script, Counter())):
                counter["discovered"] += 1
                for flag, key in [("lean_checked", "lean"), ("frontend_only", "frontend"),
                                  ("paired", "agrees"), ("oracle_excluded", "oracle_excluded"),
                                  ("disagreements", "disagreement"), ("infrastructure", "infrastructure")]:
                    counter[flag] += key in row
            if "oracle_excluded" in row:
                exclusions.setdefault(corpus, Counter())[row["oracle_excluded"]] += 1
        if next(rows, None) is not None:
            raise ValueError("command records beyond the discovered inventory")
    return counts, groups, suites, exclusions


def test(args):
    RESULTS.mkdir(parents=True, exist_ok=True)
    policy = pinned_policy()
    errors = []
    trusted = {}
    for checkout_dir, rev in [(SPEC, SPEC_REV), (HARNESS, HARNESS_REV), (FIXTURES, FIXTURE_REV)]:
        try:
            verify_checkout(checkout_dir, rev)
            trusted[checkout_dir] = True
        except FAULTS as e:
            trusted[checkout_dir] = False
            errors.append(f"pin verification: {e}")
    scripts = suite_inventory(errors)
    args.lean, args.wasm3 = args.lean.resolve(), args.wasm3.resolve()
    printer = None
    try:
        printer = offline_printer()
        source = ROOT / "WasmTest/Core3/witnesses.wast"
        directory = RESULTS / "generated-witnesses"
        directory.mkdir(exist_ok=True)
        script = directory / "witnesses.json"
        run(printer, "json-from-wast", "--wasm-dir", directory, "-o", script, source)
        commands = json.loads(script.read_bytes())["commands"]
        if not commands:
            raise ValueError("empty project witness suite")
        scripts.append(("witnesses", sha256(source.read_bytes()).hexdigest(), Path(script.name), script, commands))
    except FAULTS as e:
        errors.append(f"witness generation or pinned converter: {e}")
    families = Counter()
    with (RESULTS / "inventory.jsonl").open("w") as out:
        for corpus, rev, rel, path, commands in scripts:
            for i, c in enumerate(commands, 1):
                dump_line(out, {"id": [corpus, str(rel), i, c["line"]], "type": c["type"], "revision": rev})
    oracle_ok = False
    try:
        verify_profile(args, policy, RESULTS)
        oracle_ok = True
    except FAULTS as e:
        errors.append(f"wasm3 profile: {e}")
    for name, argv in [("proof", ["lake", "env", "python3", "tools/core3_gate.py"]),
                       ("comparison", [sys.executable, "-m", "unittest", "discover", "-s", "tools",
                                       "-p", "test_core3*.py"])]:
        try:
            with (RESULTS / f"{name}-gate.log").open("wb") as log:
                run(*argv, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
        except FAULTS as e:
            errors.append(f"{name} gate: {e}")
    upstream = [p for c, _, rel, p, _ in scripts if c == "converted" and str(rel.parent) in
                {".", "bulk-memory", "exceptions", "multi-memory"}]
    for name, exe, skip, available in [
        ("wasm3", [args.wasm3, "--spec-repl"], args.skip_features, oracle_ok),
        ("lean", [sys.executable, Path(__file__).resolve(), "spec-repl", "--lean", args.lean],
         "atomics", os.access(args.lean, os.X_OK))]:
        try:
            if not (available and trusted[FIXTURES] and trusted[HARNESS]):
                raise ValueError("verified engine or upstream fixtures unavailable")
            upstream_gate(name, exe, skip, upstream, args.timeout)
        except FAULTS as e:
            errors.append(f"{name} upstream: {e}")
    with (RESULTS / "commands.jsonl").open("w") as records, (RESULTS / "mismatches.jsonl").open("w") as failures:
        for script in scripts:
            corpus, _, rel, _, commands = script
            if not trusted[SPEC] or (corpus == "converted" and not trusted[FIXTURES]):
                for n, command in enumerate(commands, 1):
                    dump_line(records, {"id": [corpus, str(rel), n, command["line"]],
                                        "type": command["type"], "infrastructure": ["untrusted suite or frontend"]})
                continue
            run_script(script, args, policy, printer, oracle_ok, records, failures, families, errors)
    for corpus in ("converted", "deployed"):
        for family in ("scalar-add", "division-trap", "validation", "bad-magic", "bulk-memory",
                       "multi-memory", "memory64", "table64", "tail-call", "exceptions"):
            if not families[(corpus, family)]:
                errors.append(f"{corpus}: no successful paired {family} observation")
    counts, groups, suites, exclusions = command_counts()
    summary = {"counts": counts, "paired_family_witnesses": {f"{c}/{f}": n for (c, f), n in families.items()},
               "by_family": groups, "by_script": suites, "exclusions_by_reason": exclusions,
               "infrastructure_errors": errors}
    text = json.dumps(summary, indent=2)
    (RESULTS / "summary.json").write_text(text + "\n")
    print(text)
    if errors or any(c["disagreements"] or c["infrastructure"] for c in counts.values()):
        raise SystemExit(1)


def offline_lake(*args, **kwargs):
    cmd = ["lake", "--no-cache", *args]
    if shutil.which("elan"):
        # Unlike the lake proxy, `elan run` without --install requires a local toolchain.
        cmd = ["elan", "run", (ROOT / "lean-toolchain").read_text().strip(), *cmd]
    run(*cmd, cwd=ROOT, env={**os.environ, "GIT_ALLOW_PROTOCOL": ""}, **kwargs)


def parse_signext_rows(raw, ordinals):
    if isinstance(raw, bytes):
        raw = raw.decode("utf-8")
    rows = {}
    for line in raw.removesuffix("\n").split("\n"):
        row = json.loads(line, object_pairs_hook=unique_fields)
        if not isinstance(row, list) or len(row) != 2:
            raise ValueError(f"expected [ordinal, value], got {row!r}")
        i, value = row
        if type(i) is not int or i in rows:
            raise ValueError(f"invalid or repeated Lean ordinal: {i!r}")
        if not isinstance(value, dict) or value.get("type") not in ("i32", "i64"):
            raise ValueError(f"case {i}: not an integer observation: {value!r}")
        _, n = concrete(value)
        if value["value"] != str(n):
            raise ValueError(f"case {i}: expected unsigned decimal bits: {value!r}")
        rows[i] = value
    if list(rows) != list(ordinals):
        raise ValueError(f"expected Lean ordinals {list(ordinals)}, got {list(rows)}")
    return rows


def signext_lean(module, exports, cases, folder, timeout):
    lines = ["import WasmTest.SignExtension", "#eval do"]
    for e in exports:
        trials = []
        for i in e.ordinals:
            t, n = concrete(cases[i]["action"]["args"][0])
            ctor = {"i32": ".int32", "i64": ".int64"}[t]
            trials.append(f"({i}, {ctor} {n})")
        body = list(module[e.start:e.start + 6])
        lines.append(f"  WasmTest.SignExtension.printCases ⟨#{body}⟩ #[{', '.join(trials)}]")
    source = ("\n".join(lines) + "\n").encode()
    (folder / "batch.lean").write_bytes(source)
    stdout = folder / "lean.stdout"
    with stdout.open("wb") as out, (folder / "lean.stderr").open("wb") as err:
        offline_lake("env", "lean", "--stdin", input=source, stdout=out, stderr=err, timeout=timeout)
    return parse_signext_rows(stdout.read_bytes(), cases)


def signext_fuzz_batches(width, exports, count, seed):
    bits = SCALARS[width]
    # Separate streams keep each export's operands stable across batch sizes and longer runs.
    streams = {e.field: random.Random(f"{seed}:{width}:{e.field}") for e in exports}
    for start in range(0, count, 32):  # bound the generated Lean program, not the campaign
        stop = min(start + 32, count)
        batch, cases = [], {}
        for slot, e in enumerate(exports):
            k = {"extend8_s": 8, "extend16_s": 16, "extend32_s": 32}[e.field]
            sign, mask = 1 << (k - 1), (1 << k) - 1
            edges = (0, 1, sign - 1, sign, sign + 1, mask)
            ids = range(slot * count + start + 1, slot * count + stop + 1)
            batch.append(e._replace(ordinals=ids))
            for trial, i in enumerate(ids, start):
                n = streams[e.field].getrandbits(bits)
                if trial % 2 == 0:
                    n = (n & ~mask) | edges[(trial // 2) % len(edges)]
                low = n & mask
                signed = low if low < sign else low - (1 << k)
                cases[i] = {"type": "assert_return",
                            "action": {"type": "invoke", "field": e.field,
                                       "args": [{"type": width, "value": str(n)}]},
                            "expected": [{"type": width, "value": str(signed % (1 << bits))}]}
        yield start, batch, cases


def signext_pairs(args, width, module, exports, cases, folder, records, *, seed=None):
    folder.mkdir()
    filename = f"{width}.0.wasm"
    (folder / filename).write_bytes(module)
    rows = signext_lean(module, exports, cases, folder, args.timeout)
    with (folder / "oracle.raw").open("wb") as raw, Wasm3Client(
            args.wasm3, timeout=args.timeout, record=raw.write) as client:
        client.request({"type": "reset"})
        loaded = client.request({"type": "module", "name": width, "bytes": module.hex()})
        if loaded["kind"] != "ok":
            raise ValueError(f"{filename}: wasm3 module load: {loaded}")
        for e in exports:
            for i in e.ordinals:
                c = cases[i]
                case_id = (["converted", f"{width}.json", i, c["line"]] if seed is None
                           else ["fuzz-signext", seed, width, i])
                lean = {"kind": "return", "values": [rows[i]]}
                try:
                    oracle = client.request({**c["action"], "module": width})
                except FAULTS as err:
                    raise ValueError(f"{case_id}: wasm3: {err}") from err
                agrees = compare_pair(c, lean, oracle, allow_choices=False)
                dump_line(records, {"id": case_id, "revision": FIXTURE_REV, "module": filename,
                                    "module_sha256": SIGNEXT[width][0], "function_index": e.index,
                                    "byte_range": [e.start, e.start + 6], "export": e.field,
                                    "args": c["action"]["args"], "expected": c["expected"],
                                    "lean": lean, "oracle": oracle, "agrees": agrees})
                if agrees:
                    yield i, (c, lean, oracle)
                elif seed is not None:
                    message = (f"Disagreement {case_id}: {width}.{e.field}({c['action']['args'][0]['value']})"
                               f"\n  expected: {c['expected']}\n  Lean: {lean}\n  wasm3: {oracle}")
                    if not args.keep_going:
                        raise SystemExit(f"{message}\n  Evidence: {folder.parent / 'cases.jsonl'}"
                                         f"\n  Replay: {folder.parent / 'replay.txt'}")
                    print(message, file=sys.stderr)
                else:
                    print(f"Mismatch: {case_id} (see cases.jsonl)", file=sys.stderr)


def signext_directory(prefix):
    parent = CACHE / "fragment-results"
    parent.mkdir(parents=True, exist_ok=True)
    out_dir = Path(mkdtemp(prefix=prefix, dir=parent))
    print(f"Evidence: {out_dir}", flush=True)
    return out_dir


def prepare_signext(args, out_dir):
    inputs = list(signext_inputs())
    args.wasm3 = args.wasm3.resolve()
    verify_profile(args, pinned_policy(), out_dir)
    offline_lake("--log-level=error", "build", "WasmTest.SignExtension")
    return inputs


def check_signext(args):
    out_dir = signext_directory("signext-")
    passed = {}
    try:
        inputs = prepare_signext(args, out_dir)
        with (out_dir / "cases.jsonl").open("w") as records:
            for width, module, exports, cases in inputs:
                for i, trial in signext_pairs(args, width, module, exports, cases, out_dir / width, records):
                    passed[width, i] = trial
    finally:
        print(f"{len(passed)}/38 matched (isolated function bodies)", flush=True)

    if ("i64", 226) not in passed or ("i64", 233) not in passed:
        raise ValueError("wrong-width control requires passing i64.json ordinals 226 and 233")
    narrow, _, oracle = passed["i64", 226]
    wide, lean, _ = passed["i64", 233]
    if wide["action"]["args"] != narrow["action"]["args"]:
        raise ValueError("wrong-width control requires identical arguments")
    crossed = compare_pair(narrow, lean, oracle, allow_choices=False)
    print(f"Wrong-width control (i64.json Lean 233 vs oracle/assertion 226): "
          f"{'ACCEPTED' if crossed else 'rejected'}")
    if len(passed) != 38 or crossed:
        raise SystemExit(1)


def fuzz_signext(args):
    if args.out_dir is None:
        out_dir = signext_directory("fuzz-signext-")
    else:
        out_dir = args.out_dir
        out_dir.mkdir(parents=True)  # an existing campaign must never supply this run's evidence
        print(f"Evidence: {out_dir}", flush=True)
    seed = random.SystemRandom().getrandbits(64) if args.seed is None else args.seed
    cmd = ["python3", "-B", "tools/core3.py", "fuzz-signext", "--seed", str(seed),
           "--cases", str(args.cases), "--wasm3", str(args.wasm3),
           "--skip-features", args.skip_features, "--timeout", str(args.timeout)]
    if args.keep_going:
        cmd.append("--keep-going")
    replay = shlex.join(cmd)
    (out_dir / "replay.txt").write_text(replay + "\n")
    print(f"Replay from package root: {replay}", flush=True)
    matched = 0
    try:
        inputs = prepare_signext(args, out_dir)
        with (out_dir / "cases.jsonl").open("w") as records:
            for width, module, exports, _ in inputs:
                for start, batch, cases in signext_fuzz_batches(width, exports, args.cases, seed):
                    folder = out_dir / f"{width}-{start}"
                    for _ in signext_pairs(args, width, module, batch, cases, folder, records, seed=seed):
                        matched += 1
    except FAULTS as err:
        raise ValueError(f"fuzz run incomplete after {matched} matches: {err}; see {out_dir}") from err
    required = 5 * args.cases
    print(f"{matched}/{required} fuzz comparisons matched (isolated function bodies)")
    if matched != required:
        raise SystemExit(f"Fuzz parity check failed; see {out_dir / 'cases.jsonl'}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("prepare", help="verify and convert pinned fixtures")
    adapter = commands.add_parser("spec-repl", help="serve the upstream text protocol using Lean")
    adapter.add_argument("--lean", type=Path, default=ROOT / ".lake/build/bin/wasm-core")
    tests = commands.add_parser("test", help="run full Lean, upstream protocol and direct differential lanes")
    tests.add_argument("--lean", type=Path, default=ROOT / ".lake/build/bin/wasm-core")
    fragment = commands.add_parser("check-signext", help="compare isolated sign-extension function bodies")
    fuzz = commands.add_parser("fuzz-signext", help="fuzz valid integer operands against live wasm3")
    fuzz.add_argument("--seed", type=int, help="replay seed (default: print a fresh random seed)")
    fuzz.add_argument("--cases", type=int, default=64, help="inputs per export (default: 64)")
    fuzz.add_argument("--out-dir", type=Path, help="write evidence to this new directory")
    fuzz.add_argument("--keep-going", action="store_true", help="record all parity disagreements before failing")
    for p in (tests, fragment, fuzz):
        p.add_argument("--wasm3", type=Path, default=Path("/usr/bin/wasm3"))
        p.add_argument("--skip-features", choices=("atomics", "none"), required=True)
        p.add_argument("--timeout", type=int, default=30, help="per observation watchdog, in seconds")
    args = parser.parse_args()
    if args.command == "prepare":
        prepare()
    elif args.command in {"test", "check-signext", "fuzz-signext"}:
        if args.timeout < 1:
            parser.error("--timeout must be positive")
        if args.command == "test":
            test(args)
        elif args.command == "fuzz-signext":
            if args.cases < 1:
                parser.error("--cases must be positive")
            fuzz_signext(args)
        else:
            check_signext(args)
    else:
        spec_repl(args.lean)


if __name__ == "__main__":
    try:
        main()
    except (OSError, LookupError, TypeError, ValueError, subprocess.SubprocessError) as error:
        sys.exit(f"core3: {error}")
