# Iris-Wasm in Lean 4

Iris-Wasm lets you prove a property of a WebAssembly module in isolation, then use that
property when you link the module to a client. The [PLDI 2023 paper](https://dl.acm.org/doi/10.1145/3591265)
develops the logic for WebAssembly 1.0 in Coq. This repository ports the
[Coq proofs](https://github.com/logsem/iriswasm) to Lean 4 using
[iris-lean](https://github.com/leanprover-community/iris-lean).

The [stack case study](IrisWasm/Examples/Stack/) is a good place to start: you can read the
[proof for `push`](IrisWasm/Examples/Stack/Push.lean) on its own, then see how a
[client](IrisWasm/Examples/Stack/StackClient.lean) uses the stack. The port follows the
original development file by file, from the Wasm type checker and reduction rules through
module instantiation, the logical relation and its fundamental theorem, and every worked
example, including the host-level adequacy proof.

## Build the Lean library

Install [elan](https://github.com/leanprover/elan) and Git, then clone the Lean port:

```sh
git clone https://github.com/elefthei/iris-wasm-lean.git
cd iris-wasm-lean
```

Run the following in the directory containing `lean-toolchain`. Elan selects
`leanprover/lean4:v4.36.0`; Lake fetches the dependencies on the first build, including
iris-lean `v4.36.0` and [ctrees-lean](https://github.com/elefthei/ctrees-lean) `v0.1.2`.

```bash
lake build
```

`lake build` checks the `Wasm`, `IrisWasm` and `WasmTest` libraries. You do not need Coq
or wasm3 for this. To build just the exported semantics and its exact-step examples, run
`lake build IrisWasm WasmTest.Denotational`.

## Check a proof

Save this as `Example.lean` in the package root. `import IrisWasm` brings the program logic
and its examples into scope. Use `import Wasm` when you only need the core language.

```lean
import IrisWasm
open Wasm

example (s : StoreRecord) (f : Frame) :
    Reduce s f [.basic (.const (.int32 0x12340080)), .basic (.unop .i32 (.extendS .i8))]
      s f [.basic (.const (.int32 0xffffff80))] :=
  .simple (.unop rfl rfl)
```

```sh
lake env lean Example.lean
```

Lean exits silently if the proof checks. The instruction `i32.extend8_s` reads the low byte
of `0x12340080`. That byte represents `-128`, so the 32-bit result is `0xffffff80`.
The same `s` and `f` on both sides say the step leaves the store and frame unchanged.
To inspect a module-level theorem, open `Example.lean` in a Lean editor and add
`#check IrisWasm.Examples.Stack.instantiate_stack_spec` to see the stack's instantiation contract.

## Compare Lean with wasm3

The proof above uses the port's own reduction rule. The sign-extension check also asks a
second implementation for the result. Run it when changing the integer decoder, unary
operations or CTree stepper.

With Python 3 and the Lean dependencies installed, fetch the two pinned fixture checkouts
once (no WAST conversion):

```sh
PYTHONPATH=tools python3 -B - <<'PY'
from core3 import checkout, HARNESS, HARNESS_REV, FIXTURES, FIXTURE_REV
checkout(HARNESS, "wasm3/wasm3", HARNESS_REV)
checkout(FIXTURES, "wasm3/wasm-core-testsuite", FIXTURE_REV)
PY
```

Then run the check from the package root with the pinned wasm3 binary and its matching profile:

```sh
python3 -B tools/core3.py check-signext --wasm3 /usr/bin/wasm3 --skip-features=atomics
```

Lean decodes five function bodies from the fixtures and steps each with its original
arguments. wasm3 calls the same exports in the original modules. A passing run reports
`38/38 matched (isolated function bodies)`: both implementations agree with each other
and with the expected bits on all 14 i32 and 24 i64 calls.

The same input distinguishes two instructions. On `32768:i64`, `i64.extend16_s` returns
`18446744073709518848` (the unsigned bits of `-32768`); `i64.extend32_s` returns `32768`.
Once both assertions pass, the driver pairs the second Lean result with the first assertion
and wasm3 result. The driver reports that comparison separately and must reject it.

The driver prints a fresh `.lake/core3/fragment-results/signext-*/` directory for each run.
Use `cases.jsonl` to find the fixture line, arguments and results; the original modules,
Lean batches and raw output are beside it in the `i32/` and `i64/` subdirectories.
The full suite counts its pairs separately. This check covers only isolated function bodies;
it does not test whole-module validation or instantiation in Lean.

## Layout

| Directory | Contents | Coq source |
|---|---|---|
| `Wasm/` | Wasm 1.0 syntax, numerics, operational semantics, typing, type preservation and progress, instantiation, type checker | `theories/*.v` |
| `IrisWasm/` | Iris language instance, custom WP, proof rules, instantiation spec, host language, logical relation, examples | `theories/iris/**` |
| `IrisWasm/Denotational/` | Effect-based choice trees and exact-step correspondence with the Iris language | original Lean development |
| `WasmTest/` | Checks of numerics, operations, the type checker, and denotational observations | none |

Each Coq file `theories/<path>/snake_name.v` maps to one Lean file with the path components in UpperCamelCase, e.g. `theories/iris/examples/stack/function/is_empty.v` becomes `IrisWasm/Examples/Stack/Function/IsEmpty.lean`.

## Correspondence with the Coq development

- Every ported Coq declaration carries `@[rocq_alias iriswasm.<CoqName>]`, so `Rocq.iriswasm.<CoqName>` resolves to its Lean counterpart. Each declaration that is deliberately left out (Ltac tactics, mathcomp/stdpp bridging lemmas) has a `#rocq_ignore` entry with a reason.
- Files outside the scope of the Iris development (binary format, parser, interpreter, extraction, pretty printing) and the upstream `iris_adequacy.v`, which is commented out, are listed with `#rocq_ignore_file` in `Wasm/Porting.lean` and `IrisWasm/Porting.lean`.
- Lemma names are kept verbatim. Types and Prop-valued relations use UpperCamelCase (`reduce` → `Reduce`, `be_typing` → `BeTyping`), and definitions use lowerCamelCase (`app_binop` → `appBinop`).
- Integers and floats use bit patterns. `Wasm.IEEE` computes binary32/64 arithmetic with integer intermediates, including ties-to-even rounding, subnormals and signed zero. The concrete float operations choose a canonical NaN for generated NaNs. Coq `gmap` becomes `Std.ExtTreeMap`.

### Deviations

- **Later credits.** The custom Wasm WP is built on iris-lean's WP definition, which threads later credits; each step consumes one. No rule statement mentions them.
- **Host WP.** The host language uses iris-lean's standard WP, as the Coq development uses Iris's.
- **Module typing.** Typing of the example modules is proved by reflection through the verified type checker (`b_e_type_checker_reflects_typing`) instead of porting the Coq typing tactics.
- **Packed loads.** Signed loads extend the sign bit of the last byte read. Their WP retains ownership of the unextended bytes in memory.
- **Runtime storage.** Memory uses sparse 64-KiB pages; uniform table regions use runs. Runtime
  lookup and growth do not build a list of every entry. The list views remain available to proofs.
- **Numeric instructions and initializers.** Scalar sign extension and saturating truncation run
  through the same reduction and finite effect program as other arithmetic. Integer constant
  expressions can add, subtract and multiply when initializing globals and segment offsets.
- **Numeric traps and stuck terms.** Integer division by zero traps. An operand of the wrong width,
  a comparison in the wrong opcode family, or a width-changing reinterpretation has no successor.
- **Full-width vectors.** `v128.const` preserves all 16 bytes. NOT, AND, ANDNOT, OR, XOR, BITSELECT
  and ANY_TRUE operate on those bits. A full-width memory access reads or writes 16 bytes;
  scalar packed accesses require an integer wider than the packed field. Lane arithmetic and
  relaxed SIMD are not covered by these rules.
- **`si64_trunc`.** The truncation range check uses the i64 bound; upstream `numerics.v:1745` uses the i32 bound.
- **Name clashes.** Lemmas whose Coq names occur in more than one file live in per-file namespaces (e.g. `IrisWasm.Examples.Stack.StackClient`), with file-qualified aliases.

## Status

The ported theorems below apply to the public language in this tree. They are not a conformance claim for all Core 3 modules.

Main results:

| Result | Lean name |
|---|---|
| Determinism outside grow-memory and trap reductions | `IrisWasm.reduce_det` |
| Reachable configurations and results after exactly `i` primitive steps | `IrisWasm.Denotational.exact_config_iff`, `IrisWasm.Denotational.exact_result_iff` |
| Type preservation / progress | `Wasm.t_preservation`, `Wasm.t_progress` |
| Instantiation spec | `IrisWasm.instantiation_wasm_spec` |
| Fundamental theorem of the logical relation | `IrisWasm.be_fundamental` |
| Instance allocation is safe | `IrisWasm.interp_instance_alloc` |
| Host-level adequacy of the robust example | `IrisWasm.Examples.lse_adequacy` |
| Stack module specs | `IrisWasm.Examples.Stack.instantiate_stack_spec`, `instantiate_stack_adv_spec`, `instantiate_client` |

For a basic program `p`, start `IrisWasm.Denotational.denote` at `(Wasm.toEList p, σ)`. Each native τ is one Iris primitive reduction. `cutAfter i` observes the residual instructions, store and frame at that exact index, including nonterminal or stuck endpoints. A pending host call is an Iris result at its current index; its request and reply form one external observation and do not consume a Wasm step.

Entering a native closure from `.invoke` creates the callee frame around its result label in one
step. It does not execute a synthetic source `block`. The label arity is the number of results;
caller operands below the arguments and the caller's frame survive the return.

`runRound` and the native CTree fold the same finite effect program. `runCut n` follows the concrete
chooser for exactly `n` internal reductions; `runCut_sound` proves the residual is reached in the
native cut and the Iris singleton pool. It does not run a module loader or a host.

## Core 3 coverage and known limits

`Wasm.Binary` reads bounded sections and function bodies, recursive types, external signatures,
indexed memory32/memory64 operations, local/global indices, scalar numerics and full-width
`v128` logical operations. Binary local groups retain their repeat counts; decoding a group of
2³²−1 locals does not allocate a list of that length.

`Wasm.CoreTypes.validateGroups_iff` characterizes acceptance of a decoded type section:
each declared parent is earlier and non-final, the child's body matches it, and the output
contains each closed projection in declaration order. `Composite.matches_iff` and
`External.matches_iff` prove the variance rules for those closed types, including invariant
mutable fields, tags and table elements. These theorems do not extend the runtime's value types.

`Binary.structuredExpr` consumes nested `block`/`loop`/`if` regions through their matching `end`;
the caller supplies the inline-type and leaf readers. An `else` cannot cross a block or loop.
`block`, `loop`, and `if_` retain their block-type immediate: `.result none`, `.result (some t)`,
or `.index i`. Indexed block and loop entry resolve `i` in the **active frame's instance**.
Block labels use result arity; loop labels use parameter arity and retain the index for re-entry.
`if_` chooses a branch first: a missing index makes the resulting `block` stuck, not the `if_`.

Loads and stores resolve `MemArg.memory` in the active instance, then add the unsigned operand
and `MemArg.offset` as natural numbers. Validation checks the offset and operand against the
selected memory's declared width. `memory.size` returns an exact page count in that width;
it has no step on a partial page. A permitted grow failure returns all ones in the **operand**
width, even if its index does not resolve. Iris tracks width, byte length and declared minimum
by store address, so imports of the same memory see the same writes and growth.

`initMems` returns the updated store on success or the store at the first failed segment. The
existing host instantiation rule still checks segment bounds before initialization; this helper
does not establish the full Core contract for a trapping initializer or start.

The whole-module decoder and `wasm-core` executable are not implemented. `tools/core3.py prepare`
checks out the pinned inputs and checks that each deployed WAST converts to JSON. With the pinned
wasm-tools 1.256.0 this exits nonzero: `gc/type-subtyping.wast:958` uses a second supertype in
an `assert_invalid` that the converter cannot parse. A missing script is an infrastructure failure.
The driver refuses untracked files in either pinned corpus input directory. Its `by_script`
counts separate frontend-only checks, paired commands, exclusions and infrastructure failures;
each command record gives the reason for any exclusion.

`WasmTest/Core3/global-initializer.wast` diagnoses the pinned instantiation rules. `$evalglobals`
stores a module-relative type index before `$allocmodule` appends a second, closed global. Reading
the export succeeds in the reference interpreter, but the first global's type cannot satisfy
`Globalinst_ok` in the empty type context. This tree does not claim full Core 3 store validity.

There is also a boundary case in the pinned [`memory.fill-succ` residual](https://github.com/WebAssembly/spec/blob/6fca707686ed4f36a1e30ec2ae7d3dd32b276704/specification/wasm-3.0/4.3-execution.instructions.spectec#L573-L586).
In a 65,536-page memory32, filling one byte at `0xffffffff` is in bounds. The residual
contains `i32.const (i+1)` with mathematical value `2^32`, outside the `i32` grammar.
`WasmTest.Memory64.last_byte_fill_residual` checks the same arithmetic for both widths.
The [bulk-memory erratum](WasmTest/Core3/bulk-memory-errata.patch) uses modular addition
only for the address constants emitted by forward `memory.fill`, `memory.copy` and `memory.init`.
Bounds still use natural numbers, and the zero-count continuation still takes a step. The
patch does not modify the pinned checkout or count those rules as implemented in Lean.

## Citation

This repository ports the Coq artefact of:

> Xiaojia Rao, Aïna Linn Georges, Maxime Legoupil, Conrad Watt, Jean Pichon-Pharabod, Philippa Gardner, and Lars Birkedal.
> **Iris-Wasm: Robust and Modular Verification of WebAssembly Programs.**
> Proc. ACM Program. Lang. 7, PLDI, Article 151 (June 2023).
> <https://dl.acm.org/doi/10.1145/3591265> · [Paper PDF](https://iris-project.org/pdfs/2023-pldi-iris-wasm.pdf)

```bibtex
@article{rao2023iriswasm,
  author    = {Rao, Xiaojia and Georges, A\"{\i}na Linn and Legoupil, Maxime and Watt, Conrad and Pichon-Pharabod, Jean and Gardner, Philippa and Birkedal, Lars},
  title     = {Iris-Wasm: Robust and Modular Verification of WebAssembly Programs},
  journal   = {Proc. ACM Program. Lang.},
  volume    = {7},
  number    = {PLDI},
  articleno = {151},
  year      = {2023},
  doi       = {10.1145/3591265},
  url       = {https://dl.acm.org/doi/10.1145/3591265}
}
```

Source revision ported: [`logsem/iriswasm@e37f838`](https://github.com/logsem/iriswasm/tree/e37f8387a1171d104d78a2f77f9e637e090cf3d4).

## License

MIT, as for the upstream development. See `LICENSE`.
