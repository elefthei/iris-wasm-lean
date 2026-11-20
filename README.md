# Iris-Wasm in Lean 4

A Lean 4 port of [Iris-Wasm](https://github.com/logsem/iriswasm), a higher-order separation logic and logical relation for WebAssembly 1.0, built on [iris-lean](https://github.com/leanprover-community/iris-lean).

The port follows the Coq development file by file: the Wasm 1.0 semantics and type system, the Iris language instance with its custom weakest precondition, the proof rules, module instantiation, the host language, the logical relation with its fundamental theorem, the type checker, and every example including the stack case study and host-level adequacy.

## Citation

This repository ports the Coq artefact of:

> Xiaojia Rao, Aïna Linn Georges, Maxime Legoupil, Conrad Watt, Jean Pichon-Pharabod, Philippa Gardner, and Lars Birkedal.
> **Iris-Wasm: Robust and Modular Verification of WebAssembly Programs.**
> Proc. ACM Program. Lang. 7, PLDI, Article 151 (June 2023).
> <https://dl.acm.org/doi/10.1145/3591265>

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

## Building

Requires [elan](https://github.com/leanprover/elan). The toolchain (`leanprover/lean4:v4.36.0`) is pinned in `lean-toolchain` and iris-lean (tag `v4.36.0`) in `lakefile.toml`.

```bash
lake build
```

The first build also compiles iris-lean.

## Layout

| Directory | Contents | Coq source |
|---|---|---|
| `Wasm/` | Wasm 1.0 syntax, numerics, operational semantics, typing, type preservation and progress, instantiation, type checker | `theories/*.v` |
| `IrisWasm/` | Iris language instance, custom WP, proof rules, instantiation spec, host language, logical relation, examples | `theories/iris/**` |
| `WasmTest/` | Executable checks of numerics, operations and the type checker | none |

Each Coq file `theories/<path>/snake_name.v` maps to one Lean file with the path components in UpperCamelCase, e.g. `theories/iris/examples/stack/function/is_empty.v` becomes `IrisWasm/Examples/Stack/Function/IsEmpty.lean`.

## Correspondence with the Coq development

- Every ported Coq declaration carries `@[rocq_alias iriswasm.<CoqName>]`, so `Rocq.iriswasm.<CoqName>` resolves to its Lean counterpart. Each declaration that is deliberately left out (Ltac tactics, mathcomp/stdpp bridging lemmas) has a `#rocq_ignore` entry with a reason.
- Files outside the scope of the Iris development (binary format, parser, interpreter, extraction, pretty printing) and the upstream `iris_adequacy.v`, which is commented out, are listed with `#rocq_ignore_file` in `Wasm/Porting.lean` and `IrisWasm/Porting.lean`.
- Lemma names are kept verbatim. Types and Prop-valued relations use UpperCamelCase (`reduce` → `Reduce`, `be_typing` → `BeTyping`), and definitions use lowerCamelCase (`app_binop` → `appBinop`).
- Integers are `BitVec 32`/`BitVec 64`. Floats wrap the bit patterns of Lean's `Float32`/`Float`. Coq `gmap` becomes `Std.ExtTreeMap`.

### Deviations

- **Later credits.** The custom Wasm WP is built on iris-lean's WP definition, which threads later credits; each step consumes one. No rule statement mentions them.
- **Host WP.** The host language uses iris-lean's standard WP, as the Coq development uses Iris's.
- **Module typing.** Typing of the example modules is proved by reflection through the verified type checker (`b_e_type_checker_reflects_typing`) instead of porting the Coq typing tactics.
- **`si64_trunc`.** The truncation range check uses the i64 bound; upstream `numerics.v:1745` uses the i32 bound.
- **Name clashes.** Lemmas whose Coq names occur in more than one file live in per-file namespaces (e.g. `IrisWasm.Examples.Stack.StackClient`), with file-qualified aliases.

## Status

The port is complete. The build has no `sorry`, `admit`, `axiom`, `native_decide` or `implemented_by`. Every constant in `Wasm` and `IrisWasm` depends only on `propext`, `Classical.choice` and `Quot.sound`.

Main results:

| Result | Lean name |
|---|---|
| Determinism of reduction | `IrisWasm.reduce_det` |
| Type preservation / progress | `Wasm.t_preservation`, `Wasm.t_progress` |
| Instantiation spec | `IrisWasm.instantiation_wasm_spec` |
| Fundamental theorem of the logical relation | `IrisWasm.be_fundamental` |
| Instance allocation is safe | `IrisWasm.interp_instance_alloc` |
| Host-level adequacy of the robust example | `IrisWasm.Examples.lse_adequacy` |
| Stack module specs | `IrisWasm.Examples.Stack.instantiate_stack_spec`, `instantiate_stack_adv_spec`, `instantiate_client` |

## License

MIT, as for the upstream development. See `LICENSE`.
