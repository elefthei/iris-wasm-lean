/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import Iris.Std.RocqPorting

/-! Coq files of `theories/iris/` deliberately not ported. -/

#rocq_ignore_file iriswasm "iris/language/iris_adequacy.v" "entire file is commented out upstream"

/-! Coq declarations that cannot carry `@[rocq_alias]`: Ltacs ported as Lean tactic syntax (macros take no
attributes) and local abbreviations of iris-lean notions. -/

#rocq_ignore iriswasm.iris_lfilled_properties.false_assumption
  "Ltac; ported as the `false_assumption` macro (IrisLfilledProperties)"
#rocq_ignore iriswasm.iris_wasm_lang_properties.false_assumption
  "Ltac duplicate of iris_lfilled_properties.false_assumption; same macro"
#rocq_ignore iriswasm.filled_trap "Ltac; ported as the `filled_trap` macro (IrisLfilledProperties)"
#rocq_ignore iriswasm.simple_filled "Ltac; ported as the `simple_filled` tactic (IrisLfilledProperties)"
#rocq_ignore iriswasm.simple_filled2 "Ltac; ported as the `simple_filled2` tactic (IrisLfilledProperties)"
#rocq_ignore iriswasm.get_tail "Ltac; ported as the `get_tail` tactic (IrisWasmLangProperties)"
#rocq_ignore iriswasm.no_reduce "Ltac; ported as the `no_reduce` tactic (IrisReduceProperties)"
#rocq_ignore iriswasm.empty_list_no_reduce
  "Ltac (declared twice in iris_reduce_properties.v); ported as the `empty_list_no_reduce` macro"
#rocq_ignore iriswasm.intruse_among_values
  "Ltac; ported as the `intruse_among_values` tactic (IrisReduceProperties)"
#rocq_ignore iriswasm.iris_reduce_det_prelude.only_one_reduction
  "Ltac; ported as the scoped `only_one_reduction` tactic (IrisWasm.Helpers.ReduceDetPrelude)"
#rocq_ignore iriswasm.only_one "Ltac; ported as the scoped `only_one` tactic (IrisWasm.Helpers.ReduceDetPrelude)"
#rocq_ignore iriswasm.iris_wp_def.only_one_reduction
  "Ltac; ported as the `only_one_reduction` tactic (IrisWpDef)"
#rocq_ignore iriswasm.reduce_det_label.reducible "Local abbreviation of iris-lean `Reducible`"
#rocq_ignore iriswasm.iris_atomicity.reducible "Local abbreviation of iris-lean `Reducible`"
#rocq_ignore iriswasm.irisGS "iris-lean's `IrisGS_gen` plays this role (IrisWp variable binder)"
#rocq_ignore iriswasm.build_llfill "Ltac; ported as the `build_llfill` macro (Proofmode)"
#rocq_ignore iriswasm.build_ctx "Ltac; ported as the `build_ctx` elaborator (Proofmode)"
#rocq_ignore iriswasm.deconstruct_ctx "Ltac; ported as the `deconstruct_ctx` elaborator (Proofmode)"
#rocq_ignore iriswasm.iris_examples_factorial.type_next_rewrite
  "Ltac; module typing is proved by the type checker (`b_e_type_checker_reflects_typing`)"
#rocq_ignore iriswasm.iris_examples_factorial.type_next
  "Ltac; module typing is proved by the type checker (`b_e_type_checker_reflects_typing`)"
#rocq_ignore iriswasm.iris_examples_factorial.weaken
  "Ltac; module typing is proved by the type checker (`b_e_type_checker_reflects_typing`)"
#rocq_ignore iriswasm.iris_examples_factorial.type_go
  "Ltac; module typing is proved by the type checker (`b_e_type_checker_reflects_typing`)"
#rocq_ignore iriswasm.unfold_irwt_all "Ltac; ported as the `unfold_irwt_all` macro (IrisInstantiation)"
#rocq_ignore iriswasm.iris_robust_example.type_next
  "Ltac; module typing is proved by the type checker (`b_e_type_checker_reflects_typing`)"
#rocq_ignore iriswasm.iris_robust_example_host.type_next
  "Ltac; module typing is proved by the type checker (`b_e_type_checker_reflects_typing`)"
#rocq_ignore iriswasm.iris_robust_example.unfold_irwt_all
  "Ltac; duplicate of the `unfold_irwt_all` macro (IrisInstantiation)"
#rocq_ignore iriswasm.iris_robust_example_host.unfold_irwt_all
  "Ltac; duplicate of the `unfold_irwt_all` macro (IrisInstantiation)"
#rocq_ignore iriswasm.invert_cllookup
  "Ltac; closure lookups are resolved by the private `spec*_holds` lemmas (StackInstantiation)"
#rocq_ignore iriswasm.resolve_cl_lookup
  "Ltac; closure lookups are resolved by the private `spec*_holds` lemmas (StackInstantiation)"
