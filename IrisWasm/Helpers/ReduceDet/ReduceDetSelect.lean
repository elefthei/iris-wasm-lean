/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Helpers.Prelude.IrisReduceDetPrelude

/-! Port of `theories/iris/helpers/reduce_det/reduce_det_select.v`. -/

namespace IrisWasm

open Wasm Helpers.ReduceDetPrelude
open AdministrativeInstruction (basic trap)

@[rocq_alias iriswasm.select_false_det]
theorem select_false_det {v1 v2 : Value} {n : I32} {s : StoreRecord} {f : Frame}
    {s' : StoreRecord} {f' : Frame} {es : List AdministrativeInstruction} :
    n = Wasm.Int.zero →
    Reduce s f [basic (.const v1), basic (.const v2), basic (.const (.int32 n)), basic .select]
      s' f' es →
    reduceDetGoal s f [basic (.const v2)] s' f' es
      [basic (.const v1), basic (.const v2), basic (.const (.int32 n)), basic .select] := by
  intro _ Hred
  only_one Hred

@[rocq_alias iriswasm.select_true_det]
theorem select_true_det {v1 v2 : Value} {n : I32} {s : StoreRecord} {f : Frame}
    {s' : StoreRecord} {f' : Frame} {es : List AdministrativeInstruction} :
    n ≠ Wasm.Int.zero →
    Reduce s f [basic (.const v1), basic (.const v2), basic (.const (.int32 n)), basic .select]
      s' f' es →
    reduceDetGoal s f [basic (.const v1)] s' f' es
      [basic (.const v1), basic (.const v2), basic (.const (.int32 n)), basic .select] := by
  intro _ Hred
  only_one Hred

end IrisWasm
