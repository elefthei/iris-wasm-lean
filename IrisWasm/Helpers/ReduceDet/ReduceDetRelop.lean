/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Helpers.Prelude.IrisReduceDetPrelude

/-! Port of `theories/iris/helpers/reduce_det/reduce_det_relop.v`. -/

namespace IrisWasm

open Wasm Helpers.ReduceDetPrelude
open AdministrativeInstruction (basic trap)

@[rocq_alias iriswasm.relop_det]
theorem relop_det {v1 v2 : Value} {op : Relop} {t : ValueType} {s : StoreRecord} {f : Frame}
    {s' : StoreRecord} {f' : Frame} {es : List AdministrativeInstruction} :
    Reduce s f [basic (.const v1), basic (.const v2), basic (.relop t op)] s' f' es →
    reduceDetGoal s f [basic (.const (.int32 (wasmBool (appRelop op v1 v2))))] s' f' es
      [basic (.const v1), basic (.const v2), basic (.relop t op)] := by
  intro Hred
  only_one Hred

end IrisWasm
