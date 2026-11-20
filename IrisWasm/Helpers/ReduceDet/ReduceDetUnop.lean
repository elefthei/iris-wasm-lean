/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Helpers.Prelude.IrisReduceDetPrelude

/-! Port of `theories/iris/helpers/reduce_det/reduce_det_unop.v`. -/

namespace IrisWasm

open Wasm Helpers.ReduceDetPrelude
open AdministrativeInstruction (basic trap)

@[rocq_alias iriswasm.unop_det]
theorem unop_det {v : Value} {op : Unop} {t : ValueType} {s : StoreRecord} {f : Frame}
    {s' : StoreRecord} {f' : Frame} {es : List AdministrativeInstruction} :
    Reduce s f [basic (.const v), basic (.unop t op)] s' f' es →
    reduceDetGoal s f [basic (.const (appUnop op v))] s' f' es
      [basic (.const v), basic (.unop t op)] := by
  intro Hred
  only_one Hred

end IrisWasm
