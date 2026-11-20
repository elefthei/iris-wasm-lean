/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Helpers.Prelude.IrisReduceDetPrelude

/-! Port of `theories/iris/helpers/reduce_det/reduce_det_binop.v`. -/

namespace IrisWasm

open Wasm Helpers.ReduceDetPrelude
open AdministrativeInstruction (basic trap)

@[rocq_alias iriswasm.binop_det]
theorem binop_det {v1 v2 v : Value} {op : Binop} {t : ValueType} {s : StoreRecord} {f : Frame}
    {s' : StoreRecord} {f' : Frame} {es : List AdministrativeInstruction} :
    appBinop op v1 v2 = some v →
    Reduce s f [basic (.const v1), basic (.const v2), basic (.binop t op)] s' f' es →
    reduceDetGoal s f [basic (.const v)] s' f' es
      [basic (.const v1), basic (.const v2), basic (.binop t op)] := by
  intro _ Hred
  only_one Hred

@[rocq_alias iriswasm.binop_none_det]
theorem binop_none_det {v1 v2 : Value} {op : Binop} {t : ValueType} {s : StoreRecord} {f : Frame}
    {s' : StoreRecord} {f' : Frame} {es : List AdministrativeInstruction} :
    appBinop op v1 v2 = none →
    Reduce s f [basic (.const v1), basic (.const v2), basic (.binop t op)] s' f' es →
    reduceDetGoal s f [trap] s' f' es
      [basic (.const v1), basic (.const v2), basic (.binop t op)] := by
  intro _ Hred
  only_one Hred

end IrisWasm
