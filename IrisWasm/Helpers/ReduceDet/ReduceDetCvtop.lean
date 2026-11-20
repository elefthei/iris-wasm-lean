/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Helpers.Prelude.IrisReduceDetPrelude

/-! Port of `theories/iris/helpers/reduce_det/reduce_det_cvtop.v`. -/

namespace IrisWasm

open Wasm Helpers.ReduceDetPrelude
open AdministrativeInstruction (basic trap)

@[rocq_alias iriswasm.cvtop_convert_det]
theorem cvtop_convert_det {v v' : Value} {t1 t2 : ValueType} {sx : Option Sx} {s : StoreRecord}
    {f : Frame} {s' : StoreRecord} {f' : Frame} {es : List AdministrativeInstruction} :
    typesAgree t1 v = true → cvt t2 sx v = some v' →
    Reduce s f [basic (.const v), basic (.cvtop t2 .convert t1 sx)] s' f' es →
    reduceDetGoal s f [basic (.const v')] s' f' es
      [basic (.const v), basic (.cvtop t2 .convert t1 sx)] := by
  intro _ _ Hred
  only_one Hred

@[rocq_alias iriswasm.cvtop_convert_none_det]
theorem cvtop_convert_none_det {v : Value} {t1 t2 : ValueType} {sx : Option Sx} {s : StoreRecord}
    {f : Frame} {s' : StoreRecord} {f' : Frame} {es : List AdministrativeInstruction} :
    typesAgree t1 v = true → cvt t2 sx v = none →
    Reduce s f [basic (.const v), basic (.cvtop t2 .convert t1 sx)] s' f' es →
    reduceDetGoal s f [trap] s' f' es [basic (.const v), basic (.cvtop t2 .convert t1 sx)] := by
  intro _ _ Hred
  only_one Hred

@[rocq_alias iriswasm.cvtop_reinterpret_det]
theorem cvtop_reinterpret_det {v : Value} {t1 t2 : ValueType} {s : StoreRecord} {f : Frame}
    {s' : StoreRecord} {f' : Frame} {es : List AdministrativeInstruction} :
    typesAgree t1 v = true →
    Reduce s f [basic (.const v), basic (.cvtop t2 .reinterpret t1 none)] s' f' es →
    reduceDetGoal s f [basic (.const (wasmDeserialise (bits v) t2))] s' f' es
      [basic (.const v), basic (.cvtop t2 .reinterpret t1 none)] := by
  intro _ Hred
  only_one Hred

end IrisWasm
