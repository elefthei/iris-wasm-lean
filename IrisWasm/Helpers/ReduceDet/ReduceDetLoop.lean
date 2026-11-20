/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Helpers.Prelude.IrisReduceDetPrelude

/-! Port of `theories/iris/helpers/reduce_det/reduce_det_loop.v`. -/

namespace IrisWasm

open Wasm Helpers.ReduceDetPrelude
open AdministrativeInstruction (basic trap)

@[rocq_alias iriswasm.loop_det]
theorem loop_det {vs : List AdministrativeInstruction} {n m : Nat} {t1s t2s : List ValueType}
    {s : StoreRecord} {f : Frame} {es : List BasicInstruction} {s' : StoreRecord} {f' : Frame}
    {es' : List AdministrativeInstruction} :
    constList vs = true → vs.length = n → t1s.length = n → t2s.length = m →
    Reduce s f (vs ++ [basic (.loop (.tf t1s t2s) es)]) s' f' es' →
    reduceDetGoal s f [.label n [basic (.loop (.tf t1s t2s) es)] (vs ++ toEList es)] s' f' es'
      (vs ++ [basic (.loop (.tf t1s t2s) es)]) := by
  intro _ _ _ _ Hred
  only_one Hred

end IrisWasm
