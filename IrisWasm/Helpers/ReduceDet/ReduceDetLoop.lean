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

theorem loop_det {vs : List AdministrativeInstruction} {bt : BlockType} {t1s t2s : List ValueType}
    {s : StoreRecord} {f : Frame} {es : List BasicInstruction} {s' : StoreRecord} {f' : Frame}
    {es' : List AdministrativeInstruction} :
    expandBlockType f.inst.types bt = some (.tf t1s t2s) →
    constList vs = true → vs.length = t1s.length →
    Reduce s f (vs ++ [basic (.loop bt es)]) s' f' es' →
    reduceDetGoal s f [.label t1s.length [basic (.loop bt es)] (vs ++ toEList es)] s' f' es'
      (vs ++ [basic (.loop bt es)]) := by
  intro hsig hc hlen hr
  only_one hr <;> simp_all

end IrisWasm
