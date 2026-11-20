/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Helpers.Prelude.IrisReduceDetPrelude

/-! Port of `theories/iris/helpers/reduce_det/reduce_det_return.v`. -/

namespace IrisWasm

open Wasm Helpers.ReduceDetPrelude
open AdministrativeInstruction (basic trap)

@[rocq_alias iriswasm.return_det]
theorem return_det {vs : List AdministrativeInstruction} {n i : Nat} {lh : Lholed} {s : StoreRecord}
    {f f0 : Frame} {es : List AdministrativeInstruction} {s' : StoreRecord} {f' : Frame}
    {es' : List AdministrativeInstruction} :
    constList vs = true → vs.length = n →
    lfilled i lh (vs ++ [basic .return_]) es = true →
    Reduce s f [.local n f0 es] s' f' es' →
    reduceDetGoal s f vs s' f' es' [.local n f0 es] := by
  intro hvs hl hret Hred
  exact .inl (local_step_goal (.inr (.inr ⟨i, lh, vs, hvs, hl, hret, rfl⟩)) Hred)

end IrisWasm
