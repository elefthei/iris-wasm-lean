/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Helpers.Prelude.IrisReduceDetPrelude

/-! Port of `theories/iris/helpers/reduce_det/reduce_det_local.v`. -/

namespace IrisWasm

open Wasm Helpers.ReduceDetPrelude
open AdministrativeInstruction (basic trap)

@[rocq_alias iriswasm.local_det]
theorem local_det {s : StoreRecord} {f : Frame} {es : List AdministrativeInstruction}
    {s' : StoreRecord} {f' : Frame} {es' : List AdministrativeInstruction} {ws2 : StoreRecord}
    {n : Nat} {f0 f2 : Frame} {es2 : List AdministrativeInstruction} {nnn : Nat} :
    (∀ (f f2 f1 : Frame) (es2 es1 es : List AdministrativeInstruction),
      Reduce s f es s' f1 es1 → Reduce s f es ws2 f2 es2 → lengthRec es < nnn →
        reduceDetGoal s' f1 es1 ws2 f2 es2 es) →
    Reduce s f es s' f' es' →
    Reduce s f0 [.local n f es] ws2 f2 es2 →
    lengthRec [.local n f es] < nnn + 1 →
    ((∀ (f f2 f1 : Frame) (es2 es1 es : List AdministrativeInstruction),
      Reduce s f es s' f1 es1 → Reduce s f es ws2 f2 es2 → lengthRec es < nnn →
        reduceDetGoal s' f1 es1 ws2 f2 es2 es) →
      Reduce s f es ws2 f2 es2 → lengthRec es < nnn + 1 →
        reduceDetGoal s' f' es' ws2 f2 es2 es) →
    reduceDetGoal s' f0 [.local n f' es'] ws2 f2 es2 [.local n f es] := by
  intro IHnnn H Hred2 Hlen _
  rcases inv_local' Hred2 with ⟨-, -, hst⟩ | ⟨f1, LI', hr, rfl, rfl⟩
  · exact (local_step_no_reduce hst H).elim
  · exact goal_local (IHnnn _ _ _ _ _ _ H hr (by rw [lengthRec_local] at Hlen; omega))

end IrisWasm
