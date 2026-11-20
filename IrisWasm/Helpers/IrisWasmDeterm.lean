/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Helpers.ReduceDet.ReduceDetInvokeNative
import IrisWasm.Helpers.ReduceDet.ReduceDetUnop
import IrisWasm.Helpers.ReduceDet.ReduceDetBinop
import IrisWasm.Helpers.ReduceDet.ReduceDetTestop
import IrisWasm.Helpers.ReduceDet.ReduceDetRelop
import IrisWasm.Helpers.ReduceDet.ReduceDetCvtop
import IrisWasm.Helpers.ReduceDet.ReduceDetSelect
import IrisWasm.Helpers.ReduceDet.ReduceDetBlock
import IrisWasm.Helpers.ReduceDet.ReduceDetLoop
import IrisWasm.Helpers.ReduceDet.ReduceDetReturn
import IrisWasm.Helpers.ReduceDet.ReduceDetLabel
import IrisWasm.Helpers.ReduceDet.ReduceDetLocal

/-! Port of `theories/iris/helpers/iris_wasm_determ.v`: determinism of the reduction relation. -/

namespace IrisWasm

open Wasm Helpers.ReduceDetPrelude

@[rocq_alias iriswasm.reduce_det]
theorem reduce_det {ws : StoreRecord} {f : Frame} {es : List AdministrativeInstruction}
    {ws1 : StoreRecord} {f1 : Frame} {es1 : List AdministrativeInstruction} {ws2 : StoreRecord}
    {f2 : Frame} {es2 : List AdministrativeInstruction} :
    Reduce ws f es ws1 f1 es1 → Reduce ws f es ws2 f2 es2 →
    reduceDetGoal ws1 f1 es1 ws2 f2 es2 es := by
  intro h1 h2
  -- strong induction on `lengthRec es`, then induction on `h1` (as in Coq)
  suffices H : ∀ nnn (f f2 f1 : Frame) (es2 es1 es : List AdministrativeInstruction),
      Reduce ws f es ws1 f1 es1 → Reduce ws f es ws2 f2 es2 → lengthRec es < nnn →
        reduceDetGoal ws1 f1 es1 ws2 f2 es2 es from
    H _ _ _ _ _ _ _ h1 h2 (Nat.lt_succ_self _)
  clear h1 h2 f f1 f2 es es1 es2
  intro nnn
  induction nnn with
  | zero => intro _ _ _ _ _ _ _ _ hlen; exact absurd hlen (Nat.not_lt_zero _)
  | succ nnn IHnnn =>
    intro f f2 f1 es2 es1 es h1 h2 hlen
    induction h1 with
    | simple hs =>
      cases hs
      case unop => exact unop_det h2
      case binopSuccess => exact binop_det (by assumption) h2
      case binopFailure => exact binop_none_det (by assumption) h2
      case testopI32 => exact testop_i32_det h2
      case testopI64 => exact testop_i64_det h2
      case relop => exact relop_det h2
      case convertSuccess => exact cvtop_convert_det (by assumption) (by assumption) h2
      case convertFailure => exact cvtop_convert_none_det (by assumption) (by assumption) h2
      case reinterpret => exact cvtop_reinterpret_det (by assumption) h2
      case selectFalse => exact select_false_det (by assumption) h2
      case selectTrue => exact select_true_det (by assumption) h2
      case block =>
        exact block_det (by assumption) (by assumption) (by assumption) (by assumption) h2
      case loop =>
        exact loop_det (by assumption) (by assumption) (by assumption) (by assumption) h2
      case labelConst => exact .inl (label_step_goal (.inl ⟨by assumption, rfl⟩) h2)
      case labelTrap => exact .inl (label_step_goal (.inr (.inl ⟨rfl, rfl⟩)) h2)
      case br =>
        exact .inl (label_step_goal
          (.inr (.inr ⟨_, _, _, by assumption, by assumption, by assumption, rfl⟩)) h2)
      case localConst hc hl => exact .inl (local_step_goal (.inl ⟨hc, hl, rfl⟩) h2)
      case localTrap => exact .inl (local_step_goal (.inr (.inl ⟨rfl, rfl⟩)) h2)
      case return_ => exact return_det (by assumption) (by assumption) (by assumption) h2
      case trap lh hne hlf =>
        obtain ⟨bef, aft, rfl, hbef, rfl⟩ := lfilled0 hlf
        exact goal_trap (.simple (.trap _ hne hlf)) h2 (vs := bef) (rest := aft) (by simp) hbef
      all_goals only_one h2
    | invokeNative cl t1s ts vcs n k zs i hcl hcl' hves hn hk ht1 ht2 hzs hfi hfl =>
      subst hcl' hves hzs hfi ht2
      exact .inl (invoke_native_det hcl (by omega) hfl h2)
    | invokeHost cl m n hcl hcl' hves hn ht1 ht2 =>
      subst hcl' hves
      only_one h2
      obtain rfl := v_to_e_inj ‹vToEList _ = vToEList _›
      simp_all
    | setLocal =>
      only_one h2
      simp only [Prod.mk.injEq, and_true, true_and]
      exact frame_ext (by simp_all) (by simp_all)
    | growMemorySuccess | growMemoryFailure =>
      exact .inr (.inl ⟨0, by simp [firstInstr, findFirstSome, firstInstrInstr]⟩)
    | label _ _ _ _ hsub hf1 hf2 ih => exact label_det IHnnn hsub hf1 hf2 h2 hlen ih
    | «local» hsub ih => exact local_det IHnnn hsub h2 hlen ih
    | _ => only_one h2

end IrisWasm
