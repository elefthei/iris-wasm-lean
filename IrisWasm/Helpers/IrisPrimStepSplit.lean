/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Helpers.LfilledReduce
import IrisWasm.Helpers.Prelude.IrisSplitReduce

/-! Port of `theories/iris/helpers/iris_prim_step_split.v`. -/

namespace IrisWasm

open Wasm Iris.ProgramLogic

#rocq_ignore iriswasm.iris_prim_step_split.solve_prim_step_split_reduce_r
  "Ltac unused in this file and downstream; `iris_split_reduce.v` uses its own copy"

open LfilledReduce

/-- Inversion of a reduction of a single `local` frame (not in Coq). -/
private theorem local_inv {s : StoreRecord} {f0 : Frame} {s' : StoreRecord} {f0' : Frame} {n : Nat}
    {f : Frame} {LI R : List AdministrativeInstruction} :
    Reduce s f0 [.local n f LI] s' f0' R →
    (∃ f' LI', Reduce s f LI s' f' LI' ∧ R = [.local n f' LI'] ∧ f0' = f0) ∨
      constList LI = true ∨ LI = [.trap] ∨
      ∃ j lh vs, constList vs = true ∧ lfilled j lh (vs ++ [.basic .return_]) LI = true := by
  intro h
  generalize hE : [AdministrativeInstruction.local n f LI] = E at h
  induction h with
  | simple hs =>
    cases hs <;> first
      | simp at hE; done
      | (have := congrArg List.getLast? hE; simp at this; done)
      | skip
    case trap hf =>
      obtain ⟨_, _, _, _, h⟩ := lfilled_zero_inv hf
      subst hE; have := congrArg (AdministrativeInstruction.trap ∈ ·) h; simp at this
    all_goals
      simp only [List.cons.injEq, AdministrativeInstruction.local.injEq, and_true] at hE
      obtain ⟨rfl, rfl, rfl⟩ := hE
    · exact .inr (.inl ‹_›)
    · exact .inr (.inr (.inl rfl))
    · exact .inr (.inr (.inr ⟨_, _, _, ‹_›, ‹_›⟩))
  | label es0 es0' k lh hr hf hf' ih =>
    subst hE
    rw [lfilled_Ind_Equivalent] at hf hf'
    rcases singleton_split hf rfl (fun h => empty_no_reduce (h ▸ hr)) with
      ⟨rfl, rfl, rfl⟩ | ⟨_, _, _, _, _, -, -, he, -⟩
    · obtain ⟨_, _, he, -, rfl⟩ := ind0 hf'
      cases he
      simpa using ih rfl
    · cases he
  | «local» hr =>
    simp only [List.cons.injEq, AdministrativeInstruction.local.injEq, and_true] at hE
    obtain ⟨rfl, rfl, rfl⟩ := hE
    exact .inl ⟨_, _, hr, rfl, rfl⟩
  | block | loop | invokeNative | invokeHost => have := congrArg List.getLast? hE; simp at this
  | _ => simp at hE

@[rocq_alias iriswasm.lfilled_prim_step_split_reduce_r]
theorem lfilled_prim_step_split_reduce_r (i : Nat) (lh : Lholed) (es1 es2 : Expr) (σ : State)
    (LI e2 : Expr) (σ2 : State) (obs2 : List Observation) (efs2 : List Expr) :
    lfilled i lh (es1 ++ es2) LI = true → PrimStep.Reducible (es1, σ) →
    primStep (LI, σ) obs2 (e2, σ2, efs2) →
    (∃ e', primStep (es1, σ) obs2 (e', σ2, efs2) ∧ lfilled i lh (e' ++ es2) e2 = true) ∨
      ((∃ lh, lfilled 0 lh [.trap] es1 = true) ∧ σ = σ2) := by
  obtain ⟨s, locs, inst⟩ := σ
  obtain ⟨s2, locs2, inst2⟩ := σ2
  rintro hf ⟨_, _, ⟨_, _, _⟩, _, hred, -, -⟩ ⟨hLI, rfl, rfl⟩
  rw [lfilled_Ind_Equivalent] at hf
  rcases lfilled_reduce_app hred i lh LI e2 hf hLI with ⟨e', h1, h2⟩ | ⟨lh0, h0, hsf⟩
  · exact .inl ⟨e', ⟨h1, rfl, rfl⟩, (lfilled_Ind_Equivalent _ _ _ _).2 h2⟩
  · simp only [Prod.mk.injEq, Frame.mk.injEq] at hsf
    obtain ⟨rfl, rfl, rfl⟩ := hsf
    exact .inr ⟨⟨lh0, h0⟩, rfl⟩

@[rocq_alias iriswasm.local_frame_lfilled_prim_step_split_reduce_r]
theorem local_frame_lfilled_prim_step_split_reduce_r (es1 es2 : Expr) (s : StoreRecord)
    (v : List Value) (i : Instance) (n : Nat) (v' : List Value) (i' : Instance) (e2 : Expr)
    (s2 : StoreRecord) (v2 : List Value) (i2 : Instance) (efs2 : List Expr)
    (obs2 : List Observation) (j : Nat) (lh : Lholed) (LI : Expr) :
    lfilled j lh (es1 ++ es2) LI = true → PrimStep.Reducible (es1, (s, v, i)) →
    primStep ([.local n ⟨v, i⟩ LI], (s, v', i')) obs2 (e2, (s2, v2, i2), efs2) →
    (∃ e' v'' i'' LI', primStep (es1, (s, v, i)) obs2 (e', (s2, v'', i''), efs2) ∧ v' = v2 ∧
        i' = i2 ∧ e2 = [.local n ⟨v'', i''⟩ LI'] ∧ lfilled j lh (e' ++ es2) LI' = true) ∨
      ∃ lh0, lfilled 0 lh0 [.trap] es1 = true ∧ (s, v', i') = (s2, v2, i2) := by
  rintro hf ⟨_, e1, ⟨s1, v1, i1⟩, _, hred, -, -⟩ ⟨hLI, rfl, rfl⟩
  rw [lfilled_Ind_Equivalent] at hf
  have hred2 : Reduce s ⟨v, i⟩ (es1 ++ es2) s1 ⟨v1, i1⟩ (e1 ++ es2) :=
    .label es1 _ 0 (.base [] es2) hred (by simp [lfilled, lfill, constList])
      (by simp [lfilled, lfill, constList])
  have hf' := (lfilled_Ind_Equivalent _ _ _ _).2 hf
  rcases local_inv hLI with ⟨⟨v'', i''⟩, LI', hLI', rfl, hfr⟩ | hc | rfl | ⟨k, lhr, vs, hvs, hret⟩
  · simp only [Frame.mk.injEq] at hfr
    obtain ⟨rfl, rfl⟩ := hfr
    rcases lfilled_reduce_app hred j lh LI LI' hf hLI' with ⟨e', h1, h2⟩ | ⟨lh0, h0, hsf⟩
    · exact .inl ⟨e', v'', i'', LI', ⟨h1, rfl, rfl⟩, rfl, rfl, rfl,
        (lfilled_Ind_Equivalent _ _ _ _).2 h2⟩
    · simp only [Prod.mk.injEq] at hsf
      obtain ⟨rfl, -⟩ := hsf
      exact .inr ⟨lh0, h0, rfl⟩
  · exact (values_no_reduce hred2 (lfilled_const _ _ _ _ hf' hc).2).elim
  · have hne : es1 ++ es2 ≠ [] := fun h => by
      obtain ⟨rfl, -⟩ := List.append_eq_nil_iff.1 h; exact empty_no_reduce hred
    obtain ⟨-, -, h⟩ := filled_singleton _ _ _ _ hf' (by simp) hne
    rcases List.append_eq_singleton_iff.1 h with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact (empty_no_reduce hred).elim
    · exact (test_no_reduce_trap hred).elim
  · exact (lfilled_return_and_reduce hred2 hvs hret hf').elim

@[rocq_alias iriswasm.local_frame_prim_step_split_reduce_r]
theorem local_frame_prim_step_split_reduce_r (es1 es2 : Expr) (s : StoreRecord) (v : List Value)
    (i : Instance) (n : Nat) (v' : List Value) (i' : Instance) (e2 : Expr) (s2 : StoreRecord)
    (v2 : List Value) (i2 : Instance) (efs2 : List Expr) (obs2 : List Observation) :
    PrimStep.Reducible (es1, (s, v, i)) →
    primStep ([.local n ⟨v, i⟩ (es1 ++ es2)], (s, v', i')) obs2 (e2, (s2, v2, i2), efs2) →
    (∃ e' v'' i'', primStep (es1, (s, v, i)) obs2 (e', (s2, v'', i''), efs2) ∧ v' = v2 ∧
        i' = i2 ∧ e2 = [.local n ⟨v'', i''⟩ (e' ++ es2)]) ∨
      (∃ lh0, lfilled 0 lh0 [.trap] es1 = true ∧ (s, v', i') = (s2, v2, i2)) := by
  intro hred hstep
  rcases local_frame_lfilled_prim_step_split_reduce_r es1 es2 s v i n v' i' e2 s2 v2 i2 efs2 obs2
      0 (.base [] []) (es1 ++ es2) (by simp [lfilled, lfill, constList]) hred hstep with
    ⟨e', v'', i'', LI', h1, rfl, rfl, rfl, h2⟩ | h
  · obtain ⟨-, rfl⟩ := lfilled_zero_base_inv h2
    exact .inl ⟨e', v'', i'', h1, rfl, rfl, by simp⟩
  · exact .inr h

end IrisWasm
