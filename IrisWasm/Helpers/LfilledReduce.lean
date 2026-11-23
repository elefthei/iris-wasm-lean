/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Helpers.IrisReductionCore
import IrisWasm.Helpers.Prelude.IrisReduceProperties
import IrisWasm.Language.Iris.Iris

/-! Port of `theories/iris/helpers/lfilled_reduce.v`.

The Coq proof is a case analysis on the reduction of `LI` (with the Ltacs `filled0/1/2`). Here the
depth-0 case is a direct application of `reduction_core`; the depth-`i+1` case uses
`reduction_core` on the enclosing `label` and an inversion lemma for reductions of a single
`label`. The auxiliary lemmas (namespace `IrisWasm.LfilledReduce`) are not in Coq. -/

namespace IrisWasm

open Wasm Iris.ProgramLogic

#rocq_ignore iriswasm.filled0 "Ltac used only inside lfilled_reduce's Coq proof"
#rocq_ignore iriswasm.filled1 "Ltac used only inside lfilled_reduce's Coq proof"
#rocq_ignore iriswasm.filled2 "Ltac used only inside lfilled_reduce's Coq proof"

namespace LfilledReduce

theorem ind0 {lh : Lholed} {es LI : List AdministrativeInstruction} :
    LfilledInd 0 lh es LI →
    ∃ vs es', lh = .base vs es' ∧ constList vs = true ∧ LI = vs ++ es ++ es' := by
  intro h; cases h; exact ⟨_, _, rfl, ‹_›, rfl⟩

/-- A reduction of the singleton list `[e]` is either a reduction of `[e]` by a non-`label` rule,
or a `label` rule with the trivial context. -/
theorem singleton_split {k : Nat} {lh : Lholed} {es les : List AdministrativeInstruction}
    {e : AdministrativeInstruction} :
    LfilledInd k lh es les → les = [e] → es ≠ [] →
    (k = 0 ∧ lh = .base [] [] ∧ es = [e]) ∨
    ∃ k' n es' lh' l, k = k' + 1 ∧ lh = .rec_ [] n es' lh' [] ∧ e = .label n es' l ∧
      LfilledInd k' lh' es l := by
  intro hf hl hne
  cases hf with
  | lfilledBase vs es aft hc =>
    left
    have h := congrArg List.length hl
    simp only [List.length_append, List.length_singleton] at h
    have : es.length ≠ 0 := by simpa using hne
    obtain rfl : vs = [] := List.eq_nil_of_length_eq_zero (by omega)
    obtain rfl : aft = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp_all
  | lfilledRec k vs n es' lh' aft es l hc hl' =>
    right
    have h := congrArg List.length hl
    simp only [List.length_append, List.length_cons] at h
    obtain rfl : vs = [] := List.eq_nil_of_length_eq_zero (by omega)
    obtain rfl : aft = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp only [List.nil_append, List.append_nil, List.cons.injEq, and_true] at hl
    exact ⟨k, n, es', lh', l, rfl, rfl, hl.symm, hl'⟩

private theorem label_inv {s f s' f' n es LI R} :
    Reduce s f [.label n es LI] s' f' R →
    (∃ LI', Reduce s f LI s' f' LI' ∧ R = [.label n es LI']) ∨ constList LI = true ∨
      LI = [.trap] ∨
      ∃ j lh vs, constList vs = true ∧ lfilled j lh (vs ++ [.basic (.br j)]) LI = true := by
  intro h
  generalize hE : [AdministrativeInstruction.label n es LI] = E at h
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
      simp only [List.cons.injEq, AdministrativeInstruction.label.injEq, and_true] at hE
      obtain ⟨rfl, rfl, rfl⟩ := hE
    · exact .inr (.inl ‹_›)
    · exact .inr (.inr (.inl rfl))
    · exact .inr (.inr (.inr ⟨_, _, _, ‹_›, ‹_›⟩))
  | label es0 es0' k lh hr hf hf' ih =>
    subst hE
    rw [lfilled_Ind_Equivalent] at hf hf'
    rcases singleton_split hf rfl (fun h => empty_no_reduce (h ▸ hr)) with
      ⟨rfl, rfl, rfl⟩ | ⟨k', n', es', lh', l, rfl, rfl, he, hl⟩
    · obtain ⟨_, _, he, -, rfl⟩ := ind0 hf'
      cases he
      simpa using ih rfl
    · simp only [AdministrativeInstruction.label.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      cases hf' with
      | lfilledRec _ _ _ _ _ _ _ l' _ hl' =>
        exact .inl ⟨l', .label _ _ k' lh' hr ((lfilled_Ind_Equivalent _ _ _ _).2 hl)
          ((lfilled_Ind_Equivalent _ _ _ _).2 hl'), by simp⟩
  | block | loop | invokeNative | invokeHost => have := congrArg List.getLast? hE; simp at this
  | _ => simp at hE

private theorem singleton_core {e : AdministrativeInstruction}
    {bc0 core ac0 : List AdministrativeInstruction} :
    [e] = bc0 ++ core ++ ac0 → constList bc0 = true → isConst e = false → core ≠ [] →
    bc0 = [] ∧ core = [e] ∧ ac0 = [] := by
  intro h hc he hne
  rcases bc0 with _ | ⟨x, bc0⟩
  · have hl := congrArg List.length h
    simp only [List.length_append, List.length_singleton, List.length_nil] at hl
    have : core.length ≠ 0 := by simpa using hne
    obtain rfl : ac0 = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp_all
  · simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp_all [constList]

/-- Generalisation of `lfilled_reduce` to a context hole filled by `es ++ es2`. -/
theorem lfilled_reduce_app {s f s0 f0 s' f'} {es es2 es0 : List AdministrativeInstruction}
    (Hes : Reduce s f es s0 f0 es0) :
    ∀ (i : Nat) (lh : Lholed) (LI LI' : List AdministrativeInstruction),
    LfilledInd i lh (es ++ es2) LI → Reduce s f LI s' f' LI' →
    (∃ es', Reduce s f es s' f' es' ∧ LfilledInd i lh (es' ++ es2) LI') ∨
      (∃ lh0, lfilled 0 lh0 [.trap] es = true ∧ (s, f) = (s', f'))
  | 0, lh, LI, LI', hf, hLI => by
    obtain ⟨bef, aft, rfl, hc, rfl⟩ := ind0 hf
    rcases reduction_core (bef0 := bef) (aft0 := es2 ++ aft) (bef1 := []) (aft1 := [])
        Hes hLI hc rfl (by simp) with
      ⟨core, bc0, ac0, bc1, ac1, core', hbc0, -, rfl, -, hb, ha, hcore, rfl⟩ | ⟨lh0, -, h0, -, hsf⟩
    · left
      refine ⟨bc0 ++ core' ++ ac0, .label core core' 0 (.base bc0 ac0) hcore ?_ ?_, ?_⟩
      · rw [lfilled_Ind_Equivalent]; simpa using LfilledInd.lfilledBase bc0 core ac0 hbc0
      · rw [lfilled_Ind_Equivalent]; simpa using LfilledInd.lfilledBase bc0 core' ac0 hbc0
      · simp only [List.nil_append] at hb
        simp only [List.append_nil] at ha
        subst hb ha
        simpa using LfilledInd.lfilledBase bef (bc0 ++ core' ++ ac0 ++ es2) aft hc
    · exact .inr ⟨lh0, h0, hsf⟩
  | i + 1, lh, LI, LI', hf, hLI => by
    cases hf with
    | lfilledRec _ vs n es' lh' aft _ l hvs hl =>
    have hne : es ++ es2 ≠ [] := fun h => by
      obtain ⟨rfl, -⟩ := List.append_eq_nil_iff.1 h; exact empty_no_reduce Hes
    have Hes2 : Reduce s f (es ++ es2) s0 f0 (es0 ++ es2) :=
      .label es es0 0 (.base [] es2) Hes (by simp [lfilled, lfill, constList])
        (by simp [lfilled, lfill, constList])
    obtain ⟨l0, hl0⟩ := lfilled_swap (es0 ++ es2) ((lfilled_Ind_Equivalent _ _ _ _).2 hl)
    have Hred0 : Reduce s f [.label n es' l] s0 f0 [.label n es' l0] :=
      .label _ _ (i + 1) (.rec_ [] n es' lh' []) Hes2
        ((lfilled_Ind_Equivalent _ _ _ _).2 (by
          simpa using LfilledInd.lfilledRec i [] n es' lh' [] _ _ rfl hl))
        ((lfilled_Ind_Equivalent _ _ _ _).2 (by
          simpa using LfilledInd.lfilledRec i [] n es' lh' [] _ _ rfl
            ((lfilled_Ind_Equivalent _ _ _ _).1 hl0)))
    rcases reduction_core (bef0 := vs) (aft0 := aft) (bef1 := []) (aft1 := [])
        Hred0 hLI hvs rfl (by simp) with
      ⟨core, bc0, ac0, bc1, ac1, core', hbc0, -, he, -, hb, ha, hcore, rfl⟩ | ⟨lh0, -, h0, -, -⟩
    · obtain ⟨rfl, rfl, rfl⟩ := singleton_core he hbc0 rfl (fun h => empty_no_reduce (h ▸ hcore))
      simp only [List.append_nil, List.nil_append] at hb ha
      subst hb ha
      rcases label_inv hcore with ⟨l', hl', rfl⟩ | hc | rfl | ⟨j, lhb, vsb, hvsb, hbr⟩
      · rcases lfilled_reduce_app Hes i lh' l l' hl hl' with ⟨es'', h1, h2⟩ | h
        · exact .inl ⟨es'', h1, by simpa using LfilledInd.lfilledRec i vs n es' lh' aft _ _ hvs h2⟩
        · exact .inr h
      · have := (lfilled_const _ _ _ _ ((lfilled_Ind_Equivalent _ _ _ _).2 hl) hc).2
        exact (values_no_reduce Hes2 this).elim
      · obtain ⟨-, -, h⟩ := filled_singleton _ _ _ _ ((lfilled_Ind_Equivalent _ _ _ _).2 hl)
          (by simp) hne
        rcases List.append_eq_singleton_iff.1 h with ⟨rfl, -⟩ | ⟨rfl, -⟩
        · exact (empty_no_reduce Hes).elim
        · exact (test_no_reduce_trap Hes).elim
      · exact (lfilled_br_and_reduce Hes2 hvsb (Nat.le_refl j) hbr
          ((lfilled_Ind_Equivalent _ _ _ _).2 hl)).elim
    · obtain ⟨_, _, _, _, h⟩ := lfilled_zero_inv h0
      have := congrArg (AdministrativeInstruction.trap ∈ ·) h; simp at this

end LfilledReduce

open LfilledReduce in
/-- Enclosing `es` in an `lh` context cannot generate new reduction paths. -/
@[rocq_alias iriswasm.lfilled_reduce]
theorem lfilled_reduce (i : Nat) (lh : Lholed) (es LI : Expr) (σ : State) (LI' : Expr)
    (σ' : State) (obs : List Observation) (efs : List Expr) :
    lfilled i lh es LI = true → PrimStep.Reducible (es, σ) →
    primStep (LI, σ) obs (LI', σ', efs) →
    (∃ es', primStep (es, σ) obs (es', σ', efs) ∧ lfilled i lh es' LI' = true) ∨
      (∃ lh0, lfilled 0 lh0 [.trap] es = true ∧ σ = σ') := by
  obtain ⟨s, locs, inst⟩ := σ
  obtain ⟨s', locs', inst'⟩ := σ'
  rintro hf ⟨_, _, ⟨_, _, _⟩, _, hred, -, -⟩ ⟨hLI, rfl, rfl⟩
  rw [lfilled_Ind_Equivalent] at hf
  rcases lfilled_reduce_app (es2 := []) hred i lh LI LI' (by simpa using hf) hLI with
    ⟨es', h1, h2⟩ | ⟨lh0, h0, hsf⟩
  · exact .inl ⟨es', ⟨h1, rfl, rfl⟩, (lfilled_Ind_Equivalent _ _ _ _).2 (by simpa using h2)⟩
  · simp only [Prod.mk.injEq, Frame.mk.injEq] at hsf
    obtain ⟨rfl, rfl, rfl⟩ := hsf
    exact .inr ⟨lh0, h0, rfl⟩

end IrisWasm
