/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Helpers.Prelude.IrisReduceProperties

/-! Port of `theories/iris/helpers/prelude/iris_split_reduce.v`. -/

namespace IrisWasm

open Wasm Iris.ProgramLogic

section helpers
open AdministrativeInstruction (basic trap)

private theorem lfilled0_iff {lh : Lholed} {es LI : List AdministrativeInstruction} :
    lfilled 0 lh es LI = true ↔
      ∃ p q, lh = .base p q ∧ constList p = true ∧ LI = p ++ es ++ q := by
  rw [lfilled_Ind_Equivalent]
  constructor
  · intro h
    cases h with
    | lfilledBase vs es es' hc => exact ⟨vs, es', rfl, hc, rfl⟩
  · rintro ⟨p, q, rfl, hc, rfl⟩
    exact .lfilledBase p es q hc

private theorem constList_append {a b : List AdministrativeInstruction} :
    constList (a ++ b) = (constList a && constList b) := by
  simp [constList]

private theorem const_not_mem_trap {l : List AdministrativeInstruction}
    (h : constList l = true) : trap ∉ l := fun hm => by
  simp only [constList, List.all_eq_true] at h
  simpa [isConst] using h _ hm

private theorem first_nonconst_unique {p q r t : List AdministrativeInstruction}
    {x y : AdministrativeInstruction} (h : p ++ x :: q = r ++ y :: t) (hp : constList p = true)
    (hr : constList r = true) (hx : isConst x = false) (hy : isConst y = false) :
    p = r ∧ x = y ∧ q = t := by
  induction p generalizing r with
  | nil =>
    cases r with
    | nil => simpa using h
    | cons a r =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, -⟩ := h
      simp [constList, hx] at hr
  | cons a p ih =>
    cases r with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, -⟩ := h
      simp [constList, hy] at hp
    | cons b r =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      simp only [constList, List.all_cons, Bool.and_eq_true] at hp hr
      obtain ⟨rfl, rfl, rfl⟩ := ih h hp.2 hr.2
      exact ⟨rfl, rfl, rfl⟩

private theorem exists_first_nonconst {l : List AdministrativeInstruction}
    (h : constList l = false) :
    ∃ p x q, l = p ++ x :: q ∧ constList p = true ∧ isConst x = false := by
  induction l with
  | nil => simp [constList] at h
  | cons a l ih =>
    cases ha : isConst a
    · exact ⟨[], a, l, rfl, rfl, ha⟩
    · simp only [constList, List.all_cons, ha, Bool.true_and] at h
      obtain ⟨p, x, q, rfl, hp, hx⟩ := ih h
      exact ⟨a :: p, x, q, rfl, by simpa [constList, ha] using hp, hx⟩

private theorem reduce_not_const {s f les s' f' les'} (h : Reduce s f les s' f' les') :
    constList les = false := by
  induction h with
  | @simple e e' s f hs =>
    cases hs with
    | trap lh _ hl =>
      obtain ⟨p, q, -, -, rfl⟩ := lfilled0_iff.1 hl
      simp [constList, isConst]
    | _ => simp_all [constList, isConst]
  | @label s f es les s' f' es' les' k lh hr hl hl' ih =>
    rw [lfilled_Ind_Equivalent] at hl
    cases hl with
    | lfilledBase vs _ es'' _ => simp [constList_append, ih]
    | lfilledRec => simp [constList, isConst]
  | _ => simp_all [constList, isConst, vToEList]

private theorem reduce_trap_filled {s f les s' f' les'} (h : Reduce s f les s' f' les') :
    ∀ p q, les = p ++ trap :: q → constList p = true →
    (∃ lh, lfilled 0 lh [trap] les' = true) ∧ s' = s ∧ f' = f := by
  induction h with
  | @simple e e' s f hs =>
    intro p q heq hp
    cases hs with
    | trap lh _ _ =>
      exact ⟨⟨.base [] [], lfilled0_iff.2 ⟨[], [], rfl, rfl, rfl⟩⟩, rfl, rfl⟩
    | _ =>
      have hm : trap ∈ p ++ trap :: q := by simp
      rw [← heq] at hm
      simp at hm
      all_goals first
        | (refine absurd hm (const_not_mem_trap ?_); assumption)
        | (subst hm; simp_all [isConst])
  | @label s f es les s' f' es' les' k lh hr hl hl' ih =>
    intro p q heq hp
    cases k with
    | zero =>
      obtain ⟨bef, aft, rfl, hbef, rfl⟩ := lfilled0_iff.1 hl
      obtain ⟨bef2, aft2, he, -, rfl⟩ := lfilled0_iff.1 hl'
      cases he
      obtain ⟨p2, x, q2, rfl, hp2, hx⟩ := exists_first_nonconst (reduce_not_const hr)
      have h' : (bef ++ p2) ++ x :: (q2 ++ aft) = p ++ trap :: q := by rw [← heq]; simp
      obtain ⟨-, rfl, -⟩ :=
        first_nonconst_unique h' (by simp [constList_append, hbef, hp2]) hp hx rfl
      obtain ⟨⟨lh0, hlh0⟩, rfl, rfl⟩ := ih p2 q2 rfl hp2
      obtain ⟨p', q', -, hp', rfl⟩ := lfilled0_iff.1 hlh0
      exact ⟨⟨.base (bef ++ p') (q' ++ aft),
        lfilled0_iff.2 ⟨_, _, rfl, by simp [constList_append, hbef, hp'], by simp⟩⟩, rfl, rfl⟩
    | succ k =>
      rw [lfilled_Ind_Equivalent] at hl
      cases hl with
      | lfilledRec _ vs n es0 lh' es'' _ LI hvs _ =>
        have h' : vs ++ AdministrativeInstruction.label n es0 LI :: es'' = p ++ trap :: q := by
          rw [← heq]; simp
        obtain ⟨-, h, -⟩ := first_nonconst_unique h' hvs hp rfl rfl
        cases h
  | _ =>
    intro p q heq hp
    have hm : trap ∈ p ++ trap :: q := by simp
    rw [← heq] at hm
    simp at hm
    all_goals first
      | exact (const_not_mem_trap (by assumption) hm).elim
      | (subst_vars; simp [vToEList] at hm)


/-- An exact redex cannot lose its first operand and still reduce. -/
private theorem reduce_ves_direct {s f es s0 f0 es0} (hes : Reduce s f es s0 f0 es0) {v : Value}
    {l : List AdministrativeInstruction} (hl : l ≠ []) (heq : l = basic (.const v) :: es)
    (hvs : constList l.dropLast = true) (he : isConst (l.getLast hl) = false)
    (hn : l.dropLast.length ≤ redexArity s f (l.getLast hl)) : False := by
  have heq' := (List.dropLast_concat_getLast hl).trans heq
  generalize l.dropLast = vs at heq' hvs hn
  generalize l.getLast hl = e at heq' he hn
  cases vs with
  | nil =>
    simp only [List.nil_append, List.cons.injEq] at heq'
    obtain ⟨rfl, rfl⟩ := heq'
    exact reduce_not_nil hes rfl
  | cons a vs =>
    simp only [List.cons_append, List.cons.injEq] at heq'
    obtain ⟨rfl, rfl⟩ := heq'
    simp only [constList, List.all_cons, Bool.and_eq_true] at hvs
    have := redexArity_le hes hvs.2 he
    simp only [List.length_cons] at hn
    omega

/-- Core of `prim_step_split_reduce_r`, on `Reduce`. -/
private theorem reduce_split_r {s f les s' f' les'} (h : Reduce s f les s' f' les') :
    ∀ es1 es2, Reduce s f les s' f' les' → les = es1 ++ es2 → constList es1 = false →
    (∃ es'', les' = es'' ++ es2 ∧ Reduce s f es1 s' f' es'') ∨
    (∃ n m, m ≤ (es1 ++ es2).length ∧
      lfilled 0 (.base (es1.take n) ((es1 ++ es2).drop m)) [trap] les' = true ∧
      (∃ lh, lfilled 0 lh [trap] es1 = true) ∧ s' = s ∧ f' = f) := by
  have split_ne {es1 es2 l : List AdministrativeInstruction} (heq : l = es1 ++ es2)
      (h2 : es2 ≠ []) (hc : constList l.dropLast = true) : constList es1 = true := by
    subst heq
    rw [List.dropLast_append_of_ne_nil h2, constList_append, Bool.and_eq_true] at hc
    exact hc.1
  induction h with
  | @simple e e' s f hs =>
    intro es1 es2 h' heq hc
    by_cases h2 : es2 = []
    · subst h2; exact .inl ⟨_, (List.append_nil _).symm, by simpa [heq] using h'⟩
    cases hs with
    | trap lh _ hl =>
      obtain ⟨p, q, -, hp, rfl⟩ := lfilled0_iff.1 hl
      have hsplit : es1 ++ es2 = p ++ trap :: q := by rw [← heq]; simp
      rcases List.append_eq_append_iff.1 hsplit with ⟨a', rfl, -⟩ | ⟨c', rfl, hc'⟩
      · simp [constList_append, hc] at hp
      cases c' with
      | nil => simp [hp] at hc
      | cons x c =>
        simp only [List.cons_append, List.cons.injEq] at hc'
        obtain ⟨rfl, -⟩ := hc'
        refine .inr ⟨0, (p ++ trap :: c ++ es2).length, Nat.le_refl _, ?_, ⟨.base p c, ?_⟩,
          rfl, rfl⟩
        · exact lfilled0_iff.2 ⟨[], [], by simp, rfl, rfl⟩
        · exact lfilled0_iff.2 ⟨p, c, rfl, hp, by simp⟩
    | _ =>
      exfalso
      have := split_ne heq h2 (by clear heq h' hc; simp_all [constList, isConst])
      simp_all
  | @label s f es les s' f' es' les' k lh hr hl hl' ih =>
    intro es1 es2 h' heq hc
    by_cases h2 : es2 = []
    · subst h2; exact .inl ⟨_, (List.append_nil _).symm, by simpa [heq] using h'⟩
    cases k with
    | zero =>
      obtain ⟨bef, aft, rfl, hbef, rfl⟩ := lfilled0_iff.1 hl
      obtain ⟨bef2, aft2, he, -, rfl⟩ := lfilled0_iff.1 hl'
      cases he
      have hsplit : es1 ++ es2 = bef ++ (es ++ aft) := by rw [← heq]; simp
      rcases List.append_eq_append_iff.1 hsplit with ⟨a', rfl, -⟩ | ⟨x, rfl, hx⟩
      · simp [constList_append, hc] at hbef
      have hcx : constList x = false := by simpa [constList_append, hbef] using hc
      rcases List.append_eq_append_iff.1 hx.symm with ⟨a', rfl, rfl⟩ | ⟨c', rfl, rfl⟩
      · rcases ih x a' hr rfl hcx with ⟨es'', rfl, hr'⟩ | ⟨n, m, hm, hfill, ⟨lh0, hlh0⟩, rfl, rfl⟩
        · refine .inl ⟨bef ++ es'', by simp, ?_⟩
          exact .label x es'' 0 (.base bef []) hr' (lfilled0_iff.2 ⟨_, _, rfl, hbef, by simp⟩)
            (lfilled0_iff.2 ⟨_, _, rfl, hbef, by simp⟩)
        · obtain ⟨p, q, hpq, hp, rfl⟩ := lfilled0_iff.1 hfill
          cases hpq
          obtain ⟨p0, q0, -, hp0, rfl⟩ := lfilled0_iff.1 hlh0
          simp at hm
          refine .inr ⟨bef.length + n, bef.length + m, by simp; omega, ?_,
            ⟨.base (bef ++ p0) q0, lfilled0_iff.2 ⟨_, _, rfl, by simp [constList_append, *],
              by simp⟩⟩, rfl, rfl⟩
          have hm' : m ≤ (p0 ++ [trap] ++ q0 ++ a').length := by simp; omega
          have e1 : List.take (bef.length + n) (bef ++ (p0 ++ [trap] ++ q0)) =
              bef ++ List.take n (p0 ++ [trap] ++ q0) := List.take_length_add_append ..
          have e2 : List.drop (bef.length + m) (bef ++ (p0 ++ [trap] ++ q0) ++ (a' ++ aft)) =
              List.drop m (p0 ++ [trap] ++ q0 ++ a') ++ aft := by
            rw [List.append_assoc, List.drop_length_add_append,
              show p0 ++ [trap] ++ q0 ++ (a' ++ aft) = (p0 ++ [trap] ++ q0 ++ a') ++ aft by simp,
              List.drop_append_of_le_length hm']
          refine lfilled0_iff.2 ⟨_, _, rfl, ?_, ?_⟩
          · rw [e1, constList_append, hbef, hp]
          · rw [e1, e2]; simp
      · refine .inl ⟨bef ++ es' ++ c', by simp, ?_⟩
        exact .label es es' 0 (.base bef c') hr (lfilled0_iff.2 ⟨_, _, rfl, hbef, by simp⟩)
          (lfilled0_iff.2 ⟨_, _, rfl, hbef, by simp⟩)
    | succ k =>
      rw [lfilled_Ind_Equivalent] at hl hl'
      cases hl with
      | lfilledRec _ vs n es0 lh' es'' _ LI hvs hLI =>
        cases hl' with
        | lfilledRec _ _ _ _ _ _ _ LI' _ hLI' =>
          have hsplit : es1 ++ es2 = vs ++ (AdministrativeInstruction.label n es0 LI :: es'') := by
            rw [← heq]; simp
          rcases List.append_eq_append_iff.1 hsplit with ⟨a', rfl, -⟩ | ⟨c', rfl, hc'⟩
          · simp [constList_append, hc] at hvs
          cases c' with
          | nil => simp [hvs] at hc
          | cons x c =>
            simp only [List.cons_append, List.cons.injEq] at hc'
            obtain ⟨rfl, rfl⟩ := hc'
            refine .inl ⟨vs ++ [.label n es0 LI'] ++ c, by simp, ?_⟩
            refine .label es es' (k + 1) (.rec_ vs n es0 lh' c) hr ?_ ?_
            · rw [lfilled_Ind_Equivalent]
              simpa using LfilledInd.lfilledRec k vs n es0 lh' c es LI hvs hLI
            · rw [lfilled_Ind_Equivalent]
              simpa using LfilledInd.lfilledRec k vs n es0 lh' c es' LI' hvs hLI'
  | _ =>
    intro es1 es2 h' heq hc
    by_cases h2 : es2 = []
    · subst h2; exact .inl ⟨_, (List.append_nil _).symm, by simpa [heq] using h'⟩
    exfalso
    have := split_ne heq h2
      (by clear heq h' hc; subst_vars; simp_all [constList, isConst, vToEList])
    simp_all


/-- Core of `reduce_ves`, on `Reduce`. -/
private theorem reduce_ves_core {s f les s' f' les'} (h : Reduce s f les s' f' les') :
    ∀ v es, les = basic (.const v) :: es → (∃ s0 f0 es0, Reduce s f es s0 f0 es0) →
    (les' = basic (.const v) :: les'.drop 1 ∧ Reduce s f es s' f' (les'.drop 1)) ∨
    ((∃ lh, lfilled 0 lh [trap] les' = true) ∧ (∃ lh', lfilled 0 lh' [trap] es = true) ∧
      s' = s ∧ f' = f) := by
  induction h with
  | @simple e e' s f hs =>
    intro v es heq ⟨s0, f0, es0, hes⟩
    cases hs with
    | trap lh _ hl =>
      obtain ⟨p, q, -, hp, rfl⟩ := lfilled0_iff.1 hl
      cases p with
      | nil => simp at heq
      | cons a p =>
        simp only [List.cons_append, List.cons.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        simp only [constList, List.all_cons, Bool.and_eq_true] at hp
        exact .inr ⟨⟨.base [] [], lfilled0_iff.2 ⟨[], [], rfl, rfl, rfl⟩⟩,
          ⟨.base p q, lfilled0_iff.2 ⟨p, q, rfl, hp.2, rfl⟩⟩, rfl, rfl⟩
    | _ =>
      exfalso
      exact reduce_ves_direct hes (by simp) heq (by clear heq; simp_all [constList, isConst])
        (by simp [isConst]) (by clear heq; simp_all [redexArity])
  | @label s f ces les s' f' ces' les' k lh hr hl hl' ih =>
    intro v es heq ⟨s0, f0, es0, hes⟩
    cases k with
    | zero =>
      obtain ⟨bef, aft, rfl, hbef, rfl⟩ := lfilled0_iff.1 hl
      obtain ⟨bef2, aft2, he, -, rfl⟩ := lfilled0_iff.1 hl'
      cases he
      cases bef with
      | cons b bef =>
        simp only [List.cons_append, List.cons.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        simp only [constList, List.all_cons, Bool.and_eq_true] at hbef
        refine .inl ⟨by simp, ?_⟩
        simp only [List.cons_append, List.drop_succ_cons, List.drop_zero]
        exact .label ces ces' 0 (.base bef aft) hr (lfilled0_iff.2 ⟨_, _, rfl, hbef.2, rfl⟩)
          (lfilled0_iff.2 ⟨_, _, rfl, hbef.2, rfl⟩)
      | nil =>
        simp only [List.nil_append] at heq
        cases ces with
        | nil => exact absurd rfl (reduce_not_nil hr)
        | cons c ces0 =>
          simp only [List.cons_append, List.cons.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          cases hc0 : constList ces0
          · rcases reduce_split_r hes ces0 aft hes rfl hc0 with
              ⟨es'', -, hr0⟩ | ⟨-, -, -, -, ⟨lh0, hlh0⟩, -⟩
            · rcases ih v ces0 rfl ⟨_, _, _, hr0⟩ with
                ⟨hc', hr1⟩ | ⟨⟨lh1, h1⟩, ⟨lh0, hlh0⟩, rfl, rfl⟩
              · refine .inl ⟨?_, ?_⟩
                · rw [hc']; simp
                · rw [hc']
                  simp only [List.nil_append, List.cons_append, List.drop_succ_cons, List.drop_zero]
                  exact .label ces0 (ces'.drop 1) 0 (.base [] aft) hr1
                    (lfilled0_iff.2 ⟨_, _, rfl, rfl, by simp⟩)
                    (lfilled0_iff.2 ⟨_, _, rfl, rfl, by simp⟩)
              · obtain ⟨p1, q1, -, hp1, rfl⟩ := lfilled0_iff.1 h1
                obtain ⟨p0, q0, -, hp0, rfl⟩ := lfilled0_iff.1 hlh0
                exact .inr ⟨⟨.base p1 (q1 ++ aft), lfilled0_iff.2 ⟨_, _, rfl, hp1, by simp⟩⟩,
                  ⟨.base p0 (q0 ++ aft), lfilled0_iff.2 ⟨_, _, rfl, hp0, by simp⟩⟩, rfl, rfl⟩
            · obtain ⟨p0, q0, -, hp0, rfl⟩ := lfilled0_iff.1 hlh0
              obtain ⟨⟨lh1, h1⟩, rfl, rfl⟩ :=
                reduce_trap_filled hr (basic (.const v) :: p0) q0 (by simp)
                  (by simpa [constList, isConst] using hp0)
              obtain ⟨p1, q1, -, hp1, rfl⟩ := lfilled0_iff.1 h1
              exact .inr ⟨⟨.base p1 (q1 ++ aft), lfilled0_iff.2 ⟨_, _, rfl, hp1, by simp⟩⟩,
                ⟨.base p0 (q0 ++ aft), lfilled0_iff.2 ⟨_, _, rfl, hp0, by simp⟩⟩, rfl, rfl⟩
          · exact absurd (reduce_not_const hr) (by simp [constList, isConst] at hc0 ⊢; exact hc0)
    | succ k =>
      rw [lfilled_Ind_Equivalent] at hl hl'
      cases hl with
      | lfilledRec _ vs n es0 lh' es'' _ LI hvs hLI =>
        cases hl' with
        | lfilledRec _ _ _ _ _ _ _ LI' _ hLI' =>
          cases vs with
          | nil => simp at heq
          | cons a vs =>
            simp only [List.cons_append, List.cons.injEq] at heq
            obtain ⟨rfl, rfl⟩ := heq
            simp only [constList, List.all_cons, Bool.and_eq_true] at hvs
            refine .inl ⟨by simp, ?_⟩
            simp only [List.cons_append, List.drop_succ_cons, List.drop_zero]
            refine .label ces ces' (k + 1) (.rec_ vs n es0 lh' es'') hr ?_ ?_
            · rw [lfilled_Ind_Equivalent]
              simpa using LfilledInd.lfilledRec k vs n es0 lh' es'' ces LI hvs.2 hLI
            · rw [lfilled_Ind_Equivalent]
              simpa using LfilledInd.lfilledRec k vs n es0 lh' es'' ces' LI' hvs.2 hLI'
  | _ =>
    intro v es heq ⟨s0, f0, es0, hes⟩
    exfalso
    exact reduce_ves_direct hes (by simp) heq
      (by clear heq; subst_vars; simp_all [constList, isConst, vToEList])
      (by simp [isConst]) (by clear heq; subst_vars; simp_all [redexArity, clType, vToEList])

end helpers

#rocq_ignore iriswasm.iris_split_reduce.solve_prim_step_split_reduce_r
  "Ltac used only inside the proof of prim_step_split_reduce_r, whose Lean proof is restructured"

@[rocq_alias iriswasm.prim_step_split_reduce_r]
theorem prim_step_split_reduce_r (es1 es2 es' : List AdministrativeInstruction) (σ σ' : State)
    (obs : List Observation) (efs : List Expr) :
    toVal es1 = none →
    primStep (es1 ++ es2, σ) obs (es', σ', efs) →
    (∃ es'', es' = es'' ++ es2 ∧ primStep (es1, σ) obs (es'', σ', efs)) ∨
    (∃ n m lh, lfilled 0 (.base (es1.take n) ((es1 ++ es2).drop m)) [.trap] es' = true ∧
      lfilled 0 lh [.trap] es1 = true ∧ σ' = σ) := by
  intro hv hstep
  obtain ⟨s, l, i⟩ := σ
  obtain ⟨s', l', i'⟩ := σ'
  obtain ⟨hr, rfl, rfl⟩ := hstep
  have hc : constList es1 = false := by
    cases h : constList es1
    · rfl
    · obtain ⟨vs, hvs⟩ := const_list_to_val es1 h
      simp [hvs] at hv
  rcases reduce_split_r hr es1 es2 hr rfl hc with
    ⟨es'', rfl, hr'⟩ | ⟨n, m, -, hfill, ⟨lh, hlh⟩, rfl, hf⟩
  · exact .inl ⟨es'', rfl, hr', rfl, rfl⟩
  · cases hf
    exact .inr ⟨n, m, lh, hfill, hlh, rfl⟩

@[rocq_alias iriswasm.reduce_ves]
theorem reduce_ves (v : Value) (es es' : List AdministrativeInstruction) (σ σ' : State)
    (efs : List Expr) (obs : List Observation) :
    PrimStep.Reducible ((es : Expr), σ) →
    primStep ([.basic (.const v)] ++ es, σ) obs (es', σ', efs) →
    (es' = [.basic (.const v)] ++ es'.drop 1 ∧ primStep (es, σ) obs (es'.drop 1, σ', efs)) ∨
    (∃ lh lh', lfilled 0 lh [.trap] es' = true ∧ lfilled 0 lh' [.trap] es = true ∧ σ = σ') := by
  rintro ⟨obs0, e0, ⟨s0, l0, i0⟩, efs0, hr0, -, -⟩ hstep
  obtain ⟨s, l, i⟩ := σ
  obtain ⟨s', l', i'⟩ := σ'
  obtain ⟨hr, rfl, rfl⟩ := hstep
  rcases reduce_ves_core hr v es rfl ⟨_, _, _, hr0⟩ with
    ⟨h1, h2⟩ | ⟨⟨lh, h1⟩, ⟨lh', h2⟩, rfl, hf⟩
  · exact .inl ⟨h1, h2, rfl, rfl⟩
  · cases hf
    exact .inr ⟨lh, lh', h1, h2, rfl⟩

end IrisWasm
