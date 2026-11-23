/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Helpers.Prelude.IrisReduceProperties
import IrisWasm.Helpers.Prelude.FirstInstr

/-! Port of `theories/iris/helpers/prelude/iris_reduce_det_prelude.v`. -/

namespace IrisWasm

open Wasm

/-- The conclusion of `reduce_det`: the two reducts agree, or the reduced expression starts with
`grow_memory`, or everything starts with a trap and the states agree. -/
@[rocq_alias iriswasm.reduce_det_goal]
def reduceDetGoal (ws1 : StoreRecord) (f1 : Frame) (es1 : List AdministrativeInstruction)
    (ws2 : StoreRecord) (f2 : Frame) (es2 es : List AdministrativeInstruction) : Prop :=
  (ws1, f1, es1) = (ws2, f2, es2) ∨
  (∃ x depth, firstInstr es = some (.basic (.growMemory x), depth)) ∨
  (∃ i1 i2 i3, firstInstr es = some (.trap, i1) ∧ firstInstr es1 = some (.trap, i2) ∧
    firstInstr es2 = some (.trap, i3) ∧ (ws1, f1) = (ws2, f2))

end IrisWasm

/-! Helper lemmas for the `reduce_det` chain (no Coq counterpart: they replace the Ltac case
analyses). -/

namespace IrisWasm.Helpers.ReduceDetPrelude
open Wasm
open AdministrativeInstruction (basic trap)

theorem lfilled0 {lh : Lholed} {es LI : List AdministrativeInstruction} :
    lfilled 0 lh es LI = true →
      ∃ bef aft, lh = .base bef aft ∧ constList bef = true ∧ LI = bef ++ es ++ aft := by
  intro h; rw [lfilled_Ind_Equivalent] at h; cases h; exact ⟨_, _, rfl, ‹_›, rfl⟩

theorem lfilledS {k : Nat} {lh : Lholed} {es LI : List AdministrativeInstruction} :
    lfilled (k + 1) lh es LI = true →
      ∃ bef n es0 lh' aft LI0, lh = .rec_ bef n es0 lh' aft ∧ constList bef = true ∧
        lfilled k lh' es LI0 = true ∧ LI = bef ++ .label n es0 LI0 :: aft := by
  intro h; rw [lfilled_Ind_Equivalent] at h; cases h
  exact ⟨_, _, _, _, _, _, rfl, ‹_›, (lfilled_Ind_Equivalent ..).2 ‹_›, by simp⟩

theorem lfilled_label {k : Nat} {lh : Lholed} {es LI : List AdministrativeInstruction} (n : Nat)
    (es0 : List AdministrativeInstruction) (h : lfilled k lh es LI = true) :
    lfilled (k + 1) (.rec_ [] n es0 lh []) es [.label n es0 LI] = true := by
  rw [lfilled_Ind_Equivalent] at h ⊢
  simpa using LfilledInd.lfilledRec k [] n es0 lh [] es LI rfl h

theorem lfilled_base {es LI : List AdministrativeInstruction} :
    lfilled 0 (.base [] []) es LI = true ↔ LI = es := by
  simp [lfilled, lfill, constList]

theorem exists_first_nonconst {es : List AdministrativeInstruction} (h : constList es = false) :
    ∃ u x w, es = u ++ x :: w ∧ constList u = true ∧ isConst x = false := by
  induction es with
  | nil => simp [constList] at h
  | cons a es ih =>
    by_cases ha : isConst a = true
    · have : constList es = false := by simpa [constList, ha] using h
      obtain ⟨u, x, w, rfl, hu, hx⟩ := ih this
      exact ⟨a :: u, x, w, rfl, by simp_all [constList], hx⟩
    · exact ⟨[], a, es, rfl, rfl, by simpa using ha⟩

theorem base_split {L vs rest : List AdministrativeInstruction} {e : AdministrativeInstruction}
    (heq : L = vs ++ e :: rest) (hc : constList L.dropLast = true)
    (hl : ∀ x, L.getLast? = some x → isConst x = false) (hvs : constList vs = true)
    (he : isConst e = false) : vs = L.dropLast ∧ L.getLast? = some e ∧ rest = [] := by
  have hne : L ≠ [] := by simp [heq]
  obtain ⟨x, hx⟩ : ∃ x, L.getLast? = some x := by
    cases h : L.getLast? with
    | none => simp_all
    | some x => exact ⟨x, rfl⟩
  obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.1 hx
  simp only [List.dropLast_concat] at hc ⊢
  obtain ⟨h1, h2, h3⟩ := first_values _ _ _ _ _ _ (hl x hx) he hc hvs heq
  exact ⟨h1.symm, h2 ▸ hx, h3.symm⟩

theorem const_nonempty {es : List AdministrativeInstruction} {s f s' f' es'}
    (h : Reduce s f es s' f' es') :
    ∃ u x w, es = u ++ x :: w ∧ constList u = true ∧ isConst x = false := by
  apply exists_first_nonconst
  cases hc : constList es with
  | false => rfl
  | true => exact (values_no_reduce h hc).elim

theorem trap_first_aux {s f es s' f'} {es' : List AdministrativeInstruction}
    (h : Reduce s f es s' f' es') :
    ∀ vs rest, es = vs ++ trap :: rest → constList vs = true →
      s' = s ∧ f' = f ∧ ∃ vs' rest', es' = vs' ++ trap :: rest' ∧ constList vs' = true := by
  induction h with
  | label es1 es1' k lh hsub h1 h2 ih =>
    intro vs rest heq hvs
    cases k with
    | zero =>
      obtain ⟨bef, aft, rfl, hbef, rfl⟩ := lfilled0 h1
      obtain ⟨bef', aft', hh, -, rfl⟩ := lfilled0 h2
      cases hh
      obtain ⟨u, x, w, rfl, hu, hx⟩ := const_nonempty hsub
      obtain ⟨rfl, rfl, rfl⟩ := first_values (bef ++ u) x (w ++ aft) vs trap rest hx rfl
        (const_list_concat hbef hu) hvs (by simpa using heq)
      obtain ⟨rfl, rfl, vs', rest', rfl, hvs'⟩ := ih u w rfl hu
      exact ⟨rfl, rfl, bef ++ vs', rest' ++ aft, by simp, const_list_concat hbef hvs'⟩
    | succ k =>
      obtain ⟨bef, n, es0, lh', aft, LI0, rfl, hbef, -, rfl⟩ := lfilledS h1
      obtain ⟨-, h, -⟩ := first_values bef _ aft vs trap rest (by simp [isConst]) rfl hbef hvs heq
      cases h
  | simple hs =>
    intro vs rest heq hvs
    cases hs
    case trap => exact ⟨rfl, rfl, [], [], rfl, rfl⟩
    all_goals
      obtain ⟨-, hlast, -⟩ := base_split heq
        (by first | rfl | (simp only [List.dropLast_concat]; assumption) |
          (simp [constList]; assumption)) (by simp [isConst]) hvs rfl
      simp at hlast
  | _ =>
    intro vs rest heq hvs
    obtain ⟨-, hlast, -⟩ := base_split heq
      (by first | rfl | (simp only [List.dropLast_concat]; assumption) |
        (simp only [List.dropLast_concat]; subst_vars; exact v_to_e_is_const_list _))
      (by simp [isConst]) hvs rfl
    simp at hlast

theorem reduce_trap_first {s f es s' f'} {es' vs rest : List AdministrativeInstruction}
    (h : Reduce s f es s' f' es') (heq : es = vs ++ trap :: rest) (hvs : constList vs = true) :
    s' = s ∧ f' = f ∧ ∃ vs' rest', es' = vs' ++ trap :: rest' ∧ constList vs' = true :=
  trap_first_aux h vs rest heq hvs

theorem singleton_split {x : AdministrativeInstruction}
    {bef es aft : List AdministrativeInstruction}
    (h : [x] = bef ++ es ++ aft) (hne : es ≠ []) : bef = [] ∧ es = [x] ∧ aft = [] := by
  have hl := congrArg List.length h
  simp at hl
  have : es.length ≠ 0 := by simpa using hne
  have hb : bef = [] := List.eq_nil_of_length_eq_zero (by omega)
  have ha : aft = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst hb ha; simp at h; exact ⟨rfl, h.symm, rfl⟩

theorem inv_label {s f s' f'} {n : Nat} {es0 LI m : List AdministrativeInstruction}
    (h : Reduce s f [.label n es0 LI] s' f' m) :
    (s' = s ∧ f' = f ∧ ((constList LI = true ∧ m = LI) ∨ (LI = [trap] ∧ m = [trap]) ∨
      (∃ i lh vs, constList vs = true ∧ vs.length = n ∧
        lfilled i lh (vs ++ [basic (.br i)]) LI = true ∧ m = vs ++ es0))) ∨
    (∃ LI', Reduce s f LI s' f' LI' ∧ m = [.label n es0 LI']) := by
  generalize heq : [AdministrativeInstruction.label n es0 LI] = es at h
  induction h with
  | label es1 es1' k lh hsub h1 h2 ih =>
    cases k with
    | zero =>
      obtain ⟨bef, aft, rfl, -, rfl⟩ := lfilled0 h1
      obtain ⟨rfl, rfl, rfl⟩ := singleton_split heq (reduce_not_nil hsub)
      rw [lfilled_base] at h2; subst h2; exact ih rfl
    | succ k =>
      obtain ⟨bef, n', es0', lh', aft, LI0, rfl, -, hf, rfl⟩ := lfilledS h1
      obtain ⟨bef', n'', es0'', lh'', aft', LI1, hh, -, hf', rfl⟩ := lfilledS h2
      cases hh
      obtain ⟨rfl, h, rfl⟩ := singleton_split (es := [_]) (by simpa using heq) (by simp)
      simp at h; obtain ⟨rfl, rfl, rfl⟩ := h
      exact .inr ⟨LI1, .label es1 es1' k lh' hsub hf hf', by simp⟩
  | simple hs =>
    cases hs
    case labelConst =>
      cases heq; exact .inl ⟨rfl, rfl, .inl ⟨‹_›, rfl⟩⟩
    case labelTrap => cases heq; exact .inl ⟨rfl, rfl, .inr (.inl ⟨rfl, rfl⟩)⟩
    case br =>
      cases heq; exact .inl ⟨rfl, rfl, .inr (.inr ⟨_, _, _, ‹_›, ‹_›, ‹_›, rfl⟩)⟩
    case trap =>
      rename_i hlf
      obtain ⟨bef, aft, rfl, -, rfl⟩ := lfilled0 hlf
      have h' := congrArg (trap ∈ ·) heq; simp at h'
    all_goals first | (simp at heq; done) | (have := congrArg List.getLast? heq; simp at this)
  | _ => first | (simp at heq; done) | (have := congrArg List.getLast? heq; simp at this)

theorem inv_local {s f s' f'} {n : Nat} {f0 : Frame} {LI m : List AdministrativeInstruction}
    (h : Reduce s f [.local n f0 LI] s' f' m) :
    (s' = s ∧ f' = f ∧ ((constList LI = true ∧ LI.length = n ∧ m = LI) ∨
      (LI = [trap] ∧ m = [trap]) ∨
      (∃ i lh vs, constList vs = true ∧ vs.length = n ∧
        lfilled i lh (vs ++ [basic .return_]) LI = true ∧ m = vs))) ∨
    (∃ f0' LI', Reduce s f0 LI s' f0' LI' ∧ m = [.local n f0' LI'] ∧ f' = f) := by
  generalize heq : [AdministrativeInstruction.local n f0 LI] = es at h
  induction h with
  | label es1 es1' k lh hsub h1 h2 ih =>
    cases k with
    | zero =>
      obtain ⟨bef, aft, rfl, -, rfl⟩ := lfilled0 h1
      obtain ⟨rfl, rfl, rfl⟩ := singleton_split heq (reduce_not_nil hsub)
      rw [lfilled_base] at h2; subst h2; exact ih rfl
    | succ k =>
      obtain ⟨bef, n', es0', lh', aft, LI0, rfl, -, -, rfl⟩ := lfilledS h1
      have h' := congrArg (AdministrativeInstruction.label n' es0' LI0 ∈ ·) heq; simp at h'
  | simple hs =>
    cases hs
    case localConst =>
      cases heq; exact .inl ⟨rfl, rfl, .inl ⟨‹_›, ‹_›, rfl⟩⟩
    case localTrap => cases heq; exact .inl ⟨rfl, rfl, .inr (.inl ⟨rfl, rfl⟩)⟩
    case return_ =>
      cases heq; exact .inl ⟨rfl, rfl, .inr (.inr ⟨_, _, _, ‹_›, ‹_›, ‹_›, rfl⟩)⟩
    case trap =>
      rename_i hlf
      obtain ⟨bef, aft, rfl, -, rfl⟩ := lfilled0 hlf
      have h' := congrArg (trap ∈ ·) heq; simp at h'
    all_goals first | (simp at heq; done) | (have := congrArg List.getLast? heq; simp at this)
  | «local» hsub _ => cases heq; exact .inr ⟨_, _, hsub, rfl, rfl⟩
  | _ => first | (simp at heq; done) | (have := congrArg List.getLast? heq; simp at this)

theorem goal_lift {s1 f1 s2 f2} {vs0 rest m1 m2 M : List AdministrativeInstruction}
    (hc : constList vs0 = true) (h : reduceDetGoal s1 f1 m1 s2 f2 m2 M) :
    reduceDetGoal s1 f1 (vs0 ++ m1 ++ rest) s2 f2 (vs0 ++ m2 ++ rest) (vs0 ++ M ++ rest) := by
  simp only [List.append_assoc]
  rcases h with h | ⟨x, i, hi⟩ | ⟨i1, i2, i3, h1, h2, h3, h4⟩
  · simp at h; obtain ⟨rfl, rfl, rfl⟩ := h; exact .inl rfl
  · exact .inr (.inl ⟨x, i, by rw [first_instr_const _ _ hc, first_instr_app _ _ _ hi]⟩)
  · exact .inr (.inr ⟨i1, i2, i3, by rw [first_instr_const _ _ hc, first_instr_app _ _ _ h1],
      by rw [first_instr_const _ _ hc, first_instr_app _ _ _ h2],
      by rw [first_instr_const _ _ hc, first_instr_app _ _ _ h3], h4⟩)

theorem firstInstr_label {n : Nat} {es0 LI : List AdministrativeInstruction} {e i}
    (h : firstInstr LI = some (e, i)) : firstInstr [.label n es0 LI] = some (e, i + 1) := by
  rw [firstInstr_cons, firstInstrInstr_label, h]

theorem goal_label {s1 f1 s2 f2} {n : Nat} {es0 l1 l2 LI : List AdministrativeInstruction}
    (h : reduceDetGoal s1 f1 l1 s2 f2 l2 LI) :
    reduceDetGoal s1 f1 [.label n es0 l1] s2 f2 [.label n es0 l2] [.label n es0 LI] := by
  rcases h with h | ⟨x, i, hi⟩ | ⟨i1, i2, i3, h1, h2, h3, h4⟩
  · simp at h; obtain ⟨rfl, rfl, rfl⟩ := h; exact .inl rfl
  · exact .inr (.inl ⟨x, i + 1, firstInstr_label hi⟩)
  · exact .inr (.inr ⟨_, _, _, firstInstr_label h1, firstInstr_label h2, firstInstr_label h3, h4⟩)

theorem goal_local {s1 f1 s2 f2} {n : Nat} {f f0 : Frame}
    {l1 l2 LI : List AdministrativeInstruction}
    (h : reduceDetGoal s1 f1 l1 s2 f2 l2 LI) :
    reduceDetGoal s1 f0 [.local n f1 l1] s2 f0 [.local n f2 l2] [.local n f LI] := by
  rcases h with h | ⟨x, i, hi⟩ | ⟨i1, i2, i3, h1, h2, h3, h4⟩
  · simp at h; obtain ⟨rfl, rfl, rfl⟩ := h; exact .inl rfl
  · exact .inr (.inl ⟨x, i + 1, first_instr_local _ _ _ _ _ hi⟩)
  · simp at h4
    exact .inr (.inr ⟨_, _, _, first_instr_local _ _ _ _ _ h1, first_instr_local _ _ _ _ _ h2,
      first_instr_local _ _ _ _ _ h3, by simp [h4]⟩)

theorem stuck_no_reduce {s f s' f'} {cs m : List AdministrativeInstruction}
    {e : AdministrativeInstruction} (h : Reduce s f (cs ++ [e]) s' f' m)
    (hcs : constList cs = true) (hlen : cs.length < redexArity s f e) : False := by
  cases he : isConst e
  · exact (Nat.not_lt_of_ge (redexArity_le h hcs he)) hlen
  · exact values_no_reduce h (const_list_concat hcs (by simp [constList, he]))

theorem flat_label_case {s f s' f'} {L es1 es1' les' : List AdministrativeInstruction} {k lh}
    {e : AdministrativeInstruction} (hlast : L.getLast? = some e) (hsub : Reduce s f es1 s' f' es1')
    (hc : constList L.dropLast = true)
    (hlen : L.dropLast.length ≤ redexArity s f e) (hlab : ∀ n es LI, e ≠ .label n es LI)
    (h1 : lfilled k lh es1 L = true) (h2 : lfilled k lh es1' les' = true) :
    es1 = L ∧ les' = es1' := by
  obtain ⟨cs, rfl⟩ := List.getLast?_eq_some_iff.1 hlast
  simp only [List.dropLast_concat] at hc hlen
  cases k with
  | succ k =>
    obtain ⟨bef, n, es0, lh', aft, LI0, rfl, -, -, heq⟩ := lfilledS h1
    have hmem : AdministrativeInstruction.label n es0 LI0 ∈ cs ++ [e] := by rw [heq]; simp
    rcases List.mem_append.1 hmem with h' | h'
    · simp [constList] at hc; have := hc _ h'; simp [isConst] at this
    · simp at h'; exact (hlab _ _ _ h'.symm).elim
  | zero =>
    obtain ⟨bef, aft, rfl, hbef, heq⟩ := lfilled0 h1
    obtain ⟨bef', aft', hh, -, rfl⟩ := lfilled0 h2
    cases hh
    have hne := reduce_not_nil hsub
    rcases List.eq_nil_or_concat aft with rfl | ⟨aft', b, rfl⟩
    · obtain ⟨es1'', x, rfl⟩ : ∃ es1'' x, es1 = es1'' ++ [x] := by
        rcases List.eq_nil_or_concat es1 with h | h
        · exact (hne h).elim
        · obtain ⟨l', b, h⟩ := h; exact ⟨l', b, by simpa using h⟩
      have := List.append_inj' (show cs ++ [e] = (bef ++ es1'') ++ [x] by simpa using heq) rfl
      simp at this; obtain ⟨rfl, rfl⟩ := this
      rcases bef with _ | ⟨b0, bef⟩
      · simp
      · exfalso; exact stuck_no_reduce hsub (const_list_split hc).2 (by simp at hlen; omega)
    · have := List.append_inj' (show cs ++ [e] = (bef ++ es1 ++ aft') ++ [b] by simpa using heq) rfl
      simp at this; obtain ⟨rfl, -⟩ := this
      exact (values_no_reduce hsub (const_list_split (const_list_split hc).2).1).elim


theorem flat_trap_case {L : List AdministrativeInstruction} {e : AdministrativeInstruction} {lh}
    (hlast : L.getLast? = some e) (hc : constList L.dropLast = true) (het : e ≠ trap)
    (h : lfilled 0 lh [trap] L = true) : False := by
  obtain ⟨cs, rfl⟩ := List.getLast?_eq_some_iff.1 hlast
  simp only [List.dropLast_concat] at hc
  obtain ⟨bef, aft, -, -, heq⟩ := lfilled0 h
  have hmem : trap ∈ cs ++ [e] := by rw [heq]; simp
  rcases List.mem_append.1 hmem with h' | h'
  · simp [constList] at hc; have := hc _ h'; simp [isConst] at this
  · simp at h'; exact het h'.symm


theorem reduce_gen {s f s' f'} {L es' : List AdministrativeInstruction}
    (h : Reduce s f L s' f' es') :
    ∃ s0 f0 L0 s0' f0' es0, (s0, f0, L0, s0', f0', es0) = (s, f, L, s', f', es') ∧
      Reduce s0 f0 L0 s0' f0' es0 := ⟨_, _, _, _, _, _, rfl, h⟩

theorem flat_trap {L : List AdministrativeInstruction} {lh} (hne : L ≠ [])
    (hc : constList L.dropLast = true) (het : L.getLast hne ≠ trap)
    (h : lfilled 0 lh [trap] L = true) : False :=
  flat_trap_case (List.getLast?_eq_some_getLast hne) hc het h

/-- The `r_label` case of `only_one_reduction`: a flat redex `L` is only reduced by `r_label`
through the trivial context, so the induction hypothesis applies. -/
theorem flat_label_close {G : Prop} {s f s' f' S F S' F'} {k : Nat} {lh : Lholed}
    {es1 es1' les les' L ES' : List AdministrativeInstruction}
    (hsub : Reduce s f es1 s' f' es1') (h1 : lfilled k lh es1 les = true)
    (h2 : lfilled k lh es1' les' = true)
    (heq : (s, f, les, s', f', les') = (S, F, L, S', F', ES'))
    (ih : (s, f, es1, s', f', es1') = (S, F, L, S', F', ES') → G)
    (hne : L ≠ []) (hc : constList L.dropLast = true)
    (hlen : L.dropLast.length ≤ redexArity S F (L.getLast hne))
    (hlab : ∀ n es LI, L.getLast hne ≠ .label n es LI) : G := by
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq
  obtain ⟨rfl, rfl⟩ :=
    flat_label_case (List.getLast?_eq_some_getLast hne) hsub hc hlen hlab h1 h2
  exact ih rfl

/-- Side conditions of `only_one_reduction` about the shape of the reduced list. -/
scoped syntax "rdp_side" : tactic
macro_rules
  | `(tactic| rdp_side) => `(tactic| first
      | rfl | (simp; done) | (simp [redexArity]; done)
      | (simp_all [redexArity, clType, vToEList, constList, isConst]; done)
      | (simp_all [redexArity, clType, vToEList, constList, isConst]; omega)
      | (subst_vars; simp_all [redexArity, clType, vToEList, v_to_e_is_const_list]; done))

/-- One case of `only_one_reduction`, with
`heq : (s0, f0, lhs, s0', f0', rhs) = (s, f, L, s', f', es')`
equating the rule's instance with the analysed reduction: closes the case if the rule cannot
apply to `L`, else unifies and tries to close the goal trivially. -/
scoped syntax "rdp_close " ident : tactic
macro_rules
  | `(tactic| rdp_close $heq) => `(tactic| first
      | (cases $heq:ident
         first
           | (refine (flat_trap ?_ ?_ ?_ (by assumption)).elim <;> first | (simp; done) | rdp_side)
           | (try (first | rfl | (simp_all; done) | (exfalso; omega))))
      | (have hl := congrArg (fun x => x.2.2.1.getLast?) $heq:ident; simp at hl; done)
      | (simp only [Prod.mk.injEq] at $heq:ident
         obtain ⟨hh1, hh2, hh3, hh4, hh5, hh6⟩ := $heq:ident
         obtain ⟨hh7, hh8⟩ := List.append_inj' hh3 rfl
         cases hh8
         (try subst hh1); (try subst hh2); (try subst hh4); (try subst hh5); (try subst hh6)
         (try subst hh7); (try clear hh3)
         try (first | rfl | (simp_all; done) | (exfalso; omega)))
      | skip)

/-- Port of the Coq Ltac `only_one_reduction`. `only_one_reduction H`, for
`H : Reduce s f L s' f' es'` with `L` an explicit list (constants followed by one instruction, or
`vs ++ [e]`), performs an induction on `H` and closes every case whose rule cannot produce `L`:
mismatching left-hand sides, the `rs_trap` case (`L` holds no `trap`), and the `r_label` case
(through `flat_label_close`: only the empty context fits, where the induction hypothesis
applies; skipped when `L` ends with a `label`/`local`, as in Coq). The remaining cases are those of
rules matching `L`; their equations are unified and `rfl`/`simp_all` is tried on them. Differences
with Coq: the Coq tactic takes the equation `Heqes0 : objs = es` as an extra argument; here the
generalisation is internal, and hypothesis names in the remaining cases are inaccessible. -/
scoped syntax "only_one_reduction " ident : tactic
macro_rules
  | `(tactic| only_one_reduction $h) => `(tactic| (
      have hg := reduce_gen $h
      clear $h
      obtain ⟨_, _, _, _, _, _, heq, $h:ident⟩ := hg
      revert heq
      induction $h:ident
      all_goals intro heq
      all_goals first
        | (cases ‹ReduceSimple _ _› <;> rdp_close heq)
        | (exact flat_label_close ‹Reduce _ _ _ _ _ _› (by assumption) (by assumption) heq
            (by assumption) (by simp) (by rdp_side) (by rdp_side) (by simp))
        | rdp_close heq))

/-- Port of the Coq Ltac `only_one objs Hred2`: `left; only_one_reduction Hred2` (the explicit list
`objs` is read off the type of `Hred2`). -/
scoped syntax "only_one " ident : tactic
macro_rules
  | `(tactic| only_one $h) => `(tactic| (left; only_one_reduction $h))

theorem frame_ext {f1 f2 : Frame} (h1 : f1.locs = f2.locs) (h2 : f1.inst = f2.inst) : f1 = f2 := by
  cases f1; cases f2; simp_all

theorem lfilled_base' {bef aft es : List AdministrativeInstruction} (hc : constList bef = true) :
    lfilled 0 (.base bef aft) es (bef ++ es ++ aft) = true := by
  simp [lfilled, lfill, hc]

theorem lfilled_mem_shape {k : Nat} {lh : Lholed} {vs LI : List AdministrativeInstruction}
    {e : AdministrativeInstruction} (h : lfilled k lh (vs ++ [e]) LI = true) :
    e ∈ LI ∨ ∃ n es0 LI0, AdministrativeInstruction.label n es0 LI0 ∈ LI := by
  cases k with
  | zero => obtain ⟨bef, aft, -, -, rfl⟩ := lfilled0 h; left; simp
  | succ k =>
    obtain ⟨bef, n, es0, lh', aft, LI0, -, -, -, rfl⟩ := lfilledS h
    exact .inr ⟨n, es0, LI0, by simp⟩

theorem lfilled_const_false {k : Nat} {lh : Lholed} {vs LI : List AdministrativeInstruction}
    {e : AdministrativeInstruction} (h : lfilled k lh (vs ++ [e]) LI = true)
    (hc : constList LI = true) (he : isConst e = false) : False := by
  simp only [constList, List.all_eq_true] at hc
  rcases lfilled_mem_shape h with h' | ⟨_, _, _, h'⟩
  · simp [hc _ h'] at he
  · simpa [isConst] using hc _ h'

theorem lfilled_trap_false {k : Nat} {lh : Lholed} {vs : List AdministrativeInstruction}
    {e : AdministrativeInstruction} (h : lfilled k lh (vs ++ [e]) [trap] = true)
    (he : e ≠ trap) : False := by
  rcases lfilled_mem_shape h with h' | ⟨_, _, _, h'⟩ <;> simp_all

theorem lfilled_const_es {k : Nat} {lh : Lholed} {es LI : List AdministrativeInstruction}
    (h : lfilled k lh es LI = true) (hc : constList LI = true) : constList es = true := by
  cases k with
  | zero =>
    obtain ⟨bef, aft, -, -, rfl⟩ := lfilled0 h
    exact (const_list_split (const_list_split hc).1).2
  | succ k =>
    obtain ⟨bef, n, es0, lh', aft, LI0, -, -, -, rfl⟩ := lfilledS h
    simp [constList, isConst] at hc

theorem lfilled_trap_es {k : Nat} {lh : Lholed} {es : List AdministrativeInstruction}
    (h : lfilled k lh es [trap] = true) (hne : es ≠ []) : es = [trap] := by
  cases k with
  | zero =>
    obtain ⟨bef, aft, -, -, h⟩ := lfilled0 h
    exact (singleton_split h hne).2.1
  | succ k =>
    obtain ⟨bef, n, es0, lh', aft, LI0, -, -, -, h⟩ := lfilledS h
    have := congrArg (AdministrativeInstruction.label n es0 LI0 ∈ ·) h; simp at this

/-- A reducing `es` cannot sit inside a constant list or `[trap]`. -/
theorem lfilled_reduce_const {s f s' f'} {k : Nat} {lh : Lholed}
    {es es' LI : List AdministrativeInstruction} (hr : Reduce s f es s' f' es')
    (h : lfilled k lh es LI = true) (hc : constList LI = true ∨ LI = [trap]) : False := by
  rcases hc with hc | rfl
  · exact values_no_reduce hr (lfilled_const_es h hc)
  · obtain rfl := lfilled_trap_es h (reduce_not_nil hr); exact test_no_reduce_trap hr

theorem firstInstr_trap {vs rest : List AdministrativeInstruction} (hvs : constList vs = true) :
    firstInstr (vs ++ trap :: rest) = some (trap, 0) := by
  rw [first_instr_const _ _ hvs, firstInstr_cons]; simp [firstInstrInstr]

theorem goal_trap {s f s1 f1 s2 f2} {L L1 L2 vs rest : List AdministrativeInstruction}
    (h1 : Reduce s f L s1 f1 L1) (h2 : Reduce s f L s2 f2 L2) (hL : L = vs ++ trap :: rest)
    (hvs : constList vs = true) : reduceDetGoal s1 f1 L1 s2 f2 L2 L := by
  obtain ⟨rfl, rfl, vs1, r1, rfl, hv1⟩ := reduce_trap_first h1 hL hvs
  obtain ⟨rfl, rfl, vs2, r2, rfl, hv2⟩ := reduce_trap_first h2 hL hvs
  subst hL
  exact .inr (.inr ⟨0, 0, 0, firstInstr_trap hvs, firstInstr_trap hv1, firstInstr_trap hv2, rfl⟩)

/-- The non-recursive reducts of `[label n es0 LI]` (`rs_label_const`, `rs_label_trap`, `rs_br`). -/
def LabelStep (n : Nat) (es0 LI m : List AdministrativeInstruction) : Prop :=
  (constList LI = true ∧ m = LI) ∨ (LI = [trap] ∧ m = [trap]) ∨
    (∃ i lh vs, constList vs = true ∧ vs.length = n ∧
      lfilled i lh (vs ++ [basic (.br i)]) LI = true ∧ m = vs ++ es0)

theorem label_step_no_reduce {s f s' f'} {n : Nat} {es0 LI m LI' : List AdministrativeInstruction}
    (h : LabelStep n es0 LI m) (hr : Reduce s f LI s' f' LI') : False := by
  rcases h with ⟨hc, -⟩ | ⟨rfl, -⟩ | ⟨i, lh, vs, hvs, -, hbr, -⟩
  · exact values_no_reduce hr hc
  · exact test_no_reduce_trap hr
  · exact lfilled_br_and_reduce hr hvs (Nat.le_refl _) hbr (lfilled_base.2 rfl)

theorem label_step_det {n : Nat} {es0 LI m1 m2 : List AdministrativeInstruction}
    (h1 : LabelStep n es0 LI m1) (h2 : LabelStep n es0 LI m2) : m1 = m2 := by
  rcases h1 with ⟨hc, rfl⟩ | ⟨rfl, rfl⟩ | ⟨i, lh, vs, hvs, hl, hbr, rfl⟩
  · rcases h2 with ⟨-, rfl⟩ | ⟨rfl, -⟩ | ⟨_, _, _, -, -, hbr', -⟩
    · rfl
    · simp [constList, isConst] at hc
    · exact (lfilled_const_false hbr' hc rfl).elim
  · rcases h2 with ⟨hc', -⟩ | ⟨-, rfl⟩ | ⟨_, _, _, -, -, hbr', -⟩
    · simp [constList, isConst] at hc'
    · rfl
    · exact (lfilled_trap_false hbr' (by simp)).elim
  · rcases h2 with ⟨hc', -⟩ | ⟨rfl, -⟩ | ⟨i', lh', vs', hvs', hl', hbr', rfl⟩
    · exact (lfilled_const_false hbr hc' rfl).elim
    · exact (lfilled_trap_false hbr (by simp)).elim
    · obtain ⟨-, -, h⟩ := lfilled_first_values hbr hbr' hvs hvs' rfl rfl (by simp) (by simp)
      rw [(h (hl.trans hl'.symm)).1]

/-- Every reduction of `[label n es0 LI]` is either a `LabelStep` or a reduction of `LI`. -/
theorem inv_label' {s f s' f'} {n : Nat} {es0 LI m : List AdministrativeInstruction}
    (h : Reduce s f [.label n es0 LI] s' f' m) :
    (s' = s ∧ f' = f ∧ LabelStep n es0 LI m) ∨
      (∃ LI', Reduce s f LI s' f' LI' ∧ m = [.label n es0 LI']) := inv_label h

theorem label_step_goal {s f s2 f2} {n : Nat} {es0 LI m1 m2 : List AdministrativeInstruction}
    (h1 : LabelStep n es0 LI m1) (h2 : Reduce s f [.label n es0 LI] s2 f2 m2) :
    (s, f, m1) = (s2, f2, m2) := by
  rcases inv_label' h2 with ⟨rfl, rfl, h2'⟩ | ⟨LI', hr, -⟩
  · rw [label_step_det h1 h2']
  · exact (label_step_no_reduce h1 hr).elim

/-- The non-recursive reducts of `[local n f0 LI]` (`rs_local_const`, `rs_local_trap`,
`rs_return`). -/
def LocalStep (n : Nat) (LI m : List AdministrativeInstruction) : Prop :=
  (constList LI = true ∧ LI.length = n ∧ m = LI) ∨ (LI = [trap] ∧ m = [trap]) ∨
    (∃ i lh vs, constList vs = true ∧ vs.length = n ∧
      lfilled i lh (vs ++ [basic .return_]) LI = true ∧ m = vs)

theorem local_step_no_reduce {s f s' f'} {n : Nat} {LI m LI' : List AdministrativeInstruction}
    (h : LocalStep n LI m) (hr : Reduce s f LI s' f' LI') : False := by
  rcases h with ⟨hc, -⟩ | ⟨rfl, -⟩ | ⟨i, lh, vs, hvs, -, hret, -⟩
  · exact values_no_reduce hr hc
  · exact test_no_reduce_trap hr
  · exact lfilled_return_and_reduce hr hvs hret (lfilled_base.2 rfl)

theorem local_step_det {n : Nat} {LI m1 m2 : List AdministrativeInstruction}
    (h1 : LocalStep n LI m1) (h2 : LocalStep n LI m2) : m1 = m2 := by
  rcases h1 with ⟨hc, -, rfl⟩ | ⟨rfl, rfl⟩ | ⟨i, lh, vs, hvs, hl, hret, rfl⟩
  · rcases h2 with ⟨-, -, rfl⟩ | ⟨rfl, -⟩ | ⟨_, _, _, -, -, hret', -⟩
    · rfl
    · simp [constList, isConst] at hc
    · exact (lfilled_const_false hret' hc rfl).elim
  · rcases h2 with ⟨hc', -⟩ | ⟨-, rfl⟩ | ⟨_, _, _, -, -, hret', -⟩
    · simp [constList, isConst] at hc'
    · rfl
    · exact (lfilled_trap_false hret' (by simp)).elim
  · rcases h2 with ⟨hc', -⟩ | ⟨rfl, -⟩ | ⟨i', lh', vs', hvs', hl', hret', rfl⟩
    · exact (lfilled_const_false hret hc' rfl).elim
    · exact (lfilled_trap_false hret (by simp)).elim
    · obtain ⟨-, -, h⟩ := lfilled_first_values hret hret' hvs hvs' rfl rfl (by simp) (by simp)
      exact (h (hl.trans hl'.symm)).1

theorem inv_local' {s f s' f'} {n : Nat} {f0 : Frame} {LI m : List AdministrativeInstruction}
    (h : Reduce s f [.local n f0 LI] s' f' m) :
    (s' = s ∧ f' = f ∧ LocalStep n LI m) ∨
      (∃ f0' LI', Reduce s f0 LI s' f0' LI' ∧ m = [.local n f0' LI'] ∧ f' = f) := inv_local h

theorem local_step_goal {s f s2 f2} {n : Nat} {f0 : Frame}
    {LI m1 m2 : List AdministrativeInstruction}
    (h1 : LocalStep n LI m1) (h2 : Reduce s f [.local n f0 LI] s2 f2 m2) :
    (s, f, m1) = (s2, f2, m2) := by
  rcases inv_local' h2 with ⟨rfl, rfl, h2'⟩ | ⟨_, LI', hr, -⟩
  · rw [local_step_det h1 h2']
  · exact (local_step_no_reduce h1 hr).elim

theorem lengthRec_append (l1 l2 : List AdministrativeInstruction) :
    lengthRec (l1 ++ l2) = lengthRec l1 + lengthRec l2 := by
  simp [lengthRec]

theorem lengthRec_cons (a : AdministrativeInstruction) (l : List AdministrativeInstruction) :
    lengthRec (a :: l) = sizeOfInstruction a + lengthRec l := by
  simp [lengthRec]

theorem lengthRec_pos {l : List AdministrativeInstruction} (h : l ≠ []) : 0 < lengthRec l := by
  obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil h
  have : 0 < sizeOfInstruction a := by cases a <;> simp [sizeOfInstruction]
  rw [lengthRec_cons]; omega

theorem sizeOfInstruction_label {n : Nat} {es0 LI : List AdministrativeInstruction} :
    sizeOfInstruction (.label n es0 LI) = lengthRec LI + 1 := by
  simp [sizeOfInstruction, lengthRec]

theorem sizeOfInstruction_local {n : Nat} {f : Frame} {LI : List AdministrativeInstruction} :
    sizeOfInstruction (.local n f LI) = lengthRec LI + 1 := by
  simp [sizeOfInstruction, lengthRec]

theorem lengthRec_label {n : Nat} {es0 LI : List AdministrativeInstruction} :
    lengthRec [.label n es0 LI] = lengthRec LI + 1 := by
  simp [lengthRec, sizeOfInstruction]

theorem lengthRec_local {n : Nat} {f : Frame} {LI : List AdministrativeInstruction} :
    lengthRec [.local n f LI] = lengthRec LI + 1 := by
  simp [lengthRec, sizeOfInstruction]

end IrisWasm.Helpers.ReduceDetPrelude
