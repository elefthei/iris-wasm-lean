/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Language.Iris.Iris
import IrisWasm.Helpers.Prelude.IrisLfilledProperties

/-! Port of `theories/iris/helpers/prelude/iris_wasm_lang_properties.v`. -/

namespace IrisWasm

open Wasm Iris Iris.ProgramLogic

/-! ## Tactics

Coq's `false_assumption` is the macro of the same name in `IrisLfilledProperties.lean` (identical
Ltac declared in both Coq files). The macros below use non-reserved atoms (`&"…"`) so that their
names stay usable as identifiers (e.g. the lemma `const_list_app`). -/

/-- Closes (or splits) a goal `constList (l1 ++ l2) = true` into the two halves. -/
syntax (name := constListAppTac) &"const_list_app" : tactic
macro_rules (kind := constListAppTac)
  | `(tactic| const_list_app) => `(tactic|
      (simp only [constList, List.all_append, Bool.and_eq_true]
       refine ⟨?_, ?_⟩ <;> try simp_all [constList]))

#rocq_ignore iriswasm.not_const "Ltac, unused upstream"

/-- `get_tail x xs ys y Htail` introduces `Htail : x :: xs = ys ++ [y]`. -/
syntax (name := getTailTac)
  &"get_tail " term:max ppSpace term:max ppSpace ident ppSpace ident ppSpace ident : tactic
macro_rules (kind := getTailTac)
  | `(tactic| get_tail $x $xs $ys $y $Htail) => `(tactic|
      obtain ⟨$ys:ident, $y:ident, $Htail:ident⟩ : ∃ ys y, $x :: $xs = ys ++ [y] :=
        ⟨($x :: $xs).dropLast, ($x :: $xs).getLast (List.cons_ne_nil _ _),
          (List.dropLast_concat_getLast (List.cons_ne_nil _ _)).symm⟩)

/-! ## Computation helpers for `toVal` (not in Coq) -/

theorem toVal_eq_some_iff {es : Expr} {v : Val} :
    toVal es = some v ↔ mergeValuesList (es.map toValInstr) = .val v := by
  unfold toVal; split <;> simp_all

theorem toVal_eq_none_iff {es : Expr} :
    toVal es = none ↔ mergeValuesList (es.map toValInstr) = .notVal es := by
  unfold toVal
  rcases hm : mergeValuesList (es.map toValInstr) with v | e
  · simp
  · simp [merge_is_not_val _ _ hm]

theorem toVal_singleton (e : AdministrativeInstruction) :
    toVal [e] = valOfValNotVal (toValInstr e) := by
  simp only [toVal, List.map_cons, List.map_nil]
  rcases toValInstr e with v | x <;> rfl

theorem toVal_cons_const (v : Value) (es : Expr) :
    toVal (.basic (.const v) :: es) =
      valOfValNotVal (valNotValCombine (.immV [v]) (mergeValuesList (es.map toValInstr))) := by
  unfold toVal
  rw [List.map_cons, show toValInstr (.basic (.const v)) = .val (.immV [v]) by rw [toValInstr]]
  show (match mergeValues (.immV [v]) (es.map toValInstr) with | .val v => some v | _ => none) = _
  rw [merge_prepend]; generalize valNotValCombine _ _ = x; cases x <;> rfl

theorem toVal_app_some {es1 es2 : Expr} {v1 : Val} (h : toVal es1 = some v1) :
    toVal (es1 ++ es2) =
      valOfValNotVal (valNotValCombine v1 (mergeValuesList (es2.map toValInstr))) := by
  rw [toVal_eq_some_iff] at h
  unfold toVal; rw [List.map_append, merge_app, h]; dsimp only
  generalize valNotValCombine _ _ = x; cases x <;> rfl

theorem toValInstr_label (n : Nat) (es LI : Expr) :
    toValInstr (.label n es LI) =
      match toVal LI with
      | some (.brV vh) =>
        match vhDecrease (.rec_ [] n es vh []) with
        | some vh' => .val (.brV vh')
        | none => .notVal [.label n es LI]
      | some (.retV lh) => .val (.retV (.rec_ [] n es lh []))
      | some (.callHostV tf h cvs lh) => .val (.callHostV tf h cvs (.label [] n es lh []))
      | _ => .notVal [.label n es LI] := by
  rw [toValInstr]; unfold toVal
  rcases mergeValuesList (LI.map toValInstr) with (_ | _ | _ | _ | _) | _ <;> rfl

theorem toValInstr_local (n : Nat) (f : Frame) (LI : Expr) :
    toValInstr (.local n f LI) =
      match toVal LI with
      | some (.callHostV tf h cvs sh) => .val (.callHostV tf h cvs (.local [] n f sh []))
      | _ => .notVal [.local n f LI] := by
  rw [toValInstr]; unfold toVal
  rcases mergeValuesList (LI.map toValInstr) with (_ | _ | _ | _ | _) | _ <;> rfl

theorem isConst_false_of_toVal_none {e : AdministrativeInstruction} (h : toVal [e] = none) :
    isConst e = false := by
  cases e <;> try rfl
  rename_i b; cases b <;> try rfl
  rw [toVal_singleton, toValInstr] at h; simp [valOfValNotVal] at h

theorem toVal_label_some {n : Nat} {es LI : Expr} {v : Val}
    (h : toVal [.label n es LI] = some v) :
    (∃ i, ∃ vh : ValidHoled i, toVal LI = some (.brV vh)) ∨ (∃ sh, toVal LI = some (.retV sh)) ∨
      (∃ tf h vcs sh, toVal LI = some (.callHostV tf h vcs sh)) := by
  rw [toVal_singleton, toValInstr_label] at h
  rcases hv : toVal LI with _ | (_ | _ | _ | _ | _) <;> simp_all [valOfValNotVal]

theorem toVal_local_some {n : Nat} {f : Frame} {LI : Expr} {v : Val}
    (h : toVal [.local n f LI] = some v) :
    ∃ tf h vcs sh, toVal LI = some (.callHostV tf h vcs sh) := by
  rw [toVal_singleton, toValInstr_local] at h
  rcases hv : toVal LI with _ | (_ | _ | _ | _ | _) <;> simp_all [valOfValNotVal]

/-- The shape of a non-constant, non-trap instruction, as in `to_val_None_first_singleton`. -/
theorem singleton_cases (a : AdministrativeInstruction) (hc : isConst a = false)
    (ht : a ≠ .trap) :
    toVal [a] = none ∨
      (∃ n, a = .basic (.br n)) ∨
      a = .basic .return_ ∨
      (∃ tf h vcs, a = .callHost tf h vcs) ∨
      (∃ n es LI, a = .label n es LI ∧
        ((∃ i, ∃ vh : ValidHoled i, toVal LI = some (.brV vh)) ∨
          (∃ sh, toVal LI = some (.retV sh)) ∨
          (∃ tf h vcs sh, toVal LI = some (.callHostV tf h vcs sh)))) ∨
      (∃ n f LI tf h vcs sh, a = .local n f LI ∧ toVal LI = some (.callHostV tf h vcs sh)) := by
  cases a with
  | basic b =>
    cases b
    case br n => exact .inr (.inl ⟨n, rfl⟩)
    case return_ => exact .inr (.inr (.inl rfl))
    case const => simp [isConst] at hc
    all_goals exact .inl (by simp [toVal_singleton, toValInstr, valOfValNotVal])
  | trap => exact absurd rfl ht
  | invoke => exact .inl (by simp [toVal_singleton, toValInstr, valOfValNotVal])
  | label n es LI =>
    cases h : toVal [.label n es LI] with
    | none => exact .inl rfl
    | some v => exact .inr (.inr (.inr (.inr (.inl ⟨n, es, LI, rfl, toVal_label_some h⟩))))
  | «local» n f LI =>
    cases h : toVal [.local n f LI] with
    | none => exact .inl rfl
    | some v =>
      obtain ⟨tf, h', vcs, sh, hv⟩ := toVal_local_some h
      exact .inr (.inr (.inr (.inr (.inr ⟨n, f, LI, tf, h', vcs, sh, rfl, hv⟩))))
  | callHost tf h vcs => exact .inr (.inr (.inr (.inl ⟨tf, h, vcs, rfl⟩)))

/-- Composition of contexts: `lhCompose lh' lh` fills `lh` and then `lh'`. -/
def lhCompose : Lholed → Lholed → Lholed
  | .base bef' aft', .base bef aft => .base (bef' ++ bef) (aft ++ aft')
  | .base bef' aft', .rec_ bef n es lh aft => .rec_ (bef' ++ bef) n es lh (aft ++ aft')
  | .rec_ bef' n' es' lh' aft', lh => .rec_ bef' n' es' (lhCompose lh' lh) aft'

theorem lfilled_compose {k k' : Nat} {lh lh' : Lholed} {es1 es2 es3 : Expr}
    (h1 : lfilled k lh es1 es2 = true) (h2 : lfilled k' lh' es2 es3 = true) :
    lfilled (k + k') (lhCompose lh' lh) es1 es3 = true := by
  rw [lfilled_Ind_Equivalent] at *
  induction h2 with
  | lfilledBase bef' _ aft' hc' =>
    cases h1 with
    | lfilledBase bef _ aft hc =>
      simpa [lhCompose, List.append_assoc] using
        LfilledInd.lfilledBase (bef' ++ bef) es1 (aft ++ aft')
          (by simp_all [constList])
    | lfilledRec k0 bef n es lh0 aft _ LI hc hf =>
      simpa [lhCompose, List.append_assoc] using
        LfilledInd.lfilledRec k0 (bef' ++ bef) n es lh0 (aft ++ aft') es1 LI
          (by simp_all [constList]) hf
  | lfilledRec k' bef' n' es' lh'1 aft' _ LI3 hc' _ ih =>
    exact .lfilledRec (k + k') bef' n' es' (lhCompose lh'1 lh) aft' es1 LI3 hc' (ih h1)

theorem split_first_nonconst {P A B S : List AdministrativeInstruction}
    {x : AdministrativeInstruction} (hP : constList P = true) (h : A ++ B = P ++ x :: S) :
    (∃ A1 A2, A = A1 ++ x :: A2 ∧ constList A1 = true) ∨
      (constList A = true ∧ ∃ B1 B2, B = B1 ++ x :: B2 ∧ constList B1 = true) := by
  rcases List.append_eq_append_iff.1 h with ⟨l', rfl, rfl⟩ | ⟨bs, rfl, hS⟩
  · simp only [constList, List.all_append, Bool.and_eq_true] at hP
    exact .inr ⟨hP.1, l', S, rfl, hP.2⟩
  · rcases bs with _ | ⟨b, bs⟩
    · exact .inr ⟨by simpa using hP, [], S, by simpa using hS.symm, rfl⟩
    · simp only [List.cons_append, List.cons.injEq] at hS
      obtain ⟨rfl, rfl⟩ := hS
      exact .inl ⟨P, bs, rfl, hP⟩

/-- Common core of the `filled_is_val_*_base_app_cases` lemmas. -/
theorem app_cases_aux {x : AdministrativeInstruction} (hx : isConst x = false)
    {P S vs es1 es2 es' : List AdministrativeInstruction} (hP : constList P = true)
    (hvs : constList vs = true) (h : vs ++ (es1 ++ es2) ++ es' = P ++ [x] ++ S) :
    (∃ es11 es12, es1 = es11 ++ x :: es12 ∧ constList es11 = true) ∨
      (∃ es21 es22, es2 = es21 ++ x :: es22 ∧ constList es21 = true ∧ constList es1 = true) ∨
      (∃ es1' es2', es' = es1' ++ x :: es2' ∧ constList es1 = true ∧ constList es2 = true ∧
        constList es1' = true) := by
  have h1 : vs ++ (es1 ++ (es2 ++ es')) = P ++ x :: S := by simpa using h
  rcases split_first_nonconst hP h1 with ⟨A1, A2, rfl, -⟩ | ⟨-, B1, B2, h2, hB1⟩
  · simp [constList, hx] at hvs
  rcases split_first_nonconst hB1 h2 with h3 | ⟨hc1, C1, C2, h3, hC1⟩
  · exact .inl h3
  rcases split_first_nonconst hC1 h3 with h4 | ⟨hc2, D1, D2, h4, hD1⟩
  · obtain ⟨A1, A2, h4, h5⟩ := h4
    exact .inr (.inl ⟨A1, A2, h4, h5, hc1⟩)
  · exact .inr (.inr ⟨D1, D2, h4, hc1, hc2, hD1⟩)

theorem toVal_ne_nil {es : List AdministrativeInstruction} (h : toVal es = none) : es ≠ [] := by
  rintro rfl; simp [toVal, mergeValuesList] at h

theorem toVal_ne_trap {es : List AdministrativeInstruction} (h : toVal es = none) :
    es ≠ [.trap] := by
  rintro rfl; simp [toVal, mergeValuesList, mergeValues, toValInstr] at h

theorem toVal_constList_false {es : List AdministrativeInstruction} (h : toVal es = none) :
    constList es = false := by
  cases hc : constList es
  · rfl
  · obtain ⟨_, h'⟩ := const_list_to_val _ hc; simp_all

@[rocq_alias iriswasm.last_inj]
theorem last_inj {A : Type} (l1 l2 : List A) (a b : A) :
    l1 = l2 → l1.getLast? = some a → l2.getLast? = some b → a = b := by
  rintro rfl h1 h2; rw [h1] at h2; exact Option.some.inj h2

@[rocq_alias iriswasm.destruct_list_rev]
theorem destruct_list_rev {A : Type} (l : List A) : l = [] ∨ ∃ a l', l = l' ++ [a] := by
  rcases l.eq_nil_or_concat with h | ⟨l', a, h⟩
  · exact .inl h
  · exact .inr ⟨a, l', by simpa using h⟩

@[rocq_alias iriswasm.v_to_e_is_fmap]
theorem v_to_e_is_fmap (vs : List Value) :
    vToEList vs = vs.map fun x => .basic (.const x) := by
  rfl

@[rocq_alias iriswasm.to_val_cat]
theorem to_val_cat (es1 es2 : List AdministrativeInstruction) (vs : List Value) :
    toVal (es1 ++ es2) = some (.immV vs) →
      toVal es1 = some (.immV (vs.take es1.length)) ∧
      toVal es2 = some (.immV (vs.drop es1.length)) := by
  intro h
  have h' : vToEList vs = es1 ++ es2 := of_to_val _ _ h
  have h1 : es1 = vToEList (vs.take es1.length) := by
    have := congrArg (List.take es1.length) h'
    simp only [List.take_left'] at this
    rw [← this]; simp [vToEList, List.map_take]
  have h2 : es2 = vToEList (vs.drop es1.length) := by
    have := congrArg (List.drop es1.length) h'
    simp only [List.drop_left'] at this
    rw [← this]; simp [vToEList, List.map_drop]
  refine ⟨?_, ?_⟩
  · calc toVal es1 = toVal (vToEList (vs.take es1.length)) := by rw [← h1]
      _ = _ := to_of_val (.immV _)
  · calc toVal es2 = toVal (vToEList (vs.drop es1.length)) := by rw [← h2]
      _ = _ := to_of_val (.immV _)

@[rocq_alias iriswasm.to_val_cat_inv]
theorem to_val_cat_inv (es1 es2 : List AdministrativeInstruction) (vs1 vs2 : List Value) :
    toVal es1 = some (.immV vs1) → toVal es2 = some (.immV vs2) →
      toVal (es1 ++ es2) = some (.immV (vs1 ++ vs2)) := by
  intro h1 h2
  rw [to_val_is_immV _ _ h1, to_val_is_immV _ _ h2, ← List.map_append]
  exact to_of_val (.immV _)

@[rocq_alias iriswasm.to_val_cat_None1]
theorem to_val_cat_None1 (es1 es2 : List AdministrativeInstruction) :
    toVal es1 = none → toVal (es1 ++ es2) = none := by
  exact to_val_None_append es1 es2

@[rocq_alias iriswasm.to_val_cat_None2]
theorem to_val_cat_None2 (es1 es2 : List AdministrativeInstruction) :
    constList es1 = true → toVal es2 = none → toVal (es1 ++ es2) = none := by
  exact to_val_None_prepend_const es1 es2

@[rocq_alias iriswasm.app_to_val]
theorem app_to_val (vs es es' : List AdministrativeInstruction) :
    constList vs = true → (toVal (vs ++ es ++ es')).isSome = true → (toVal es).isSome = true := by
  intro hc hs
  cases h : toVal es with
  | some _ => rfl
  | none =>
    rw [List.append_assoc, to_val_None_prepend_const _ _ hc (to_val_None_append _ es' h)] at hs
    simp at hs

@[rocq_alias iriswasm.lfilled_to_val]
theorem lfilled_to_val (i : Nat) :
    ∀ lh es LI, (toVal LI).isSome = true → lfilled i lh es LI = true →
      (toVal es).isSome = true := by
  induction i with
  | zero =>
    intro lh es LI hs hf
    rw [lfilled_Ind_Equivalent] at hf
    cases hf with
    | lfilledBase vs _ es' hc => exact app_to_val _ _ _ hc hs
  | succ i ih =>
    intro lh es LI hs hf
    rw [lfilled_Ind_Equivalent] at hf
    cases hf with
    | lfilledRec _ vs n es' lh' es'' _ LI' hc hf' =>
      have h := app_to_val _ _ _ hc hs
      rw [← lfilled_Ind_Equivalent] at hf'
      refine ih lh' es LI' ?_ hf'
      rw [toVal_singleton, toValInstr_label] at h
      rcases hv : toVal LI' with _ | (_ | _ | _ | _ | _) <;> simp_all [valOfValNotVal]

@[rocq_alias iriswasm.first_values_elem_of]
theorem first_values_elem_of (vs1 : List AdministrativeInstruction) (e1 : AdministrativeInstruction)
    (es1 vs2 : List AdministrativeInstruction) (e2 : AdministrativeInstruction)
    (es2 : List AdministrativeInstruction) :
    isConst e1 = false → isConst e2 = false → e2 ∉ vs1 → e1 ∉ vs2 →
      vs1 ++ e1 :: es1 = vs2 ++ e2 :: es2 → vs1 = vs2 ∧ e1 = e2 ∧ es1 = es2 := by
  intro he1 he2
  induction vs1 generalizing vs2 with
  | nil =>
    intro _ hvs2 heq
    cases vs2 with
    | nil => simpa using heq
    | cons b vs2 =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at heq
      obtain ⟨rfl, -⟩ := heq; simp at hvs2
  | cons a vs1 ih =>
    intro hvs1 hvs2 heq
    cases vs2 with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at heq
      obtain ⟨rfl, -⟩ := heq; simp at hvs1
    | cons b vs2 =>
      simp only [List.cons_append, List.cons.injEq] at heq
      obtain ⟨rfl, heq⟩ := heq
      have := ih vs2 (fun h => hvs1 (List.mem_cons_of_mem _ h))
        (fun h => hvs2 (List.mem_cons_of_mem _ h)) heq
      simp_all

@[rocq_alias iriswasm.const_list_elem_of]
theorem const_list_elem_of (e : AdministrativeInstruction) (es : List AdministrativeInstruction) :
    constList es = true → isConst e = false → e ∉ es := by
  intro hes he hin
  have := List.all_eq_true.1 hes e hin
  simp_all

@[rocq_alias iriswasm.to_val_br_base]
theorem to_val_br_base (es1 : List AdministrativeInstruction) (n : Nat) (l : List Value)
    (e : List AdministrativeInstruction) :
    toVal es1 = some (.brV (ValidHoled.base (n := n) l e)) →
      es1 = l.map (fun v => .basic (.const v)) ++ [.basic (.br n)] ++ e := by
  intro h
  have := of_to_val _ _ h
  simp only [ofVal, vfill] at this
  rw [← this]; simp [vToEList]

@[rocq_alias iriswasm.to_val_br_rec]
theorem to_val_br_rec (es1 : List AdministrativeInstruction) (n : Nat) (bef : List Value) (m : Nat)
    (es : List AdministrativeInstruction) (vh : ValidHoled n) (aft : List AdministrativeInstruction) :
    toVal es1 = some (.brV (.rec_ bef m es vh aft)) →
      ∃ LI, es1 = bef.map (fun v => .basic (.const v)) ++ [.label m es LI] ++ aft ∧
        toVal LI = some (.brV (vhIncrease vh)) := by
  intro h
  have := of_to_val _ _ h
  simp only [ofVal, vfill] at this
  refine ⟨vfill vh [.basic (.br (n + 1))], by rw [← this]; simp [vToEList], ?_⟩
  rw [← vfill_increase vh]
  exact to_of_val (.brV (vhIncrease vh))

@[rocq_alias iriswasm.to_val_ret_base]
theorem to_val_ret_base (es1 : List AdministrativeInstruction) (l : List Value)
    (e : List AdministrativeInstruction) :
    toVal es1 = some (.retV (.base l e)) →
      es1 = l.map (fun v => .basic (.const v)) ++ [.basic .return_] ++ e := by
  intro h
  have := of_to_val _ _ h
  simp only [ofVal, sfill] at this
  rw [← this]; simp [vToEList]

@[rocq_alias iriswasm.to_val_call_host_base]
theorem to_val_call_host_base (es1 : List AdministrativeInstruction) (l : List Value)
    (e : List AdministrativeInstruction) (tf : FunctionType) (h : Hostfuncidx) (vcs : List Value) :
    toVal es1 = some (.callHostV tf h vcs (.base l e)) →
      es1 = l.map (fun v => .basic (.const v)) ++ [.callHost tf h vcs] ++ e := by
  intro h
  have := of_to_val _ _ h
  simp only [ofVal, llfill] at this
  rw [← this]; simp [vToEList]

@[rocq_alias iriswasm.to_val_ret_rec]
theorem to_val_ret_rec (es1 : List AdministrativeInstruction) (bef : List Value) (m : Nat)
    (es : List AdministrativeInstruction) (sh : SimpleValidHoled)
    (aft : List AdministrativeInstruction) :
    toVal es1 = some (.retV (.rec_ bef m es sh aft)) →
      ∃ LI, es1 = bef.map (fun v => .basic (.const v)) ++ [.label m es LI] ++ aft ∧
        toVal LI = some (.retV sh) := by
  intro h
  have := of_to_val _ _ h
  simp only [ofVal, sfill] at this
  exact ⟨sfill sh [.basic .return_], by rw [← this]; simp [vToEList], to_of_val (.retV sh)⟩

@[rocq_alias iriswasm.to_val_call_host_rec_label]
theorem to_val_call_host_rec_label (es1 : List AdministrativeInstruction) (bef : List Value)
    (m : Nat) (es : List AdministrativeInstruction) (sh : Llholed)
    (aft : List AdministrativeInstruction) (tf : FunctionType) (h : Hostfuncidx)
    (vcs : List Value) :
    toVal es1 = some (.callHostV tf h vcs (.label bef m es sh aft)) →
      ∃ LI, es1 = bef.map (fun v => .basic (.const v)) ++ [.label m es LI] ++ aft ∧
        toVal LI = some (.callHostV tf h vcs sh) := by
  intro hv
  have := of_to_val _ _ hv
  simp only [ofVal, llfill] at this
  exact ⟨llfill sh [.callHost tf h vcs], by rw [← this]; simp [vToEList],
    to_of_val (.callHostV tf h vcs sh)⟩

@[rocq_alias iriswasm.to_val_call_host_rec_local]
theorem to_val_call_host_rec_local (es1 : List AdministrativeInstruction) (bef : List Value)
    (n : Nat) (f : Frame) (sh : Llholed) (aft : List AdministrativeInstruction)
    (tf : FunctionType) (h : Hostfuncidx) (vcs : List Value) :
    toVal es1 = some (.callHostV tf h vcs (.local bef n f sh aft)) →
      ∃ LI, es1 = vToEList bef ++ [.local n f LI] ++ aft ∧
        toVal LI = some (.callHostV tf h vcs sh) := by
  intro hv
  have := of_to_val _ _ hv
  simp only [ofVal, llfill] at this
  exact ⟨llfill sh [.callHost tf h vcs], by rw [← this]; simp,
    to_of_val (.callHostV tf h vcs sh)⟩

@[rocq_alias iriswasm.to_val_br_eq]
theorem to_val_br_eq (vs : List Value) (j : Nat) (es0 : List AdministrativeInstruction) :
    toVal (vToEList vs ++ [.basic (.br j)] ++ es0) =
      some (.brV (ValidHoled.base (n := j) vs es0)) := by
  have := to_of_val (.brV (ValidHoled.base (n := j) vs es0))
  simpa [ofVal, vfill] using this

@[rocq_alias iriswasm.to_val_ret_eq]
theorem to_val_ret_eq (vs : List Value) (es0 : List AdministrativeInstruction) :
    toVal (vToEList vs ++ [.basic .return_] ++ es0) = some (.retV (.base vs es0)) := by
  have := to_of_val (.retV (.base vs es0))
  simpa [ofVal, sfill] using this

@[rocq_alias iriswasm.to_val_call_host_eq]
theorem to_val_call_host_eq (vs : List Value) (es0 : List AdministrativeInstruction)
    (tf : FunctionType) (h : Hostfuncidx) (vcs : List Value) :
    toVal (vToEList vs ++ [.callHost tf h vcs] ++ es0) =
      some (.callHostV tf h vcs (.base vs es0)) := by
  have := to_of_val (.callHostV tf h vcs (.base vs es0))
  simpa [ofVal, llfill] using this

@[rocq_alias iriswasm.first_non_value]
theorem first_non_value (es : List AdministrativeInstruction) :
    toVal es = none →
      ∃ vs e es', constList vs = true ∧ (toVal [e] = none ∨ e = .trap) ∧ es = vs ++ e :: es' := by
  induction es with
  | nil => intro h; simp [toVal, mergeValuesList] at h
  | cons a es ih =>
    intro h
    cases ha : toVal [a] with
    | none => exact ⟨[], a, es, rfl, .inl ha, rfl⟩
    | some v =>
      cases v with
      | immV vs =>
        have hvs := to_val_is_immV _ _ ha
        rcases vs with _ | ⟨v0, vs⟩
        · simp at hvs
        simp only [List.map_cons, List.cons.injEq] at hvs
        obtain ⟨rfl, -⟩ := hvs
        cases hes : toVal es with
        | none =>
          obtain ⟨vs, e, es', hc, he, rfl⟩ := ih hes
          exact ⟨.basic (.const v0) :: vs, e, es', by simpa [constList, isConst] using hc, he, rfl⟩
        | some w =>
          rw [toVal_cons_const, toVal_eq_some_iff.1 hes] at h
          cases w with
          | trapV =>
            rw [to_val_trap_is_singleton _ hes]
            exact ⟨[.basic (.const v0)], .trap, [], rfl, .inr rfl, rfl⟩
          | _ => simp [valNotValCombine, valOfValNotVal] at h
      | trapV =>
        have := to_val_trap_is_singleton _ ha
        simp only [List.cons.injEq] at this
        obtain ⟨rfl, -⟩ := this
        exact ⟨[], .trap, es, rfl, .inr rfl, rfl⟩
      | _ =>
        rw [show a :: es = [a] ++ es from rfl, toVal_app_some ha] at h
        simp [valNotValCombine, valOfValNotVal] at h

@[rocq_alias iriswasm.to_val_None_first_singleton]
theorem to_val_None_first_singleton (es : List AdministrativeInstruction) :
    constList es = false → es ≠ [.trap] →
      ∃ vs e es', es = vs ++ [e] ++ es' ∧ constList vs = true ∧
        (toVal [e] = none ∨
          (e = .trap ∧ (vs ≠ [] ∨ es' ≠ [])) ∨
          (∃ n, e = .basic (.br n)) ∨
          e = .basic .return_ ∨
          (∃ tf h vcs, e = .callHost tf h vcs) ∨
          (∃ n es LI, e = .label n es LI ∧
            ((∃ i, ∃ vh : ValidHoled i, toVal LI = some (.brV vh)) ∨
              (∃ sh, toVal LI = some (.retV sh)) ∨
              (∃ tf h vcs sh, toVal LI = some (.callHostV tf h vcs sh)))) ∨
          (∃ n f LI tf h vcs sh, e = .local n f LI ∧ toVal LI = some (.callHostV tf h vcs sh))) := by
  induction es with
  | nil => intro h; simp [constList] at h
  | cons a es ih =>
    intro hc hne
    by_cases hca : isConst a = true
    · obtain ⟨v0, rfl⟩ : ∃ v0, a = .basic (.const v0) := by
        cases a <;> simp [isConst] at hca
        rename_i b; cases b <;> simp at hca; exact ⟨_, rfl⟩
      have hc' : constList es = false := by simpa [constList, isConst] using hc
      by_cases het : es = [.trap]
      · subst het
        exact ⟨[.basic (.const v0)], .trap, [], rfl, rfl, .inr (.inl ⟨rfl, .inl (by simp)⟩)⟩
      obtain ⟨vs, e, es', heq, hvs, hd⟩ := ih hc' het
      refine ⟨.basic (.const v0) :: vs, e, es', by simp [heq], by
        simpa [constList, isConst] using hvs, ?_⟩
      rcases hd with h | ⟨h1, -⟩ | h
      · exact .inl h
      · exact .inr (.inl ⟨h1, .inl (by simp)⟩)
      · exact .inr (.inr h)
    · by_cases hta : a = .trap
      · subst hta
        have : es ≠ [] := by rintro rfl; exact hne rfl
        exact ⟨[], .trap, es, rfl, rfl, .inr (.inl ⟨rfl, .inr this⟩)⟩
      · refine ⟨[], a, es, rfl, rfl, ?_⟩
        rcases singleton_cases a (by simpa using hca) hta with h | h
        · exact .inl h
        · exact .inr (.inr h)

@[rocq_alias iriswasm.const_list_snoc_eq3]
theorem const_list_snoc_eq3 (es'' : List AdministrativeInstruction) :
    ∀ (vs es ves : List AdministrativeInstruction) (e : AdministrativeInstruction)
      (es' : List AdministrativeInstruction),
      constList ves = true → constList vs = true → es ≠ [] → constList es = false →
      es ≠ [.trap] → isConst e = false → vs ++ es ++ es' = ves ++ [e] ++ es'' →
      ∃ vs2 es2, ves = vs ++ vs2 ∧ es = vs2 ++ [e] ++ es2 ∧ es'' = es2 ++ es' ∧
        constList vs2 = true := by
  intro vs es ves e es' hc1 hc2 hne hnv1 hnv2 he heq
  obtain ⟨vs', e', es2, rfl, hc', HH⟩ := to_val_None_first_singleton es hnv1 hnv2
  have he' : isConst e' = false := by
    rcases HH with h | ⟨rfl, -⟩ | ⟨_, rfl⟩ | rfl | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl, -⟩ |
      ⟨_, _, _, _, _, _, _, rfl, -⟩ <;> first | rfl | exact isConst_false_of_toVal_none h
  have heq' : (vs ++ vs') ++ e' :: (es2 ++ es') = ves ++ e :: es'' := by
    simpa [List.append_assoc] using heq
  obtain ⟨h1, rfl, h3⟩ := first_values _ _ _ _ _ _ he' he
    (by simp_all [constList]) hc1 heq'
  exact ⟨vs', es2, h1.symm, rfl, h3.symm, hc'⟩

@[rocq_alias iriswasm.const_list_l_snoc_eq3]
theorem const_list_l_snoc_eq3 (es'' : List AdministrativeInstruction) :
    ∀ (vs es ves : List AdministrativeInstruction) (e : AdministrativeInstruction)
      (es' : List AdministrativeInstruction),
      constList ves = true → e ∉ vs → es ≠ [] → constList es = false →
      es ≠ [.trap] → isConst e = false → vs ++ es ++ es' = ves ++ [e] ++ es'' →
      ∃ vs2 es2, ves = vs ++ vs2 ∧ es = vs2 ++ [e] ++ es2 ∧ es'' = es2 ++ es' ∧
        constList vs2 = true := by
  intro vs es ves e es' hc1 hnin hne hnv1 hnv2 he heq
  obtain ⟨vs', e', es2, rfl, hc', HH⟩ := to_val_None_first_singleton es hnv1 hnv2
  have he' : isConst e' = false := by
    rcases HH with h | ⟨rfl, -⟩ | ⟨_, rfl⟩ | rfl | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl, -⟩ |
      ⟨_, _, _, _, _, _, _, rfl, -⟩ <;> first | rfl | exact isConst_false_of_toVal_none h
  have heq' : (vs ++ vs') ++ e' :: (es2 ++ es') = ves ++ e :: es'' := by
    simpa [List.append_assoc] using heq
  obtain ⟨h1, rfl, h3⟩ := first_values_elem_of _ _ _ _ _ _ he' he
    (by simp only [List.mem_append, not_or]; exact ⟨hnin, const_list_elem_of _ _ hc' he⟩)
    (const_list_elem_of _ _ hc1 he') heq'
  exact ⟨vs', es2, h1.symm, rfl, h3.symm, hc'⟩

@[rocq_alias iriswasm.filled_is_val_imm]
theorem filled_is_val_imm :
    ∀ (i : Nat) (lh : Lholed) (es LI : List AdministrativeInstruction) (vals : List Value),
      toVal LI = some (.immV vals) → lfilled i lh es LI = true →
      ∃ vs es', i = 0 ∧ lh = .base vs es' ∧ constList vs = true ∧ constList es' = true := by
  intro i lh es LI vals htv hlf
  have hc := to_val_const_list _ _ htv
  obtain ⟨rfl, -⟩ := lfilled_const _ _ _ _ hlf hc
  rw [lfilled_Ind_Equivalent] at hlf
  cases hlf with
  | lfilledBase vs _ es' hvs => exact ⟨vs, es', rfl, rfl, hvs, by simp_all [constList]⟩

@[rocq_alias iriswasm.filled_is_val_trap]
theorem filled_is_val_trap :
    ∀ (i : Nat) (lh : Lholed) (es LI : List AdministrativeInstruction),
      toVal LI = some .trapV → lfilled i lh es LI = true → es ≠ [] →
      i = 0 ∧ lh = .base [] [] := by
  intro i lh es LI hval hfill hne
  have ht := to_val_trap_is_singleton _ hval
  rw [lfilled_Ind_Equivalent] at hfill
  cases hfill with
  | lfilledBase vs _ es' =>
    rcases vs with _ | ⟨a, vs⟩ <;> rcases es with _ | ⟨b, es⟩ <;> simp_all
  | lfilledRec _ vs _ _ _ _ _ _ _ _ =>
    rcases vs with _ | ⟨a, vs⟩ <;> simp_all

@[rocq_alias iriswasm.filled_is_val_br_base]
theorem filled_is_val_br_base :
    ∀ (i : Nat) (lh : Lholed) (es LI : List AdministrativeInstruction) (j : Nat) (v1 : List Value)
      (e1 : List AdministrativeInstruction),
      toVal LI = some (.brV (ValidHoled.base (n := j) v1 e1)) → lfilled i lh es LI = true →
      es ≠ [] → i = 0 := by
  intro i lh es LI j v1 e1 hval hfill _
  have hb := to_val_br_base _ _ _ _ hval
  rw [lfilled_Ind_Equivalent] at hfill
  cases hfill with
  | lfilledBase => rfl
  | lfilledRec _ vs n es' lh' es'' _ LI' hc _ =>
    have := first_values _ _ _ _ _ _ rfl rfl hc (v_to_e_is_const_list v1)
      (by simpa [vToEList] using hb)
    simp at this

@[rocq_alias iriswasm.filled_is_val_ret_base]
theorem filled_is_val_ret_base :
    ∀ (i : Nat) (lh : Lholed) (es LI : List AdministrativeInstruction) (v1 : List Value)
      (e1 : List AdministrativeInstruction),
      toVal LI = some (.retV (.base v1 e1)) → lfilled i lh es LI = true → es ≠ [] → i = 0 := by
  intro i lh es LI v1 e1 hval hfill _
  have hb := to_val_ret_base _ _ _ hval
  rw [lfilled_Ind_Equivalent] at hfill
  cases hfill with
  | lfilledBase => rfl
  | lfilledRec _ vs n es' lh' es'' _ LI' hc _ =>
    have := first_values _ _ _ _ _ _ rfl rfl hc (v_to_e_is_const_list v1)
      (by simpa [vToEList] using hb)
    simp at this

@[rocq_alias iriswasm.filled_is_val_call_host_base]
theorem filled_is_val_call_host_base :
    ∀ (i : Nat) (lh : Lholed) (es LI : List AdministrativeInstruction) (v1 : List Value)
      (e1 : List AdministrativeInstruction) (tf : FunctionType) (h : Hostfuncidx)
      (cvs : List Value),
      toVal LI = some (.callHostV tf h cvs (.base v1 e1)) → lfilled i lh es LI = true →
      es ≠ [] → i = 0 := by
  intro i lh es LI v1 e1 tf h cvs hval hfill _
  have hb := to_val_call_host_base _ _ _ _ _ _ hval
  rw [lfilled_Ind_Equivalent] at hfill
  cases hfill with
  | lfilledBase => rfl
  | lfilledRec _ vs n es' lh' es'' _ LI' hc _ =>
    have := first_values _ _ _ _ _ _ rfl rfl hc (v_to_e_is_const_list v1)
      (by simpa [vToEList] using hb)
    simp at this

@[rocq_alias iriswasm.filled_is_val_trap_nil]
theorem filled_is_val_trap_nil :
    ∀ (i : Nat) (lh : Lholed) (LI : List AdministrativeInstruction),
      toVal LI = some .trapV → lfilled i lh [] LI = true →
      ∃ vs es, i = 0 ∧ lh = .base vs es ∧
        ((vs = [] ∧ es = [.trap]) ∨ (es = [] ∧ vs = [.trap])) := by
  intro i lh LI hval hfill
  have ht := to_val_trap_is_singleton _ hval
  rw [lfilled_Ind_Equivalent] at hfill
  cases hfill with
  | lfilledBase vs _ es' =>
    refine ⟨vs, es', rfl, rfl, ?_⟩
    rcases vs with _ | ⟨a, vs⟩ <;> simp_all
  | lfilledRec _ vs _ _ _ _ _ _ _ _ =>
    rcases vs with _ | ⟨a, vs⟩ <;> simp_all

@[rocq_alias iriswasm.to_val_nil]
theorem to_val_nil : ∀ e : List AdministrativeInstruction, toVal e = some (.immV []) → e = [] := by
  intro e h; simpa using to_val_is_immV _ _ h

@[rocq_alias iriswasm.fill_val]
theorem fill_val :
    ∀ (l : List Value) (LI : List AdministrativeInstruction) (v1 v2 : List Value)
      (vs es' es : List AdministrativeInstruction),
      lfilled 0 (.base vs es') es LI = true → toVal LI = some (.immV l) →
      toVal vs = some (.immV v1) → toVal es' = some (.immV v2) →
      ∃ vs, toVal es = some (.immV vs) ∧ l = v1 ++ vs ++ v2 := by
  intro l LI v1 v2 vs es' es hfill hLI hvs hes'
  rw [lfilled_Ind_Equivalent] at hfill
  cases hfill with
  | lfilledBase _ _ _ hc =>
    have hcl := to_val_const_list _ _ hLI
    obtain ⟨vs0, hes⟩ := const_list_to_val es (by simp_all [constList])
    refine ⟨vs0, hes, ?_⟩
    have := to_val_cat_inv _ _ _ _ hvs (to_val_cat_inv _ _ _ _ hes hes')
    rw [← List.append_assoc, hLI] at this
    simp only [Option.some.injEq, Val.immV.injEq] at this
    simp [this]

@[rocq_alias iriswasm.lfilled_eq]
theorem lfilled_eq (i1 i2 : Nat) (lh1 lh2 : Lholed) (e1 e2 : AdministrativeInstruction)
    (LI : List AdministrativeInstruction) :
    lfilled i1 lh1 [e1] LI = true → lfilled i2 lh2 [e2] LI = true →
      (isConst e1 = false ∧ ∀ a b c, e1 ≠ .label a b c) →
      (isConst e2 = false ∧ ∀ a b c, e2 ≠ .label a b c) →
      i1 = i2 ∧ lh1 = lh2 ∧ e1 = e2 := by
  intro h1 h2 ⟨hc1, hl1⟩ ⟨hc2, hl2⟩
  obtain ⟨he, hi, hlh⟩ := lfilled_first_values (vs := []) (vs' := []) h1 h2 rfl rfl hc1 hc2 hl1 hl2
  exact ⟨hi, (hlh rfl).2, he⟩

@[rocq_alias iriswasm.lfilled_trans2]
theorem lfilled_trans2 :
    ∀ (k : Nat) (lh : Lholed) (es1 es1' es2 es2' : List AdministrativeInstruction) (k' : Nat)
      (lh' : Lholed) (es3 es3' : List AdministrativeInstruction),
      lfilled k lh es1 es2 = true → lfilled k lh es1' es2' = true →
      lfilled k' lh' es2 es3 = true → lfilled k' lh' es2' es3' = true →
      ∃ lh'', lfilled (k + k') lh'' es1 es3 = true ∧ lfilled (k + k') lh'' es1' es3' = true := by
  intro k lh es1 es1' es2 es2' k' lh' es3 es3' h1 h1' h2 h2'
  exact ⟨lhCompose lh' lh, lfilled_compose h1 h2, lfilled_compose h1' h2'⟩

@[rocq_alias iriswasm.assoc_list_seq]
theorem assoc_list_seq {A : Type} (a b c : List A) : a ++ (b ++ c) = (a ++ b) ++ c := by
  exact (List.append_assoc _ _ _).symm

@[rocq_alias iriswasm.const_list_singleton]
theorem const_list_singleton (e : AdministrativeInstruction) :
    isConst e = true → constList [e] = true := by
  intro h; simpa [constList] using h

@[rocq_alias iriswasm.const_list_In]
theorem const_list_In (es : List AdministrativeInstruction) (e : AdministrativeInstruction) :
    e ∈ es → constList es = true → isConst e = true := by
  intro hin hc; exact List.all_eq_true.1 hc e hin

@[rocq_alias iriswasm.to_val_immV_inj]
theorem to_val_immV_inj (es es' : List AdministrativeInstruction) (vs : List Value) :
    toVal es = some (.immV vs) → toVal es' = some (.immV vs) → es = es' := by
  intro h1 h2; rw [to_val_is_immV _ _ h1, to_val_is_immV _ _ h2]

@[rocq_alias iriswasm.const_list_snoc_eq]
theorem const_list_snoc_eq (vs : List AdministrativeInstruction) :
    ∀ (ves es es' : List AdministrativeInstruction) (e : AdministrativeInstruction),
      constList ves = true → constList vs = true → es ≠ [] → toVal es = none →
      vs ++ es ++ es' = ves ++ [e] →
      es' = [] ∧ ∃ vs2, ves = vs ++ vs2 ∧ es = vs2 ++ [e] ∧ constList vs2 = true := by
  induction vs with
  | nil =>
    intro ves es es' e hc1 _ hne hnv heq
    simp only [List.nil_append] at heq
    rcases destruct_list_rev es' with rfl | ⟨a, l', rfl⟩
    · simp only [List.append_nil] at heq
      exact ⟨rfl, ves, rfl, heq, hc1⟩
    · rw [← List.append_assoc] at heq
      obtain ⟨h1, -⟩ := List.append_inj' heq rfl
      have : constList es = true := by
        rw [← h1] at hc1; simp only [constList, List.all_append, Bool.and_eq_true] at hc1
        exact hc1.1
      obtain ⟨_, h⟩ := const_list_to_val _ this
      simp_all
  | cons a vs ih =>
    intro ves es es' e hc1 hc2 hne hnv heq
    rcases ves with _ | ⟨b, ves⟩
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at heq
      simp_all
    · simp only [List.cons_append, List.cons.injEq] at heq
      obtain ⟨rfl, heq⟩ := heq
      obtain ⟨h1, vs2, h2, h3, h4⟩ := ih ves es es' e (by simp_all [constList])
        (by simp_all [constList]) hne hnv heq
      exact ⟨h1, vs2, by simp [h2], h3, h4⟩

@[rocq_alias iriswasm.length_to_val_immV]
theorem length_to_val_immV (v1 : List AdministrativeInstruction) :
    ∀ vs1 : List Value, toVal v1 = some (.immV vs1) → v1.length = vs1.length := by
  intro vs1 h; rw [to_val_is_immV _ _ h]; simp

@[rocq_alias iriswasm.lfilled_one_depth_trap]
theorem lfilled_one_depth_trap (k : Nat) (lh : Lholed) (es vs : List AdministrativeInstruction)
    (n : Nat) (es' es'' : List AdministrativeInstruction) :
    constList vs = true → lfilled k lh es (vs ++ [.label n es' [.trap]] ++ es'') = true →
      k = 0 ∨ k = 1 := by
  intro hc hfill
  rcases k with _ | _ | k
  · exact .inl rfl
  · exact .inr rfl
  exfalso
  rw [lfilled_Ind_Equivalent] at hfill
  generalize hLI : vs ++ [AdministrativeInstruction.label n es' [.trap]] ++ es'' = LI0 at hfill
  cases hfill with
  | lfilledRec _ vs0 n0 es0 lh0 es''0 _ LI hc0 hf =>
    obtain ⟨-, h2, -⟩ := first_values _ _ _ _ _ _ rfl rfl hc0 hc (by simpa using hLI.symm)
    simp only [AdministrativeInstruction.label.injEq] at h2
    obtain ⟨-, -, rfl⟩ := h2
    generalize hT : [AdministrativeInstruction.trap] = T at hf
    cases hf with
    | lfilledRec _ vs1 _ _ _ _ _ _ _ _ =>
      rcases vs1 with _ | ⟨_, _ | _⟩ <;> simp_all

@[rocq_alias iriswasm.lfilled_trap_not_br]
theorem lfilled_trap_not_br (i : Nat) (lh : Lholed) (LI : List AdministrativeInstruction) :
    lfilled i lh [.trap] LI = true →
      ∀ (i j : Nat) (lh : Lholed) (vs0 : List AdministrativeInstruction), constList vs0 = true →
        lfilled i lh (vs0 ++ [.basic (.br j)]) LI = true → False := by
  intro hfill i' j lh'' vs0 hc hfill'
  have := lfilled_first_values (vs := []) hfill hfill' rfl hc rfl rfl (by simp) (by simp)
  simp at this

@[rocq_alias iriswasm.lfilled_singleton]
theorem lfilled_singleton (a : AdministrativeInstruction) (k : Nat) (lh : Lholed)
    (es les : List AdministrativeInstruction) (i : Nat) (lh' : Lholed) :
    es ≠ [] → constList es = false → es ≠ [.trap] → isConst a = false →
      (∀ n e1 e2, a ≠ .label n e1 e2) → lfilled k lh es les = true →
      lfilled i lh' [a] les = true → ∃ j lh, lfilled j lh [a] es = true ∧ j + k = i := by
  intro hne hnc hnt ha hal h1 h2
  rw [lfilled_Ind_Equivalent] at h1 h2
  suffices H : ∀ i k lh les lh', LfilledInd k lh es les → LfilledInd i lh' [a] les →
      ∃ j lh, LfilledInd j lh [a] es ∧ j + k = i by
    obtain ⟨j, lh0, h, hj⟩ := H i k lh les lh' h1 h2
    exact ⟨j, lh0, (lfilled_Ind_Equivalent _ _ _ _).2 h, hj⟩
  intro i
  induction i with
  | zero =>
    intro k lh les lh' h1 h2
    generalize hL : les = L at h1
    cases h2 with
    | lfilledBase vs _ es' hvs =>
      cases h1 with
      | lfilledBase vs' _ es'' hvs' =>
        obtain ⟨vs2, es2, -, rfl, -, hc⟩ :=
          const_list_snoc_eq3 es' vs' es vs a es'' hvs hvs' hne hnc hnt ha hL.symm
        exact ⟨0, .base vs2 es2, .lfilledBase _ _ _ hc, rfl⟩
      | lfilledRec _ vs' n es0 _ es'' _ LI hvs' _ =>
        obtain ⟨-, h, -⟩ := first_values _ _ _ _ _ _ ha rfl hvs hvs' (by simpa using hL)
        exact absurd h (hal _ _ _)
  | succ i ih =>
    intro k lh les lh' h1 h2
    generalize hL : les = L at h1
    cases h2 with
    | lfilledRec _ vs n es0 lh'0 es' _ LI hvs hf =>
      cases h1 with
      | lfilledBase vs' _ es'' hvs' =>
        obtain ⟨vs2, es2, -, rfl, -, hc⟩ :=
          const_list_snoc_eq3 es' vs' es vs (.label n es0 LI) es'' hvs hvs' hne hnc hnt rfl
            hL.symm
        exact ⟨i + 1, .rec_ vs2 n es0 lh'0 es2, .lfilledRec _ _ _ _ _ _ _ _ hc hf, rfl⟩
      | lfilledRec k0 vs' n' es0' lh0 es'' _ LI' hvs' hf' =>
        obtain ⟨-, h, -⟩ := first_values _ _ _ _ _ _ rfl rfl hvs hvs' (by simpa using hL)
        simp only [AdministrativeInstruction.label.injEq] at h
        obtain ⟨-, -, rfl⟩ := h
        obtain ⟨j, lh0', h, hj⟩ := ih k0 lh0 LI lh'0 hf' hf
        exact ⟨j, lh0', h, by omega⟩

@[rocq_alias iriswasm.filled_is_val_br_base_app_cases]
theorem filled_is_val_br_base_app_cases :
    ∀ (i : Nat) (lh : Lholed) (es1 es2 LI : List AdministrativeInstruction) (j : Nat)
      (v1 : List Value) (e1 : List AdministrativeInstruction),
      toVal LI = some (.brV (ValidHoled.base (n := j) v1 e1)) → es1 ++ es2 ≠ [] →
      lfilled i lh (es1 ++ es2) LI = true →
      i = 0 ∧ ∃ vs es, lh = .base vs es ∧
        ((∃ es11 es12, es1 = es11 ++ .basic (.br j) :: es12 ∧ constList es11 = true) ∨
          (∃ es21 es22, es2 = es21 ++ .basic (.br j) :: es22 ∧ constList es21 = true ∧
            constList es1 = true) ∨
          (∃ es1' es2', es = es1' ++ .basic (.br j) :: es2' ∧ constList es1 = true ∧
            constList es2 = true ∧ constList es1' = true)) := by
  intro i lh es1 es2 LI j v1 e1 hLI hnil hfill
  obtain rfl := filled_is_val_br_base _ _ _ _ _ _ _ hLI hfill hnil
  have hb := to_val_br_base _ _ _ _ hLI
  rw [lfilled_Ind_Equivalent] at hfill
  cases hfill with
  | lfilledBase vs _ es' hvs =>
    exact ⟨rfl, vs, es', rfl, app_cases_aux rfl (v_to_e_is_const_list v1) hvs hb⟩

@[rocq_alias iriswasm.filled_is_val_ret_base_app_cases]
theorem filled_is_val_ret_base_app_cases :
    ∀ (i : Nat) (lh : Lholed) (es1 es2 LI : List AdministrativeInstruction) (v1 : List Value)
      (e1 : List AdministrativeInstruction),
      toVal LI = some (.retV (.base v1 e1)) → es1 ++ es2 ≠ [] →
      lfilled i lh (es1 ++ es2) LI = true →
      i = 0 ∧ ∃ vs es, lh = .base vs es ∧
        ((∃ es11 es12, es1 = es11 ++ .basic .return_ :: es12 ∧ constList es11 = true) ∨
          (∃ es21 es22, es2 = es21 ++ .basic .return_ :: es22 ∧ constList es21 = true ∧
            constList es1 = true) ∨
          (∃ es1' es2', es = es1' ++ .basic .return_ :: es2' ∧ constList es1 = true ∧
            constList es2 = true ∧ constList es1' = true)) := by
  intro i lh es1 es2 LI v1 e1 hLI hnil hfill
  obtain rfl := filled_is_val_ret_base _ _ _ _ _ _ hLI hfill hnil
  have hb := to_val_ret_base _ _ _ hLI
  rw [lfilled_Ind_Equivalent] at hfill
  cases hfill with
  | lfilledBase vs _ es' hvs =>
    exact ⟨rfl, vs, es', rfl, app_cases_aux rfl (v_to_e_is_const_list v1) hvs hb⟩

@[rocq_alias iriswasm.filled_is_val_call_host_base_app_cases]
theorem filled_is_val_call_host_base_app_cases :
    ∀ (i : Nat) (lh : Lholed) (es1 es2 LI : List AdministrativeInstruction) (v1 : List Value)
      (e1 : List AdministrativeInstruction) (tf : FunctionType) (h : Hostfuncidx)
      (cvs : List Value),
      toVal LI = some (.callHostV tf h cvs (.base v1 e1)) → es1 ++ es2 ≠ [] →
      lfilled i lh (es1 ++ es2) LI = true →
      i = 0 ∧ ∃ vs es, lh = .base vs es ∧
        ((∃ es11 es12, es1 = es11 ++ .callHost tf h cvs :: es12 ∧ constList es11 = true) ∨
          (∃ es21 es22, es2 = es21 ++ .callHost tf h cvs :: es22 ∧ constList es21 = true ∧
            constList es1 = true) ∨
          (∃ es1' es2', es = es1' ++ .callHost tf h cvs :: es2' ∧ constList es1 = true ∧
            constList es2 = true ∧ constList es1' = true)) := by
  intro i lh es1 es2 LI v1 e1 tf h cvs hLI hnil hfill
  obtain rfl := filled_is_val_call_host_base _ _ _ _ _ _ _ _ _ hLI hfill hnil
  have hb := to_val_call_host_base _ _ _ _ _ _ hLI
  rw [lfilled_Ind_Equivalent] at hfill
  cases hfill with
  | lfilledBase vs _ es' hvs =>
    exact ⟨rfl, vs, es', rfl, app_cases_aux rfl (v_to_e_is_const_list v1) hvs hb⟩

@[rocq_alias iriswasm.of_val_br_app_r]
theorem of_val_br_app_r (n : Nat) (vh : ValidHoled n) (es2 : List AdministrativeInstruction) :
    ofVal (.brV vh) ++ es2 = ofVal (.brV (vhAppend vh es2)) := by
  cases vh <;> simp [ofVal, vfill, vhAppend]

@[rocq_alias iriswasm.of_val_ret_app_r]
theorem of_val_ret_app_r (sh : SimpleValidHoled) (es2 : List AdministrativeInstruction) :
    ofVal (.retV sh) ++ es2 = ofVal (.retV (shAppend sh es2)) := by
  cases sh <;> simp [ofVal, sfill, shAppend]

@[rocq_alias iriswasm.lfilled_to_val_app]
theorem lfilled_to_val_app (i : Nat) (lh : Lholed) (es1 es2 LI : List AdministrativeInstruction)
    (vs : Val) :
    lfilled i lh (es1 ++ es2) LI = true → toVal LI = some vs →
      ∃ vs', toVal es1 = some vs' ∧ lfilled i lh (ofVal vs' ++ es2) LI = true := by
  intro hfill hLI
  cases h : toVal es1 with
  | none =>
    have := lfilled_to_val i lh (es1 ++ es2) LI (by simp [hLI]) hfill
    rw [to_val_None_append es1 es2 h] at this; simp at this
  | some v => exact ⟨v, rfl, by rw [of_to_val _ _ h]; exact hfill⟩

@[rocq_alias iriswasm.to_val_brV_None]
theorem to_val_brV_None (vs : List AdministrativeInstruction) (n i : Nat) (lh : Lholed)
    (es LI : List AdministrativeInstruction) :
    constList vs = true → vs.length = n → lfilled i lh (vs ++ [.basic (.br i)]) LI = true →
      toVal [.label n es LI] = none := by
  intro hc hlen hfill
  exact val_head_stuck_reduce (s1 := default) (f1 := default) (s2 := default) (f2 := default)
    (.simple (.br i lh hc hlen hfill))

@[rocq_alias iriswasm.to_val_immV_label_None]
theorem to_val_immV_label_None (es : List AdministrativeInstruction) (v : List Value) (m : Nat)
    (ctx : List AdministrativeInstruction) :
    toVal es = some (.immV v) → toVal [.label m ctx es] = none := by
  intro h; rw [toVal_singleton, toValInstr_label, h]; rfl

@[rocq_alias iriswasm.to_val_trapV_label_None]
theorem to_val_trapV_label_None (es : List AdministrativeInstruction) (m : Nat)
    (ctx : List AdministrativeInstruction) :
    toVal es = some .trapV → toVal [.label m ctx es] = none := by
  intro h; rw [toVal_singleton, toValInstr_label, h]; rfl

@[rocq_alias iriswasm.to_val_cons_immV]
theorem to_val_cons_immV (v : Value) (l : List Value) :
    toVal (.basic (.const v) :: ofVal (.immV l)) = some (.immV (v :: l)) := by
  exact to_val_cat_inv [.basic (.const v)] (ofVal (.immV l)) [v] l (to_of_val (.immV [v]))
    (to_of_val _)

@[rocq_alias iriswasm.to_val_cons_brV]
theorem to_val_cons_brV (i : Nat) (lh : ValidHoled i) (v : Value)
    (es : List AdministrativeInstruction) :
    toVal es = some (.brV lh) → toVal (.basic (.const v) :: es) = some (.brV (vhPushConst lh [v])) := by
  intro h; rw [toVal_cons_const, toVal_eq_some_iff.1 h]; rfl

@[rocq_alias iriswasm.to_val_cons_retV]
theorem to_val_cons_retV (s : SimpleValidHoled) (v : Value) (es : List AdministrativeInstruction) :
    toVal es = some (.retV s) → toVal (.basic (.const v) :: es) = some (.retV (shPushConst s [v])) := by
  intro h; rw [toVal_cons_const, toVal_eq_some_iff.1 h]; rfl

@[rocq_alias iriswasm.to_val_cons_callHostV]
theorem to_val_cons_callHostV (tf : FunctionType) (h : Hostfuncidx) (cvs : List Value)
    (s : Llholed) (v : Value) (es : List AdministrativeInstruction) :
    toVal es = some (.callHostV tf h cvs s) →
      toVal (.basic (.const v) :: es) = some (.callHostV tf h cvs (llhPushConst s [v])) := by
  intro h; rw [toVal_cons_const, toVal_eq_some_iff.1 h]; rfl

@[rocq_alias iriswasm.to_val_cons_None]
theorem to_val_cons_None (es : List AdministrativeInstruction) (v : Value) :
    toVal es = none → toVal (.basic (.const v) :: es) = none := by
  intro h; exact to_val_None_prepend_const [.basic (.const v)] es rfl h

@[rocq_alias iriswasm.to_val_AI_trap_Some_nil]
theorem to_val_AI_trap_Some_nil (es : List AdministrativeInstruction) (vs : Val) :
    toVal ([.trap] ++ es) = some vs → es = [] := by
  intro h
  cases es with
  | nil => rfl
  | cons a es =>
    rw [show [AdministrativeInstruction.trap] ++ a :: es = [] ++ [.trap] ++ a :: es from rfl,
      to_val_not_trap_interweave [] (a :: es) rfl (.inr (by simp))] at h
    simp at h

@[rocq_alias iriswasm.to_val_None_label]
theorem to_val_None_label (n : Nat) (es' LI : List AdministrativeInstruction) :
    toVal LI = none → toVal [.label n es' LI] = none := by
  intro h; rw [toVal_singleton, toValInstr_label, h]; rfl

@[rocq_alias iriswasm.to_val_None_lfilled]
theorem to_val_None_lfilled (LI : List AdministrativeInstruction) (k : Nat) (lh : Lholed)
    (es : List AdministrativeInstruction) :
    toVal es = none → lfilled k lh es LI = true → toVal LI = none := by
  intro hnone hfill
  rw [lfilled_Ind_Equivalent] at hfill
  induction hfill with
  | lfilledBase vs _ es' hc =>
    rw [List.append_assoc]; exact to_val_cat_None2 _ _ hc (to_val_cat_None1 _ _ hnone)
  | lfilledRec _ vs n es' lh' es'' _ LI hc _ ih =>
    rw [List.append_assoc]
    exact to_val_cat_None2 _ _ hc (to_val_cat_None1 _ _ (to_val_None_label _ _ _ (ih hnone)))

@[rocq_alias iriswasm.to_val_app_retV]
theorem to_val_app_retV (v : List Value) :
    ∀ (s : SimpleValidHoled) (es : Expr), toVal es = some (.retV s) →
      toVal (vToEList v ++ es) = some (.retV (shPushConst s v)) := by
  induction v with
  | nil => intro s es h; simpa [vToEList, sh_push_const_nil] using h
  | cons a v ih =>
    intro s es h
    have := to_val_cons_retV _ a _ (ih s es h)
    rw [show a :: v = [a] ++ v from rfl, sh_push_const_app]
    simpa [vToEList] using this

@[rocq_alias iriswasm.to_val_local_inv]
theorem to_val_local_inv (n : Nat) (f : Frame) (LI : List AdministrativeInstruction) (v : Val) :
    toVal [.local n f LI] = some v → ∃ tf h w vh, v = .callHostV tf h w (.local [] n f vh []) := by
  intro h
  rw [toVal_singleton, toValInstr_local] at h
  rcases hv : toVal LI with _ | (_ | _ | _ | _ | ⟨tf, h', w, vh⟩) <;>
    simp only [hv, valOfValNotVal, reduceCtorEq, Option.some.injEq] at h
  exact ⟨tf, h', w, vh, h.symm⟩

@[rocq_alias iriswasm.to_val_local_add_frame]
theorem to_val_local_add_frame (LI' : List AdministrativeInstruction) (tf : FunctionType)
    (h : Hostfuncidx) (w : List Value) (vh : Llholed) (n : Nat) (f : Frame) :
    toVal LI' = some (.callHostV tf h w vh) →
      toVal [.local n f LI'] = some (.callHostV tf h w (.local [] n f vh [])) := by
  intro hv; rw [toVal_singleton, toValInstr_local, hv]; rfl

@[rocq_alias iriswasm.sfill_call_host_compose]
theorem sfill_call_host_compose (wh vh : SimpleValidHoled) (tf : FunctionType) (h : Hostfuncidx)
    (w : List Value) (es1 : List AdministrativeInstruction) :
    toVal es1 = none → sfill wh [.callHost tf h w] = sfill vh es1 →
      ∃ vh', es1 = sfill vh' [.callHost tf h w] := by
  intro hnone hs
  have hne := toVal_ne_nil hnone
  have hnc := toVal_constList_false hnone
  have hnt := toVal_ne_trap hnone
  induction vh generalizing wh with
  | base bef aft =>
    cases wh with
    | base b a =>
      obtain ⟨vs2, es2, -, rfl, -, hc⟩ := const_list_snoc_eq3 a (vToEList bef) es1 (vToEList b) _ aft
        (v_to_e_is_const_list _) (v_to_e_is_const_list _) hne hnc hnt rfl
        (by simpa [sfill] using hs.symm)
      obtain ⟨x, rfl⟩ := const_es_exists hc
      exact ⟨.base x es2, by simp [sfill]⟩
    | rec_ b n es wh' a =>
      obtain ⟨vs2, es2, -, rfl, -, hc⟩ := const_list_snoc_eq3 a (vToEList bef) es1 (vToEList b) _ aft
        (v_to_e_is_const_list _) (v_to_e_is_const_list _) hne hnc hnt rfl
        (by simpa [sfill] using hs.symm)
      obtain ⟨x, rfl⟩ := const_es_exists hc
      exact ⟨.rec_ x n es wh' es2, by simp [sfill]⟩
  | rec_ bef n es0 vh0 aft ih =>
    cases wh with
    | base b a =>
      obtain ⟨-, h, -⟩ := first_values _ _ _ _ _ _ rfl rfl (v_to_e_is_const_list b)
        (v_to_e_is_const_list bef) (by simpa [sfill] using hs)
      simp at h
    | rec_ b m es wh' a =>
      obtain ⟨-, h, -⟩ := first_values _ _ _ _ _ _ rfl rfl (v_to_e_is_const_list b)
        (v_to_e_is_const_list bef) (by simpa [sfill] using hs)
      simp only [AdministrativeInstruction.label.injEq] at h
      exact ih wh' h.2.2

@[rocq_alias iriswasm.llfill_call_host_compose]
theorem llfill_call_host_compose (wh vh : Llholed) (tf : FunctionType) (h : Hostfuncidx)
    (w : List Value) (es1 : List AdministrativeInstruction) :
    toVal es1 = none → llfill wh [.callHost tf h w] = llfill vh es1 →
      ∃ vh', es1 = llfill vh' [.callHost tf h w] := by
  intro hnone hs
  have hne := toVal_ne_nil hnone
  have hnc := toVal_constList_false hnone
  have hnt := toVal_ne_trap hnone
  induction vh generalizing wh with
  | base bef aft =>
    cases wh with
    | base b a =>
      obtain ⟨vs2, es2, -, rfl, -, hc⟩ := const_list_snoc_eq3 a (vToEList bef) es1 (vToEList b) _ aft
        (v_to_e_is_const_list _) (v_to_e_is_const_list _) hne hnc hnt rfl
        (by simpa [llfill] using hs.symm)
      obtain ⟨x, rfl⟩ := const_es_exists hc
      exact ⟨.base x es2, by simp [llfill]⟩
    | label b n es wh' a =>
      obtain ⟨vs2, es2, -, rfl, -, hc⟩ := const_list_snoc_eq3 a (vToEList bef) es1 (vToEList b) _ aft
        (v_to_e_is_const_list _) (v_to_e_is_const_list _) hne hnc hnt rfl
        (by simpa [llfill] using hs.symm)
      obtain ⟨x, rfl⟩ := const_es_exists hc
      exact ⟨.label x n es wh' es2, by simp [llfill]⟩
    | «local» b n f wh' a =>
      obtain ⟨vs2, es2, -, rfl, -, hc⟩ := const_list_snoc_eq3 a (vToEList bef) es1 (vToEList b) _ aft
        (v_to_e_is_const_list _) (v_to_e_is_const_list _) hne hnc hnt rfl
        (by simpa [llfill] using hs.symm)
      obtain ⟨x, rfl⟩ := const_es_exists hc
      exact ⟨.local x n f wh' es2, by simp [llfill]⟩
  | label bef n es0 vh0 aft ih =>
    cases wh with
    | base b a =>
      obtain ⟨-, h, -⟩ := first_values _ _ _ _ _ _ rfl rfl (v_to_e_is_const_list b)
        (v_to_e_is_const_list bef) (by simpa [llfill] using hs)
      simp at h
    | label b m es wh' a =>
      obtain ⟨-, h, -⟩ := first_values _ _ _ _ _ _ rfl rfl (v_to_e_is_const_list b)
        (v_to_e_is_const_list bef) (by simpa [llfill] using hs)
      simp only [AdministrativeInstruction.label.injEq] at h
      exact ih wh' h.2.2
    | «local» b m f wh' a =>
      obtain ⟨-, h, -⟩ := first_values _ _ _ _ _ _ rfl rfl (v_to_e_is_const_list b)
        (v_to_e_is_const_list bef) (by simpa [llfill] using hs)
      simp at h
  | «local» bef n f0 vh0 aft ih =>
    cases wh with
    | base b a =>
      obtain ⟨-, h, -⟩ := first_values _ _ _ _ _ _ rfl rfl (v_to_e_is_const_list b)
        (v_to_e_is_const_list bef) (by simpa [llfill] using hs)
      simp at h
    | label b m es wh' a =>
      obtain ⟨-, h, -⟩ := first_values _ _ _ _ _ _ rfl rfl (v_to_e_is_const_list b)
        (v_to_e_is_const_list bef) (by simpa [llfill] using hs)
      simp at h
    | «local» b m f wh' a =>
      obtain ⟨-, h, -⟩ := first_values _ _ _ _ _ _ rfl rfl (v_to_e_is_const_list b)
        (v_to_e_is_const_list bef) (by simpa [llfill] using hs)
      simp only [AdministrativeInstruction.local.injEq] at h
      exact ih wh' h.2.2

@[rocq_alias iriswasm.to_val_local_none]
theorem to_val_local_none (n : Nat) (f : Frame) (es1 : List AdministrativeInstruction)
    (vh : Llholed) :
    toVal [.local n f (llfill vh es1)] = none → toVal [.local n f es1] = none := by
  intro hv
  cases hs : toVal [.local n f es1] with
  | none => rfl
  | some v =>
    exfalso
    obtain ⟨tf, h, w, wh, hw⟩ := toVal_local_some hs
    have he := of_to_val _ _ hw
    simp only [ofVal] at he
    obtain ⟨vh', hvh'⟩ := llfill_nested vh wh [.callHost tf h w]
    rw [← he, hvh'] at hv
    have := to_val_local_add_frame _ tf h w vh' n f (to_of_val (.callHostV tf h w vh'))
    simp only [ofVal] at this
    rw [this] at hv; simp at hv

@[rocq_alias iriswasm.to_val_local_none_inv]
theorem to_val_local_none_inv (n : Nat) (f : Frame) (es1 : List AdministrativeInstruction)
    (vh : Llholed) :
    toVal es1 = none → toVal [.local n f es1] = none →
      toVal [.local n f (llfill vh es1)] = none := by
  intro hnone _
  cases hs : toVal [.local n f (llfill vh es1)] with
  | none => rfl
  | some v =>
    exfalso
    obtain ⟨tf, h, w, wh, hw⟩ := toVal_local_some hs
    have he := of_to_val _ _ hw
    simp only [ofVal] at he
    obtain ⟨vh', rfl⟩ := llfill_call_host_compose wh vh tf h w es1 hnone he
    rw [show llfill vh' [.callHost tf h w] = ofVal (.callHostV tf h w vh') from rfl,
      to_of_val] at hnone
    simp at hnone

@[rocq_alias iriswasm.to_val_local_no_local_none]
theorem to_val_local_no_local_none (n : Nat) (f : Frame) (e : List AdministrativeInstruction) :
    toVal [.local n f e] = none →
      match toVal e with
      | some (.callHostV _ _ _ _) => False
      | _ => True := by
  intro hv
  rcases he : toVal e with _ | (_ | _ | _ | _ | ⟨tf, h, w, vh⟩) <;> simp only
  rw [to_val_local_add_frame _ tf h w vh n f he] at hv; simp at hv

@[rocq_alias iriswasm.ll_of_sh]
def llOfSh : SimpleValidHoled → Llholed
  | .base bef aft => .base bef aft
  | .rec_ bef n es sh aft => .label bef n es (llOfSh sh) aft

@[rocq_alias iriswasm.sfill_to_llfill]
theorem sfill_to_llfill (sh : SimpleValidHoled) (e : List AdministrativeInstruction) :
    sfill sh e = llfill (llOfSh sh) e := by
  induction sh with
  | base => rfl
  | rec_ bef n es sh aft ih => simp [sfill, llfill, llOfSh, ih]

@[rocq_alias iriswasm.to_val_local_ret_none]
theorem to_val_local_ret_none (n : Nat) (f : Frame) (e : List AdministrativeInstruction)
    (vh : SimpleValidHoled) :
    toVal e = some (.retV vh) → toVal [.local n f e] = none := by
  intro h; rw [toVal_singleton, toValInstr_local, h]; rfl

@[rocq_alias iriswasm.to_val_local_none_none]
theorem to_val_local_none_none (n : Nat) (f : Frame) (e : List AdministrativeInstruction) :
    toVal e = none → toVal [.local n f e] = none := by
  intro h; rw [toVal_singleton, toValInstr_local, h]; rfl

end IrisWasm
