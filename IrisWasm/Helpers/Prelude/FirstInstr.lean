/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Helpers.Prelude.IrisWasmLangProperties

/-! Port of `theories/iris/helpers/prelude/first_instr.v`. -/

namespace IrisWasm

open Wasm

@[rocq_alias iriswasm.first_instr.find_first_some]
def findFirstSome {A : Type} : List (Option A) → Option A
  | [] => none
  | some e :: _ => some e
  | none :: q => findFirstSome q

@[rocq_alias iriswasm.first_instr.first_instr_instr]
def firstInstrInstr (e : AdministrativeInstruction) : Option (AdministrativeInstruction × Nat) :=
  match e with
  | .basic (.const _) => none
  | .label _ _ LI =>
    match findFirstSome (LI.map firstInstrInstr) with
    | some (e', i) => some (e', i + 1)
    | none => some (e, 0)
  | .local _ _ LI =>
    match findFirstSome (LI.map firstInstrInstr) with
    | some (e', i) => some (e', i + 1)
    | none => some (e, 0)
  | _ => some (e, 0)

@[rocq_alias iriswasm.first_instr.first_instr]
def firstInstr (es : List AdministrativeInstruction) : Option (AdministrativeInstruction × Nat) :=
  findFirstSome (es.map firstInstrInstr)

@[simp] theorem firstInstr_nil : firstInstr [] = none := rfl

theorem firstInstr_cons (e : AdministrativeInstruction) (es : List AdministrativeInstruction) :
    firstInstr (e :: es) =
      match firstInstrInstr e with
      | some p => some p
      | none => firstInstr es := by
  simp only [firstInstr, List.map_cons]
  cases firstInstrInstr e <;> rfl

theorem firstInstrInstr_label (n : Nat) (es LI : List AdministrativeInstruction) :
    firstInstrInstr (.label n es LI) =
      match firstInstr LI with
      | some (e', i) => some (e', i + 1)
      | none => some (.label n es LI, 0) := by
  simp only [firstInstr, firstInstrInstr]

theorem firstInstrInstr_local (n : Nat) (f : Frame) (LI : List AdministrativeInstruction) :
    firstInstrInstr (.local n f LI) =
      match firstInstr LI with
      | some (e', i) => some (e', i + 1)
      | none => some (.local n f LI, 0) := by
  simp only [firstInstr, firstInstrInstr]

theorem firstInstrInstr_eq_none {e : AdministrativeInstruction} :
    firstInstrInstr e = none ↔ isConst e = true := by
  rcases e with ⟨b⟩ | _ | _ | ⟨n, es, LI⟩ | ⟨n, f, LI⟩ | _
  · cases b <;> simp [firstInstrInstr, isConst]
  · simp [firstInstrInstr, isConst]
  · simp [firstInstrInstr, isConst]
  · simp only [firstInstrInstr, isConst]
    split <;> simp
  · simp only [firstInstrInstr, isConst]
    split <;> simp
  · simp [firstInstrInstr, isConst]

@[rocq_alias iriswasm.first_instr.first_instr_const]
theorem first_instr_const (vs es : List AdministrativeInstruction) :
    constList vs = true → firstInstr (vs ++ es) = firstInstr es := by
  intro hvs
  induction vs with
  | nil => rfl
  | cons a vs ih =>
    simp only [constList, List.all_cons, Bool.and_eq_true] at hvs
    rw [List.cons_append, firstInstr_cons, firstInstrInstr_eq_none.2 hvs.1]
    exact ih hvs.2

@[rocq_alias iriswasm.first_instr.first_instr_app]
theorem first_instr_app (e : List AdministrativeInstruction) :
    ∀ a es', firstInstr e = some a → firstInstr (e ++ es') = some a := by
  induction e with
  | nil => simp
  | cons x e ih =>
    intro a es' h
    rw [firstInstr_cons] at h
    rw [List.cons_append, firstInstr_cons]
    cases hx : firstInstrInstr x <;> simp only [hx] at h ⊢
    · exact ih a es' h
    · exact h

@[rocq_alias iriswasm.first_instr_app_skip]
theorem first_instr_app_skip (e : List AdministrativeInstruction) :
    ∀ es', firstInstr e = none → firstInstr (e ++ es') = firstInstr es' := by
  induction e with
  | nil => simp
  | cons x e ih =>
    intro es' h
    rw [firstInstr_cons] at h
    rw [List.cons_append, firstInstr_cons]
    split at h <;> simp_all

@[rocq_alias iriswasm.first_instr_None_const]
theorem first_instr_None_const (es : List AdministrativeInstruction) :
    firstInstr es = none → constList es = true := by
  induction es with
  | nil => simp [constList]
  | cons a es ih =>
    intro h
    rw [firstInstr_cons] at h
    split at h
    · simp at h
    · simp only [constList, List.all_cons, Bool.and_eq_true]
      exact ⟨firstInstrInstr_eq_none.1 ‹_›, ih h⟩

@[rocq_alias iriswasm.find_first_const_label]
theorem find_first_const_label (es es1 : List AdministrativeInstruction) (n : Nat) :
    constList es = true →
    firstInstr [.label n es1 es] = some (.label n es1 es, 0) := by
  intro h
  have := first_instr_const es [] h
  simp only [List.append_nil, firstInstr_nil] at this
  rw [firstInstr_cons, firstInstrInstr_label, this]

@[rocq_alias iriswasm.first_instr_local]
theorem first_instr_local (es : List AdministrativeInstruction) (e : AdministrativeInstruction)
    (i n : Nat) (f : Frame) :
    firstInstr es = some (e, i) →
    firstInstr [.local n f es] = some (e, i + 1) := by
  intro h
  rw [firstInstr_cons, firstInstrInstr_local, h]

@[rocq_alias iriswasm.find_first_const]
theorem find_first_const (es : List AdministrativeInstruction) (n : Nat) (f : Frame) :
    constList es = true →
    firstInstr [.local n f es] = some (.local n f es, 0) := by
  intro h
  have := first_instr_const es [] h
  simp only [List.append_nil, firstInstr_nil] at this
  rw [firstInstr_cons, firstInstrInstr_local, this]

@[rocq_alias iriswasm.first_instr.starts_with_lfilled]
theorem starts_with_lfilled (e : AdministrativeInstruction) (i : Nat)
    (es : List AdministrativeInstruction) (k : Nat) (lh : Lholed)
    (les : List AdministrativeInstruction) :
    firstInstr es = some (e, i) →
    lfilled k lh es les = true →
    firstInstr les = some (e, i + k) := by
  intro hf hlf
  rw [lfilled_Ind_Equivalent] at hlf
  induction hlf generalizing i with
  | lfilledBase vs es es' hc =>
    rw [List.append_assoc, first_instr_const _ _ hc]
    exact first_instr_app _ _ _ hf
  | lfilledRec k vs n es' lh' es'' es LI hc _ ih =>
    rw [List.append_assoc, first_instr_const _ _ hc, List.singleton_append, firstInstr_cons,
      firstInstrInstr_label, ih i hf]
    simp [Nat.add_assoc]

@[rocq_alias iriswasm.starts_implies_not_constant]
theorem starts_implies_not_constant (e : AdministrativeInstruction × Nat)
    (es : List AdministrativeInstruction) :
    firstInstr es = some e → constList es = true → False := by
  intro h hc
  have := first_instr_const es [] hc
  simp_all

@[rocq_alias iriswasm.first_instr.lfilled_implies_starts]
theorem lfilled_implies_starts (k : Nat) (lh : Lholed) (e : AdministrativeInstruction)
    (es : List AdministrativeInstruction) :
    (∀ n es' LI, e ≠ .label n es' LI) →
    (∀ n es' LI, e ≠ .local n es' LI) →
    (isConst e = true → False) →
    lfilled k lh [e] es = true →
    firstInstr es = some (e, k) := by
  intro hnlab hnloc hnconst hlf
  have := starts_with_lfilled e 0 [e] k lh es ?_ hlf
  · simpa using this
  rw [firstInstr_cons]
  rcases e with ⟨b⟩ | _ | _ | ⟨n, es, LI⟩ | ⟨n, f, LI⟩ | _
  · cases b <;> first | exact (hnconst rfl).elim | simp [firstInstrInstr]
  · simp [firstInstrInstr]
  · simp [firstInstrInstr]
  · exact absurd rfl (hnlab n es LI)
  · exact absurd rfl (hnloc n f LI)
  · simp [firstInstrInstr]

@[rocq_alias iriswasm.first_instr_Ind]
inductive FirstInstrInd :
    List AdministrativeInstruction → AdministrativeInstruction → Nat → Prop where
  | firstInstrConstBase (vs es : List AdministrativeInstruction) (a : AdministrativeInstruction)
      (i : Nat) : constList vs = true → FirstInstrInd es a i → FirstInstrInd (vs ++ es) a i
  | firstInstrTrap (es : List AdministrativeInstruction) : FirstInstrInd (.trap :: es) .trap 0
  | firstInstrInvoke (es : List AdministrativeInstruction) (a : Funcaddr) :
      FirstInstrInd (.invoke a :: es) (.invoke a) 0
  | firstInstrCallHost (es : List AdministrativeInstruction) (tf : FunctionType)
      (h : Hostfuncidx) (cvs : List Value) :
      FirstInstrInd (.callHost tf h cvs :: es) (.callHost tf h cvs) 0
  | firstInstrLocalInd (n : Nat) (f : Frame) (es es' : List AdministrativeInstruction)
      (a : AdministrativeInstruction) (i : Nat) :
      FirstInstrInd es a i → FirstInstrInd (.local n f es :: es') a (i + 1)
  | firstInstrLabel (n : Nat) (es1 es es' : List AdministrativeInstruction)
      (a : AdministrativeInstruction) (i : Nat) :
      FirstInstrInd es a i → FirstInstrInd (.label n es1 es :: es') a (i + 1)
  | firstInstrLocalBase (n : Nat) (f : Frame) (es es' : List AdministrativeInstruction) :
      constList es = true → FirstInstrInd (.local n f es :: es') (.local n f es) 0
  | firstInstrLabelBase (n : Nat) (es1 es es' : List AdministrativeInstruction) :
      constList es = true → FirstInstrInd (.label n es1 es :: es') (.label n es1 es) 0
  | firstInstrBasic (bi : BasicInstruction) (es' : List AdministrativeInstruction) :
      (∀ b, bi ≠ .const b) → FirstInstrInd (.basic bi :: es') (.basic bi) 0

@[rocq_alias iriswasm.first_instr_Ind_not_empty]
theorem first_instr_Ind_not_empty (es : List AdministrativeInstruction)
    (a : AdministrativeInstruction) (i : Nat) :
    FirstInstrInd es a i → es ≠ [] := by
  intro h
  induction h <;> simp_all

@[rocq_alias iriswasm.first_instr_Ind_Equivalent]
theorem first_instr_Ind_Equivalent (es : List AdministrativeInstruction)
    (a : AdministrativeInstruction) (i : Nat) :
    firstInstr es = some (a, i) ↔ FirstInstrInd es a i := by
  constructor
  · intro hf
    induction i using Nat.strongRecOn generalizing es a with
    | ind i IHi =>
    induction es generalizing a with
    | nil => simp at hf
    | cons e es ih =>
      rw [firstInstr_cons] at hf
      split at hf
      next p hp =>
        cases hf
        rcases e with ⟨b⟩ | _ | _ | ⟨n, es1, LI⟩ | ⟨n, f, LI⟩ | _
        · cases b <;> simp [firstInstrInstr] at hp <;> (obtain ⟨rfl, rfl⟩ := hp) <;>
            exact .firstInstrBasic _ _ (by simp)
        · simp [firstInstrInstr] at hp; obtain ⟨rfl, rfl⟩ := hp; exact .firstInstrTrap _
        · simp [firstInstrInstr] at hp; obtain ⟨rfl, rfl⟩ := hp; exact .firstInstrInvoke _ _
        · rw [firstInstrInstr_label] at hp
          split at hp
          next e' j hj =>
            cases hp
            exact .firstInstrLabel _ _ _ _ _ _ (IHi j (by omega) _ _ hj)
          next hn =>
            cases hp
            exact .firstInstrLabelBase _ _ _ _ (first_instr_None_const _ hn)
        · rw [firstInstrInstr_local] at hp
          split at hp
          next e' j hj =>
            cases hp
            exact .firstInstrLocalInd _ _ _ _ _ _ (IHi j (by omega) _ _ hj)
          next hn =>
            cases hp
            exact .firstInstrLocalBase _ _ _ _ (first_instr_None_const _ hn)
        · simp [firstInstrInstr] at hp; obtain ⟨rfl, rfl⟩ := hp; exact .firstInstrCallHost _ _ _ _
      next hn =>
        have hc := firstInstrInstr_eq_none.1 hn
        exact .firstInstrConstBase [e] es a i (by simp [constList, hc]) (ih a hf)
  · intro h
    induction h with
    | firstInstrConstBase vs es a i hc _ ih => rw [first_instr_const _ _ hc, ih]
    | firstInstrLocalInd n f es es' a i _ ih =>
      rw [firstInstr_cons, firstInstrInstr_local, ih]
    | firstInstrLabel n es1 es es' a i _ ih =>
      rw [firstInstr_cons, firstInstrInstr_label, ih]
    | firstInstrLocalBase n f es es' hc =>
      exact first_instr_app [_] _ es' (find_first_const es n f hc)
    | firstInstrLabelBase n es1 es es' hc =>
      exact first_instr_app [_] _ es' (find_first_const_label es es1 n hc)
    | firstInstrBasic bi es' hb =>
      rw [firstInstr_cons]
      cases bi <;> first | exact absurd rfl (hb _) | simp [firstInstrInstr]
    | _ => simp [firstInstr_cons, firstInstrInstr]

@[rocq_alias iriswasm.llfill_prepend]
theorem llfill_prepend (llh : Llholed) (vs es lles : List AdministrativeInstruction) :
    llfill llh es = lles →
    constList vs = true →
    ∃ llh', llfill llh' es = vs ++ lles := by
  intro hllf hc
  obtain ⟨vs0, rfl⟩ := const_es_exists hc
  subst hllf
  cases llh with
  | base l l0 => exact ⟨.base (vs0 ++ l) l0, by simp [llfill, vToEList]⟩
  | label l n l0 llh l1 => exact ⟨.label (vs0 ++ l) n l0 llh l1, by simp [llfill, vToEList]⟩
  | «local» l n f llh l0 => exact ⟨.local (vs0 ++ l) n f llh l0, by simp [llfill, vToEList]⟩

@[rocq_alias iriswasm.first_instr_Ind_llfill]
theorem first_instr_Ind_llfill (es : List AdministrativeInstruction)
    (a : AdministrativeInstruction) (i : Nat) :
    FirstInstrInd es a i → ∃ llh, llfill llh [a] = es := by
  intro h
  induction h with
  | firstInstrConstBase vs es a i hc _ ih =>
    obtain ⟨llh, hllf⟩ := ih
    exact llfill_prepend llh vs [a] es hllf hc
  | firstInstrLocalInd n f es es' a i _ ih =>
    obtain ⟨llh, rfl⟩ := ih
    exact ⟨.local [] n f llh es', by simp [llfill, vToEList]⟩
  | firstInstrLabel n es1 es es' a i _ ih =>
    obtain ⟨llh, rfl⟩ := ih
    exact ⟨.label [] n es1 llh es', by simp [llfill, vToEList]⟩
  | firstInstrTrap es | firstInstrInvoke es | firstInstrCallHost es
  | firstInstrLocalBase _ _ _ es | firstInstrLabelBase _ _ _ es | firstInstrBasic _ es =>
    exact ⟨.base [] es, by simp [llfill, vToEList]⟩

@[rocq_alias iriswasm.first_instr_llfill]
theorem first_instr_llfill (es : List AdministrativeInstruction) (a : AdministrativeInstruction)
    (i : Nat) :
    firstInstr es = some (a, i) → ∃ llh, llfill llh [a] = es := fun hf =>
  first_instr_Ind_llfill es a i ((first_instr_Ind_Equivalent es a i).1 hf)

end IrisWasm
