/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Helpers.LfillPrelude.LfillExtension
import Wasm.Properties

/-! Port of `theories/iris/helpers/lfill_prelude/lfill_prelude.v`. -/

namespace IrisWasm

open Wasm

@[rocq_alias iriswasm.length_cons_rec]
theorem length_cons_rec (a : AdministrativeInstruction) (es : List AdministrativeInstruction) :
    lengthRec (a :: es) > lengthRec es := by
  have : 1 ≤ sizeOfInstruction a := by cases a <;> simp [sizeOfInstruction]
  simp only [lengthRec, List.map_cons, List.sum_cons]; omega

@[rocq_alias iriswasm.length_app_rec]
theorem length_app_rec (l1 l2 : List AdministrativeInstruction) :
    lengthRec (l1 ++ l2) = lengthRec l1 + lengthRec l2 := by
  simp [lengthRec, List.sum_append]

@[rocq_alias iriswasm.length_lfilled_rec]
theorem length_lfilled_rec (k : Nat) (lh : Lholed) (es les : List AdministrativeInstruction) :
    lfilled k lh es les = true → lengthRec es ≤ lengthRec les := by
  rw [lfilled_Ind_Equivalent]
  intro h
  induction h with
  | lfilledBase => simp only [length_app_rec]; omega
  | lfilledRec _ _ n es' _ _ _ LI _ _ ih =>
    have : lengthRec [AdministrativeInstruction.label n es' LI] = lengthRec LI + 1 := by
      simp [lengthRec, sizeOfInstruction]
    simp only [length_app_rec, this]; omega

/-- Also stated in `properties.v` (`Wasm.lfill_cons_not_Some_nil`); namespaced to avoid the
clash. -/
@[rocq_alias iriswasm.lfill_prelude.lfill_cons_not_Some_nil]
theorem LfillPrelude.lfill_cons_not_Some_nil (i : Nat) (lh : Lholed)
    (es : List AdministrativeInstruction)
    (es' : Option (List AdministrativeInstruction)) (e : AdministrativeInstruction)
    (es0 : List AdministrativeInstruction) :
    lfill i lh es = es' → es = e :: es0 → es' ≠ some [] := by
  exact Wasm.lfill_cons_not_Some_nil

/-- Also stated in `properties.v` (`Wasm.lfilled_not_nil`); namespaced to avoid the clash. -/
@[rocq_alias iriswasm.lfill_prelude.lfilled_not_nil]
theorem LfillPrelude.lfilled_not_nil (i : Nat) (lh : Lholed)
    (es es' : List AdministrativeInstruction) :
    lfilled i lh es es' = true → es ≠ [] → es' ≠ [] := by
  exact Wasm.lfilled_not_nil

private theorem constList_app_iff {a b : List AdministrativeInstruction} :
    constList (a ++ b) = true ↔ constList a = true ∧ constList b = true := by
  simp [constList]

/-- Inversion principle for `LfilledInd` usable when the filled list is not a variable. -/
private theorem lfilledInd_inv {k : Nat} {lh : Lholed} {es LI : List AdministrativeInstruction}
    (h : LfilledInd k lh es LI) :
    (∃ bef aft, k = 0 ∧ lh = .base bef aft ∧ constList bef = true ∧ LI = bef ++ es ++ aft) ∨
    (∃ k' bef n es0 lh0 aft LI0, k = k' + 1 ∧ lh = .rec_ bef n es0 lh0 aft ∧
      constList bef = true ∧ LfilledInd k' lh0 es LI0 ∧ LI = bef ++ [.label n es0 LI0] ++ aft) := by
  cases h with
  | lfilledBase bef _ aft hc => exact .inl ⟨bef, aft, rfl, rfl, hc, rfl⟩
  | lfilledRec k' bef n es0 lh0 aft _ LI0 hc h =>
    exact .inr ⟨k', bef, n, es0, lh0, aft, LI0, rfl, rfl, hc, h, rfl⟩

@[rocq_alias iriswasm.lfilled_first_values]
theorem lfilled_first_values {i : Nat} {lh : Lholed} {vs : List AdministrativeInstruction}
    {e : AdministrativeInstruction} {i' : Nat} {lh' : Lholed} {vs' : List AdministrativeInstruction}
    {e' : AdministrativeInstruction} {LI : List AdministrativeInstruction} :
    lfilled i lh (vs ++ [e]) LI = true →
    lfilled i' lh' (vs' ++ [e']) LI = true →
    constList vs = true → constList vs' = true →
    isConst e = false → isConst e' = false →
    (∀ n es LI, e ≠ .label n es LI) → (∀ n es LI, e' ≠ .label n es LI) →
    e = e' ∧ i = i' ∧ (vs.length = vs'.length → vs = vs' ∧ lh = lh') := by
  intro h1 h2 hvs hvs' he he' hl hl'
  rw [lfilled_Ind_Equivalent] at h1 h2
  generalize hes : vs ++ [e] = es at h1
  induction h1 generalizing i' lh' with
  | lfilledBase bef _ aft hc =>
    subst hes
    rcases lfilledInd_inv h2 with ⟨bef', aft', rfl, rfl, hc', hLI⟩ |
      ⟨k', bef', n', es0', lh0', aft', LI0', rfl, rfl, hc', -, hLI⟩
    · obtain ⟨h, rfl, rfl⟩ := first_values (bef ++ vs) e aft (bef' ++ vs') e' aft' he he'
        (constList_app_iff.2 ⟨hc, hvs⟩) (constList_app_iff.2 ⟨hc', hvs'⟩) (by simpa using hLI)
      refine ⟨rfl, rfl, fun hlen => ?_⟩
      obtain ⟨rfl, rfl⟩ := List.append_inj' h hlen
      exact ⟨rfl, rfl⟩
    · obtain ⟨-, rfl, -⟩ := first_values (bef ++ vs) e aft bef' _ aft' he rfl
        (constList_app_iff.2 ⟨hc, hvs⟩) hc' (by simpa using hLI)
      exact absurd rfl (hl _ _ _)
  | lfilledRec k bef n es0 lh0 aft _ LI0 hc h ih =>
    rcases lfilledInd_inv h2 with ⟨bef', aft', rfl, rfl, hc', hLI⟩ |
      ⟨k', bef', n', es0', lh0', aft', LI0', rfl, rfl, hc', h', hLI⟩
    · subst hes
      obtain ⟨-, rfl, -⟩ := first_values (bef' ++ vs') e' aft' bef _ aft he' rfl
        (constList_app_iff.2 ⟨hc', hvs'⟩) hc (by simpa using hLI.symm)
      exact absurd rfl (hl' _ _ _)
    · obtain ⟨rfl, hlab, rfl⟩ := first_values bef _ aft bef' _ aft' rfl rfl hc hc'
        (by simpa using hLI)
      simp only [AdministrativeInstruction.label.injEq] at hlab
      obtain ⟨rfl, rfl, rfl⟩ := hlab
      obtain ⟨rfl, rfl, hlen⟩ := ih h' hes
      exact ⟨rfl, rfl, fun hl => by obtain ⟨rfl, rfl⟩ := hlen hl; exact ⟨rfl, rfl⟩⟩

@[rocq_alias iriswasm.lfilled_trans]
theorem lfilled_trans {k : Nat} {lh : Lholed} {es1 es2 : List AdministrativeInstruction} {k' : Nat}
    {lh' : Lholed} {es3 : List AdministrativeInstruction} :
    lfilled k lh es1 es2 = true → lfilled k' lh' es2 es3 = true →
    ∃ lh'', lfilled (k + k') lh'' es1 es3 = true := by
  simp only [lfilled_Ind_Equivalent]
  intro h1 h2
  induction h2 with
  | lfilledBase vs _ es' hc =>
    rcases lfilledInd_inv h1 with ⟨bef, aft, rfl, rfl, hc1, rfl⟩ |
      ⟨k0, bef, n, es0, lh0, aft, LI0, rfl, rfl, hc1, h, rfl⟩
    · exact ⟨.base (vs ++ bef) (aft ++ es'), by
        simpa using LfilledInd.lfilledBase (vs ++ bef) es1 (aft ++ es')
          (constList_app_iff.2 ⟨hc, hc1⟩)⟩
    · exact ⟨.rec_ (vs ++ bef) n es0 lh0 (aft ++ es'), by
        simpa using LfilledInd.lfilledRec _ (vs ++ bef) n es0 lh0 (aft ++ es') _ _
          (constList_app_iff.2 ⟨hc, hc1⟩) h⟩
  | lfilledRec k' vs n es' _ es'' _ _ hc _ ih =>
    obtain ⟨lh'', h⟩ := ih h1
    exact ⟨.rec_ vs n es' lh'' es'', LfilledInd.lfilledRec _ _ n es' _ es'' _ _ hc h⟩

@[rocq_alias iriswasm.vfill_is_nil]
theorem vfill_is_nil {n : Nat} (vh : ValidHoled n) (es : List AdministrativeInstruction) :
    vfill vh es = [] → es = [] ∧ vh = .base [] [] := by
  cases vh <;> simp [vfill, vToEList]
  intros; simp_all

@[rocq_alias iriswasm.sfill_is_nil]
theorem sfill_is_nil (sh : SimpleValidHoled) (es : List AdministrativeInstruction) :
    sfill sh es = [] → es = [] ∧ sh = .base [] [] := by
  cases sh <;> simp [sfill, vToEList]
  intros; simp_all

@[rocq_alias iriswasm.llfill_is_nil]
theorem llfill_is_nil (lh : Llholed) (es : List AdministrativeInstruction) :
    llfill lh es = [] → es = [] ∧ lh = .base [] [] := by
  cases lh <;> simp [llfill, vToEList]
  intros; simp_all

@[rocq_alias iriswasm.vh_push_const_inj]
theorem vh_push_const_inj {n : Nat} (vh vh' : ValidHoled n) (vs : List Value) :
    vhPushConst vh vs = vhPushConst vh' vs → vh = vh' := by
  cases vh <;> cases vh' <;> simp_all [vhPushConst]

@[rocq_alias iriswasm.vfill_decrease]
theorem vfill_decrease {n : Nat} (vh1 : ValidHoled (n + 1)) (vh2 : ValidHoled n)
    (es : List AdministrativeInstruction) :
    vhDecrease vh1 = some vh2 → vfill vh1 es = vfill vh2 es := by
  induction n with
  | zero =>
    cases vh1 with
    | base => simp only [vhDecrease, Option.some.injEq]; rintro rfl; rfl
    | rec_ => simp [vhDecrease]
  | succ n ih =>
    cases vh1 with
    | base => simp only [vhDecrease, Option.some.injEq]; rintro rfl; rfl
    | rec_ bef m es0 vh aft =>
      simp only [vhDecrease, Option.map_eq_some_iff]
      rintro ⟨vh', h, rfl⟩
      simp [vfill, ih vh vh' h]

@[rocq_alias iriswasm.vh_decrease_push_const]
theorem vh_decrease_push_const {m : Nat} (vh : ValidHoled (m + 1)) (vs : List Value)
    (vh' : ValidHoled m) :
    vhDecrease vh = some vh' → vhDecrease (vhPushConst vh vs) = some (vhPushConst vh' vs) := by
  cases m with
  | zero =>
    cases vh with
    | base => simp only [vhDecrease, vhPushConst, Option.some.injEq]; rintro rfl; rfl
    | rec_ => simp [vhDecrease]
  | succ m =>
    cases vh with
    | base => simp only [vhDecrease, vhPushConst, Option.some.injEq]; rintro rfl; rfl
    | rec_ =>
      simp only [vhDecrease, vhPushConst, Option.map_eq_some_iff]
      rintro ⟨vh'', h, rfl⟩
      exact ⟨vh'', h, rfl⟩

@[rocq_alias iriswasm.vh_decrease_push_const_inv]
theorem vh_decrease_push_const_inv {m : Nat} (vh : ValidHoled (m + 1)) (vs : List Value)
    (vh' : ValidHoled m) :
    vhDecrease (vhPushConst vh vs) = some vh' →
    ∃ vh'', vhDecrease vh = some vh'' ∧ vhPushConst vh'' vs = vh' := by
  cases m with
  | zero =>
    cases vh with
    | base =>
      simp only [vhDecrease, vhPushConst, Option.some.injEq]; rintro rfl; exact ⟨_, rfl, rfl⟩
    | rec_ => simp [vhDecrease, vhPushConst]
  | succ m =>
    cases vh with
    | base =>
      simp only [vhDecrease, vhPushConst, Option.some.injEq]; rintro rfl; exact ⟨_, rfl, rfl⟩
    | rec_ bef n0 es0 vh0 aft =>
      intro H
      simp only [vhDecrease, vhPushConst, Option.map_eq_some_iff] at H
      obtain ⟨vh'', h, rfl⟩ := H
      exact ⟨.rec_ bef n0 es0 vh'' aft, by simp [vhDecrease, h], rfl⟩

@[rocq_alias iriswasm.sh_push_const_app]
theorem sh_push_const_app (sh : SimpleValidHoled) (vs1 vs2 : List Value) :
    shPushConst sh (vs1 ++ vs2) = shPushConst (shPushConst sh vs2) vs1 := by
  cases sh <;> simp [shPushConst]

@[rocq_alias iriswasm.vh_push_const_app]
theorem vh_push_const_app {n : Nat} (vh : ValidHoled n) (vs1 vs2 : List Value) :
    vhPushConst vh (vs1 ++ vs2) = vhPushConst (vhPushConst vh vs2) vs1 := by
  cases vh <;> simp [vhPushConst]

@[rocq_alias iriswasm.llh_push_const_app]
theorem llh_push_const_app (lh : Llholed) (vs1 vs2 : List Value) :
    llhPushConst lh (vs1 ++ vs2) = llhPushConst (llhPushConst lh vs2) vs1 := by
  cases lh <;> simp [llhPushConst]

@[rocq_alias iriswasm.sh_push_const_nil]
theorem sh_push_const_nil (sh : SimpleValidHoled) : shPushConst sh [] = sh := by
  cases sh <;> simp [shPushConst]

@[rocq_alias iriswasm.vh_push_const_nil]
theorem vh_push_const_nil {n : Nat} (vh : ValidHoled n) : vhPushConst vh [] = vh := by
  cases vh <;> simp [vhPushConst]

@[rocq_alias iriswasm.llh_push_const_nil]
theorem llh_push_const_nil (lh : Llholed) : llhPushConst lh [] = lh := by
  cases lh <;> simp [llhPushConst]

@[rocq_alias iriswasm.sh_append_app]
theorem sh_append_app (sh : SimpleValidHoled) (es1 es2 : List AdministrativeInstruction) :
    shAppend sh (es1 ++ es2) = shAppend (shAppend sh es1) es2 := by
  cases sh <;> simp [shAppend]

@[rocq_alias iriswasm.vh_append_app]
theorem vh_append_app {n : Nat} (vh : ValidHoled n) (es1 es2 : List AdministrativeInstruction) :
    vhAppend vh (es1 ++ es2) = vhAppend (vhAppend vh es1) es2 := by
  cases vh <;> simp [vhAppend]

@[rocq_alias iriswasm.llh_append_app]
theorem llh_append_app (lh : Llholed) (es1 es2 : List AdministrativeInstruction) :
    llhAppend lh (es1 ++ es2) = llhAppend (llhAppend lh es1) es2 := by
  cases lh <;> simp [llhAppend]

@[rocq_alias iriswasm.sh_append_nil]
theorem sh_append_nil (sh : SimpleValidHoled) : shAppend sh [] = sh := by
  cases sh <;> simp [shAppend]

@[rocq_alias iriswasm.vh_append_nil]
theorem vh_append_nil {n : Nat} (vh : ValidHoled n) : vhAppend vh [] = vh := by
  cases vh <;> simp [vhAppend]

@[rocq_alias iriswasm.llh_append_nil]
theorem llh_append_nil (lh : Llholed) : llhAppend lh [] = lh := by
  cases lh <;> simp [llhAppend]

@[rocq_alias iriswasm.sh_push_const_append]
theorem sh_push_const_append (sh : SimpleValidHoled) (vs : List Value)
    (es : List AdministrativeInstruction) :
    shPushConst (shAppend sh es) vs = shAppend (shPushConst sh vs) es := by
  cases sh <;> rfl

@[rocq_alias iriswasm.vh_push_const_append]
theorem vh_push_const_append {n : Nat} (vh : ValidHoled n) (vs : List Value)
    (es : List AdministrativeInstruction) :
    vhPushConst (vhAppend vh es) vs = vhAppend (vhPushConst vh vs) es := by
  cases vh <;> rfl

@[rocq_alias iriswasm.llh_push_const_append]
theorem llh_push_const_append (lh : Llholed) (vs : List Value)
    (es : List AdministrativeInstruction) :
    llhPushConst (llhAppend lh es) vs = llhAppend (llhPushConst lh vs) es := by
  cases lh <;> rfl

@[rocq_alias iriswasm.vfill_increase]
theorem vfill_increase {m : Nat} (vh : ValidHoled m) (es : List AdministrativeInstruction) :
    vfill (vhIncrease vh) es = vfill vh es := by
  induction vh with
  | base => rfl
  | rec_ _ _ _ _ _ ih => simp [vhIncrease, vfill, ih]

@[rocq_alias iriswasm.vh_decrease_increase]
theorem vh_decrease_increase {m : Nat} (vh : ValidHoled m) :
    vhDecrease (vhIncrease vh) = some vh := by
  induction vh with
  | base => cases ‹Nat› <;> simp [vhIncrease, vhDecrease]
  | rec_ _ _ _ _ _ ih => simp [vhIncrease, vhDecrease, ih]

@[rocq_alias iriswasm.vh_increase_push_const]
theorem vh_increase_push_const {m : Nat} (vh : ValidHoled m) (vs : List Value) :
    vhIncrease (vhPushConst vh vs) = vhPushConst (vhIncrease vh) vs := by
  cases vh <;> rfl

@[rocq_alias iriswasm.vh_increase_repeat_push_const]
theorem vh_increase_repeat_push_const {m : Nat} (vh : ValidHoled m) (vs : List Value) (j : Nat) :
    vhIncreaseRepeat (vhPushConst vh vs) j = vhPushConst (vhIncreaseRepeat vh j) vs := by
  induction j with
  | zero => rfl
  | succ j ih => simp [vhIncreaseRepeat, ih, vh_increase_push_const]

/-- Coq: `S (m + n) = m + S n`; definitional in Lean. -/
@[rocq_alias iriswasm.S_plus]
theorem S_plus (m n : Nat) : m + n + 1 = m + (n + 1) := rfl

/-- Lean's `vhIncreaseRepeat` is indexed by `m + j` (Coq: `j + m`), so the cast is along
`m + j + 1 = m + 1 + j` instead of Coq's `S_plus j m`. -/
@[rocq_alias iriswasm.vh_increase_repeat_rec]
theorem vh_increase_repeat_rec {m : Nat} (vh : ValidHoled m) (bef : List Value) (n : Nat)
    (es : List AdministrativeInstruction) (aft : List AdministrativeInstruction) (j : Nat) :
    vhIncreaseRepeat (.rec_ bef n es vh aft) j =
      Nat.add_right_comm m j 1 ▸ ValidHoled.rec_ bef n es (vhIncreaseRepeat vh j) aft := by
  have hinc : ∀ {a b : Nat} (h : a = b) (x : ValidHoled a),
      vhIncrease (h ▸ x) = (congrArg (· + 1) h ▸ vhIncrease x : ValidHoled (b + 1)) := by
    intro a b h x; subst h; rfl
  induction j with
  | zero => rfl
  | succ j ih => simp only [vhIncreaseRepeat]; rw [ih, hinc]; rfl

private def constOf : AdministrativeInstruction → Option Value
  | .basic (.const v) => some v
  | _ => none

private theorem those_constOf {bef : List AdministrativeInstruction} (hc : constList bef = true) :
    ∃ vs, vToEList vs = bef ∧ those (bef.map constOf) = some vs := by
  simp only [← those_those0]
  induction bef with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons a bef ih =>
    simp only [constList, List.all_cons, Bool.and_eq_true] at hc
    obtain ⟨vs, rfl, h⟩ := ih hc.2
    match a, hc.1 with
    | .basic (.const v), _ => exact ⟨v :: vs, rfl, by simp [those0, constOf, h]⟩

private theorem vhOfLh_base (bef aft : List AdministrativeInstruction) (i : Nat) :
    vhOfLh (.base bef aft) i = (those (bef.map constOf)).map fun bef => .base bef aft := rfl

private theorem vhOfLh_rec (bef : List AdministrativeInstruction) (n : Nat)
    (es : List AdministrativeInstruction) (lh : Lholed) (aft : List AdministrativeInstruction)
    (i : Nat) :
    vhOfLh (.rec_ bef n es lh aft) (i + 1) =
      match those (bef.map constOf) with
      | some bef => (vhOfLh lh i).map fun vh => .rec_ bef n es vh aft
      | none => none := rfl

@[rocq_alias iriswasm.vfill_to_lfilled]
theorem vfill_to_lfilled {i : Nat} (vh : ValidHoled i) (es : List AdministrativeInstruction) :
    i ≥ lhDepth (lhOfVh vh) ∧
      lfilled (lhDepth (lhOfVh vh)) (lhOfVh vh) es (vfill vh es) = true := by
  induction vh with
  | base bef aft =>
    refine ⟨Nat.zero_le _, ?_⟩
    rw [lfilled_Ind_Equivalent]
    exact LfilledInd.lfilledBase _ _ _ (by simp [constList, isConst])
  | rec_ bef n es0 vh aft ih =>
    obtain ⟨hk, hf⟩ := ih
    refine ⟨by simp only [lhOfVh, lhDepth]; omega, ?_⟩
    rw [lfilled_Ind_Equivalent] at hf ⊢
    have := LfilledInd.lfilledRec _ (vToEList bef) n es0 _ aft _ _
      (by simp [vToEList, constList, isConst]) hf
    simpa [vfill, lhOfVh, lhDepth, vToEList] using this

@[rocq_alias iriswasm.sfill_to_lfilled]
theorem sfill_to_lfilled (sh : SimpleValidHoled) (es : List AdministrativeInstruction) :
    lfilled (lhDepth (lhOfSh sh)) (lhOfSh sh) es (sfill sh es) = true := by
  induction sh with
  | base bef aft =>
    rw [lfilled_Ind_Equivalent]
    exact LfilledInd.lfilledBase _ _ _ (by simp [constList, isConst])
  | rec_ bef n es0 sh aft ih =>
    rw [lfilled_Ind_Equivalent] at ih ⊢
    have := LfilledInd.lfilledRec _ (vToEList bef) n es0 _ aft _ _
      (by simp [vToEList, constList, isConst]) ih
    simpa [sfill, lhOfSh, lhDepth, vToEList] using this

@[rocq_alias iriswasm.lfilled_to_vfill]
theorem lfilled_to_vfill {k : Nat} {lh : Lholed} {es LI : List AdministrativeInstruction}
    {i : Nat} :
    lfilled k lh es LI = true → i ≥ k → ∃ vh, vhOfLh lh i = some vh ∧ vfill vh es = LI := by
  rw [lfilled_Ind_Equivalent]
  intro h
  induction h generalizing i with
  | lfilledBase bef _ aft hc =>
    intro _
    obtain ⟨vs, rfl, hvs⟩ := those_constOf hc
    exact ⟨.base vs aft, by rw [vhOfLh_base, hvs]; rfl, by simp [vfill]⟩
  | lfilledRec k bef n es0 lh0 aft _ LI0 hc _ ih =>
    intro hi
    obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    obtain ⟨vh, hvh, rfl⟩ := ih (i := i) (by omega)
    obtain ⟨vs, rfl, hvs⟩ := those_constOf hc
    exact ⟨.rec_ vs n es0 vh aft, by rw [vhOfLh_rec, hvs]; simp [hvh], by simp [vfill]⟩

@[rocq_alias iriswasm.lfilled_implies_llfill]
theorem lfilled_implies_llfill {k : Nat} {lh : Lholed} {es LI : List AdministrativeInstruction} :
    lfilled k lh es LI = true → ∃ llh, llfill llh es = LI := by
  rw [lfilled_Ind_Equivalent]
  intro h
  induction h with
  | lfilledBase bef _ aft hc =>
    obtain ⟨vs, rfl, -⟩ := those_constOf hc
    exact ⟨.base vs aft, rfl⟩
  | lfilledRec k bef n es0 lh0 aft _ LI0 hc _ ih =>
    obtain ⟨llh, rfl⟩ := ih
    obtain ⟨vs, rfl, -⟩ := those_constOf hc
    exact ⟨.label vs n es0 llh aft, by simp [llfill]⟩

/-- Normalises both sides of a fill equation to the `pre ++ x :: post` shape of `first_values`. -/
local macro "fv_eq " H:term : term =>
  `(by simpa only [llfill, List.append_assoc, List.singleton_append, List.cons_append,
    List.nil_append] using $H)

private theorem cl_vte_app {bef : List Value} {vs : List AdministrativeInstruction}
    (h : constList vs = true) : constList (vToEList bef ++ vs) = true :=
  constList_app_iff.2 ⟨v_to_e_is_const_list bef, h⟩

/-- A fill of a non-constant, non-trap instruction is neither a constant list nor `[trap]`. -/
private theorem llfill_not_vals {lh : Llholed} {vs : List AdministrativeInstruction}
    {e : AdministrativeInstruction} (he : isConst e = false) (ht : e ≠ .trap) :
    ¬ (constList (llfill lh (vs ++ [e])) = true ∨ llfill lh (vs ++ [e]) = [.trap]) := by
  have hmem : ∃ x ∈ llfill lh (vs ++ [e]), isConst x = false ∧ x ≠ .trap := by
    cases lh with
    | base => exact ⟨e, by simp [llfill], he, ht⟩
    | label bef n es lh0 aft =>
      exact ⟨.label n es (llfill lh0 (vs ++ [e])), by simp [llfill], rfl, by simp⟩
    | «local» bef n f lh0 aft =>
      exact ⟨.local n f (llfill lh0 (vs ++ [e])), by simp [llfill], rfl, by simp⟩
  obtain ⟨x, hx, hc, hxt⟩ := hmem
  rintro (h | h)
  · simp only [constList, List.all_eq_true] at h; simp [h x hx] at hc
  · rw [h] at hx; simp at hx; exact hxt hx

@[rocq_alias iriswasm.llfill_all_values']
theorem llfill_all_values' {lh : Llholed} {vs : List AdministrativeInstruction}
    {e : AdministrativeInstruction} {lh' : Llholed} {n0 : Nat}
    {es vs' LI : List AdministrativeInstruction} :
    llfill lh (vs ++ [e]) = LI →
    llfill lh' [.label n0 es vs'] = LI →
    constList vs = true → (constList vs' = true ∨ vs' = [.trap]) →
    isConst e = false →
    e ≠ .trap →
    (∀ n es LI, e ≠ .label n es LI) →
    (∀ n f LI, e ≠ .local n f LI) →
    False := by
  intro h1 h2 hvs hvs' he ht hl hlo
  have H := h1.trans h2.symm
  clear h1 h2
  induction lh generalizing lh' with
  | base bef aft =>
    cases lh' with
    | base bef' aft' =>
      obtain ⟨-, h, -⟩ := first_values (vToEList bef ++ vs) e aft (vToEList bef') _ aft' he rfl
        (cl_vte_app hvs) (v_to_e_is_const_list _) (fv_eq H)
      exact hl _ _ _ h
    | label bef' n' es' lh0' aft' =>
      obtain ⟨-, h, -⟩ := first_values (vToEList bef ++ vs) e aft (vToEList bef') _ aft' he rfl
        (cl_vte_app hvs) (v_to_e_is_const_list _) (fv_eq H)
      exact hl _ _ _ h
    | «local» bef' n' f' lh0' aft' =>
      obtain ⟨-, h, -⟩ := first_values (vToEList bef ++ vs) e aft (vToEList bef') _ aft' he rfl
        (cl_vte_app hvs) (v_to_e_is_const_list _) (fv_eq H)
      exact hlo _ _ _ h
  | label bef n es0 lh0 aft ih =>
    cases lh' with
    | base bef' aft' =>
      obtain ⟨-, h, -⟩ := first_values (vToEList bef) _ aft (vToEList bef') _ aft' rfl rfl
        (v_to_e_is_const_list _) (v_to_e_is_const_list _) (fv_eq H)
      simp only [AdministrativeInstruction.label.injEq] at h
      exact llfill_not_vals he ht (h.2.2 ▸ hvs')
    | label bef' n' es' lh0' aft' =>
      obtain ⟨-, h, -⟩ := first_values (vToEList bef) _ aft (vToEList bef') _ aft' rfl rfl
        (v_to_e_is_const_list _) (v_to_e_is_const_list _) (fv_eq H)
      simp only [AdministrativeInstruction.label.injEq] at h
      exact ih h.2.2
    | «local» bef' n' f' lh0' aft' =>
      obtain ⟨-, h, -⟩ := first_values (vToEList bef) _ aft (vToEList bef') _ aft' rfl rfl
        (v_to_e_is_const_list _) (v_to_e_is_const_list _) (fv_eq H)
      simp at h
  | «local» bef n f0 lh0 aft ih =>
    cases lh' with
    | base bef' aft' =>
      obtain ⟨-, h, -⟩ := first_values (vToEList bef) _ aft (vToEList bef') _ aft' rfl rfl
        (v_to_e_is_const_list _) (v_to_e_is_const_list _) (fv_eq H)
      simp at h
    | label bef' n' es' lh0' aft' =>
      obtain ⟨-, h, -⟩ := first_values (vToEList bef) _ aft (vToEList bef') _ aft' rfl rfl
        (v_to_e_is_const_list _) (v_to_e_is_const_list _) (fv_eq H)
      simp at h
    | «local» bef' n' f' lh0' aft' =>
      obtain ⟨-, h, -⟩ := first_values (vToEList bef) _ aft (vToEList bef') _ aft' rfl rfl
        (v_to_e_is_const_list _) (v_to_e_is_const_list _) (fv_eq H)
      simp only [AdministrativeInstruction.local.injEq] at h
      exact ih h.2.2

@[rocq_alias iriswasm.lfilled_all_values']
theorem lfilled_all_values' {i : Nat} {lh : Lholed} {vs : List AdministrativeInstruction}
    {e : AdministrativeInstruction} {i' : Nat} {lh' : Lholed} {n0 : Nat}
    {es vs' LI : List AdministrativeInstruction} :
    lfilled i lh (vs ++ [e]) LI = true →
    lfilled i' lh' [.label n0 es vs'] LI = true →
    constList vs = true → (constList vs' = true ∨ vs' = [.trap]) →
    isConst e = false →
    e ≠ .trap →
    (∀ n es LI, e ≠ .label n es LI) →
    False := by
  intro h1 h2 hvs hvs' he ht hl
  rw [lfilled_Ind_Equivalent] at h1 h2
  generalize hes : vs ++ [e] = ves at h1
  induction h1 generalizing i' lh' with
  | lfilledBase bef _ aft hc =>
    subst hes
    rcases lfilledInd_inv h2 with ⟨bef', aft', rfl, rfl, hc', hLI⟩ |
      ⟨k', bef', n', es0', lh0', aft', LI0', rfl, rfl, hc', -, hLI⟩
    · obtain ⟨-, h, -⟩ := first_values (bef ++ vs) e aft bef' _ aft' he rfl
        (constList_app_iff.2 ⟨hc, hvs⟩) hc' (fv_eq hLI)
      exact hl _ _ _ h
    · obtain ⟨-, h, -⟩ := first_values (bef ++ vs) e aft bef' _ aft' he rfl
        (constList_app_iff.2 ⟨hc, hvs⟩) hc' (fv_eq hLI)
      exact hl _ _ _ h
  | lfilledRec k bef n es1 lh0 aft _ LI0 hc h ih =>
    rcases lfilledInd_inv h2 with ⟨bef', aft', rfl, rfl, hc', hLI⟩ |
      ⟨k', bef', n', es0', lh0', aft', LI0', rfl, rfl, hc', h', hLI⟩
    · obtain ⟨-, hx, -⟩ := first_values bef _ aft bef' _ aft' rfl rfl hc hc' (fv_eq hLI)
      simp only [AdministrativeInstruction.label.injEq] at hx
      subst hes
      obtain ⟨llh, hllh⟩ := lfilled_implies_llfill ((lfilled_Ind_Equivalent _ _ _ _).2 h)
      exact llfill_not_vals (lh := llh) he ht (by rw [hllh, hx.2.2]; exact hvs')
    · obtain ⟨-, hx, -⟩ := first_values bef _ aft bef' _ aft' rfl rfl hc hc' (fv_eq hLI)
      simp only [AdministrativeInstruction.label.injEq] at hx
      obtain ⟨rfl, rfl, rfl⟩ := hx
      exact ih h' hes

@[rocq_alias iriswasm.llfill_all_values'']
theorem llfill_all_values'' {lh : Llholed} {vs : List AdministrativeInstruction}
    {e : AdministrativeInstruction} {lh' : Llholed} {n0 : Nat} {es : Frame}
    {vs' LI : List AdministrativeInstruction} :
    llfill lh (vs ++ [e]) = LI →
    llfill lh' [.local n0 es vs'] = LI →
    constList vs = true → (constList vs' = true ∨ vs' = [.trap]) →
    isConst e = false →
    e ≠ .trap →
    (∀ n es LI, e ≠ .label n es LI) →
    (∀ n f LI, e ≠ .local n f LI) →
    False := by
  intro h1 h2 hvs hvs' he ht hl hlo
  have H := h1.trans h2.symm
  clear h1 h2
  induction lh generalizing lh' with
  | base bef aft =>
    cases lh' with
    | base bef' aft' =>
      obtain ⟨-, h, -⟩ := first_values (vToEList bef ++ vs) e aft (vToEList bef') _ aft' he rfl
        (cl_vte_app hvs) (v_to_e_is_const_list _) (fv_eq H)
      exact hlo _ _ _ h
    | label bef' n' es' lh0' aft' =>
      obtain ⟨-, h, -⟩ := first_values (vToEList bef ++ vs) e aft (vToEList bef') _ aft' he rfl
        (cl_vte_app hvs) (v_to_e_is_const_list _) (fv_eq H)
      exact hl _ _ _ h
    | «local» bef' n' f' lh0' aft' =>
      obtain ⟨-, h, -⟩ := first_values (vToEList bef ++ vs) e aft (vToEList bef') _ aft' he rfl
        (cl_vte_app hvs) (v_to_e_is_const_list _) (fv_eq H)
      exact hlo _ _ _ h
  | label bef n es0 lh0 aft ih =>
    cases lh' with
    | base bef' aft' =>
      obtain ⟨-, h, -⟩ := first_values (vToEList bef) _ aft (vToEList bef') _ aft' rfl rfl
        (v_to_e_is_const_list _) (v_to_e_is_const_list _) (fv_eq H)
      simp at h
    | label bef' n' es' lh0' aft' =>
      obtain ⟨-, h, -⟩ := first_values (vToEList bef) _ aft (vToEList bef') _ aft' rfl rfl
        (v_to_e_is_const_list _) (v_to_e_is_const_list _) (fv_eq H)
      simp only [AdministrativeInstruction.label.injEq] at h
      exact ih h.2.2
    | «local» bef' n' f' lh0' aft' =>
      obtain ⟨-, h, -⟩ := first_values (vToEList bef) _ aft (vToEList bef') _ aft' rfl rfl
        (v_to_e_is_const_list _) (v_to_e_is_const_list _) (fv_eq H)
      simp at h
  | «local» bef n f0 lh0 aft ih =>
    cases lh' with
    | base bef' aft' =>
      obtain ⟨-, h, -⟩ := first_values (vToEList bef) _ aft (vToEList bef') _ aft' rfl rfl
        (v_to_e_is_const_list _) (v_to_e_is_const_list _) (fv_eq H)
      simp only [AdministrativeInstruction.local.injEq] at h
      exact llfill_not_vals he ht (h.2.2 ▸ hvs')
    | label bef' n' es' lh0' aft' =>
      obtain ⟨-, h, -⟩ := first_values (vToEList bef) _ aft (vToEList bef') _ aft' rfl rfl
        (v_to_e_is_const_list _) (v_to_e_is_const_list _) (fv_eq H)
      simp at h
    | «local» bef' n' f' lh0' aft' =>
      obtain ⟨-, h, -⟩ := first_values (vToEList bef) _ aft (vToEList bef') _ aft' rfl rfl
        (v_to_e_is_const_list _) (v_to_e_is_const_list _) (fv_eq H)
      simp only [AdministrativeInstruction.local.injEq] at h
      exact ih h.2.2

/-- If `e` is the first non-constant instruction of `LI`, then `e` is the last instruction of any
non-empty `es` (with constant prefix) filled into `LI`. -/
private theorem last_eq {i : Nat} {lh : Lholed} {vs : List AdministrativeInstruction}
    {e : AdministrativeInstruction} {LI : List AdministrativeInstruction} {k : Nat} {lh' : Lholed}
    {es : List AdministrativeInstruction}
    (h1 : lfilled i lh (vs ++ [e]) LI = true) (hvs : constList vs = true)
    (he : isConst e = false) (hl : ∀ n es LI, e ≠ .label n es LI)
    (h2 : lfilled k lh' es LI = true) (hne : es ≠ []) (hc : constList es.dropLast = true)
    (hx : isConst (es.getLast hne) = false) (hxl : ∀ n es0 LI, es.getLast hne ≠ .label n es0 LI) :
    e = es.getLast hne := by
  rw [← List.dropLast_concat_getLast hne] at h2
  exact (lfilled_first_values h1 h2 hvs hc he hx hl hxl).1

/-- Common proof of `lfilled_{br,return,call_host}_and_reduce`. -/
private theorem lfilled_stuck_and_reduce {s : StoreRecord} {f : Frame}
    {es LI : List AdministrativeInstruction} {s' : StoreRecord} {f' : Frame}
    {es' : List AdministrativeInstruction} {i : Nat} {lh : Lholed}
    {vs : List AdministrativeInstruction} {k : Nat} {lh' : Lholed} {e : AdministrativeInstruction}
    (hred : Reduce s f es s' f' es') (hvs : constList vs = true)
    (h1 : lfilled i lh (vs ++ [e]) LI = true) (h2 : lfilled k lh' es LI = true)
    (he : isConst e = false) (ht : e ≠ .trap) (hl : ∀ n es LI, e ≠ .label n es LI)
    (hb : ∀ b, e = .basic b → (∃ j, b = .br j) ∨ b = .return_)
    (hinv : ∀ a, e ≠ .invoke a) (hloc : ∀ n f LI, e ≠ .local n f LI)
    (hbr : ∀ {i0 m : Nat} {lh0 : Lholed} {vs0 : List AdministrativeInstruction},
      constList vs0 = true → lfilled (i0 + 1 + m) lh0 (vs0 ++ [.basic (.br i0)]) LI = true →
      False) :
    False := by
  induction hred generalizing k lh' with
  | simple hs =>
    cases hs with
    | labelConst hc => exact lfilled_all_values' h1 h2 hvs (.inl hc) he ht hl
    | labelTrap => exact lfilled_all_values' h1 h2 hvs (.inr rfl) he ht hl
    | @br n0 vs0 es0 i0 LI0 lh0 hc _ hf =>
      have hf' : lfilled (i0 + 1) (.rec_ [] n0 es0 lh0 []) (vs0 ++ [.basic (.br i0)])
          [.label n0 es0 LI0] = true := by
        rw [lfilled_Ind_Equivalent] at hf ⊢
        simpa using LfilledInd.lfilledRec _ [] _ _ _ [] _ _ rfl hf
      obtain ⟨_, h⟩ := lfilled_trans hf' h2
      exact hbr hc h
    | trap lh0 _ hf =>
      obtain ⟨_, h⟩ := lfilled_trans hf h2
      exact ht (last_eq h1 hvs he hl h (by simp) rfl rfl (by simp))
    | _ =>
      have hx := last_eq h1 hvs he hl h2 (by simp)
        (by simp_all [constList, isConst]) (by simp [isConst]) (by simp)
      simp at hx
      first
        | exact hloc _ _ _ hx
        | (rcases hb _ hx with ⟨_, hj⟩ | hj <;> simp at hj)
  | label _ _ _ _ _ hf _ ih =>
    obtain ⟨_, h⟩ := lfilled_trans hf h2
    exact ih h
  | _ =>
    have hx := last_eq h1 hvs he hl h2 (by simp)
      (by simp_all [constList, isConst, vToEList]) (by simp [isConst]) (by simp)
    simp at hx
    first
      | exact hloc _ _ _ hx
      | exact hinv _ hx
      | (rcases hb _ hx with ⟨_, hj⟩ | hj <;> simp at hj)

@[rocq_alias iriswasm.lfilled_br_and_reduce]
theorem lfilled_br_and_reduce {s : StoreRecord} {f : Frame} {es LI : List AdministrativeInstruction}
    {s' : StoreRecord} {f' : Frame} {es' : List AdministrativeInstruction} {i j : Nat} {lh : Lholed}
    {vs : List AdministrativeInstruction} {k : Nat} {lh' : Lholed} :
    Reduce s f es s' f' es' →
    constList vs = true →
    i ≤ j →
    lfilled i lh (vs ++ [.basic (.br j)]) LI = true →
    lfilled k lh' es LI = true →
    False := by
  intro hred hvs hij h1 h2
  refine lfilled_stuck_and_reduce hred hvs h1 h2 rfl (by simp) (by simp) (by simp) (by simp)
    (by simp) fun hc h => ?_
  obtain ⟨hx, hi, -⟩ := lfilled_first_values h1 h hvs hc rfl rfl (by simp) (by simp)
  simp only [AdministrativeInstruction.basic.injEq, BasicInstruction.br.injEq] at hx
  subst hx hi
  exact absurd hij (by omega)

@[rocq_alias iriswasm.lfilled_return_and_reduce]
theorem lfilled_return_and_reduce {s : StoreRecord} {f : Frame}
    {es LI : List AdministrativeInstruction} {s' : StoreRecord} {f' : Frame}
    {es' : List AdministrativeInstruction} {i : Nat} {lh : Lholed}
    {vs : List AdministrativeInstruction} {k : Nat} {lh' : Lholed} :
    Reduce s f es s' f' es' →
    constList vs = true →
    lfilled i lh (vs ++ [.basic .return_]) LI = true →
    lfilled k lh' es LI = true →
    False := by
  intro hred hvs h1 h2
  refine lfilled_stuck_and_reduce hred hvs h1 h2 rfl (by simp) (by simp) (by simp) (by simp)
    (by simp) fun hc h => ?_
  simpa using (lfilled_first_values h1 h hvs hc rfl rfl (by simp) (by simp)).1

@[rocq_alias iriswasm.llfill_first_values]
theorem llfill_first_values {lh : Llholed} {vs : List AdministrativeInstruction}
    {e : AdministrativeInstruction} {lh' : Llholed} {vs' : List AdministrativeInstruction}
    {e' : AdministrativeInstruction} {LI : List AdministrativeInstruction} :
    llfill lh (vs ++ [e]) = LI →
    llfill lh' (vs' ++ [e']) = LI →
    constList vs = true → constList vs' = true →
    isConst e = false → isConst e' = false →
    (∀ n es LI, e ≠ .label n es LI) →
    (∀ n es LI, e' ≠ .label n es LI) →
    (∀ n f LI, e ≠ .local n f LI) →
    (∀ n f LI, e' ≠ .local n f LI) →
    e = e' ∧ (vs.length = vs'.length → vs = vs' ∧ lh = lh') := by
  intro h1 h2 hvs hvs' he he' hl hl' hlo hlo'
  have H := h1.trans h2.symm
  clear h1 h2
  induction lh generalizing lh' with
  | base bef aft =>
    cases lh' with
    | base bef' aft' =>
      obtain ⟨h, rfl, rfl⟩ := first_values (vToEList bef ++ vs) e aft (vToEList bef' ++ vs') e' aft'
        he he' (cl_vte_app hvs) (cl_vte_app hvs') (fv_eq H)
      refine ⟨rfl, fun hlen => ?_⟩
      obtain ⟨hb, rfl⟩ := List.append_inj' h hlen
      rw [v_to_e_inj hb]
      exact ⟨rfl, rfl⟩
    | label bef' n' es' lh0' aft' =>
      obtain ⟨-, h, -⟩ := first_values (vToEList bef ++ vs) e aft (vToEList bef') _ aft' he rfl
        (cl_vte_app hvs) (v_to_e_is_const_list _) (fv_eq H)
      exact absurd h (hl _ _ _)
    | «local» bef' n' f' lh0' aft' =>
      obtain ⟨-, h, -⟩ := first_values (vToEList bef ++ vs) e aft (vToEList bef') _ aft' he rfl
        (cl_vte_app hvs) (v_to_e_is_const_list _) (fv_eq H)
      exact absurd h (hlo _ _ _)
  | label bef n es0 lh0 aft ih =>
    cases lh' with
    | base bef' aft' =>
      obtain ⟨-, h, -⟩ := first_values (vToEList bef) _ aft (vToEList bef' ++ vs') e' aft' rfl he'
        (v_to_e_is_const_list _) (cl_vte_app hvs') (fv_eq H)
      exact absurd h.symm (hl' _ _ _)
    | label bef' n' es' lh0' aft' =>
      obtain ⟨hb, h, rfl⟩ := first_values (vToEList bef) _ aft (vToEList bef') _ aft' rfl rfl
        (v_to_e_is_const_list _) (v_to_e_is_const_list _) (fv_eq H)
      simp only [AdministrativeInstruction.label.injEq] at h
      obtain ⟨rfl, rfl, h⟩ := h
      obtain ⟨rfl, hlen⟩ := ih h
      refine ⟨rfl, fun hl => ?_⟩
      obtain ⟨rfl, rfl⟩ := hlen hl
      rw [v_to_e_inj hb]
      exact ⟨rfl, rfl⟩
    | «local» bef' n' f' lh0' aft' =>
      obtain ⟨-, h, -⟩ := first_values (vToEList bef) _ aft (vToEList bef') _ aft' rfl rfl
        (v_to_e_is_const_list _) (v_to_e_is_const_list _) (fv_eq H)
      simp at h
  | «local» bef n f0 lh0 aft ih =>
    cases lh' with
    | base bef' aft' =>
      obtain ⟨-, h, -⟩ := first_values (vToEList bef) _ aft (vToEList bef' ++ vs') e' aft' rfl he'
        (v_to_e_is_const_list _) (cl_vte_app hvs') (fv_eq H)
      exact absurd h.symm (hlo' _ _ _)
    | label bef' n' es' lh0' aft' =>
      obtain ⟨-, h, -⟩ := first_values (vToEList bef) _ aft (vToEList bef') _ aft' rfl rfl
        (v_to_e_is_const_list _) (v_to_e_is_const_list _) (fv_eq H)
      simp at h
    | «local» bef' n' f' lh0' aft' =>
      obtain ⟨hb, h, rfl⟩ := first_values (vToEList bef) _ aft (vToEList bef') _ aft' rfl rfl
        (v_to_e_is_const_list _) (v_to_e_is_const_list _) (fv_eq H)
      simp only [AdministrativeInstruction.local.injEq] at h
      obtain ⟨rfl, rfl, h⟩ := h
      obtain ⟨rfl, hlen⟩ := ih h
      refine ⟨rfl, fun hl => ?_⟩
      obtain ⟨rfl, rfl⟩ := hlen hl
      rw [v_to_e_inj hb]
      exact ⟨rfl, rfl⟩

@[rocq_alias iriswasm.lfilled_llfill_first_values]
theorem lfilled_llfill_first_values {i : Nat} {lh : Lholed} {vs : List AdministrativeInstruction}
    {e : AdministrativeInstruction} {lh' : Llholed} {vs' : List AdministrativeInstruction}
    {e' : AdministrativeInstruction} {LI : List AdministrativeInstruction} :
    lfilled i lh (vs ++ [e]) LI = true →
    llfill lh' (vs' ++ [e']) = LI →
    constList vs = true → constList vs' = true →
    isConst e = false → isConst e' = false →
    (∀ n es LI, e ≠ .label n es LI) →
    (∀ n es LI, e' ≠ .label n es LI) →
    (∀ n f LI, e ≠ .local n f LI) →
    e = e' ∧ (vs.length = vs'.length → vs = vs') := by
  intro h1 h2 hvs hvs' he he' hl hl' hlo
  rw [lfilled_Ind_Equivalent] at h1
  generalize hes : vs ++ [e] = ves at h1
  induction h1 generalizing lh' with
  | lfilledBase bef _ aft hc =>
    subst hes
    cases lh' with
    | base bef' aft' =>
      obtain ⟨h, rfl, rfl⟩ := first_values (bef ++ vs) e aft (vToEList bef' ++ vs') e' aft' he he'
        (constList_app_iff.2 ⟨hc, hvs⟩) (cl_vte_app hvs') (fv_eq h2.symm)
      exact ⟨rfl, fun hlen => (List.append_inj' h hlen).2⟩
    | label bef' n' es' lh0' aft' =>
      obtain ⟨-, h, -⟩ := first_values (bef ++ vs) e aft (vToEList bef') _ aft' he rfl
        (constList_app_iff.2 ⟨hc, hvs⟩) (v_to_e_is_const_list _) (fv_eq h2.symm)
      exact absurd h (hl _ _ _)
    | «local» bef' n' f' lh0' aft' =>
      obtain ⟨-, h, -⟩ := first_values (bef ++ vs) e aft (vToEList bef') _ aft' he rfl
        (constList_app_iff.2 ⟨hc, hvs⟩) (v_to_e_is_const_list _) (fv_eq h2.symm)
      exact absurd h (hlo _ _ _)
  | lfilledRec k bef n es1 lh0 aft _ LI0 hc h ih =>
    cases lh' with
    | base bef' aft' =>
      obtain ⟨-, h, -⟩ := first_values bef _ aft (vToEList bef' ++ vs') e' aft' rfl he'
        hc (cl_vte_app hvs') (fv_eq h2.symm)
      exact absurd h.symm (hl' _ _ _)
    | label bef' n' es' lh0' aft' =>
      obtain ⟨-, hx, -⟩ := first_values bef _ aft (vToEList bef') _ aft' rfl rfl
        hc (v_to_e_is_const_list _) (fv_eq h2.symm)
      simp only [AdministrativeInstruction.label.injEq] at hx
      exact ih hx.2.2.symm hes
    | «local» bef' n' f' lh0' aft' =>
      obtain ⟨-, hx, -⟩ := first_values bef _ aft (vToEList bef') _ aft' rfl rfl
        hc (v_to_e_is_const_list _) (fv_eq h2.symm)
      simp at hx

@[rocq_alias iriswasm.llfill_trans]
theorem llfill_trans {llh1 llh2 : Llholed} {es0 es1 es2 : List AdministrativeInstruction} :
    llfill llh1 es0 = es1 → llfill llh2 es1 = es2 → ∃ llh0, llfill llh0 es0 = es2 := by
  rintro rfl rfl
  induction llh2 with
  | base bef aft =>
    exact ⟨llhPushConst (llhAppend llh1 aft) bef, by
      cases llh1 <;> simp [llfill, llhPushConst, llhAppend, vToEList]⟩
  | label bef n es lh aft ih =>
    obtain ⟨llh0, h⟩ := ih
    exact ⟨.label bef n es llh0 aft, by simp [llfill, h]⟩
  | «local» bef n f lh aft ih =>
    obtain ⟨llh0, h⟩ := ih
    exact ⟨.local bef n f llh0 aft, by simp [llfill, h]⟩

@[rocq_alias iriswasm.lfilled_in_llfill]
theorem lfilled_in_llfill {k : Nat} {lh : Lholed} {es LI : List AdministrativeInstruction}
    {llh : Llholed} {LI' : List AdministrativeInstruction} :
    lfilled k lh es LI = true → llfill llh LI = LI' → ∃ llh', llfill llh' es = LI' := by
  intro h1 h2
  obtain ⟨llh0, h1⟩ := lfilled_implies_llfill h1
  exact llfill_trans h1 h2

/-- `llfill` analogue of `last_eq`. -/
private theorem llast_eq {lh : Llholed} {vs : List AdministrativeInstruction}
    {e : AdministrativeInstruction} {LI : List AdministrativeInstruction} {lh' : Llholed}
    {es : List AdministrativeInstruction}
    (h1 : llfill lh (vs ++ [e]) = LI) (hvs : constList vs = true) (he : isConst e = false)
    (hl : ∀ n es LI, e ≠ .label n es LI) (hlo : ∀ n f LI, e ≠ .local n f LI)
    (h2 : llfill lh' es = LI) (hne : es ≠ []) (hc : constList es.dropLast = true)
    (hx : isConst (es.getLast hne) = false) (hxl : ∀ n es0 LI, es.getLast hne ≠ .label n es0 LI)
    (hxlo : ∀ n f LI, es.getLast hne ≠ .local n f LI) :
    e = es.getLast hne := by
  rw [← List.dropLast_concat_getLast hne] at h2
  exact (llfill_first_values h1 h2 hvs hc he hx hl hxl hlo hxlo).1

@[rocq_alias iriswasm.llfill_call_host_and_reduce]
theorem llfill_call_host_and_reduce {s : StoreRecord} {f : Frame}
    {es LI : List AdministrativeInstruction} {s' : StoreRecord} {f' : Frame}
    {es' : List AdministrativeInstruction} {lh lh' : Llholed} {tf : FunctionType}
    {h : Hostfuncidx} {cvs : List Value} {vs : List AdministrativeInstruction} :
    Reduce s f es s' f' es' →
    constList vs = true →
    llfill lh (vs ++ [.callHost tf h cvs]) = LI →
    llfill lh' es = LI →
    False := by
  intro hred hvs h1 h2
  induction hred generalizing lh' with
  | simple hs =>
    cases hs with
    | labelConst hc =>
      exact llfill_all_values' h1 h2 hvs (.inl hc) rfl (by simp) (by simp) (by simp)
    | labelTrap => exact llfill_all_values' h1 h2 hvs (.inr rfl) rfl (by simp) (by simp) (by simp)
    | localConst hc _ =>
      exact llfill_all_values'' h1 h2 hvs (.inl hc) rfl (by simp) (by simp) (by simp)
    | localTrap => exact llfill_all_values'' h1 h2 hvs (.inr rfl) rfl (by simp) (by simp) (by simp)
    | @br n0 vs0 es0 i0 LI0 lh0 hc _ hf =>
      have hf' : lfilled (i0 + 1) (.rec_ [] n0 es0 lh0 []) (vs0 ++ [.basic (.br i0)])
          [.label n0 es0 LI0] = true := by
        rw [lfilled_Ind_Equivalent] at hf ⊢
        simpa using LfilledInd.lfilledRec _ [] _ _ _ [] _ _ rfl hf
      obtain ⟨_, h3⟩ := lfilled_in_llfill hf' h2
      simpa using (llfill_first_values h1 h3 hvs hc rfl rfl (by simp) (by simp) (by simp)
        (by simp)).1
    | @return_ n0 i0 vs0 es0 lh0 f0 hc _ hf =>
      have key : ∀ vs0 llh, llfill llh (vs0 ++ [.basic .return_]) = es0 →
          constList vs0 = true → False := by
        intro vs0 llh h3 hc
        obtain ⟨_, h4⟩ := llfill_trans (llh1 := .local [] n0 f0 llh [])
          (es0 := vs0 ++ [.basic .return_]) (by simp [llfill, vToEList, h3]) h2
        simpa using (llfill_first_values h1 h4 hvs hc rfl rfl (by simp) (by simp) (by simp)
          (by simp)).1
      obtain ⟨llh, h3⟩ := lfilled_implies_llfill hf
      exact key _ llh h3 hc
    | trap lh0 _ hf =>
      obtain ⟨_, h3⟩ := lfilled_in_llfill hf h2
      simpa using llast_eq h1 hvs rfl (by simp) (by simp) h3 (by simp) rfl rfl (by simp) (by simp)
    | _ =>
      have hx := llast_eq h1 hvs rfl (by simp) (by simp) h2 (by simp)
        (by simp_all [constList, isConst]) (by simp [isConst]) (by simp) (by simp)
      simp at hx
  | label _ _ _ _ _ hf _ ih =>
    obtain ⟨_, h3⟩ := lfilled_in_llfill hf h2
    exact ih h3
  | «local» _ ih =>
    obtain ⟨_, h3⟩ := llfill_trans (llh1 := .local [] _ _ (.base [] []) [])
      (by simp [llfill, vToEList]; exact ⟨rfl, rfl, rfl⟩) h2
    exact ih h3
  | _ =>
    have hx := llast_eq h1 hvs rfl (by simp) (by simp) h2 (by simp)
      (by simp_all [constList, isConst, vToEList]) (by simp [isConst]) (by simp) (by simp)
    simp at hx

@[rocq_alias iriswasm.lfilled_call_host_and_reduce]
theorem lfilled_call_host_and_reduce {s : StoreRecord} {f : Frame}
    {es LI : List AdministrativeInstruction} {s' : StoreRecord} {f' : Frame}
    {es' : List AdministrativeInstruction} {i : Nat} {lh : Lholed}
    {vs : List AdministrativeInstruction} {k : Nat} {lh' : Lholed} {tf : FunctionType}
    {h : Hostfuncidx} {cvs : List Value} :
    Reduce s f es s' f' es' →
    constList vs = true →
    lfilled i lh (vs ++ [.callHost tf h cvs]) LI = true →
    lfilled k lh' es LI = true →
    False := by
  intro hred hvs h1 h2
  refine lfilled_stuck_and_reduce hred hvs h1 h2 rfl (by simp) (by simp) (by simp) (by simp)
    (by simp) fun hc h => ?_
  simpa using (lfilled_first_values h1 h hvs hc rfl rfl (by simp) (by simp)).1

@[rocq_alias iriswasm.sfill_nested]
theorem sfill_nested (vh wh : SimpleValidHoled) (e : List AdministrativeInstruction) :
    ∃ vh', sfill vh (sfill wh e) = sfill vh' e := by
  induction vh with
  | base bef aft =>
    cases wh with
    | base bef1 aft1 => exact ⟨.base (bef ++ bef1) (aft1 ++ aft), by simp [sfill, vToEList]⟩
    | rec_ bef1 n es wh0 aft1 =>
      exact ⟨.rec_ (bef ++ bef1) n es wh0 (aft1 ++ aft), by simp [sfill, vToEList]⟩
  | rec_ bef n es vh0 aft ih =>
    obtain ⟨vh', h⟩ := ih
    exact ⟨.rec_ bef n es vh' aft, by simp [sfill, h]⟩

@[rocq_alias iriswasm.llfill_nested]
theorem llfill_nested (vh wh : Llholed) (e : List AdministrativeInstruction) :
    ∃ vh', llfill vh (llfill wh e) = llfill vh' e := by
  obtain ⟨vh', h⟩ := llfill_trans (llh1 := wh) (llh2 := vh) (es0 := e) rfl rfl
  exact ⟨vh', h.symm⟩

end IrisWasm
