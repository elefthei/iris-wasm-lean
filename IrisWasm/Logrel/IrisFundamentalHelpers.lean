/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Logrel.IrisLogrel
import IrisWasm.Rules.Proofmode

/-! Port of `theories/iris/logrel/iris_fundamental_helpers.v`. -/

namespace IrisWasm

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm

#rocq_ignore iriswasm.iris_fundamental_helpers.take_drop_app_rewrite
  "identical to the `take_drop_app_rewrite` tactic of IrisWasm.Rules.IrisExampleHelper"
#rocq_ignore iriswasm.iris_fundamental_helpers.take_drop_app_rewrite_twice
  "identical to the `take_drop_app_rewrite_twice` tactic of IrisWasm.Rules.IrisExampleHelper"

@[rocq_alias iriswasm.big_sepL2_insert]
theorem big_sepL2_insert {GF : BundledGFunctors} {A B : Type} (l1 : List A) (l2 : List B) (i : Nat)
    (a : A) (b : B) (Φ : A → B → IProp GF) :
    ⊢ iprop(Φ a b -∗ ([∗list] a0;b0 ∈ l1;l2, Φ a0 b0) -∗
      [∗list] a0;b0 ∈ l1.set i a;l2.set i b, Φ a0 b0) := by
  iintro Ha Hl
  ihave %hlen := BigSepL2.bigSepL2_length $$ Hl
  by_cases hi : i < l1.length
  · ihave ⟨-, H⟩ := BigSepL2.bigSepL2_insert_acc (List.getElem?_eq_getElem hi)
      (List.getElem?_eq_getElem (hlen ▸ hi)) $$ Hl
    iapply H
    iexact Ha
  · rw [List.set_eq_of_length_le (by omega), List.set_eq_of_length_le (by omega)]
    iexact Hl

@[rocq_alias iriswasm.big_sepL_cond_impl]
theorem big_sepL_cond_impl {GF : BundledGFunctors} {A : Type} (Φ : Nat → A → IProp GF)
    (l : List A) :
    iprop([∗list] k ↦ y ∈ l, Φ k y) ⊣⊢ iprop([∗list] k ↦ y ∈ l, True → Φ k y) := by
  constructor <;> refine BigSepL.bigSepL_mono_of_forall ?_ <;> intro k x
  · iintro H _
    iexact H
  · iintro H
    iapply H
    ipureintro
    trivial

#rocq_ignore iriswasm.iris_fundamental_helpers.iRewrite_nil_l
  "identical to IrisWasm.iRewrite_nil_l (iris_example_helper.v)"
#rocq_ignore iriswasm.iris_fundamental_helpers.iRewrite_nil_r
  "identical to IrisWasm.iRewrite_nil_r (iris_example_helper.v)"
#rocq_ignore iriswasm.iris_fundamental_helpers.iRewrite_nil_l_ctx
  "identical to IrisWasm.iRewrite_nil_l_ctx (iris_example_helper.v)"
#rocq_ignore iriswasm.iris_fundamental_helpers.iRewrite_nil_r_ctx
  "identical to IrisWasm.iRewrite_nil_r_ctx (iris_example_helper.v)"
#rocq_ignore iriswasm.iris_fundamental_helpers.lfilledInd_push_inv
  "identical to IrisWasm.lfilledInd_push_inv (iris_rules_control.v)"

/-! ### Pure helper lemmas -/

@[rocq_alias iriswasm.const_list_of_val]
theorem const_list_of_val (vs : List Value) : constList (ofVal (.immV vs)) = true :=
  v_to_e_is_const_list vs

@[rocq_alias iriswasm.lh_depth_push_base]
theorem lh_depth_push_base (lh : Lholed) (n : Nat) (es es1 vs2 : List AdministrativeInstruction) :
    lhDepth (pushBase lh n es es1 vs2) = lhDepth lh + 1 := by
  induction lh with
  | base => rfl
  | rec_ _ _ _ _ _ ih => simp [pushBase, lhDepth, ih]

@[rocq_alias iriswasm.get_layer_push_base]
theorem get_layer_push_base (lh : Lholed) (k : Nat) (vs : List AdministrativeInstruction) (j : Nat)
    (es0 : List AdministrativeInstruction) (lh' : Lholed) (es' : List AdministrativeInstruction)
    (vs' : Nat) (es es1 es0' : List AdministrativeInstruction) :
    getLayer lh k = some (vs, j, es0, lh', es') →
    getLayer (pushBase lh vs' es es1 es0') k = some (vs, j, es0, pushBase lh' vs' es es1 es0', es') := by
  induction lh generalizing k with
  | base => simp [getLayer]
  | rec_ _ _ _ _ _ ih =>
    cases k with
    | zero => simp [getLayer, pushBase]; rintro rfl rfl rfl rfl rfl; simp
    | succ k => simp only [getLayer, pushBase]; exact ih k

@[rocq_alias iriswasm.lh_minus_base_is_empty]
theorem lh_minus_base_is_empty (lh : Lholed) (l1 l2 : List AdministrativeInstruction) :
    (lhMinus lh (.base l1 l2)).isSome = true → l1 = [] ∧ l2 = [] := by
  rcases l1 with _ | _ <;> rcases l2 with _ | _ <;> cases lh <;> simp [lhMinus]

@[rocq_alias iriswasm.lh_minus_push_base_is_Some]
theorem lh_minus_push_base_is_Some (lh : Lholed) (n : Nat) (es es1 es2 : List AdministrativeInstruction)
    (lh'' : Lholed) :
    lhDepth lh'' ≤ lhDepth lh →
    (lhMinus (pushBase lh n es es1 es2) lh'').isSome = true →
    (lhMinus lh lh'').isSome = true := by
  induction lh generalizing lh'' with
  | base vs es' =>
    cases lh'' with
    | base l1 l2 =>
      intro _ h; rcases l1 with _ | _ <;> rcases l2 with _ | _ <;> simp_all [lhMinus, pushBase]
    | rec_ => simp [lhDepth]
  | rec_ vs m es' lh es'' ih =>
    cases lh'' with
    | base l1 l2 =>
      intro _ h; rcases l1 with _ | _ <;> rcases l2 with _ | _ <;> simp_all [lhMinus, pushBase]
    | rec_ b n2 e2 lh2 a2 =>
      intro hd h
      simp only [pushBase, lhMinus] at h ⊢
      split at h
      · split <;> first | exact ih lh2 (by simp [lhDepth] at hd; omega) h | simp_all
      · simp at h

@[rocq_alias iriswasm.get_layer_push_base_0]
theorem get_layer_push_base_0 (lh : Lholed) (n : Nat) (es vs1 es1 : List AdministrativeInstruction) :
    BaseIsEmpty lh →
    getLayer (pushBase lh n es vs1 es1) (lhDepth lh) = some ([], n, es, .base vs1 es1, []) := by
  induction lh with
  | base => rintro ⟨rfl, rfl⟩; rfl
  | rec_ _ _ _ _ _ ih => intro h; exact ih h

@[rocq_alias iriswasm.lh_depth_eq_lh_minus]
theorem lh_depth_eq_lh_minus (lh'' lh : Lholed) (n : Nat) (es vs1 es1 : List AdministrativeInstruction) :
    BaseIsEmpty lh →
    lhDepth lh'' = lhDepth lh →
    (lhMinus (pushBase lh n es vs1 es1) lh'').isSome = true →
    lh'' = lh := by
  induction lh'' generalizing lh with
  | base l1 l2 =>
    cases lh with
    | base =>
      rintro ⟨rfl, rfl⟩ _ h; rcases l1 with _ | _ <;> rcases l2 with _ | _ <;> simp_all [lhMinus]
    | rec_ => simp [lhDepth]
  | rec_ b m e lh2 a ih =>
    cases lh with
    | base => simp [lhDepth]
    | rec_ b' m' e' lh' a' =>
      intro hb hd h
      simp only [pushBase, lhMinus] at h
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := hc
        rw [ih lh' hb (by simpa [lhDepth] using hd) h]
      · simp at h

@[rocq_alias iriswasm.length_lholeds_length_depth]
theorem length_lholeds_length_depth (l : List (List ValueType)) (lh : Lholed) :
    lengthLholeds l lh → l.length = lhDepth lh := by
  induction l generalizing lh with
  | nil => cases lh <;> simp [lengthLholeds, lhDepth]
  | cons a l ih => cases lh <;> simp [lengthLholeds, lhDepth]; intro _ h; exact ih _ h

@[rocq_alias iriswasm.length_lholeds_gt0_get_snoc]
theorem length_lholeds_gt0_get_snoc (lh : Lholed) (lbs : List (List ValueType)) :
    lhDepth lh > 0 →
    lengthLholeds lbs.reverse lh →
    ∃ lbs' tc, lbs = lbs' ++ [tc] := by
  intro h1 h2
  rcases lbs.eq_nil_or_concat with rfl | ⟨L, b, rfl⟩
  · have := length_lholeds_length_depth _ _ h2; simp at this; omega
  · exact ⟨L, b, by simp⟩

@[rocq_alias iriswasm.of_val_length]
theorem of_val_length (ws : List Value) : (ofVal (.immV ws)).length = ws.length := by
  simp [ofVal, vToEList]

@[rocq_alias iriswasm.base_is_empty_push_base]
theorem base_is_empty_push_base (lh : Lholed) (n : Nat) (es : List AdministrativeInstruction) :
    BaseIsEmpty (pushBase lh n es [] []) := by
  induction lh with
  | base => exact ⟨rfl, rfl⟩
  | rec_ _ _ _ _ _ ih => exact ih

@[rocq_alias iriswasm.length_lholeds_push_base]
theorem length_lholeds_push_base (lh : Lholed) (l : List (List ValueType)) (tn : List ValueType)
    (es : List AdministrativeInstruction) :
    lengthLholeds l lh →
    lengthLholeds (l ++ [tn]) (pushBase lh tn.length es [] []) := by
  induction l generalizing lh with
  | nil => cases lh <;> simp [lengthLholeds, pushBase]
  | cons a l ih => cases lh <;> simp [lengthLholeds, pushBase]; intro h1 h2; exact ⟨h1, ih _ h2⟩

@[rocq_alias iriswasm.lholed_valid_push_base]
theorem lholed_valid_push_base (lh : Lholed) (n : Nat) (es : List AdministrativeInstruction) :
    LholedValid lh → LholedValid (pushBase lh n es [] []) := by
  induction lh with
  | base => intro h; exact ⟨h, rfl⟩
  | rec_ _ _ _ _ _ ih => intro h; exact ⟨h.1, ih h.2⟩

@[rocq_alias iriswasm.last_lookup_rev]
theorem last_lookup_rev {A : Type} (l : List A) (a : A) :
    l.getLast? = some a ↔ l.reverse[0]? = some a := by
  simp [List.getLast?_eq_head?_reverse, List.head?_eq_getElem?]

@[rocq_alias iriswasm.list_app_split]
theorem list_app_split {A : Type} (ws : List A) (n1 n2 : Nat) :
    ws.length = n1 + n2 →
    ∃ ws1 ws2 : List A, ws = ws1 ++ ws2 ∧ ws1.length = n1 ∧ ws2.length = n2 :=
  fun h => ⟨ws.take n1, ws.drop n1, by simp, by simp; omega, by simp; omega⟩

@[rocq_alias iriswasm.get_layer_next]
theorem get_layer_next (lh : Lholed) (i : Nat) (vs : List AdministrativeInstruction) (n : Nat)
    (es : List AdministrativeInstruction) (lh' : Lholed) (es' vs0' : List AdministrativeInstruction)
    (n1 : Nat) (es0 vs' : List AdministrativeInstruction) (n2 : Nat)
    (es2 : List AdministrativeInstruction) (lh0 : Lholed) (es2' es0' : List AdministrativeInstruction) :
    getLayer lh (i + 1) = some (vs, n, es, lh', es') →
    getLayer lh i = some (vs0', n1, es0, .rec_ vs' n2 es2 lh0 es2', es0') →
    vs = vs' ∧ n = n2 ∧ es2 = es ∧ lh' = lh0 ∧ es' = es2' := by
  induction lh generalizing i with
  | base => simp [getLayer]
  | rec_ _ _ _ lh _ ih =>
    cases i with
    | zero =>
      intro h1 h2
      simp only [getLayer, Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨-, -, -, rfl, -⟩ := h2
      simp only [getLayer, Option.some.injEq, Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h1
      simp
    | succ i => exact ih i

@[rocq_alias iriswasm.lh_depth_frame_base]
theorem lh_depth_frame_base (lh : Lholed) (l1 l2 : List AdministrativeInstruction) :
    lhDepth (frameBase lh l1 l2) = lhDepth lh := by
  induction lh with
  | base => rfl
  | rec_ _ _ _ _ _ ih => simp [frameBase, lhDepth, ih]

@[rocq_alias iriswasm.get_layer_frame_base]
theorem get_layer_frame_base (l1 l2 : List AdministrativeInstruction) (i : Nat) (lh : Lholed)
    (vs : List AdministrativeInstruction) (n : Nat) (es : List AdministrativeInstruction)
    (lh' : Lholed) (es' : List AdministrativeInstruction) :
    getLayer lh i = some (vs, n, es, lh', es') →
    getLayer (frameBase lh l1 l2) i = some (vs, n, es, frameBase lh' l1 l2, es') := by
  induction lh generalizing i with
  | base => simp [getLayer]
  | rec_ _ _ _ _ _ ih =>
    cases i with
    | zero => simp [getLayer, frameBase]; rintro rfl rfl rfl rfl rfl; simp
    | succ i => exact ih i

private theorem get_layer_length_lholeds (L : List (List ValueType)) (lh : Lholed) (k : Nat)
    (vs' : List AdministrativeInstruction) (n2 : Nat) (es : List AdministrativeInstruction)
    (lh' : Lholed) (es2' : List AdministrativeInstruction) :
    lengthLholeds L lh → getLayer lh k = some (vs', n2, es, lh', es2') →
    ∃ ts, L[k]? = some ts ∧ n2 = ts.length := by
  induction L generalizing lh k with
  | nil => cases lh <;> simp [lengthLholeds, getLayer]
  | cons a L ih =>
    cases lh with
    | base => simp [lengthLholeds]
    | rec_ b m e lh0 a' =>
      intro ⟨h1, h2⟩ h
      cases k with
      | zero => simp [getLayer] at h; exact ⟨a, rfl, by omega⟩
      | succ k => simpa using ih lh0 k h2 h

@[rocq_alias iriswasm.get_layer_lookup_lh_lengths]
theorem get_layer_lookup_lh_lengths (l : List (List ValueType)) (lh : Lholed) (i : Nat)
    (ts : List ValueType) (vs' : List AdministrativeInstruction) (n2 : Nat)
    (es : List AdministrativeInstruction) (lh' : Lholed) (es2' : List AdministrativeInstruction) :
    lengthLholeds l.reverse lh →
    l[i]? = some ts →
    getLayer lh (lhDepth lh - (i + 1)) = some (vs', n2, es, lh', es2') →
    n2 = ts.length := by
  intro hlen hlook hlay
  have hdep := length_lholeds_length_depth _ _ hlen
  obtain ⟨ts', h1, rfl⟩ := get_layer_length_lholeds _ _ _ _ _ _ _ _ hlen hlay
  have hlt : i < l.length := (List.getElem?_eq_some_iff.1 hlook).1
  rw [List.getElem?_reverse (by simp at hdep; omega)] at h1
  simp at hdep
  rw [show l.length - 1 - (lhDepth lh - (i + 1)) = i by omega, hlook] at h1
  cases h1; rfl

@[rocq_alias iriswasm.lh_minus_is_Some_frame_base]
theorem lh_minus_is_Some_frame_base (lh lh'' : Lholed) (l1 l2 : List AdministrativeInstruction) :
    (lhMinus (frameBase lh l1 l2) lh'').isSome = true → (lhMinus lh lh'').isSome = true := by
  induction lh generalizing lh'' with
  | base =>
    cases lh'' with
    | base b a => rcases b with _ | _ <;> rcases a with _ | _ <;> simp [lhMinus, frameBase]
    | rec_ => simp [lhMinus, frameBase]
  | rec_ vs m es' lh es ih =>
    cases lh'' with
    | base b a => rcases b with _ | _ <;> rcases a with _ | _ <;> simp [lhMinus, frameBase]
    | rec_ b n2 e2 lh2 a2 =>
      simp only [frameBase, lhMinus]
      split <;> first | exact ih lh2 | simp

/-- Coq states this with the 4-tuple pattern `(vs,n,lh',es')` against the (left-nested) 5-tuple
returned by `get_layer`; the Lean tuple is right-nested, so all five components are named. -/
@[rocq_alias iriswasm.get_layer_lh_depth]
theorem get_layer_lh_depth (lh : Lholed) (i : Nat) (vs : List AdministrativeInstruction) (n : Nat)
    (es : List AdministrativeInstruction) (lh' : Lholed) (es' : List AdministrativeInstruction) :
    i < lhDepth lh →
    getLayer lh (lhDepth lh - (i + 1)) = some (vs, n, es, lh', es') →
    lhDepth lh' = i := by
  induction lh generalizing i with
  | base => simp [lhDepth]
  | rec_ _ _ _ lh _ ih =>
    intro hlt h
    simp only [lhDepth] at hlt h
    rcases hk : lhDepth lh - i with _ | k
    · have : lhDepth lh + 1 - (i + 1) = 0 := by omega
      rw [this] at h; simp [getLayer] at h; obtain ⟨-, -, -, rfl, -⟩ := h; omega
    · have : lhDepth lh + 1 - (i + 1) = (lhDepth lh - (i + 1)) + 1 := by omega
      rw [this] at h; exact ih i (by omega) h

@[rocq_alias iriswasm.lh_minus_push_base_Some]
theorem lh_minus_push_base_Some (lh : Lholed) (n : Nat) (es vs1 es2 : List AdministrativeInstruction) :
    BaseIsEmpty lh →
    lhMinus (pushBase lh n es vs1 es2) lh = some (.rec_ [] n es (.base vs1 es2) []) := by
  induction lh with
  | base => rintro ⟨rfl, rfl⟩; rfl
  | rec_ _ _ _ _ _ ih => intro h; simp [pushBase, lhMinus, ih h]

@[rocq_alias iriswasm.push_base_lh_minus_is_Some]
theorem push_base_lh_minus_is_Some (lh : Lholed) (n : Nat) (es vs1 es2 : List AdministrativeInstruction)
    (lh'' : Lholed) :
    (lhMinus lh lh'').isSome = true → (lhMinus (pushBase lh n es vs1 es2) lh'').isSome = true := by
  induction lh generalizing lh'' with
  | base =>
    cases lh'' with
    | base b a => rcases b with _ | _ <;> rcases a with _ | _ <;> simp [lhMinus, pushBase]
    | rec_ => simp [lhMinus]
  | rec_ vs m es' lh es ih =>
    cases lh'' with
    | base b a => rcases b with _ | _ <;> rcases a with _ | _ <;> simp [lhMinus, pushBase]
    | rec_ b n2 e2 lh2 a2 =>
      simp only [pushBase, lhMinus]
      split <;> first | exact ih lh2 | simp

@[rocq_alias iriswasm.to_val_fmap]
theorem to_val_fmap (ws : List Value) :
    toVal (ws.map fun v => AdministrativeInstruction.basic (.const v)) = some (.immV ws) :=
  to_of_val (.immV ws)

/-! ### Pulling values out of the base of a `ValidHoled` -/

@[rocq_alias iriswasm.pull_base_l_drop_len]
def pullBaseLDropLen : {i : Nat} → ValidHoled i → Nat → ValidHoled i × List Value
  | _, .base vs es, len => (.base (vs.take len) es, vs.drop len)
  | _, .rec_ vs m es' lh' es, len =>
    let (lh'', l1) := pullBaseLDropLen lh' len
    (.rec_ vs m es' lh'' es, l1)

@[rocq_alias iriswasm.vfill_pull_base_l_take_len]
theorem vfill_pull_base_l_take_len {i : Nat} (vh : ValidHoled i) (len : Nat)
    (es : List AdministrativeInstruction) (vh' : ValidHoled i) (vs : List Value) :
    pullBaseLDropLen vh len = (vh', vs) →
    vfill vh es = vfill vh' ((vs.map fun x => AdministrativeInstruction.basic (.const x)) ++ es) := by
  induction vh generalizing vs with
  | base bef aft =>
    intro h; simp only [pullBaseLDropLen, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    simp only [vfill, vToEList, List.map_take, List.map_drop, List.append_assoc]
    rw [← List.append_assoc (List.take _ _), List.take_append_drop]
  | rec_ bef m es0 vh aft ih =>
    intro h
    simp only [pullBaseLDropLen] at h
    rcases hp : pullBaseLDropLen vh len with ⟨a, b⟩
    rw [hp] at h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    simp [vfill, ih _ _ hp]

@[rocq_alias iriswasm.lh_depth_pull_base_l_take_len]
theorem lh_depth_pull_base_l_take_len {i : Nat} (vh : ValidHoled i) (len : Nat) (vh' : ValidHoled i)
    (vs : List Value) :
    pullBaseLDropLen vh len = (vh', vs) →
    lhDepth (lhOfVh vh) = lhDepth (lhOfVh vh') := by
  induction vh generalizing vs with
  | base bef aft =>
    intro h; simp only [pullBaseLDropLen, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | rec_ bef m es0 vh aft ih =>
    intro h
    simp only [pullBaseLDropLen] at h
    rcases hp : pullBaseLDropLen vh len with ⟨a, b⟩
    rw [hp] at h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    simp [lhOfVh, lhDepth, ih _ _ hp]

@[rocq_alias iriswasm.length_pull_base_l_take_len]
theorem length_pull_base_l_take_len {i : Nat} (vh : ValidHoled i) (len : Nat) (vh' : ValidHoled i)
    (vs vs' : List Value) :
    getBaseL vh = vs' →
    pullBaseLDropLen vh len = (vh', vs) →
    vs.length = vs'.length - len := by
  induction vh generalizing vs with
  | base bef aft =>
    intro hb h; simp only [pullBaseLDropLen, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    subst hb; simp [getBaseL]
  | rec_ bef m es0 vh aft ih =>
    intro hb h
    simp only [pullBaseLDropLen] at h
    rcases hp : pullBaseLDropLen vh len with ⟨a, b⟩
    rw [hp] at h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    exact ih _ _ hb hp

@[rocq_alias iriswasm.take_drop_pull_base_l_take_len]
theorem take_drop_pull_base_l_take_len {i : Nat} (vh : ValidHoled i) (len : Nat) (vh' : ValidHoled i)
    (vs vs' : List Value) :
    len ≤ vs'.length →
    getBaseL vh = vs' →
    pullBaseLDropLen vh len = (vh', vs) →
    vs' = vs'.take len ++ vs := by
  induction vh generalizing vs with
  | base bef aft =>
    intro _ hb h; simp only [pullBaseLDropLen, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    subst hb; simp [getBaseL]
  | rec_ bef m es0 vh aft ih =>
    intro hl hb h
    simp only [pullBaseLDropLen] at h
    rcases hp : pullBaseLDropLen vh len with ⟨a, b⟩
    rw [hp] at h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    exact ih _ _ hl hb hp

@[rocq_alias iriswasm.vfill_label]
theorem vfill_label {i : Nat} (vh : ValidHoled i) (n : Nat) (es e : List AdministrativeInstruction) :
    [AdministrativeInstruction.label n es (vfill vh e)] = vfill (ValidHoled.rec_ [] n es vh []) e := by
  simp [vfill, vToEList]

@[rocq_alias iriswasm.sfill_label]
theorem sfill_label (vh : SimpleValidHoled) (n : Nat) (es e : List AdministrativeInstruction) :
    [AdministrativeInstruction.label n es (sfill vh e)] = sfill (.rec_ [] n es vh []) e := by
  simp [sfill, vToEList]

@[rocq_alias iriswasm.llfill_label]
theorem llfill_label (vh : Llholed) (n : Nat) (es e : List AdministrativeInstruction) :
    [AdministrativeInstruction.label n es (llfill vh e)] = llfill (.label [] n es vh []) e := by
  simp [llfill, vToEList]

@[rocq_alias iriswasm.lh_depth_ge]
theorem lh_depth_ge {i : Nat} (vh : ValidHoled i) (p : Nat) :
    lhDepth (lhOfVh vh) = p → i ≥ p := by
  intro h; subst h
  induction vh with
  | base => simp [lhOfVh, lhDepth]
  | rec_ _ _ _ _ _ ih => simp only [lhOfVh, lhDepth]; omega

@[rocq_alias iriswasm.vh_destruct]
theorem vh_destruct {i : Nat} (vh : ValidHoled i) :
    (∃ vs es, vh = ValidHoled.base (n := i) vs es) ∨
    (∃ (vs : List Value) (n : Nat) (es' : List AdministrativeInstruction) (vh' : ValidHoled i)
      (es : List AdministrativeInstruction), vhIncrease vh = ValidHoled.rec_ vs n es' vh' es) := by
  cases vh with
  | base vs es => exact .inl ⟨vs, es, rfl⟩
  | rec_ vs n es' vh es => exact .inr ⟨vs, n, es', vhIncrease vh, es, rfl⟩

@[rocq_alias iriswasm.lh_depth_le_None_false]
theorem lh_depth_le_None_false {i : Nat} (vh : ValidHoled (i + 1)) :
    lhDepth (lhOfVh vh) ≤ i → vhDecrease vh = none → False := by
  induction i with
  | zero =>
    cases vh with
    | base => simp [vhDecrease]
    | rec_ _ _ _ vh _ => simp [lhOfVh, lhDepth]
  | succ i ih =>
    cases vh with
    | base => simp [vhDecrease]
    | rec_ _ _ _ vh _ =>
      simp only [lhOfVh, lhDepth, vhDecrease, Option.map_eq_none_iff]
      intro h1 h2; exact ih vh (by omega) h2

@[rocq_alias iriswasm.lh_depth_le_vh_decrease]
theorem lh_depth_le_vh_decrease {i : Nat} (vh : ValidHoled (i + 1)) :
    lhDepth (lhOfVh vh) ≤ i → ∃ vs', vhDecrease vh = some vs' := by
  intro h
  rcases hd : vhDecrease vh with _ | vh'
  · exact (lh_depth_le_None_false vh h hd).elim
  · exact ⟨vh', rfl⟩

@[rocq_alias iriswasm.lh_depth_vh_decrease_eq]
theorem lh_depth_vh_decrease_eq {i : Nat} (vh : ValidHoled (i + 1)) (vh' : ValidHoled i) :
    vhDecrease vh = some vh' → lhDepth (lhOfVh vh) = lhDepth (lhOfVh vh') := by
  induction i with
  | zero =>
    cases vh with
    | base => simp only [vhDecrease, Option.some.injEq]; rintro rfl; rfl
    | rec_ => simp [vhDecrease]
  | succ i ih =>
    cases vh with
    | base => simp only [vhDecrease, Option.some.injEq]; rintro rfl; rfl
    | rec_ _ _ _ vh _ =>
      simp only [vhDecrease, Option.map_eq_some_iff]
      rintro ⟨x, hx, rfl⟩
      simp [lhOfVh, lhDepth, ih vh x hx]

@[rocq_alias iriswasm.get_base_l_vh_decrease_eq]
theorem get_base_l_vh_decrease_eq {i : Nat} (vh : ValidHoled (i + 1)) (vh' : ValidHoled i) :
    vhDecrease vh = some vh' → getBaseL vh = getBaseL vh' := by
  induction i with
  | zero =>
    cases vh with
    | base => simp only [vhDecrease, Option.some.injEq]; rintro rfl; rfl
    | rec_ => simp [vhDecrease]
  | succ i ih =>
    cases vh with
    | base => simp only [vhDecrease, Option.some.injEq]; rintro rfl; rfl
    | rec_ _ _ _ vh _ =>
      simp only [vhDecrease, Option.map_eq_some_iff]
      rintro ⟨x, hx, rfl⟩
      exact ih vh x hx

@[rocq_alias iriswasm.get_layer_push_inv]
theorem get_layer_push_inv (lh : Lholed) (n : Nat) (es v e : List AdministrativeInstruction) (i : Nat)
    (vs' : List AdministrativeInstruction) (k : Nat) (es' : List AdministrativeInstruction)
    (lh' : Lholed) (es'' : List AdministrativeInstruction) :
    lhDepth lh - i > 0 →
    getLayer (pushBase lh n es v e) (lhDepth lh - (i + 1)) = some (vs', k, es', lh', es'') →
    ∃ lh0, lh' = pushBase lh0 n es v e ∧
      getLayer lh (lhDepth lh - (i + 1)) = some (vs', k, es', lh0, es'') := by
  intro hgt
  have key : ∀ (lh : Lholed) (j : Nat), j < lhDepth lh →
      getLayer (pushBase lh n es v e) j = some (vs', k, es', lh', es'') →
      ∃ lh0, lh' = pushBase lh0 n es v e ∧ getLayer lh j = some (vs', k, es', lh0, es'') := by
    intro lh
    induction lh with
    | base => simp [lhDepth]
    | rec_ b m c lh d ih =>
      intro j hj h
      cases j with
      | zero =>
        simp only [pushBase, getLayer, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
        exact ⟨lh, rfl, rfl⟩
      | succ j => exact ih j (by simp [lhDepth] at hj; omega) h
  exact key lh _ (by omega)

/-! ### Inhabited instances -/

#rocq_ignore iriswasm.global_inhabited "Global derives Inhabited in Wasm.Datatypes"
#rocq_ignore iriswasm.value_inhabited "Value derives Inhabited in Wasm.Datatypes"
#rocq_ignore iriswasm.function_closure_inhabited "FunctionClosure derives Inhabited in Wasm.Datatypes"
#rocq_ignore iriswasm.lholed_inhabited "Lholed derives Inhabited in Wasm.Datatypes"
#rocq_ignore iriswasm.function_type_inhabited "FunctionType derives Inhabited in Wasm.Datatypes"
#rocq_ignore iriswasm.hostfuncidx_inhabited "Hostfuncidx derives Inhabited in Wasm.Datatypes"

@[rocq_alias iriswasm.valid_holed_inhabited]
instance validHoledInhabited (j : Nat) : Inhabited (ValidHoled j) := ⟨.base [] []⟩

@[rocq_alias iriswasm.simple_valid_holed_inhabited]
instance simpleValidHoledInhabited : Inhabited SimpleValidHoled := ⟨.base [] []⟩

@[rocq_alias iriswasm.llholed_inhabited]
instance llholedInhabited : Inhabited Llholed := ⟨.base [] []⟩

@[rocq_alias iriswasm.const_list_map]
theorem const_list_map (ws1 : List Value) :
    constList (ws1.map fun x => AdministrativeInstruction.basic (.const x)) = true := by
  exact v_to_e_is_const_list ws1

@[rocq_alias iriswasm.lfilled_simple_get_base_pull]
theorem lfilled_simple_get_base_pull (j : Nat) (sh : SimpleValidHoled)
    (e LI : List AdministrativeInstruction) (ws1 ws2 : List Value) :
    simpleGetBaseL sh = ws1 ++ ws2 →
    lfilled j (lhOfSh sh) e LI = true →
    ∃ lh, lfilled j lh (ofVal (.immV ws2) ++ e) LI = true := by
  induction sh generalizing j e LI with
  | base bef aft =>
    intro hb hf
    rw [lfilled_Ind_Equivalent] at hf
    cases hf with
    | lfilledBase _ _ _ _ =>
      simp only [simpleGetBaseL] at hb; subst hb
      refine ⟨.base (vToEList ws1) aft, (lfilled_Ind_Equivalent _ _ _ _).2 ?_⟩
      have := LfilledInd.lfilledBase (vToEList ws1) (ofVal (.immV ws2) ++ e) aft
        (v_to_e_is_const_list ws1)
      simpa [ofVal, vToEList, List.append_assoc] using this
  | rec_ bef n es0 sh aft ih =>
    intro hb hf
    rw [lfilled_Ind_Equivalent] at hf
    cases hf with
    | lfilledRec k _ _ _ _ _ _ LI' hc hf' =>
      obtain ⟨lh, hlh⟩ := ih k e LI' hb ((lfilled_Ind_Equivalent _ _ _ _).2 hf')
      exact ⟨.rec_ _ n es0 lh aft, (lfilled_Ind_Equivalent _ _ _ _).2
        (.lfilledRec _ _ _ _ _ _ _ _ hc ((lfilled_Ind_Equivalent _ _ _ _).1 hlh))⟩

@[rocq_alias iriswasm.lfilled_get_base_pull]
theorem lfilled_get_base_pull {i : Nat} (j : Nat) (vh : ValidHoled i)
    (e LI : List AdministrativeInstruction) (ws1 ws2 : List Value) :
    getBaseL vh = ws1 ++ ws2 →
    lfilled j (lhOfVh vh) e LI = true →
    ∃ lh, lfilled j lh (ofVal (.immV ws2) ++ e) LI = true := by
  induction vh generalizing j e LI with
  | base bef aft =>
    intro hb hf
    rw [lfilled_Ind_Equivalent] at hf
    cases hf with
    | lfilledBase _ _ _ _ =>
      simp only [getBaseL] at hb; subst hb
      refine ⟨.base (vToEList ws1) aft, (lfilled_Ind_Equivalent _ _ _ _).2 ?_⟩
      have := LfilledInd.lfilledBase (vToEList ws1) (ofVal (.immV ws2) ++ e) aft
        (v_to_e_is_const_list ws1)
      simpa [ofVal, vToEList, List.append_assoc] using this
  | rec_ bef n es0 vh aft ih =>
    intro hb hf
    rw [lfilled_Ind_Equivalent] at hf
    cases hf with
    | lfilledRec k _ _ _ _ _ _ LI' hc hf' =>
      obtain ⟨lh, hlh⟩ := ih k e LI' hb ((lfilled_Ind_Equivalent _ _ _ _).2 hf')
      exact ⟨.rec_ _ n es0 lh aft, (lfilled_Ind_Equivalent _ _ _ _).2
        (.lfilledRec _ _ _ _ _ _ _ _ hc ((lfilled_Ind_Equivalent _ _ _ _).1 hlh))⟩

/-! ### `to_val` on host calls -/

/-- Some element of `llfill vh [e]` is `e` itself or a `label`/`local` (not in Coq). -/
private theorem llfill_mem_witness (vh : Llholed) (e : AdministrativeInstruction) :
    ∃ a ∈ llfill vh [e], a = e ∨ (∃ n es LI, a = .label n es LI) ∨
      (∃ n f LI, a = .local n f LI) := by
  cases vh with
  | base => exact ⟨e, by simp [llfill], .inl rfl⟩
  | label b n es lh a =>
    exact ⟨.label n es (llfill lh [e]), by simp [llfill], .inr (.inl ⟨_, _, _, rfl⟩)⟩
  | «local» b n f lh a =>
    exact ⟨.local n f (llfill lh [e]), by simp [llfill], .inr (.inr ⟨_, _, _, rfl⟩)⟩

private def llOfVh : {i : Nat} → ValidHoled i → Llholed
  | _, .base b a => .base b a
  | _, .rec_ b n es vh a => .label b n es (llOfVh vh) a

private theorem vfill_llOfVh {i : Nat} (vh : ValidHoled i) (es : List AdministrativeInstruction) :
    vfill vh es = llfill (llOfVh vh) es := by
  induction vh with
  | base => rfl
  | rec_ _ _ _ _ _ ih => simp [vfill, llfill, llOfVh, ih]

@[rocq_alias iriswasm.to_val_call_host_label_inv]
theorem to_val_call_host_label_inv (n : Nat) (es1 es : List AdministrativeInstruction)
    (tf : FunctionType) (h : Hostfuncidx) (w : List Value) (vh : Llholed) :
    toVal [.label n es1 es] = some (.callHostV tf h w vh) →
    ∃ vh', vh = .label [] n es1 vh' [] ∧ es = llfill vh' [.callHost tf h w] := by
  intro hh
  rcases toVal_label_some hh with ⟨_, vh0, hL⟩ | ⟨sh, hL⟩ | ⟨tf', h', w', vh', hL⟩ <;>
    rw [toVal_singleton, toValInstr_label, hL] at hh
  · rcases hd : vhDecrease (ValidHoled.rec_ [] n es1 vh0 []) with _ | x <;>
      simp [hd, valOfValNotVal] at hh
  · simp [valOfValNotVal] at hh
  simp [valOfValNotVal] at hh
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hh
  exact ⟨vh', rfl, (of_to_val _ _ hL).symm⟩

@[rocq_alias iriswasm.to_es_list_llfill_contr]
theorem to_es_list_llfill_contr (es : List BasicInstruction) (vh' : Llholed) (tf : FunctionType)
    (h : Hostfuncidx) (w : List Value) :
    toEList es = llfill vh' [.callHost tf h w] → False := by
  intro heq
  obtain ⟨a, ha, hor⟩ := llfill_mem_witness vh' (.callHost tf h w)
  rw [← heq] at ha
  simp [toEList] at ha
  obtain ⟨x, -, rfl⟩ := ha
  rcases hor with h | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ <;> cases h

@[rocq_alias iriswasm.llfill_local]
theorem llfill_local (vh : Llholed) (n : Nat) (f : Frame) (e : List AdministrativeInstruction) :
    [AdministrativeInstruction.local n f (llfill vh e)] = llfill (.local [] n f vh []) e := by
  simp [llfill, vToEList]

@[rocq_alias iriswasm.to_val_local_imm_none]
theorem to_val_local_imm_none (e : Expr) (v : List Value) (n : Nat) (f : Frame) :
    toVal e = some (.immV v) → toVal [.local n f e] = none := by
  intro h; rw [toVal_singleton, toValInstr_local, h]; rfl

@[rocq_alias iriswasm.to_val_local_trap_none]
theorem to_val_local_trap_none (e : Expr) (n : Nat) (f : Frame) :
    toVal e = some .trapV → toVal [.local n f e] = none := by
  intro h; rw [toVal_singleton, toValInstr_local, h]; rfl

@[rocq_alias iriswasm.to_val_local_br_none]
theorem to_val_local_br_none {i : Nat} (e : Expr) (n : Nat) (f : Frame) (vh : ValidHoled i) :
    toVal e = some (.brV vh) → toVal [.local n f e] = none := by
  intro h; rw [toVal_singleton, toValInstr_local, h]; rfl

@[rocq_alias iriswasm.to_val_llfill_trap]
theorem to_val_llfill_trap (vh : Llholed) (v : Val) :
    toVal (llfill vh [.trap]) = some v → vh = .base [] [] := by
  intro hv
  have ho := of_to_val _ _ hv
  have key : ∀ (lh : Llholed) (e : AdministrativeInstruction), isConst e = false →
      (∀ n es LI, e ≠ .label n es LI) → (∀ n f LI, e ≠ .local n f LI) → e ≠ .trap →
      llfill lh [e] = llfill vh [.trap] → False := fun lh e hc hl hlo ht heq =>
    ht (llfill_first_values (vs := []) (vs' := []) (by simpa using heq) rfl rfl rfl hc rfl hl
      (by simp) hlo (by simp)).1
  rcases v with l | _ | @⟨i, vh0⟩ | sh | ⟨tf, h, cvs, lh⟩ <;> simp only [ofVal] at ho
  · obtain ⟨a, ha, hor⟩ := llfill_mem_witness vh .trap
    rw [← ho] at ha
    simp [vToEList] at ha
    obtain ⟨x, -, rfl⟩ := ha
    rcases hor with h | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ <;> cases h
  · cases vh with
    | base b a =>
      rcases b with _ | ⟨_, _⟩ <;> rcases a with _ | ⟨_, _⟩ <;> simp [llfill, vToEList] at ho ⊢
    | label b => rcases b with _ | ⟨_, _⟩ <;> simp [llfill, vToEList] at ho
    | «local» b => rcases b with _ | ⟨_, _⟩ <;> simp [llfill, vToEList] at ho
  · rw [vfill_llOfVh] at ho
    exact (key _ _ rfl (by simp) (by simp) (by simp) ho).elim
  · rw [sfill_to_llfill] at ho
    exact (key _ _ rfl (by simp) (by simp) (by simp) ho).elim
  · exact (key _ _ rfl (by simp) (by simp) (by simp) ho).elim

namespace IrisFundamentalHelpers

/-- Coq `to_val_trapV_lfilled_None` of `iris_fundamental_helpers.v` (the same Coq name in
`iris_reduce_properties.v` is `IrisWasm.to_val_trapV_lfilled_None`). -/
@[rocq_alias iriswasm.iris_fundamental_helpers.to_val_trapV_lfilled_None]
theorem to_val_trapV_lfilled_None (n : Nat) (e : List AdministrativeInstruction) (vh : Llholed) :
    toVal [.label n e (llfill vh (ofVal .trapV))] = none := by
  rcases hs : toVal [.label n e (llfill vh (ofVal .trapV))] with _ | v
  · rfl
  · rw [llfill_label] at hs
    cases to_val_llfill_trap _ _ hs

end IrisFundamentalHelpers

@[rocq_alias iriswasm.merge_values_list_v_to_e_list]
theorem merge_values_list_v_to_e_list (l : List Value) :
    mergeValuesList ((vToEList l).map toValInstr) = .val (.immV l) := by
  exact toVal_eq_some_iff.1 (to_of_val (.immV l))

@[rocq_alias iriswasm.flatten_left_leaves]
def flattenLeftLeaves : Llholed → List Value
  | .base v1 _ => v1
  | .label v1 _ _ vh _ => v1 ++ flattenLeftLeaves vh
  | .local v1 _ _ vh _ => v1 ++ flattenLeftLeaves vh

@[rocq_alias iriswasm.flatten_right_leaves]
def flattenRightLeaves : Llholed → List AdministrativeInstruction
  | .base _ v1 => v1
  | .label _ _ _ vh v1 => v1 ++ flattenRightLeaves vh
  | .local _ _ _ vh v1 => v1 ++ flattenRightLeaves vh

@[rocq_alias iriswasm.is_basic_Forall]
theorem is_basic_Forall (l0 : List AdministrativeInstruction) :
    isBasicExpr l0 ↔ ∀ a ∈ l0, isBasic a := by
  induction l0 <;> simp_all [isBasicExpr]

@[rocq_alias iriswasm.llholed_basic_right_leaves]
theorem llholed_basic_right_leaves (vh : Llholed) :
    llholedBasic vh ↔ ∀ a ∈ flattenRightLeaves vh, isBasic a := by
  induction vh <;> simp_all [llholedBasic, flattenRightLeaves, is_basic_Forall, or_imp, forall_and]

@[rocq_alias iriswasm.elem_of_const_false]
theorem elem_of_const_false (l : List Value) (a : AdministrativeInstruction) :
    isConst a = false → a ∈ vToEList l → False := by
  intro ha hin
  simp [vToEList] at hin
  obtain ⟨x, -, rfl⟩ := hin
  simp [isConst] at ha

@[rocq_alias iriswasm.vfill_eq_find_call_host]
theorem vfill_eq_find_call_host (e : List AdministrativeInstruction) (vh vh' : Llholed)
    (tf : FunctionType) (h : Hostfuncidx) (ves : List Value) :
    llholedBasic vh →
    constList e = true →
    llfill vh e = llfill vh' [.callHost tf h ves] →
    AdministrativeInstruction.callHost tf h ves ∈ flattenRightLeaves vh := by
  induction vh generalizing vh' with
  | base bef aft =>
    intro hb he heq
    obtain ⟨a, ha, hor⟩ := llfill_mem_witness vh' (.callHost tf h ves)
    rw [← heq] at ha
    simp only [llfill, List.mem_append] at ha
    simp only [llholedBasic, flattenRightLeaves] at hb ⊢
    rcases ha with (ha | ha) | ha
    · exact (elem_of_const_false bef a
        (by rcases hor with rfl | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> rfl) ha).elim
    · simp only [constList, List.all_eq_true] at he
      have := he a ha
      rcases hor with rfl | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> simp [isConst] at this
    · have := (is_basic_Forall aft).1 hb a ha
      rcases hor with rfl | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩
      · exact ha
      all_goals simp [isBasic] at this
  | label bef n es0 lh aft ih =>
    intro hb he heq
    simp only [llholedBasic, flattenRightLeaves] at hb ⊢
    simp only [llfill] at heq
    cases vh' with
    | base bef' aft' =>
      simp only [llfill, List.append_assoc, List.singleton_append] at heq
      have := first_values (vToEList bef) _ aft (vToEList bef') _ aft' rfl rfl
        (v_to_e_is_const_list _) (v_to_e_is_const_list _) heq
      simp at this
    | label bef' n' es' lh' aft' =>
      obtain ⟨-, h1, rfl⟩ := first_values (vToEList bef) _ aft (vToEList bef') _ aft' rfl rfl
        (v_to_e_is_const_list _) (v_to_e_is_const_list _) heq
      simp only [AdministrativeInstruction.label.injEq] at h1
      exact List.mem_append_right _ (ih lh' hb.2 he h1.2.2)
    | «local» bef' n' f' lh' aft' =>
      have := first_values (vToEList bef) _ aft (vToEList bef') _ aft' rfl rfl
        (v_to_e_is_const_list _) (v_to_e_is_const_list _) heq
      simp at this
  | «local» bef n f0 lh aft ih =>
    intro hb he heq
    simp only [llholedBasic, flattenRightLeaves] at hb ⊢
    simp only [llfill] at heq
    cases vh' with
    | base bef' aft' =>
      simp only [llfill, List.append_assoc, List.singleton_append] at heq
      have := first_values (vToEList bef) _ aft (vToEList bef') _ aft' rfl rfl
        (v_to_e_is_const_list _) (v_to_e_is_const_list _) heq
      simp at this
    | label bef' n' es' lh' aft' =>
      have := first_values (vToEList bef) _ aft (vToEList bef') _ aft' rfl rfl
        (v_to_e_is_const_list _) (v_to_e_is_const_list _) heq
      simp at this
    | «local» bef' n' f' lh' aft' =>
      obtain ⟨-, h1, rfl⟩ := first_values (vToEList bef) _ aft (vToEList bef') _ aft' rfl rfl
        (v_to_e_is_const_list _) (v_to_e_is_const_list _) heq
      simp only [AdministrativeInstruction.local.injEq] at h1
      exact List.mem_append_right _ (ih lh' hb.2 he h1.2.2)

@[rocq_alias iriswasm.to_val_immV_AI_local_is_basic_None]
theorem to_val_immV_AI_local_is_basic_None (m : Nat) (f : Frame) (n : Nat)
    (e : List AdministrativeInstruction) (vh : Llholed) (ws : List Value) :
    llholedBasic vh →
    toVal [.local m f [.label n e (llfill vh (ofVal (.immV ws)))]] = none := by
  intro hb
  rcases hs : toVal [.local m f [.label n e (llfill vh (ofVal (.immV ws)))]] with _ | v
  · rfl
  exfalso
  obtain ⟨tf, h, w, vh', rfl⟩ := to_val_local_inv _ _ _ _ hs
  obtain ⟨LI, heq, hLI⟩ := to_val_call_host_rec_local _ [] m f vh' [] tf h w hs
  simp [vToEList] at heq
  subst heq
  obtain ⟨vh'', -, heq2⟩ := to_val_call_host_label_inv _ _ _ _ _ _ _ hLI
  have hin := vfill_eq_find_call_host _ _ _ _ _ _ hb (v_to_e_is_const_list ws) heq2
  have := (llholed_basic_right_leaves vh).1 hb _ hin
  simp [isBasic] at this

/-! ### Logical-relation helpers -/

variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF] [LogrelNaInvs GF]

attribute [local instance] WasmG.invGS

/-- `na_own logrel_nais E`. -/
local notation "logrelNais" => LogrelNaInvs.logrelNais (GF := GF)

omit [LogrelNaInvs GF] in
@[rocq_alias iriswasm.interp_value_type_of]
theorem interp_value_type_of (v : Value) : ⊢ (interpValue (typeof v) v : IProp GF) := by
  cases v <;> exact BI.pure_intro ⟨_, rfl⟩

omit [LogrelNaInvs GF] in
@[rocq_alias iriswasm.wp_label_push_inv]
theorem wp_label_push_inv (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF)
    (es : List AdministrativeInstruction) (i : Nat) (lh : Lholed) (n : Nat)
    (es' l1 l2 : List AdministrativeInstruction) :
    constList l1 = true →
    iprop(WP ([AdministrativeInstruction.label n es' (l1 ++ es ++ l2)] : Expr) @ s ; E CTX i ; lh
      {{ v, Φ v }}) ⊢
      iprop(WP es @ s ; E CTX (i + 1) ; (pushBase lh n es' l1 l2) {{ v, Φ v }}) := by
  intro hconst
  unfold wpWasmCtx
  iintro H %LI %hLI
  rw [lfilled_Ind_Equivalent] at hLI
  iapply H $$ %LI %(by rw [lfilled_Ind_Equivalent]; exact lfilledInd_push_inv i lh n es' es LI l1 l2 hconst hLI)

omit [LogrelNaInvs GF] in
@[rocq_alias iriswasm.wp_label_push_nil_inv]
theorem wp_label_push_nil_inv (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF)
    (es : List AdministrativeInstruction) (i : Nat) (lh : Lholed) (n : Nat)
    (es' : List AdministrativeInstruction) :
    iprop(WP ([AdministrativeInstruction.label n es' es] : Expr) @ s ; E CTX i ; lh {{ v, Φ v }}) ⊢
      iprop(WP es @ s ; E CTX (i + 1) ; (pushBase lh n es' [] []) {{ v, Φ v }}) := by
  refine Entails.trans ?_ (wp_label_push_inv s E Φ es i lh n es' [] [] rfl)
  simp only [List.nil_append, List.append_nil]
  exact .rfl

omit [LogrelNaInvs GF] in
@[rocq_alias iriswasm.push_base_return]
theorem push_base_return (v : List Value) (lh : Lholed) (tm : List ValueType) (n : Nat)
    (es : List AdministrativeInstruction) (f : Frame) (Φf : Frame → IProp GF) :
    LholedValid lh →
    ⊢ iprop(interpVal tm (.immV v) -∗ ↪[frame] f -∗ Φf f -∗
      (∀ f, ↪[frame] f ∗ Φf f -∗
        WP (ofVal (.immV v)) CTX (lhDepth lh) ; lh
          {{ vs, interpVal tm vs ∗ ∃ f, ↪[frame] f ∗ Φf f }}) -∗
      WP (ofVal (.immV v)) CTX (lhDepth lh + 1) ; (pushBase lh n es [] [])
        {{ vs, interpVal tm vs ∗ ∃ f, ↪[frame] f ∗ Φf f }}) := by
  -- the Coq proof inducts on `lh`, but its recursive case already works for every `lh`
  intro _
  iintro _ Hf Hfv H
  iapply wp_label_push_nil_inv
  rw [show ([AdministrativeInstruction.label n es (ofVal (.immV v))] : Expr) =
      [AdministrativeInstruction.label n es (ofVal (.immV v))] ++ [] from rfl]
  iapply wp_seq_can_trap_ctx _ _ _ (fun w => iprop(⌜w = .immV v⌝)) _ _ _ _ Φf f
  isplitr
  · iintro %h
    cases h
  isplitr
  · iintro %f1 ⟨Hf1, Hfv1⟩
    isplitl []
    · iunfold interpVal
      ileft
      ipureintro
      rfl
    · iexists f1
      iframe
  isplitl [Hf]
  · iexact Hf
  isplitl [Hfv]
  · iintro Hf
    iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ [Hf]
    · iapply wp_label_value (Φ := fun w => iprop(⌜w = .immV v⌝)) (to_of_val _) $$ Hf
      inext
      ipureintro
      rfl
    · iintro %w ⟨%hw, Hf⟩
      isplitl []
      · iright
        ipureintro
        exact hw
      · iexists f
        iframe
  iintro %w %f0 ⟨%hw, Hf0, Hfv0⟩
  subst hw
  rw [List.append_nil]
  iapply H $$ %f0
  iframe

@[rocq_alias iriswasm.interp_instance_function_lookup]
theorem interp_instance_function_lookup (C : TContext) (hl : List (Hostfuncidx × FunctionType))
    (i : Nat) (tf : FunctionType) (j : Instance) :
    i + 1 ≤ C.funcT.length →
    C.funcT[i]? = some tf →
    ⊢ iprop(interpInstance (GF := GF) C hl j -∗
      ∃ f, ⌜j.funcs[i]? = some f⌝ ∗ interpFunction tf (fun _ => interpClosure hl) f) := by
  intro hlt hlook
  iintro Hi
  iunfold interpInstance, interpInstance' at Hi
  icases Hi with ⟨-, Hf, -, -, -⟩
  ihave %hlen := BigSepL2.bigSepL2_length $$ Hf
  have hf : j.funcs[i]? = some (j.funcs[i]'(by omega)) := List.getElem?_eq_getElem _
  ihave ⟨H, -⟩ := BigSepL2.bigSepL2_lookup_acc hf hlook $$ Hf
  iexists j.funcs[i]'(by omega)
  isplitr
  · ipureintro; exact hf
  · iexact H

@[rocq_alias iriswasm.interp_instance_lookup_global]
theorem interp_instance_lookup_global (C : TContext) (hl : List (Hostfuncidx × FunctionType))
    (j : Instance) (i : Nat) (t : ValueType) :
    Option.map GlobalType.t C.global[i]? = some t →
    ⊢ iprop(interpInstance (GF := GF) C hl j -∗
      ∃ (gt : GlobalType) (mt : Mutability) (n : Nat), ⌜C.global[i]? = some gt⌝ ∗
        ⌜j.globs[i]? = some n⌝ ∗
        ⌜gt = ⟨mt, t⟩⌝ ∗
        interpGlobal gt n) := by
  intro hlook
  obtain ⟨gt, hgt, rfl⟩ := Option.map_eq_some_iff.1 hlook
  iintro Hi
  iunfold interpInstance, interpInstance' at Hi
  icases Hi with ⟨-, -, -, -, Hg⟩
  ihave %hlen := BigSepL2.bigSepL2_length $$ Hg
  have hi : i < C.global.length := (List.getElem?_eq_some_iff.1 hgt).1
  have hn : j.globs[i]? = some (j.globs[i]'(by omega)) := List.getElem?_eq_getElem _
  ihave ⟨H, -⟩ := BigSepL2.bigSepL2_lookup_acc hn hgt $$ Hg
  iexists gt, gt.mut_, j.globs[i]'(by omega)
  isplitr
  · ipureintro; exact hgt
  isplitr
  · ipureintro; exact hn
  isplitr
  · ipureintro; rfl
  iexact H

@[rocq_alias iriswasm.interp_instance_get_mem]
theorem interp_instance_get_mem (C : TContext) (hl : List (Hostfuncidx × FunctionType))
    (i : Instance) :
    C.memory ≠ [] →
    ⊢ iprop(interpInstance (GF := GF) C hl i -∗
      ∃ (τm : Limits) (mem : Nat), ⌜C.memory[0]? = some τm⌝ ∗
        ⌜i.memory[0]? = some mem⌝ ∗
        mem ↪[wmlimit] τm.max ∗
        interpMem mem) := by
  intro hne
  obtain ⟨τm, hτ⟩ : ∃ τm, C.memory[0]? = some τm := by
    cases h : C.memory with
    | nil => exact absurd h hne
    | cons a _ => exact ⟨a, rfl⟩
  iintro Hi
  iunfold interpInstance, interpInstance' at Hi
  icases Hi with ⟨-, -, -, Hm, -⟩
  isimp only [hτ] at Hm
  rcases hm : i.memory[0]? with _ | a
  · isimp only [hm] at Hm
    iexfalso; iexact Hm
  · isimp only [hm] at Hm
    icases Hm with ⟨Hl, Hm⟩
    iexists τm, a
    isplitr
    · ipureintro; exact hτ
    isplitr
    · ipureintro; rfl
    iframe

omit [LogrelNaInvs GF] in
private theorem interp_val_length (τs : List ValueType) (vs : List Value) :
    interpVal (GF := GF) τs (.immV vs) ⊢ ⌜vs.length = τs.length⌝ := by
  iintro H
  iunfold interpVal, interpValues at H
  icases H with (%h | ⟨%ws, %h, H⟩)
  · cases h
  · cases h
    iapply BigSepL2.bigSepL2_length $$ H

/-- The shared core of `interp_br_stuck_push(_later)`: a break body for the pushed context is a
break for the original one, one label further out. -/
private theorem interp_br_body_push (C : TContext) (j' : Nat) (vh : ValidHoled (j' + 1))
    (vh' : ValidHoled j') (m : Nat) (vs : List Value) (p : Nat) (i : Instance) (tm : List ValueType)
    (lh : Lholed) (e : List AdministrativeInstruction) (τto : Option (List ValueType))
    (hl : List (Hostfuncidx × FunctionType))
    (hdec : vhDecrease vh = some vh') (hbase : getBaseL vh = vs) (hsize : lhDepth (lhOfVh vh) = p)
    (hpj : p ≤ j') (hlen : lengthLholeds C.label.reverse lh) :
    interpBrBody (GF := GF) (updLabel C ([tm] ++ C.label)).label (pushBase lh tm.length e [] [])
        (j' + 1) p vs C.local_ i τto hl ⊢
      interpBr C.local_ i τto hl (.brV (ValidHoled.rec_ [] m e vh' [])) lh C.label := by
  obtain ⟨d, rfl⟩ : ∃ d, j' = p + d := ⟨j' - p, by omega⟩
  rw [fixpoint_interp_br_eq]
  unfold interpBrBody interpBr interpCallHost
  dsimp only [interpCallHostBrDef]
  rw [show p + d + 1 - p = d + 1 by omega, lh_depth_push_base, show lhDepth lh + 1 - (d + 1 + 1) = lhDepth lh - (d + 1) by omega]
  simp only [updLabel, List.singleton_append, List.getElem?_cons_succ, List.drop_succ_cons]
  iintro ⟨%τs', %vs0, %k, %es, %lh', %es', %lh'', %τs'', %hlook, %hlayer, %hdepth, %hmin, #Hv, Hbr⟩
  have hdlt : d < lhDepth lh := by
    have := length_lholeds_length_depth _ _ hlen
    have := (List.getElem?_eq_some_iff.1 hlook).1
    simp at *; omega
  obtain ⟨lh0, rfl, hlayer2⟩ :=
    get_layer_push_inv lh tm.length e [] [] d vs0 k es lh' es' (by omega) hlayer
  have hk := get_layer_lookup_lh_lengths C.label lh d τs' vs0 k es lh0 es' hlen hlook hlayer2
  have hd0 := get_layer_lh_depth lh d vs0 k es lh0 es' hdlt hlayer2
  ihave %hvl := interp_val_length _ _ $$ Hv
  iexists p + d + 1, ValidHoled.rec_ [] m e vh' [], vs, p + 1
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; simp only [getBaseL]; rw [← get_base_l_vh_decrease_eq _ _ hdec, hbase]
  isplitr
  · ipureintro; simp only [lhOfVh, lhDepth]; rw [← lh_depth_vh_decrease_eq _ _ hdec, hsize]
  rw [show p + d + 1 - (p + 1) = d by omega]
  iexists τs', vs0, k, es, lh0, es', lh'', τs''
  isplitr
  · ipureintro; exact hlook
  isplitr
  · ipureintro; exact hlayer2
  isplitr
  · ipureintro; omega
  isplitr
  · ipureintro; exact lh_minus_push_base_is_Some lh _ _ _ _ _ (by omega) hmin
  isplitr
  · iexact Hv
  iintro %f Hf
  ihave Hw := Hbr $$ %f Hf
  rw [lh_depth_push_base, hd0] at *
  rw [hd0]
  iapply wp_br_ctx_shift_inv (const_list_of_val _) (show constList [] = true from rfl)
    (by simp only [List.length_append] at hvl; simp [ofVal, vToEList]; omega)
  iexact Hw

@[rocq_alias iriswasm.interp_br_stuck_push]
theorem interp_br_stuck_push (C : TContext) (j : Nat) (vh : ValidHoled j) (m : Nat) (vs : List Value)
    (p : Nat) (i : Instance) (tm tm' : List ValueType) (lh : Lholed) (f' : Frame)
    (e : List AdministrativeInstruction) (τto : Option (List ValueType))
    (hl : List (Hostfuncidx × FunctionType)) :
    m = tm.length →
    getBaseL vh = vs →
    lhDepth (lhOfVh vh) = p →
    j ≠ p →
    lengthLholeds C.label.reverse lh →
    LholedValid lh →
    BaseIsEmpty lh →
    ⊢ iprop(interpBrBody (updLabel C ([tm] ++ C.label)).label (pushBase lh tm.length e [] [])
        j p vs C.local_ i τto hl -∗
      (↪[frame] f' : IProp GF) -∗
      interpFrame C.local_ i f' -∗
      WP ([AdministrativeInstruction.label m e (vfill vh [.basic (.br j)])] : Expr)
        {{ v, (interpVal tm' v ∨
               interpBr C.local_ i τto hl v lh C.label ∨
               interpReturnOption τto C.local_ i v ∨
               interpCallHost C.local_ i τto hl v lh C.label tm') ∗
              ∃ f0, ↪[frame] f0 ∗ interpFrame C.local_ i f0 }}) := by
  intro hm hbase hsize hne hlen _ _
  have hge := lh_depth_ge vh p hsize
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨vh', hdec⟩ := lh_depth_le_vh_decrease vh (by omega)
  rw [vfill_label, vfill_decrease (ValidHoled.rec_ [] m e vh []) (ValidHoled.rec_ [] m e vh' [])
    _ (by simp [vhDecrease, hdec])]
  iintro Hbr Hf Hfv
  iapply IrisWp.wp_value (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
    (e := vfill (ValidHoled.rec_ [] m e vh' []) [.basic (.br (j' + 1))])
    (v := .brV (ValidHoled.rec_ [] m e vh' [])) ⟨rfl⟩
  isplitr [Hf Hfv]
  · iright; ileft
    iapply interp_br_body_push C j' vh vh' m vs p i tm lh e τto hl hdec hbase hsize (by omega) hlen
    iexact Hbr
  · iexists f'
    iframe

@[rocq_alias iriswasm.interp_val_timeless]
instance interpVal_timeless (t : List ValueType) (v : Val) : Timeless (interpVal (GF := GF) t v) := by
  have : ∀ τ w, Timeless (interpValue (GF := GF) τ w) := by
    intro τ w
    cases τ <;> unfold interpValue interpValueI32 interpValueI64 interpValueF32 interpValueF64 <;>
      infer_instance
  unfold interpVal interpValues; infer_instance

@[rocq_alias iriswasm.interp_br_stuck_push_later]
theorem interp_br_stuck_push_later (C : TContext) (j : Nat) (vh : ValidHoled j) (m : Nat)
    (vs : List Value) (p : Nat) (i : Instance) (tm tm' : List ValueType) (lh : Lholed) (f' : Frame)
    (e : List AdministrativeInstruction) (τto : Option (List ValueType))
    (hl : List (Hostfuncidx × FunctionType)) :
    m = tm.length →
    getBaseL vh = vs →
    lhDepth (lhOfVh vh) = p →
    j ≠ p →
    lengthLholeds C.label.reverse lh →
    LholedValid lh →
    BaseIsEmpty lh →
    ⊢ iprop(▷ interpBrBody (updLabel C ([tm] ++ C.label)).label (pushBase lh tm.length e [] [])
        j p vs C.local_ i τto hl -∗
      (↪[frame] f' : IProp GF) -∗
      interpFrame C.local_ i f' -∗
      WP ([AdministrativeInstruction.label m e (vfill vh [.basic (.br j)])] : Expr)
        {{ v, (interpVal tm' v ∨
               ▷ interpBr C.local_ i τto hl v lh C.label ∨
               interpReturnOption τto C.local_ i v ∨
               interpCallHost C.local_ i τto hl v lh C.label tm') ∗
              ∃ f0, ↪[frame] f0 ∗ interpFrame C.local_ i f0 }}) := by
  intro hm hbase hsize hne hlen _ _
  have hge := lh_depth_ge vh p hsize
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨vh', hdec⟩ := lh_depth_le_vh_decrease vh (by omega)
  rw [vfill_label, vfill_decrease (ValidHoled.rec_ [] m e vh []) (ValidHoled.rec_ [] m e vh' [])
    _ (by simp [vhDecrease, hdec])]
  iintro Hbr Hf Hfv
  iapply IrisWp.wp_value (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
    (e := vfill (ValidHoled.rec_ [] m e vh' []) [.basic (.br (j' + 1))])
    (v := .brV (ValidHoled.rec_ [] m e vh' [])) ⟨rfl⟩
  isplitr [Hf Hfv]
  · iright; ileft
    inext
    iapply interp_br_body_push C j' vh vh' m vs p i tm lh e τto hl hdec hbase hsize (by omega) hlen
    iexact Hbr
  · iexists f'
    iframe

@[rocq_alias iriswasm.interp_return_label]
theorem interp_return_label (C : TContext) (tn : List ValueType) (i : Instance) (w : Val) (f' : Frame)
    (tm : List ValueType) (lh : Lholed) (es : List AdministrativeInstruction) (m : Nat)
    (hl : List (Hostfuncidx × FunctionType)) :
    ⊢ iprop(interpReturnOption (updLabel C ([tn] ++ C.label)).return_
        (updLabel C ([tn] ++ C.label)).local_ i w -∗
      (↪[frame] f' : IProp GF) -∗
      interpFrame C.local_ i f' -∗
      WP (ofVal w) CTX 1 ; (Lholed.rec_ [] m es (.base [] []) [])
        {{ v, (interpVal tm v ∨
               interpBr C.local_ i C.return_ hl v lh C.label ∨
               interpReturnOption C.return_ C.local_ i v ∨
               interpCallHost C.local_ i C.return_ hl v lh C.label tm) ∗
              ∃ f0, ↪[frame] f0 ∗ interpFrame C.local_ i f0 }}) := by
  unfold interpReturnOption
  dsimp only [updLabel]
  iintro ⟨%sh, %v, %hw, %hbase, Hret⟩ Hf Hfv
  subst hw
  rcases hr : C.return_ with _ | τr
  · iexfalso
    iexact Hret
  icases Hret with ⟨%τs'', #Hw, Hret⟩
  ihave %hvl := interp_val_length _ _ $$ Hw
  rw [show (Lholed.rec_ [] m es (.base [] []) [] : Lholed) = pushBase (.base [] []) m es [] [] from rfl]
  iapply wp_label_push_nil_inv
  iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).1
  iapply IrisWp.wp_value (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
    (e := [.label m es (ofVal (.retV sh))]) (v := .retV (.rec_ [] m es sh [])) ⟨rfl⟩
  isplitr [Hf Hfv]
  · iright; iright; ileft
    iexists .rec_ [] m es sh [], v
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; exact hbase
    iexists τs''
    isplitr
    · iexact Hw
    iintro %f0 %f1 Hf
    ihave H := Hret $$ %f0 %f1 Hf
    have hsplit : simpleGetBaseL sh = v.take τs''.length ++ v.drop τs''.length := by
      rw [hbase, List.take_append_drop]
    obtain ⟨lh1, hlh1⟩ := lfilled_simple_get_base_pull _ sh _ _ _ _ hsplit
      (sfill_to_lfilled sh [.basic .return_])
    obtain ⟨lh2, hlh2⟩ := lfilled_simple_get_base_pull _ (.rec_ [] m es sh []) _ _ _ _ hsplit
      (sfill_to_lfilled (.rec_ [] m es sh []) [.basic .return_])
    iapply wp_ret_shift (n := τr.length) (f := f0) (LI := ofVal (.retV sh))
      (LI' := ofVal (.retV (.rec_ [] m es sh []))) (const_list_of_val _)
      (by simp only [List.length_append] at hvl; simp [ofVal, vToEList]; omega) hlh1 hlh2 $$ H
  · iexists f'
    iframe

omit [LogrelNaInvs GF] in
private theorem interp_val_drop (τs1 τs2 : List ValueType) (vs : List Value) :
    interpVal (GF := GF) (τs1 ++ τs2) (.immV vs) ⊢ interpVal τs2 (.immV (vs.drop τs1.length)) := by
  iintro H
  ihave %hl := interp_val_length _ _ $$ H
  iunfold interpVal, interpValues at H
  iunfold interpVal, interpValues
  icases H with (%h | ⟨%ws, %h, H⟩)
  · cases h
  cases h
  iright
  iexists vs.drop τs1.length
  isplitr
  · ipureintro; rfl
  have hsplit := (BigSepL2.bigSepL2_append (PROP := IProp GF)
    (Φ := fun _ w τ => interpValue τ w) (l1a := vs.take τs1.length) (l1b := vs.drop τs1.length)
    (l2a := τs1) (l2b := τs2) (Or.inl (by simp at hl ⊢; omega))).1
  rw [List.take_append_drop] at hsplit
  ihave ⟨-, H2⟩ := hsplit $$ H
  iexact H2

omit [LogrelNaInvs GF] in
local instance isExcept0WpWasm {s : Stuckness} {E : CoPset} {e : Expr} {Φ : Val → IProp GF} :
    Iris.ProofMode.IsExcept0 (WP e @ s ; E {{ Φ }} : IProp GF) :=
  IrisWp.isExcept0Wp (P := fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)

@[rocq_alias iriswasm.iris_fundamental_helpers.interp_br_step]
theorem interp_br_step (C : TContext) (j : Nat) (vh : ValidHoled j) (m : Nat) (vs : List Value)
    (p : Nat) (i : Instance) (tm : List ValueType) (lh : Lholed) (f' : Frame)
    (hl : List (Hostfuncidx × FunctionType)) :
    m = tm.length →
    getBaseL vh = vs →
    lhDepth (lhOfVh vh) = p →
    j = p →
    ⊢ iprop(▷ interpBrBody (updLabel C ([tm] ++ C.label)).label (pushBase lh tm.length [] [] [])
        j p vs C.local_ i C.return_ hl -∗
      (↪[frame] f' : IProp GF) -∗
      interpFrame C.local_ i f' -∗
      WP ([AdministrativeInstruction.label m [] (vfill vh [.basic (.br j)])] : Expr)
        {{ v, (interpVal tm v ∨
               interpBr C.local_ i C.return_ hl v lh C.label ∨
               interpReturnOption C.return_ C.local_ i v ∨
               interpCallHost C.local_ i C.return_ hl v lh C.label tm) ∗
              ∃ f0, ↪[frame] f0 ∗ interpFrame C.local_ i f0 }}) := by
  intro hm hbase hsize hjp
  subst hjp hm
  unfold interpBrBody
  simp only [Nat.sub_self, updLabel, List.singleton_append, List.getElem?_cons_zero]
  rcases hpb : pullBaseLDropLen vh (vs.length - tm.length) with ⟨vh', l⟩
  rw [vfill_pull_base_l_take_len vh _ _ vh' l hpb]
  have hfill := (vfill_to_lfilled vh'
    (l.map (fun x => AdministrativeInstruction.basic (.const x)) ++ [.basic (.br (lhDepth (lhOfVh vh)))])).2
  rw [← lh_depth_pull_base_l_take_len vh _ vh' l hpb, hsize] at hfill
  iintro Hbr Hf Hfv
  icases Hbr with ⟨%τs', %vs0, %k, %es, %lh', %es', %lh'', %τs'', >%hlook, -, -, -, >#Hv, -⟩
  cases hlook
  ihave %hvl := interp_val_length _ _ $$ Hv
  simp only [List.length_append] at hvl
  have hsplit := take_drop_pull_base_l_take_len vh _ vh' l vs (Nat.sub_le _ _) hbase hpb
  have hl := length_pull_base_l_take_len vh _ vh' l vs hbase hpb
  have hld : l = vs.drop τs''.length := by
    have h' := congrArg (List.drop (vs.length - tm.length)) hsplit
    rw [List.drop_left' (by simp <;> omega)] at h'
    rw [← h', show vs.length - tm.length = τs''.length by omega]
  iapply wp_br (const_list_map l) (by simp; omega) hfill $$ Hf
  inext
  iintro Hf
  rw [List.append_nil]
  iapply IrisWp.wp_value (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
    (e := l.map fun x => AdministrativeInstruction.basic (.const x)) (v := .immV l) ⟨rfl⟩
  isplitr [Hf Hfv]
  · ileft
    rw [hld]
    iapply interp_val_drop
    iexact Hv
  · iexists f'
    iframe

@[rocq_alias iriswasm.interp_br_label]
theorem interp_br_label (C : TContext) (i : Instance) (w : Val) (f' : Frame) (tm : List ValueType)
    (lh : Lholed) (hl : List (Hostfuncidx × FunctionType)) :
    ⊢ iprop(interpCtx C.label C.return_ hl C.local_ i lh -∗
      interpBr C.local_ i C.return_ hl w (pushBase lh tm.length [] [] [])
        (updLabel C ([tm] ++ C.label)).label -∗
      (↪[frame] f' : IProp GF) -∗
      interpFrame C.local_ i f' -∗
      WP (ofVal w) CTX 1 ; (Lholed.rec_ [] tm.length [] (.base [] []) [])
        {{ v, (interpVal tm v ∨
               interpBr C.local_ i C.return_ hl v lh C.label ∨
               interpReturnOption C.return_ C.local_ i v ∨
               interpCallHost C.local_ i C.return_ hl v lh C.label tm) ∗
              ∃ f0, ↪[frame] f0 ∗ interpFrame C.local_ i f0 }}) := by
  rw [fixpoint_interp_br_eq]
  dsimp only [interpCallHostBrDef]
  iintro #Hc ⟨%j, %vh, %vs, %p, %hw, %hbase, %hsize, Hbr⟩ Hf Hfv
  subst hw
  rw [show (Lholed.rec_ [] tm.length [] (.base [] []) [] : Lholed) =
      pushBase (.base [] []) tm.length [] [] [] from rfl]
  iapply wp_label_push_nil_inv
  iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).1
  rw [show ofVal (.brV vh) = vfill vh [.basic (.br j)] from rfl]
  by_cases hjp : j = p
  · iapply interp_br_step C j vh tm.length vs p i tm lh f' hl rfl hbase hsize hjp $$ [Hbr] Hf Hfv
    iunfold interpBrBody, interpBr, interpCallHost
    inext
    iexact Hbr
  · iunfold interpCtx at Hc
    icases Hc with ⟨%hemp, %hlen, %hvalid, -⟩
    iapply interp_br_stuck_push C j vh tm.length vs p i tm tm lh f' [] C.return_ hl rfl hbase hsize
      hjp hlen hvalid hemp $$ [Hbr] Hf Hfv
    iunfold interpBrBody, interpBr, interpCallHost
    iexact Hbr

private theorem interp_br_unfold (τl : List ValueType) (i : Instance) (τto : Option (List ValueType))
    (hl : List (Hostfuncidx × FunctionType)) (w : Val) (lh' : Lholed) (τc : List (List ValueType)) :
    interpBr (GF := GF) τl i τto hl w lh' τc ⊢
      ∃ j, ∃ (vh : ValidHoled j) (vs : List Value) (p : Nat), ⌜w = .brV vh⌝ ∗
        ⌜getBaseL vh = vs⌝ ∗ ⌜lhDepth (lhOfVh vh) = p⌝ ∗ interpBrBody τc lh' j p vs τl i τto hl := by
  rw [fixpoint_interp_br_eq]
  dsimp only [interpCallHostBrDef]
  unfold interpBrBody interpBr interpCallHost
  exact .rfl

/-- Coq `interp_call_host` unfolded once, with the inner relations folded back. -/
private abbrev callHostBody (τl : List ValueType) (i : Instance) (τto : Option (List ValueType))
    (hl : List (Hostfuncidx × FunctionType)) (vh : Llholed) (lh' : Lholed) (τc : List (List ValueType))
    (t τs2 : List ValueType) : IProp GF :=
  iprop(□ (∀ v2 f, interpVal τs2 v2 -∗ ↪[frame] f ∗ interpFrame τl i f -∗
    WP (llfill vh (ofVal v2))
      {{ vs, (interpVal t vs ∨ ▷ interpBr τl i τto hl vs lh' τc ∨ interpReturnOption τto τl i vs ∨
              ▷ interpCallHost τl i τto hl vs lh' τc t) ∗ ∃ f, ↪[frame] f ∗ interpFrame τl i f }}))

private theorem interp_call_host_unfold (τl : List ValueType) (i : Instance)
    (τto : Option (List ValueType)) (hl : List (Hostfuncidx × FunctionType)) (w : Val) (lh' : Lholed)
    (τc : List (List ValueType)) (t : List ValueType) :
    interpCallHost (GF := GF) τl i τto hl w lh' τc t ⊣⊢
      ∃ (vh : Llholed) (v : List Value) (tf : FunctionType) (h : Hostfuncidx) (τs1 τs2 : List ValueType),
        ⌜w = .callHostV tf h v vh⌝ ∗ ⌜tf = .tf τs1 τs2⌝ ∗ ⌜(h, tf) ∈ hl⌝ ∗ ⌜llholedBasic vh⌝ ∗
        interpVal τs1 (.immV v) ∗ callHostBody τl i τto hl vh lh' τc t τs2 := by
  rw [fixpoint_interp_call_host_eq]
  dsimp only [interpCallHostBrDef]
  unfold callHostBody interpBr interpCallHost
  exact .rfl

private theorem call_host_post_later {τl i τto hl lh' τc t} (v : Val) :
    iprop(interpVal (GF := GF) t v ∨ interpBr τl i τto hl v lh' τc ∨ interpReturnOption τto τl i v ∨
      interpCallHost τl i τto hl v lh' τc t) ⊢
    iprop(interpVal t v ∨ ▷ interpBr τl i τto hl v lh' τc ∨ interpReturnOption τto τl i v ∨
      ▷ interpCallHost τl i τto hl v lh' τc t) := by
  iintro (H | H | H | H)
  · ileft; iexact H
  · iright; ileft; inext; iexact H
  · iright; iright; ileft; iexact H
  · iright; iright; iright; inext; iexact H

private theorem call_host_post_later' {τl i τto hl lh' τc t} (v : Val) :
    iprop(interpVal (GF := GF) t v ∨ ▷ interpBr τl i τto hl v lh' τc ∨ interpReturnOption τto τl i v ∨
      interpCallHost τl i τto hl v lh' τc t) ⊢
    iprop(interpVal t v ∨ ▷ interpBr τl i τto hl v lh' τc ∨ interpReturnOption τto τl i v ∨
      ▷ interpCallHost τl i τto hl v lh' τc t) := by
  iintro (H | H | H | H)
  · ileft; iexact H
  · iright; ileft; iexact H
  · iright; iright; ileft; iexact H
  · iright; iright; iright; inext; iexact H

/-- The Löb induction of Coq's `interp_call_host_label`. -/
private theorem interp_call_host_label_loeb (C : TContext) (i : Instance) (tm : List ValueType)
    (lh : Lholed) (hl : List (Hostfuncidx × FunctionType)) :
    ⊢ iprop(interpCtx (GF := GF) C.label C.return_ hl C.local_ i lh -∗
      ∀ (tf : FunctionType) (h : Hostfuncidx) (v : List Value) (vh : Llholed)
        (τs1 τs2 : List ValueType),
      ⌜tf = .tf τs1 τs2⌝ -∗ ⌜(h, tf) ∈ hl⌝ -∗ ⌜llholedBasic vh⌝ -∗ interpVal τs1 (.immV v) -∗
      callHostBody C.local_ i C.return_ hl vh (pushBase lh tm.length [] [] []) (tm :: C.label) tm τs2 -∗
      interpCallHost C.local_ i C.return_ hl (.callHostV tf h v (.label [] tm.length [] vh [])) lh
        C.label tm) := by
  iintro #Hc
  iloeb as IH
  iintro %tf %h %v %vh %τs1 %τs2 %htf %hin %hb #Hv #Hch
  iapply (interp_call_host_unfold _ _ _ _ _ _ _ _).2
  iexists .label [] tm.length [] vh [], v, tf, h, τs1, τs2
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; exact htf
  isplitr
  · ipureintro; exact hin
  isplitr
  · ipureintro; exact ⟨trivial, hb⟩
  isplitr
  · iexact Hv
  unfold callHostBody
  imodintro
  iintro %v2 %f #Hw ⟨Hf, Hfv⟩
  rw [← llfill_label]
  iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).2
  iapply wp_label_push_nil
  iapply wp_ctx_bind _ _ _ _ _ _ (by simp [pushBase, BaseIsEmpty])
  ihave H := Hch $$ %v2 %f Hw [Hf Hfv]
  · isplitl [Hf]
    · iexact Hf
    · iexact Hfv
  iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ H
  iintro %w ⟨Hpost, %f0, Hf0, Hfv0⟩
  icases Hpost with (H1 | H2 | H3 | H4)
  · -- a value or a trap leaves the label
    iapply wp_label_push_nil_inv
    iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).1
    iunfold interpVal at H1
    icases H1 with (%ht | H1)
    · subst ht
      iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ [Hf0]
      · iapply wp_label_trap (Φ := fun v => iprop(⌜v = .trapV⌝)) (to_of_val _) $$ Hf0
        inext; ipureintro; rfl
      · iintro %v0 ⟨%h0, Hf⟩
        subst h0
        isplitr [Hf Hfv0]
        · ileft; iunfold interpVal; ileft; ipureintro; rfl
        · iexists f0; iframe
    · iunfold interpValues at H1
      icases H1 with ⟨%ws, %hws, #Hws⟩
      subst hws
      iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ [Hf0]
      · iapply wp_label_value (Φ := fun v => iprop(⌜v = .immV ws⌝)) (to_of_val _) $$ Hf0
        inext; ipureintro; rfl
      · iintro %v0 ⟨%h0, Hf⟩
        subst h0
        isplitr [Hf Hfv0]
        · ileft; iunfold interpVal; iright; iunfold interpValues; iexists ws
          isplitr
          · ipureintro; rfl
          · iexact Hws
        · iexists f0; iframe
  · -- a break out of the pushed label
    ihave H2 := later_mono (interp_br_unfold _ _ _ _ _ _ _) $$ H2
    iapply wp_label_push_nil_inv
    iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).1
    icases H2 with ⟨%j, %vh', %vs, %p, >%hw, >%hbase, >%hsize, Hbr⟩
    subst hw
    rw [show ofVal (.brV vh') = vfill vh' [.basic (.br j)] from rfl]
    by_cases hjp : j = p
    · have hs := interp_br_step (GF := GF) C j vh' tm.length vs p i tm lh f0 hl rfl hbase hsize hjp
      simp only [updLabel, List.singleton_append] at hs
      iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ [Hbr Hf0 Hfv0]
      · iapply hs $$ Hbr Hf0 Hfv0
      · iintro %v0 ⟨H, Hfr⟩
        isplitr [Hfr]
        · iapply call_host_post_later $$ H
        · iexact Hfr
    · iunfold interpCtx at Hc
      icases Hc with ⟨%hemp, %hlen, %hvalid, -⟩
      have hs := interp_br_stuck_push_later (GF := GF) C j vh' tm.length vs p i tm tm lh f0 []
        C.return_ hl rfl hbase hsize hjp hlen hvalid hemp
      simp only [updLabel, List.singleton_append] at hs
      iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ [Hbr Hf0 Hfv0]
      · iapply hs $$ Hbr Hf0 Hfv0
      · iintro %v0 ⟨H, Hfr⟩
        isplitr [Hfr]
        · iapply call_host_post_later' $$ H
        · iexact Hfr
  · -- a return
    rw [show pushBase (.base [] []) tm.length [] [] [] = Lholed.rec_ [] tm.length [] (.base [] []) []
      from rfl]
    have hr := interp_return_label (GF := GF) C tm i w f0 tm lh [] tm.length hl
    dsimp only [updLabel] at hr
    ihave H := hr $$ H3 Hf0 Hfv0
    iapply wp_wand_ctx $$ H
    iintro %v0 ⟨H, Hfr⟩
    isplitr [Hfr]
    · iapply call_host_post_later $$ H
    · iexact Hfr
  · -- a nested host call: Löb
    ihave H4 := later_mono (interp_call_host_unfold _ _ _ _ _ _ _ _).1 $$ H4
    iapply wp_label_push_nil_inv
    iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).1
    icases H4 with ⟨%vh0, %v0, %tf0, %h0, %τa, %τb, >%hw, >%htf0, >%hin0, >%hb0, Hv0, Hch0⟩
    subst hw
    rw [show ofVal (.callHostV tf0 h0 v0 vh0) = llfill vh0 [.callHost tf0 h0 v0] from rfl,
      llfill_label]
    iapply IrisWp.wp_value (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
      (e := llfill (.label [] tm.length [] vh0 []) [.callHost tf0 h0 v0])
      (v := .callHostV tf0 h0 v0 (.label [] tm.length [] vh0 [])) ⟨rfl⟩
    isplitr [Hf0 Hfv0]
    · iright; iright; iright
      inext
      iapply IH $$ %tf0 %h0 %v0 %vh0 %τa %τb %htf0 %hin0 %hb0 Hv0 Hch0
    · iexists f0; iframe

@[rocq_alias iriswasm.iris_fundamental_helpers.interp_call_host_label]
theorem interp_call_host_label (C : TContext) (i : Instance) (w : Val) (f' : Frame)
    (tm : List ValueType) (lh : Lholed) (hl : List (Hostfuncidx × FunctionType)) :
    ⊢ iprop(interpCtx C.label C.return_ hl C.local_ i lh -∗
      interpCallHost C.local_ i C.return_ hl w (pushBase lh tm.length [] [] [])
        (updLabel C ([tm] ++ C.label)).label tm -∗
      (↪[frame] f' : IProp GF) -∗
      interpFrame C.local_ i f' -∗
      WP (ofVal w) CTX 1 ; (Lholed.rec_ [] tm.length [] (.base [] []) [])
        {{ v, (interpVal tm v ∨
               interpBr C.local_ i C.return_ hl v lh C.label ∨
               interpReturnOption C.return_ C.local_ i v ∨
               interpCallHost C.local_ i C.return_ hl v lh C.label tm) ∗
              ∃ f0, ↪[frame] f0 ∗ interpFrame C.local_ i f0 }}) := by
  simp only [updLabel, List.singleton_append]
  iintro #Hc Hch Hf Hfv
  ihave Hch := (interp_call_host_unfold _ _ _ _ _ _ _ _).1 $$ Hch
  icases Hch with ⟨%vh, %v, %tf, %h, %τs1, %τs2, %hw, %htf, %hin, %hb, #Hv, #Hch⟩
  subst hw
  rw [show (Lholed.rec_ [] tm.length [] (.base [] []) [] : Lholed) =
      pushBase (.base [] []) tm.length [] [] [] from rfl]
  iapply wp_label_push_nil_inv
  iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).1
  rw [show ofVal (.callHostV tf h v vh) = llfill vh [.callHost tf h v] from rfl, llfill_label]
  iapply IrisWp.wp_value (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
    (e := llfill (.label [] tm.length [] vh []) [.callHost tf h v])
    (v := .callHostV tf h v (.label [] tm.length [] vh [])) ⟨rfl⟩
  isplitr [Hf Hfv]
  · iright; iright; iright
    iapply interp_call_host_label_loeb C i tm lh hl $$ Hc %tf %h %v %vh %τs1 %τs2 %htf %hin %hb Hv Hch
  · iexists f'; iframe

@[rocq_alias iriswasm.interp_instance_change_label]
theorem interp_instance_change_label (lbs : List (List ValueType)) (C : TContext) (i : Instance)
    (hl : List (Hostfuncidx × FunctionType)) :
    ⊢ iprop(interpInstance (GF := GF) C hl i -∗ interpInstance (updLabel C lbs) hl i) := by
  rw [show interpInstance (GF := GF) (updLabel C lbs) hl i = interpInstance C hl i from rfl]
  iintro H; iexact H

@[rocq_alias iriswasm.interp_instance_change_return]
theorem interp_instance_change_return (ret : Option (List ValueType)) (C : TContext) (i : Instance)
    (hl : List (Hostfuncidx × FunctionType)) :
    ⊢ iprop(interpInstance (GF := GF) C hl i -∗ interpInstance (updReturn C ret) hl i) := by
  rw [show interpInstance (GF := GF) (updReturn C ret) hl i = interpInstance C hl i from rfl]
  iintro H; iexact H

@[rocq_alias iriswasm.interp_instance_change_local]
theorem interp_instance_change_local (locs : List ValueType) (C : TContext) (i : Instance)
    (hl : List (Hostfuncidx × FunctionType)) :
    ⊢ iprop(interpInstance (GF := GF) C hl i -∗ interpInstance (updLocal C locs) hl i) := by
  rw [show interpInstance (GF := GF) (updLocal C locs) hl i = interpInstance C hl i from rfl]
  iintro H; iexact H

/-! ### Closing a function body under its `local` frame -/

private theorem wp_wand_frame {s : Stuckness} {E : CoPset} {es : Expr} {n : Nat} {f : Frame}
    {Φ Ψ : Val → IProp GF} :
    WP es @ s ; E FRAME n ; f {{ Φ }} ⊢ (∀ v, Φ v -∗ Ψ v) -∗ WP es @ s ; E FRAME n ; f {{ Ψ }} :=
  IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)

@[rocq_alias iriswasm.local_host_trap]
theorem local_host_trap (f0 : Frame) (τ1 τs : List ValueType) (i : Instance) (f : Frame)
    (τ2 : List ValueType) (hl : List (Hostfuncidx × FunctionType)) :
    ⊢ iprop(↪[frame] f0 -∗
      interpFrame (τ1 ++ τs) i f0 -∗
      WP ([AdministrativeInstruction.trap] : Expr) CTX 1 ;
        (Lholed.rec_ [] τ2.length [] (.base [] []) [])
        {{ w, ∃ f1 : Frame,
          ((↪[frame] f : IProp GF) -∗
            WP (ofVal w) @ Stuckness.NotStuck ; ⊤ FRAME τ2.length ; f1
              {{ w0, (interpVal τ2 w0 ∨ interpCallHostCls hl τ2 w0) ∗
                ↪[frame] f ∗ NonAtomicInvariant.own logrelNais ⊤ }}) ∗ ↪[frame] f1 }}) := by
  iintro Hf0 Hf0v
  have ht := wp_trap_ctx (GF := GF) Stuckness.NotStuck ⊤ f0 1
    (Lholed.rec_ [] τ2.length [] (.base [] []) []) [] [] rfl
  simp only [List.nil_append, List.append_nil] at ht
  ihave H := ht $$ Hf0
  iapply wp_wand_ctx $$ H
  iintro %v ⟨%hv, Hf⟩
  subst hv
  iexists f0
  isplitl [Hf0v]
  · iintro Hf
    rw [show ofVal .trapV = [AdministrativeInstruction.trap] from rfl]
    iapply wp_wand_frame (Φ := fun v => iprop(⌜v = .trapV⌝ ∗ ↪[frame] f)) $$ [Hf]
    · iapply wp_frame_trap (Φ := fun v => iprop(⌜v = .trapV⌝)) $$ Hf
      inext; ipureintro; rfl
    · iintro %v ⟨%hv, Hf⟩
      subst hv
      iunfold interpFrame at Hf0v
      icases Hf0v with ⟨%vs, -, -, Hown⟩
      isplitr [Hf Hown]
      · ileft; iunfold interpVal; ileft; ipureintro; rfl
      · iframe
  · iexact Hf

@[rocq_alias iriswasm.local_host_val]
theorem local_host_val (v : Val) (f0 : Frame) (τ2 τ1 τs : List ValueType) (i : Instance) (f : Frame)
    (hl : List (Hostfuncidx × FunctionType)) :
    ⊢ iprop(interpValues τ2 v -∗
      ↪[frame] f0 -∗
      interpFrame (τ1 ++ τs) i f0 -∗
      WP (ofVal v) CTX 1 ; (Lholed.rec_ [] τ2.length [] (.base [] []) [])
        {{ w, ∃ f1 : Frame,
          ((↪[frame] f : IProp GF) -∗
            WP (ofVal w) @ Stuckness.NotStuck ; ⊤ FRAME τ2.length ; f1
              {{ w0, (interpVal τ2 w0 ∨ interpCallHostCls hl τ2 w0) ∗
                ↪[frame] f ∗ NonAtomicInvariant.own logrelNais ⊤ }}) ∗ ↪[frame] f1 }}) := by
  iintro Hv Hf0 Hf0v
  iunfold interpValues at Hv
  icases Hv with ⟨%ws, %hv, #Hws⟩
  subst hv
  ihave %hlen := BigSepL2.bigSepL2_length $$ Hws
  have hval := wp_val_return (GF := GF) (s := Stuckness.NotStuck) (E := ⊤)
    (Φ := fun w => iprop(⌜w = .immV ws⌝ ∗ ↪[frame] f0)) (vs := ofVal (.immV ws)) (vs' := [])
    (es' := []) (es'' := []) (n := τ2.length) (f := f0) (const_list_of_val _)
  ihave H := hval $$ Hf0 []
  · iintro Hf
    rw [List.nil_append, List.append_nil]
    iapply IrisWp.wp_value (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
      (e := ofVal (.immV ws)) (v := .immV ws) ⟨rfl⟩
    isplitr [Hf]
    · ipureintro; rfl
    · iexact Hf
  iapply wp_wand_ctx $$ H
  iintro %v ⟨%hv, Hf⟩
  subst hv
  iexists f0
  isplitl [Hf0v]
  · iintro Hf
    iapply wp_wand_frame (Φ := fun v => iprop(⌜v = .immV ws⌝ ∗ ↪[frame] f)) $$ [Hf]
    · iapply wp_frame_value _ _ (fun v => iprop(⌜v = .immV ws⌝)) (ofVal (.immV ws)) τ2.length f0 f ws
        (to_of_val _) (by simp [ofVal, vToEList, hlen]) $$ Hf
      inext; ipureintro; rfl
    · iintro %v ⟨%hv, Hf⟩
      subst hv
      iunfold interpFrame at Hf0v
      icases Hf0v with ⟨%vs, -, -, Hown⟩
      isplitr [Hf Hown]
      · ileft; iunfold interpVal; iright; iunfold interpValues; iexists ws
        isplitr
        · ipureintro; rfl
        · iexact Hws
      · iframe
  · iexact Hf

private theorem local_host_frame_val (ws : List Value) (f0 f : Frame) (τ2 τl : List ValueType)
    (i : Instance) (hl : List (Hostfuncidx × FunctionType)) :
    interpVal (GF := GF) τ2 (.immV ws) ⊢ interpFrame τl i f0 -∗ ↪[frame] f -∗
      WP (ofVal (.immV ws)) @ Stuckness.NotStuck ; ⊤ FRAME τ2.length ; f0
        {{ w0, (interpVal τ2 w0 ∨ interpCallHostCls hl τ2 w0) ∗
          ↪[frame] f ∗ NonAtomicInvariant.own logrelNais ⊤ }} := by
  iintro Hv Hfv Hf
  ihave %hlen := interp_val_length _ _ $$ Hv
  iapply wp_wand_frame (Φ := fun v => iprop(⌜v = .immV ws⌝ ∗ ↪[frame] f)) $$ [Hf]
  · iapply wp_frame_value _ _ (fun v => iprop(⌜v = .immV ws⌝)) (ofVal (.immV ws)) τ2.length f0 f ws
      (to_of_val _) (by simp [ofVal, vToEList, hlen]) $$ Hf
    inext; ipureintro; rfl
  · iintro %v ⟨%hv, Hf⟩
    subst hv
    iunfold interpFrame at Hfv
    icases Hfv with ⟨%vs, -, -, Hown⟩
    isplitr [Hf Hown]
    · ileft; iexact Hv
    · iframe

@[rocq_alias iriswasm.local_host_br]
theorem local_host_br (v : Val) (f0 : Frame) (τ2 τ1 τs : List ValueType) (i : Instance) (f : Frame)
    (hl : List (Hostfuncidx × FunctionType)) :
    ⊢ iprop(▷ interpBr (τ1 ++ τs) i (some τ2) hl v
        (Lholed.rec_ [] τ2.length [] (.base [] []) []) [τ2] -∗
      ↪[frame] f0 -∗
      interpFrame (τ1 ++ τs) i f0 -∗
      WP (ofVal v) CTX 1 ; (Lholed.rec_ [] τ2.length [] (.base [] []) [])
        {{ w, ∃ f1 : Frame,
          ((↪[frame] f : IProp GF) -∗
            WP (ofVal w) @ Stuckness.NotStuck ; ⊤ FRAME τ2.length ; f1
              {{ w0, (interpVal τ2 w0 ∨ interpCallHostCls hl τ2 w0) ∗
                ↪[frame] f ∗ NonAtomicInvariant.own logrelNais ⊤ }}) ∗ ↪[frame] f1 }}) := by
  iintro Hbr Hf0 Hf0v
  ihave Hbr := later_mono (interp_br_unfold _ _ _ _ _ _ _) $$ Hbr
  rw [show (Lholed.rec_ [] τ2.length [] (.base [] []) [] : Lholed) =
      pushBase (.base [] []) τ2.length [] [] [] from rfl]
  iapply wp_label_push_nil_inv
  iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).1
  icases Hbr with ⟨%j, %vh, %vs', %p, >%hw, >%hbase, >%hdepth, Hbr⟩
  subst hw
  have hle := lh_depth_ge vh p hdepth
  iunfold interpBrBody at Hbr
  icases Hbr with ⟨%τs', %vs0, %k, %es, %lh', %es', %lh'', %τs'', >%hlook, -, -, -, >#Hv, -⟩
  have hjp : j - p = 0 := by
    rcases h : j - p with _ | m
    · rfl
    · rw [h] at hlook; simp at hlook
  rw [hjp] at hlook
  simp only [List.getElem?_cons_zero, Option.some.injEq] at hlook
  subst hlook
  have hjp' : j = p := by omega
  subst hjp'
  ihave %hvl := interp_val_length _ _ $$ Hv
  have hsplit : getBaseL vh = vs'.take τs''.length ++ vs'.drop τs''.length := by
    rw [hbase, List.take_append_drop]
  obtain ⟨lh1, hlh1⟩ := lfilled_get_base_pull _ vh _ _ _ _ hsplit (vfill_to_lfilled vh [.basic (.br j)]).2
  rw [hdepth] at hlh1
  rw [show ofVal (.brV vh) = vfill vh [.basic (.br j)] from rfl]
  iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
    (Φ := fun v => iprop(⌜v = .immV (vs'.drop τs''.length)⌝ ∗ ↪[frame] f0)) $$ [Hf0]
  · iapply wp_br (const_list_of_val _) (by simp [ofVal, vToEList] at hvl ⊢; omega) hlh1 $$ Hf0
    inext
    iintro Hf
    rw [List.append_nil]
    iapply IrisWp.wp_value (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
      (e := ofVal (.immV (vs'.drop τs''.length))) (v := .immV (vs'.drop τs''.length)) ⟨rfl⟩
    isplitr [Hf]
    · ipureintro; rfl
    · iexact Hf
  · iintro %v ⟨%hv, Hf⟩
    subst hv
    iexists f0
    isplitl [Hf0v]
    · iintro Hf
      ihave Hv2 := interp_val_drop _ _ _ $$ Hv
      iapply local_host_frame_val $$ Hv2 Hf0v Hf
    · iexact Hf

@[rocq_alias iriswasm.local_host_ret]
theorem local_host_ret (v : Val) (f0 : Frame) (τ2 τ1 τs : List ValueType) (i : Instance) (f : Frame)
    (hl : List (Hostfuncidx × FunctionType)) :
    ⊢ iprop(interpReturnOption (some τ2) (τ1 ++ τs) i v -∗
      ↪[frame] f0 -∗
      interpFrame (τ1 ++ τs) i f0 -∗
      WP (ofVal v) CTX 1 ; (Lholed.rec_ [] τ2.length [] (.base [] []) [])
        {{ w, ∃ f1 : Frame,
          ((↪[frame] f : IProp GF) -∗
            WP (ofVal w) @ Stuckness.NotStuck ; ⊤ FRAME τ2.length ; f1
              {{ w0, (interpVal τ2 w0 ∨ interpCallHostCls hl τ2 w0) ∗
                ↪[frame] f ∗ NonAtomicInvariant.own logrelNais ⊤ }}) ∗ ↪[frame] f1 }}) := by
  iintro Hret Hf0 Hf0v
  iunfold interpReturnOption at Hret
  icases Hret with ⟨%sh, %v', %hw, %hbase, %τs'', #Hw, -⟩
  subst hw
  ihave %hvl := interp_val_length _ _ $$ Hw
  have hsplit : simpleGetBaseL sh = v'.take τs''.length ++ v'.drop τs''.length := by
    rw [hbase, List.take_append_drop]
  obtain ⟨lh2, hlh2⟩ := lfilled_simple_get_base_pull _ (.rec_ [] τ2.length [] sh []) _ _ _ _ hsplit
    (sfill_to_lfilled (.rec_ [] τ2.length [] sh []) [.basic .return_])
  rw [show (Lholed.rec_ [] τ2.length [] (.base [] []) [] : Lholed) =
      pushBase (.base [] []) τ2.length [] [] [] from rfl]
  iapply wp_label_push_nil_inv
  iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).1
  iapply IrisWp.wp_value (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
    (e := [.label τ2.length [] (ofVal (.retV sh))]) (v := .retV (.rec_ [] τ2.length [] sh [])) ⟨rfl⟩
  iexists f0
  isplitl [Hf0v]
  · iintro Hf
    iapply (wp_frame_rewrite _ _ _ _ _ _).2
    rw [show ofVal (.retV (.rec_ [] τ2.length [] sh [])) =
      sfill (.rec_ [] τ2.length [] sh []) [.basic .return_] from rfl]
    iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
      (Φ := fun v => iprop(⌜v = .immV (v'.drop τs''.length)⌝ ∗ ↪[frame] f)) $$ [Hf]
    · iapply wp_return (to_of_val (.immV _)) (by simp [ofVal, vToEList] at hvl ⊢; omega) hlh2
      inext
      iapply IrisWp.wp_value (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
        (e := ofVal (.immV (v'.drop τs''.length))) (v := .immV (v'.drop τs''.length)) ⟨rfl⟩
      isplitr [Hf]
      · ipureintro; rfl
      · iexact Hf
    · iintro %v ⟨%hv, Hf⟩
      subst hv
      iunfold interpFrame at Hf0v
      icases Hf0v with ⟨%vs, -, -, Hown⟩
      isplitr [Hf Hown]
      · ileft; iapply interp_val_drop $$ Hw
      · iframe
  · iexact Hf0

private theorem local_host_weaken (e : Expr) (k n : Nat) (lh : Lholed) (f : Frame) (τ2 : List ValueType)
    (hl : List (Hostfuncidx × FunctionType)) :
    WP e CTX k ; lh {{ w, ∃ f1 : Frame,
      ((↪[frame] f : IProp GF) -∗
        WP (ofVal w) @ Stuckness.NotStuck ; ⊤ FRAME n ; f1
          {{ w0, (interpVal τ2 w0 ∨ interpCallHostCls hl τ2 w0) ∗
            ↪[frame] f ∗ NonAtomicInvariant.own logrelNais ⊤ }}) ∗ ↪[frame] f1 }} ⊢
    WP e CTX k ; lh {{ w, ∃ f1 : Frame,
      ((↪[frame] f : IProp GF) -∗
        WP (ofVal w) @ Stuckness.NotStuck ; ⊤ FRAME n ; f1
          {{ w0, (interpVal τ2 w0 ∨ ▷ interpCallHostCls hl τ2 w0) ∗
            ↪[frame] f ∗ NonAtomicInvariant.own logrelNais ⊤ }}) ∗ ↪[frame] f1 }} := by
  iintro H
  iapply wp_wand_ctx $$ H
  iintro %w ⟨%f1, H, Hf1⟩
  iexists f1
  isplitr [Hf1]
  · iintro Hf
    ihave H := H $$ Hf
    iapply wp_wand_frame $$ H
    iintro %w0 ⟨H, Hf, Hown⟩
    isplitl [H]
    · icases H with (H | H)
      · ileft; iexact H
      · iright; inext; iexact H
    · iframe
  · iexact Hf1

private theorem local_host_none (τ : List ValueType) (v2 : Val) (m n : Nat) (f : Frame) (vh : Llholed)
    (hb : llholedBasic vh) :
    interpVal (GF := GF) τ v2 ⊢ ⌜toVal [.local m f [.label n [] (llfill vh (ofVal v2))]] = none⌝ := by
  iintro H
  iunfold interpVal at H
  icases H with (%ht | H)
  · subst ht; ipureintro; exact to_val_local_none_none _ _ _ (IrisFundamentalHelpers.to_val_trapV_lfilled_None _ _ _)
  · iunfold interpValues at H
    icases H with ⟨%ws, %hw, -⟩
    subst hw; ipureintro; exact to_val_immV_AI_local_is_basic_None _ _ _ _ _ _ hb

/-- The Löb induction of Coq's `local_host_call`. -/
private theorem local_host_call_loeb (τ1 τs τ2 : List ValueType) (i : Instance)
    (hl : List (Hostfuncidx × FunctionType)) :
    ⊢ iprop(∀ (v2 : Val) (f1 f0 : Frame) (vs : List Value) (vh : Llholed) (τs2 : List ValueType),
      ⌜f0 = ⟨vs, i⟩⌝ -∗ ⌜llholedBasic vh⌝ -∗ interpVal (GF := GF) τs2 v2 -∗
      interpVal (τ1 ++ τs) (.immV vs) -∗
      callHostBody (τ1 ++ τs) i (some τ2) hl vh (Lholed.rec_ [] τ2.length [] (.base [] []) []) [τ2] τ2
        τs2 -∗
      ↪[frame] f1 -∗ NonAtomicInvariant.own logrelNais ⊤ -∗
      WP ([.local τ2.length f0 [.label τ2.length [] (llfill vh (ofVal v2))]] : Expr)
        {{ w, (interpVal τ2 w ∨ ▷ interpCallHostCls hl τ2 w) ∗ ↪[frame] f1 ∗
          NonAtomicInvariant.own logrelNais ⊤ }}) := by
  iloeb as IH
  iintro %v2 %f1 %f0 %vs %vh %τs2 %heqf %hb #Hv2 #Hfv #Hch Hf Hown
  ihave %hnone := local_host_none _ _ τ2.length τ2.length f0 vh hb $$ Hv2
  iapply (wp_frame_rewrite _ _ _ _ _ _).1
  iapply wp_frame_bind _ _ _ _ f0 f1 _ hnone $$ Hf
  iintro Hf
  iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).2
  iapply wp_label_push_nil
  rw [show pushBase (.base [] []) τ2.length [] [] [] = Lholed.rec_ [] τ2.length [] (.base [] []) []
    from rfl]
  iapply wp_label_bind
  ihave Hcont := Hch $$ %v2 %f0 Hv2 [Hf Hown]
  · isplitl [Hf]
    · iexact Hf
    · iunfold interpFrame
      iexists vs
      isplitr
      · ipureintro; exact heqf
      isplitr
      · iexact Hfv
      · iexact Hown
  iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ Hcont
  iintro %v1 ⟨Hres, %f2, Hf2, Hfv2⟩
  icases Hres with (H1 | H2 | H3 | H4)
  · iunfold interpVal at H1
    icases H1 with (%ht | H1)
    · subst ht
      ihave H := local_host_trap f2 τ1 τs i f1 τ2 hl $$ Hf2 Hfv2
      rw [show ofVal .trapV = [AdministrativeInstruction.trap] from rfl]
      iapply local_host_weaken $$ H
    · ihave H := local_host_val v1 f2 τ2 τ1 τs i f1 hl $$ H1 Hf2 Hfv2
      iapply local_host_weaken $$ H
  · ihave H := local_host_br v1 f2 τ2 τ1 τs i f1 hl $$ H2 Hf2 Hfv2
    iapply local_host_weaken $$ H
  · ihave H := local_host_ret v1 f2 τ2 τ1 τs i f1 hl $$ H3 Hf2 Hfv2
    iapply local_host_weaken $$ H
  · ihave H4 := later_mono (interp_call_host_unfold _ _ _ _ _ _ _ _).1 $$ H4
    rw [show (Lholed.rec_ [] τ2.length [] (.base [] []) [] : Lholed) =
        pushBase (.base [] []) τ2.length [] [] [] from rfl]
    iapply wp_label_push_nil_inv
    iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).1
    icases H4 with ⟨%vh', %v', %tf', %h', %τa, %τb, >%hw, >%htf', >%hin', >%hb', >#Hv', Hch'⟩
    subst hw
    rw [show ofVal (.callHostV tf' h' v' vh') = llfill vh' [.callHost tf' h' v'] from rfl, llfill_label]
    iapply IrisWp.wp_value (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
      (e := llfill (.label [] τ2.length [] vh' []) [.callHost tf' h' v'])
      (v := .callHostV tf' h' v' (.label [] τ2.length [] vh' [])) ⟨rfl⟩
    iexists f2
    isplitl [Hfv2 Hch']
    · iintro Hf
      iapply (wp_frame_rewrite _ _ _ _ _ _).2
      rw [show ofVal (.callHostV tf' h' v' (.label [] τ2.length [] vh' [])) =
        llfill (.label [] τ2.length [] vh' []) [.callHost tf' h' v'] from rfl, llfill_local]
      iapply IrisWp.wp_value (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
        (e := llfill (.local [] τ2.length f2 (.label [] τ2.length [] vh' []) []) [.callHost tf' h' v'])
        (v := .callHostV tf' h' v' (.local [] τ2.length f2 (.label [] τ2.length [] vh' []) [])) ⟨rfl⟩
      iunfold interpFrame at Hfv2
      icases Hfv2 with ⟨%vs2, %heqf2, #Hfv2, Hown⟩
      isplitr [Hf Hown]
      · iright
        inext
        icases Hch' with #Hch'
        rw [fixpoint_interp_call_host_cls_eq]
        unfold interpCallHostClsDef
        iexists .local [] τ2.length f2 (.label [] τ2.length [] vh' []) [], v', tf', h', τa, τb
        isplitr
        · ipureintro; rfl
        isplitr
        · ipureintro; exact htf'
        isplitr
        · ipureintro; exact hin'
        isplitr
        · ipureintro; simp [llholedBasic, isBasicExpr, hb']
        isplitr
        · iexact Hv'
        imodintro
        iintro %v4 %f3 #Hv3 Hf Hown
        rw [← llfill_local, ← llfill_label]
        rw [show pushBase (.base [] []) τ2.length [] [] [] = Lholed.rec_ [] τ2.length [] (.base [] []) []
          from rfl]
        iapply IH $$ %v4 %f3 %f2 %vs2 %vh' %τb %heqf2 %hb' Hv3 Hfv2 Hch' Hf Hown
      · iframe
    · iexact Hf2

@[rocq_alias iriswasm.local_host_call]
theorem local_host_call (v : Val) (f0 : Frame) (τ2 τ1 τs : List ValueType) (i : Instance) (f : Frame)
    (hl : List (Hostfuncidx × FunctionType)) :
    ⊢ iprop(interpCallHost (τ1 ++ τs) i (some τ2) hl v
        (Lholed.rec_ [] τ2.length [] (.base [] []) []) [τ2] τ2 -∗
      ↪[frame] f0 -∗
      interpFrame (τ1 ++ τs) i f0 -∗
      WP (ofVal v) CTX 1 ; (Lholed.rec_ [] τ2.length [] (.base [] []) [])
        {{ w, ∃ f1 : Frame,
          ((↪[frame] f : IProp GF) -∗
            WP (ofVal w) @ Stuckness.NotStuck ; ⊤ FRAME τ2.length ; f1
              {{ w0, (interpVal τ2 w0 ∨ interpCallHostCls hl τ2 w0) ∗
                ↪[frame] f ∗ NonAtomicInvariant.own logrelNais ⊤ }}) ∗ ↪[frame] f1 }}) := by
  iintro Hch Hf0 Hf0v
  ihave Hch := (interp_call_host_unfold _ _ _ _ _ _ _ _).1 $$ Hch
  icases Hch with ⟨%vh, %v0, %tf, %h, %τs1, %τs2, %hw, %htf, %hin, %hb, #Hw, #Hch⟩
  subst hw
  rw [show (Lholed.rec_ [] τ2.length [] (.base [] []) [] : Lholed) =
      pushBase (.base [] []) τ2.length [] [] [] from rfl]
  iapply wp_label_push_nil_inv
  iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).1
  rw [show ofVal (.callHostV tf h v0 vh) = llfill vh [.callHost tf h v0] from rfl, llfill_label]
  iapply IrisWp.wp_value (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
    (e := llfill (.label [] τ2.length [] vh []) [.callHost tf h v0])
    (v := .callHostV tf h v0 (.label [] τ2.length [] vh [])) ⟨rfl⟩
  iexists f0
  isplitl [Hf0v]
  · iintro Hf
    iapply (wp_frame_rewrite _ _ _ _ _ _).2
    rw [show ofVal (.callHostV tf h v0 (.label [] τ2.length [] vh [])) =
      llfill (.label [] τ2.length [] vh []) [.callHost tf h v0] from rfl, llfill_local]
    iapply IrisWp.wp_value (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
      (e := llfill (.local [] τ2.length f0 (.label [] τ2.length [] vh []) []) [.callHost tf h v0])
      (v := .callHostV tf h v0 (.local [] τ2.length f0 (.label [] τ2.length [] vh []) [])) ⟨rfl⟩
    iunfold interpFrame at Hf0v
    icases Hf0v with ⟨%vs, %heqf, #Hfv, Hown⟩
    isplitr [Hf Hown]
    · iright
      rw [fixpoint_interp_call_host_cls_eq]
      unfold interpCallHostClsDef
      iexists .local [] τ2.length f0 (.label [] τ2.length [] vh []) [], v0, tf, h, τs1, τs2
      isplitr
      · ipureintro; rfl
      isplitr
      · ipureintro; exact htf
      isplitr
      · ipureintro; exact hin
      isplitr
      · ipureintro; simp [llholedBasic, isBasicExpr, hb]
      isplitr
      · iexact Hw
      imodintro
      iintro %v2 %f1 #Hv2 Hf Hown
      rw [← llfill_local, ← llfill_label]
      rw [show pushBase (.base [] []) τ2.length [] [] [] = Lholed.rec_ [] τ2.length [] (.base [] []) []
        from rfl]
      iapply local_host_call_loeb τ1 τs τ2 i hl $$ %v2 %f1 %f0 %vs %vh %τs2 %heqf %hb Hv2 Hfv Hch Hf Hown
    · iframe
  · iexact Hf0

end IrisWasm
