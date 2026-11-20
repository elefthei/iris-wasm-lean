/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import Wasm.TypeChecker
import Wasm.Properties

/-! Port of `theories/type_checker_reflects_typing.v`: the type checker reflects typing. -/

namespace Wasm

#rocq_ignore iriswasm.simplify_hypothesis "local Ltac; proofs use simp/omega"
#rocq_ignore iriswasm.simplify_goal "local Ltac; proofs use simp/omega"
#rocq_ignore iriswasm.resolve_bet "local Ltac; proofs use simp/omega"
#rocq_ignore iriswasm.auto_rewrite_cond "local Ltac; proofs use simp/omega"
#rocq_ignore iriswasm.simplify_type_update "local Ltac; proofs use simp/omega"
#rocq_ignore iriswasm.fold_remember_check "local Ltac; `check` is already structural"
#rocq_ignore iriswasm.le_le "ssrnat `<=` vs Coq `le` bridge"


theorem ctCompat_iff {a b : CheckerTypeAux} :
    ctCompat a b = true ↔ a = .any ∨ b = .any ∨ a = b := by
  cases a <;> cases b <;> simp [ctCompat]

theorem ctListCompat_iff {l1 l2 : List CheckerTypeAux} :
    ctListCompat l1 l2 = true ↔ l1.length = l2.length ∧
      ∀ i (h1 : i < l1.length) (h2 : i < l2.length), ctCompat l1[i] l2[i] = true := by
  unfold ctListCompat
  induction l1 generalizing l2 with
  | nil => cases l2 <;> simp
  | cons a l1 ih =>
    cases l2 with
    | nil => simp
    | cons b l2 =>
      simp only [List.all2_cons, Bool.and_eq_true, ih, List.length_cons]
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨by omega, fun i hi hj => ?_⟩
        cases i with
        | zero => simpa using h1
        | succ i => simpa using h3 i (by simpa using hi) (by simpa using hj)
      · rintro ⟨h1, h2⟩
        exact ⟨by simpa using h2 0 (by simp) (by simp), by omega,
          fun i hi hj => by
            have := h2 (i+1) (by simpa using hi) (by simpa using hj); simpa using this⟩

theorem ctSuffix_iff {ts ts' : List CheckerTypeAux} :
    ctSuffix ts ts' = true ↔ ts.length ≤ ts'.length ∧
      ∀ i (h : i < ts.length) (h' : ts'.length - ts.length + i < ts'.length),
        ctCompat ts'[ts'.length - ts.length + i] ts[i] = true := by
  simp only [ctSuffix, Bool.and_eq_true, decide_eq_true_eq, ctListCompat_iff, List.length_drop,
    List.getElem_drop]
  constructor
  · rintro ⟨h1, -, h3⟩
    exact ⟨h1, fun i h h' => h3 i (by omega) h⟩
  · rintro ⟨h1, h3⟩
    exact ⟨h1, by omega, fun i h h' => h3 i h' (by omega)⟩

@[simp] theorem toCtList_length (l : List ValueType) : (toCtList l).length = l.length := by
  simp [toCtList]
theorem ctCompat_comm (a b : CheckerTypeAux) : ctCompat a b = ctCompat b a := by
  cases a <;> cases b <;> simp [ctCompat]
  rename_i a b; cases h : a == b <;> cases h' : b == a <;> simp_all

@[simp] theorem ctCompat_any_left (a : CheckerTypeAux) : ctCompat .any a = true := rfl
@[simp] theorem ctCompat_any_right (a : CheckerTypeAux) : ctCompat a .any = true := by
  cases a <;> rfl
@[simp] theorem ctCompat_self (a : CheckerTypeAux) : ctCompat a a = true := by
  cases a <;> simp [ctCompat]
@[simp] theorem ctCompat_some_some (a b : ValueType) :
    ctCompat (.some a) (.some b) = decide (a = b) := by
  simp only [ctCompat]; cases h : a == b <;> simp_all

@[simp] theorem getElem_toCtList (l : List ValueType) (i : Nat) (h : i < (toCtList l).length) :
    (toCtList l)[i] = .some (l[i]'(by simpa [toCtList] using h)) := by simp [toCtList]

@[rocq_alias iriswasm.result_typingP]
theorem result_typingP (r : Result) (ts : ResultType) :
    resultTypesAgree ts r = true ↔ ResultTyping r ts := by
  cases r with
  | values vs =>
    have key : ∀ ts vs, List.all2 typesAgree ts vs = true ↔ vs.map typeof = ts := by
      intro ts vs
      induction ts generalizing vs with
      | nil => cases vs <;> simp
      | cons t ts ih => cases vs with
        | nil => simp
        | cons v vs =>
          simp only [List.all2_cons, Bool.and_eq_true, ih, List.map_cons, List.cons.injEq,
            typesAgree, beq_iff_eq]
    simp only [resultTypesAgree]
    constructor
    · intro h; obtain rfl := (key ts vs).1 h; exact .values
    · intro h; cases h; exact (key _ _).2 rfl
  | trap => simpa [resultTypesAgree] using ResultTyping.trap

@[rocq_alias iriswasm.nth_error_ssr]
theorem nth_error_ssr {T : Type} (l : List T) (n : Nat) (x x0 : T) :
    l[n]? = some x → l.getD n x0 = x := by
  intro h; simp [List.getD_eq_getElem?_getD, h]

@[rocq_alias iriswasm.size_ct_list]
theorem size_ct_list (l : List ValueType) : (toCtList l).length = l.length := by
  simp

@[rocq_alias iriswasm.ssr_nth_error]
theorem ssr_nth_error {T : Type} (l : List T) (n : Nat) (x x0 : T) :
    l.getD n x0 = x → n < l.length → l[n]? = some x := by
  intro h hn; simp_all [List.getD_eq_getElem?_getD]

@[rocq_alias iriswasm.ct_compat_symmetry]
theorem ct_compat_symmetry (c1 c2 : CheckerTypeAux) :
    ctCompat c1 c2 = true → ctCompat c2 c1 = true := by
  rw [ctCompat_comm]; exact id

@[rocq_alias iriswasm.ct_list_compat_rcons_bool]
theorem ct_list_compat_rcons_bool (l1 l2 : List CheckerTypeAux) (x1 x2 : CheckerTypeAux) :
    ctListCompat (l1 ++ [x1]) (l2 ++ [x2]) = (ctCompat x1 x2 && ctListCompat l1 l2) := by
  unfold ctListCompat
  induction l1 generalizing l2 with
  | nil => cases l2 with
    | nil => simp
    | cons b l2 => cases l2 <;> simp
  | cons a l1 ih => cases l2 with
    | nil => cases l1 <;> simp
    | cons b l2 => simp [ih]; cases ctCompat a b <;> simp

@[rocq_alias iriswasm.ct_list_compat_rcons]
theorem ct_list_compat_rcons (l1 l2 : List CheckerTypeAux) (x1 x2 : CheckerTypeAux) :
    ctListCompat (l1 ++ [x1]) (l2 ++ [x2]) = true ↔
      ctCompat x1 x2 = true ∧ ctListCompat l1 l2 = true := by
  simp [ct_list_compat_rcons_bool]

@[rocq_alias iriswasm.ct_suffix_rcons]
theorem ct_suffix_rcons (l1 l2 : List CheckerTypeAux) (x1 x2 : CheckerTypeAux) :
    ctSuffix (l1 ++ [x1]) (l2 ++ [x2]) = true ↔ ctCompat x1 x2 = true ∧ ctSuffix l1 l2 = true := by
  simp only [ctSuffix, List.length_append, List.length_singleton, Nat.add_sub_add_right]
  by_cases h : l1.length ≤ l2.length
  · rw [List.drop_append_of_le_length (by omega), ct_list_compat_rcons_bool, ctCompat_comm]
    simp [h]
  · simp [h]

@[rocq_alias iriswasm.ct_suffix_empty]
theorem ct_suffix_empty (l : List CheckerTypeAux) : ctSuffix [] l = true := by
  simp [ctSuffix, ctListCompat]

@[rocq_alias iriswasm.ct_suffix_any_grow]
theorem ct_suffix_any_grow (l1 l2 : List CheckerTypeAux) :
    ctSuffix l1 l2 = true → l1.length < l2.length → ctSuffix (.any :: l1) l2 = true := by
  rw [ctSuffix_iff, ctSuffix_iff]
  rintro ⟨-, h⟩ hl
  refine ⟨by simp; omega, fun i hi hi' => ?_⟩
  cases i with
  | zero => simp
  | succ i =>
    have := h i (by simpa using hi) (by simp at hi hi'; omega)
    simp only [List.length_cons, List.getElem_cons_succ]
    have e : l2.length - (l1.length + 1) + (i + 1) = l2.length - l1.length + i := by
      simp at hi; omega
    simp only [e]; exact this

@[rocq_alias iriswasm.ct_suffix_any_1]
theorem ct_suffix_any_1 (l : List CheckerTypeAux) : 0 < l.length → ctSuffix [.any] l = true := by
  intro h; rw [ctSuffix_iff]; simp; omega

@[rocq_alias iriswasm.ct_list_compat_self]
theorem ct_list_compat_self (l : List CheckerTypeAux) : ctListCompat l l = true := by
  rw [ctListCompat_iff]; simp

@[rocq_alias iriswasm.ct_suffix_self]
theorem ct_suffix_self (l : List CheckerTypeAux) : ctSuffix l l = true := by
  simp [ctSuffix, ct_list_compat_self]

@[rocq_alias iriswasm.ct_suffix_suffix]
theorem ct_suffix_suffix (l1 l2 : List ValueType) :
    ctSuffix (toCtList l2) (toCtList (l1 ++ l2)) = true := by
  rw [ctSuffix_iff]; simp [List.getElem_append_right]

@[rocq_alias iriswasm.ct_suffix_prefix]
theorem ct_suffix_prefix (l1 l2 l3 : List CheckerTypeAux) :
    ctSuffix (l1 ++ l2) l3 = true → ctSuffix l2 l3 = true := by
  rw [ctSuffix_iff, ctSuffix_iff]
  rintro ⟨h1, h2⟩
  simp at h1
  refine ⟨by omega, fun i hi hi' => ?_⟩
  have := h2 (l1.length + i) (by simp; omega) (by simp; omega)
  rw [List.getElem_append_right (by omega)] at this
  simp only [List.length_append, Nat.add_sub_cancel_left] at this
  have e : l3.length - (l1.length + l2.length) + (l1.length + i) = l3.length - l2.length + i := by
    omega
  simp only [e] at this; exact this

@[rocq_alias iriswasm.ct_suffix_extend]
theorem ct_suffix_extend (l1 l2 l3 : List CheckerTypeAux) :
    ctSuffix l1 l2 = true → ctSuffix l1 (l3 ++ l2) = true := by
  rw [ctSuffix_iff, ctSuffix_iff]
  rintro ⟨h1, h2⟩
  refine ⟨by simp; omega, fun i hi hi' => ?_⟩
  have := h2 i hi (by omega)
  simp only [List.length_append]
  rw [List.getElem_append_right (by omega)]
  have e : l3.length + l2.length - l1.length + i - l3.length = l2.length - l1.length + i := by
    omega
  simp only [e]; exact this

@[rocq_alias iriswasm.ct_suffix_size]
theorem ct_suffix_size (ct1 ct2 : List CheckerTypeAux) :
    ctSuffix ct1 ct2 = true → ct1.length ≤ ct2.length := by
  rw [ctSuffix_iff]; exact And.left

@[rocq_alias iriswasm.upd_label_overwrite]
theorem upd_label_overwrite (C : TContext) (loc : List ValueType) (lab : List (List ValueType))
    (ret : Option (List ValueType)) (lab' : List (List ValueType)) :
    updLabel (updLocalLabelReturn C loc lab ret) lab' = updLocalLabelReturn C loc lab' ret := by
  rfl

@[rocq_alias iriswasm.consume_empty]
theorem consume_empty (l : CheckerType) : consume l [] = l := by
  cases l <;> simp [consume, ct_suffix_empty, toCtList]

@[rocq_alias iriswasm.produce_empty]
theorem produce_empty (l : CheckerType) : produce l (.type []) = l := by
  cases l <;> simp [produce, toCtList]

@[rocq_alias iriswasm.produce_empty_top]
theorem produce_empty_top (l : CheckerType) : l ≠ .bot → produce l (.topType []) = .topType [] := by
  cases l <;> simp [produce]

@[rocq_alias iriswasm.type_update_empty_cons]
theorem type_update_empty_cons (l ct : CheckerType) : typeUpdate l [] ct = produce l ct := by
  simp [typeUpdate, consume_empty]

@[rocq_alias iriswasm.type_update_empty_prod]
theorem type_update_empty_prod (l : CheckerType) (ts : List CheckerTypeAux) :
    typeUpdate l ts (.type []) = consume l ts := by
  simp [typeUpdate, produce_empty]

@[rocq_alias iriswasm.CT_top_empty_consume]
theorem CT_top_empty_consume (tf : List CheckerTypeAux) : consume (.topType []) tf = .topType [] := by
  simp [consume, ct_suffix_empty]

@[rocq_alias iriswasm.populate_ct_aux_single]
def populateCtAuxSingle (cta : CheckerTypeAux) : ValueType :=
  match cta with
  | .any => .i32
  | .some vt => vt

@[rocq_alias iriswasm.populate_ct_aux]
def populateCtAux (l : List CheckerTypeAux) : List ValueType := l.map populateCtAuxSingle

@[rocq_alias iriswasm.populate_ct]
def populateCt (ct : CheckerType) : List ValueType :=
  match ct with
  | .type tn => tn
  | .topType tn => populateCtAux tn
  | .bot => []

@[rocq_alias iriswasm.populate_ct_aux_suffix]
theorem populate_ct_aux_suffix (l : List CheckerTypeAux) :
    ctSuffix l (toCtList (populateCtAux l)) = true := by
  rw [ctSuffix_iff]
  simp only [toCtList_length, populateCtAux, List.length_map, Nat.sub_self, Nat.zero_add,
    Nat.le_refl, true_and]
  intro i hi _
  simp only [getElem_toCtList, List.getElem_map]
  generalize l[i] = c
  cases c <;> simp [populateCtAuxSingle]

@[rocq_alias iriswasm.populate_ct_agree]
theorem populate_ct_agree (l : CheckerType) : l ≠ .bot → cTypesAgree l (populateCt l) = true := by
  cases l <;> simp [cTypesAgree, populateCt, populate_ct_aux_suffix]

@[simp] theorem toCtList_append (l1 l2 : List ValueType) :
    toCtList (l1 ++ l2) = toCtList l1 ++ toCtList l2 := by simp [toCtList]

@[rocq_alias iriswasm.type_update_prefix]
theorem type_update_prefix (l1 l2 l3 : List ValueType) (cons : List CheckerTypeAux)
    (prod : CheckerType) :
    typeUpdate (.type l1) cons prod = .type l2 →
      typeUpdate (.type (l3 ++ l1)) cons prod = .type (l3 ++ l2) := by
  intro h
  simp only [typeUpdate, consume] at h ⊢
  split at h
  next hs =>
    have hl := ct_suffix_size _ _ hs
    simp only [toCtList_length] at hl
    have hs' : ctSuffix cons (toCtList (l3 ++ l1)) = true := by
      simpa using ct_suffix_extend _ _ (toCtList l3) hs
    simp only [hs', ↓reduceIte]
    rw [List.length_append, List.take_append,
      List.take_of_length_le (by omega), Nat.add_sub_assoc hl, Nat.add_sub_cancel_left]
    cases prod <;> simp_all [produce]
  next => cases prod <;> simp [produce] at h

@[rocq_alias iriswasm.type_update_prefix_top]
theorem type_update_prefix_top (l1 : List ValueType) (l2 : List CheckerTypeAux)
    (l3 : List ValueType) (cons : List CheckerTypeAux) (prod : CheckerType) :
    typeUpdate (.type l1) cons prod = .topType l2 →
      typeUpdate (.type (l3 ++ l1)) cons prod = .topType l2 := by
  intro h
  simp only [typeUpdate, consume] at h ⊢
  split at h
  next hs =>
    have hs' : ctSuffix cons (toCtList (l3 ++ l1)) = true := by
      simpa using ct_suffix_extend _ _ (toCtList l3) hs
    simp only [hs', ↓reduceIte]
    cases prod <;> simp_all [produce]
  next => cases prod <;> simp [produce] at h

@[rocq_alias iriswasm.check_rcons]
theorem check_rcons (es : List BasicInstruction) (e : BasicInstruction) (C : TContext)
    (ts : CheckerType) : check C (es ++ [e]) ts = checkSingle C (check C es ts) e := by
  simp [check_eq_foldl]

theorem typeUpdate_top (l : List CheckerTypeAux) (c : List CheckerTypeAux) (p : CheckerType) :
    typeUpdate (.topType l) c p = .bot ∨ ∃ l', typeUpdate (.topType l) c p = .topType l' := by
  simp only [typeUpdate, consume]
  split
  · cases p <;> simp [produce]
  · split
    · cases p <;> simp [produce]
    · simp [produce]

theorem consume_top (l : List CheckerTypeAux) (c : List CheckerTypeAux) :
    consume (.topType l) c = .bot ∨ ∃ l', consume (.topType l) c = .topType l' := by
  simp only [consume]; split
  · simp
  · split <;> simp

theorem checkSingle_top (C : TContext) (l : List CheckerTypeAux) (e : BasicInstruction) :
    checkSingle C (.topType l) e = .bot ∨ ∃ l', checkSingle C (.topType l) e = .topType l' := by
  cases e <;> (try (rename_i c _ _; cases c)) <;>
    simp only [checkSingle.eq_def, beq_iff_eq, reduceCtorEq, ite_false, typeUpdateSelect] <;>
    (repeat' split) <;>
    first
    | exact Or.inl rfl
    | exact typeUpdate_top _ _ _
    | exact consume_top _ _
    | exact Or.inr ⟨_, rfl⟩

@[rocq_alias iriswasm.check_single_bot]
theorem check_single_bot (C : TContext) (e : BasicInstruction) : checkSingle C .bot e = .bot := by
  rw [checkSingle.eq_def]; simp

@[rocq_alias iriswasm.check_single_notop]
theorem check_single_notop (C : TContext) (ct : CheckerType) (ts : List ValueType)
    (e : BasicInstruction) : checkSingle C ct e = .type ts → ∃ ts', ct = .type ts' := by
  intro h
  cases ct with
  | type l => exact ⟨l, rfl⟩
  | topType l =>
    rcases checkSingle_top C l e with h' | ⟨l', h'⟩ <;> rw [h'] at h <;> cases h
  | bot => rw [check_single_bot] at h; cases h

theorem typeUpdateSelect_weaken (ts ts2 ts0 : List ValueType) :
    typeUpdateSelect (.type ts) = .type ts0 →
      typeUpdateSelect (.type (ts2 ++ ts)) = .type (ts2 ++ ts0) := by
  simp only [typeUpdateSelect]
  intro h
  split at h
  next hc =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
    have e2 : (ts2 ++ ts)[(ts2 ++ ts).length - 2]? = ts[ts.length - 2]? := by
      rw [List.getElem?_append_right (by simp; omega)]; congr 1; simp; omega
    have e3 : (ts2 ++ ts)[(ts2 ++ ts).length - 3]? = ts[ts.length - 3]? := by
      rw [List.getElem?_append_right (by simp; omega)]; congr 1; simp; omega
    have hc' : (decide (3 ≤ (ts2 ++ ts).length) && (ts2 ++ ts)[(ts2 ++ ts).length - 2]? ==
        (ts2 ++ ts)[(ts2 ++ ts).length - 3]?) = true := by
      simp only [e2, e3, hc.2, Bool.and_eq_true, decide_eq_true_eq, beq_self_eq_true, and_true]
      simp; omega
    simp only [hc', ↓reduceIte]
    rw [← type_update_empty_prod] at h ⊢
    exact type_update_prefix _ _ _ _ _ h
  next => cases h

theorem typeUpdateSelect_type (ts : List ValueType) (l : List CheckerTypeAux) :
    typeUpdateSelect (.type ts) ≠ .topType l := by
  simp only [typeUpdateSelect, consume]
  split
  · split <;> simp
  · simp

@[rocq_alias iriswasm.check_single_weaken]
theorem check_single_weaken (C : TContext) (e : BasicInstruction) (ts ts2 ts0 : List ValueType) :
    checkSingle C (.type ts) e = .type ts0 →
      checkSingle C (.type (ts2 ++ ts)) e = .type (ts2 ++ ts0) := by
  intro h
  cases e <;> (try (rename_i c _ _; cases c)) <;>
    simp only [checkSingle.eq_def, beq_iff_eq, reduceCtorEq, ite_false] at h ⊢ <;>
    (repeat' split at h) <;>
    (try simp only [*, ↓reduceIte] at ⊢) <;>
    first
    | exact type_update_prefix _ _ _ _ _ h
    | exact typeUpdateSelect_weaken _ _ _ h
    | cases h; rfl
    | cases h
    | skip

@[rocq_alias iriswasm.check_single_weaken_top]
theorem check_single_weaken_top (C : TContext) (e : BasicInstruction) (ts ts2 : List ValueType)
    (ts0 : List CheckerTypeAux) :
    checkSingle C (.type ts) e = .topType ts0 →
      checkSingle C (.type (ts2 ++ ts)) e = .topType ts0 := by
  intro h
  cases e <;> (try (rename_i c _ _; cases c)) <;>
    simp only [checkSingle.eq_def, beq_iff_eq, reduceCtorEq, ite_false] at h ⊢ <;>
    (repeat' split at h) <;>
    (try simp only [*, ↓reduceIte] at ⊢) <;>
    first
    | exact type_update_prefix_top _ _ _ _ _ h
    | exact absurd h (typeUpdateSelect_type _ _)
    | cases h
    | skip

theorem check_bot (C : TContext) (es : List BasicInstruction) : check C es .bot = .bot := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [check, check_single_bot, ih]

theorem check_notop (C : TContext) (es : List BasicInstruction) (ct : CheckerType)
    (ts : List ValueType) : check C es ct = .type ts → ∃ ts', ct = .type ts' := by
  induction es generalizing ct with
  | nil => intro h; exact ⟨ts, h⟩
  | cons e es ih =>
    intro h
    obtain ⟨ts', h'⟩ := ih _ h
    exact check_single_notop C ct ts' e h'

@[rocq_alias iriswasm.check_weaken]
theorem check_weaken (C : TContext) (es : List BasicInstruction) (ts ts2 ts0 : List ValueType) :
    check C es (.type ts) = .type ts0 → check C es (.type (ts2 ++ ts)) = .type (ts2 ++ ts0) := by
  induction es generalizing ts with
  | nil => intro h; cases h; rfl
  | cons e es ih =>
    intro h
    simp only [check] at h ⊢
    obtain ⟨ts', h'⟩ := check_notop C es _ _ h
    rw [h'] at h
    rw [check_single_weaken C e ts ts2 ts' h']
    exact ih ts' h

@[rocq_alias iriswasm.check_weaken_top]
theorem check_weaken_top (C : TContext) (es : List BasicInstruction) (ts ts2 : List ValueType)
    (ts0 : List CheckerTypeAux) :
    check C es (.type ts) = .topType ts0 → check C es (.type (ts2 ++ ts)) = .topType ts0 := by
  induction es generalizing ts with
  | nil => intro h; cases h
  | cons e es ih =>
    intro h
    simp only [check] at h ⊢
    cases h' : checkSingle C (.type ts) e with
    | type ts' => rw [h'] at h; rw [check_single_weaken C e ts ts2 ts' h']; exact ih ts' h
    | topType l => rw [check_single_weaken_top C e ts ts2 l h']; rwa [h'] at h
    | bot => rw [h', check_bot] at h; cases h

@[rocq_alias iriswasm.same_lab_h_condition]
theorem same_lab_h_condition (C : TContext) (ts : List ValueType) (l : List Nat) :
    l.all (fun i => decide (i < C.label.length) && plop2 C i ts) = true →
      sameLabH l C.label ts = some ts := by
  induction l with
  | nil => intro; rfl
  | cons a l ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq, plop2, beq_iff_eq]
    rintro ⟨⟨h1, h2⟩, h3⟩
    simp only [sameLabH, h2]
    simp [show ¬ C.label.length ≤ a by omega, ih h3]

@[rocq_alias iriswasm.same_lab_h_all]
theorem same_lab_h_all (C : TContext) (ts : List ValueType) (l : List Nat) :
    sameLabH l C.label ts = some ts →
      l.all (fun i => decide (i < C.label.length) && plop2 C i ts) = true := by
  induction l with
  | nil => intro; rfl
  | cons a l ih =>
    simp only [sameLabH]
    intro h
    split at h; · cases h
    split at h; · cases h
    next xx hxx =>
      split at h
      next heq =>
        simp only [beq_iff_eq] at heq; subst heq
        simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq, plop2, beq_iff_eq]
        exact ⟨⟨by omega, hxx⟩, by simpa [plop2] using ih h⟩
      next => cases h

@[rocq_alias iriswasm.same_lab_h_rec]
theorem same_lab_h_rec (x : Nat) (l : List Nat) (C : TContext) (ts : List ValueType) :
    sameLabH (x :: l) C.label ts = some ts → sameLabH l C.label ts = some ts := by
  simp only [sameLabH]
  intro h
  split at h; · cases h
  split at h; · cases h
  split at h
  next heq => simp only [beq_iff_eq] at heq; subst heq; exact h
  next => cases h

@[rocq_alias iriswasm.same_lab_h_consistent]
theorem same_lab_h_consistent (l : List Nat) (lab : List (List ValueType))
    (ts ts' : List ValueType) : sameLabH l lab ts' = some ts → ts = ts' := by
  induction l generalizing ts' with
  | nil => intro h; cases h; rfl
  | cons a l ih =>
    simp only [sameLabH]
    intro h
    split at h; · cases h
    split at h; · cases h
    split at h
    next heq => simp only [beq_iff_eq] at heq; subst heq; exact ih _ h
    next => cases h

@[rocq_alias iriswasm.same_lab_same_lab_h]
theorem same_lab_same_lab_h (l : List Nat) (lab : List (List ValueType)) (ts : List ValueType) :
    sameLab l lab = some ts → sameLabH l lab ts = some ts := by
  cases l with
  | nil => intro h; cases h
  | cons a l =>
    simp only [sameLab, sameLabH]
    intro h
    split at h; · cases h
    split at h
    next xx hxx =>
      obtain rfl := same_lab_h_consistent _ _ _ _ h
      simp [hxx, h]; omega
    next => cases h

theorem ctCompat_trans_some (t : ValueType) (a b : CheckerTypeAux) :
    ctCompat (.some t) a = true → ctCompat (.some t) b = true → ctCompat a b = true := by
  cases a <;> cases b <;> simp_all

@[rocq_alias iriswasm.ct_list_compat_trans]
theorem ct_list_compat_trans (ts1 ts2 : List CheckerTypeAux) (ts : List ValueType) :
    ctListCompat (toCtList ts) ts1 = true → ctListCompat (toCtList ts) ts2 = true →
      ctListCompat ts1 ts2 = true := by
  simp only [ctListCompat_iff, toCtList_length, getElem_toCtList]
  rintro ⟨h1, h2⟩ ⟨h3, h4⟩
  exact ⟨by omega, fun i hi hj => ctCompat_trans_some _ _ _ (h2 i (by omega) hi)
    (h4 i (by omega) hj)⟩

@[rocq_alias iriswasm.ct_suffix_take]
theorem ct_suffix_take (l1 l2 : List CheckerTypeAux) (n : Nat) :
    ctSuffix l1 l2 = true → n ≤ l1.length →
      ctSuffix (l1.take (l1.length - n)) (l2.take (l2.length - n)) = true := by
  simp only [ctSuffix_iff, List.length_take, List.getElem_take]
  rintro ⟨h1, h2⟩ hn
  refine ⟨by omega, fun i hi hi' => ?_⟩
  have := h2 i (by omega) (by omega)
  have e : min (l2.length - n) l2.length - min (l1.length - n) l1.length + i =
      l2.length - l1.length + i := by omega
  simp only [e]; exact this

@[rocq_alias iriswasm.ct_list_compat_cat]
theorem ct_list_compat_cat (l1 l2 l3 l4 : List CheckerTypeAux) :
    ctListCompat l1 l2 = true → ctListCompat l3 l4 = true →
      ctListCompat (l1 ++ l3) (l2 ++ l4) = true := by
  unfold ctListCompat
  induction l1 generalizing l2 with
  | nil => cases l2 <;> simp
  | cons a l1 ih => cases l2 <;> simp_all

@[rocq_alias iriswasm.ct_list_compat_extend]
theorem ct_list_compat_extend (l1 l2 l3 : List CheckerTypeAux) :
    ctListCompat l1 l2 = true → ctListCompat (l1 ++ l3) (l2 ++ l3) = true := fun h =>
  ct_list_compat_cat _ _ _ _ h (ct_list_compat_self l3)

@[rocq_alias iriswasm.ct_list_compat_take]
theorem ct_list_compat_take (l1 l2 : List CheckerTypeAux) (n : Nat) :
    ctListCompat l1 l2 = true → ctListCompat (l1.take n) (l2.take n) = true := by
  unfold ctListCompat
  induction l1 generalizing l2 n with
  | nil => cases l2 <;> simp
  | cons a l1 ih => cases l2 <;> cases n <;> simp_all

@[rocq_alias iriswasm.ct_list_compat_drop]
theorem ct_list_compat_drop (l1 l2 : List CheckerTypeAux) (n : Nat) :
    ctListCompat l1 l2 = true → ctListCompat (l1.drop n) (l2.drop n) = true := by
  unfold ctListCompat
  induction l1 generalizing l2 n with
  | nil => cases l2 <;> simp
  | cons a l1 ih => cases l2 <;> cases n <;> simp_all

@[rocq_alias iriswasm.ct_list_compat_drop_shift]
theorem ct_list_compat_drop_shift (l1 l2 : List CheckerTypeAux) (n a b : Nat)
    (c1 c2 : CheckerTypeAux) :
    ctListCompat (l1.drop n) l2 = true → a < l1.length → b < l2.length → a = b + n →
      ctCompat (l1.getD a c1) (l2.getD b c2) = true := by
  intro h ha hb hab; subst hab
  rw [ctListCompat_iff] at h
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ha,
    List.getElem?_eq_getElem hb, Option.getD_some]
  have := h.2 b (by simp; omega) hb
  simpa [List.getElem_drop, Nat.add_comm] using this

@[rocq_alias iriswasm.ct_list_nth_type]
theorem ct_list_nth_type (l : List ValueType) (c : CheckerTypeAux) (n : Nat) :
    n < l.length → ∃ t, (toCtList l).getD n c = .some t := by
  intro h; exact ⟨l[n], by simp [toCtList, List.getD_eq_getElem?_getD, h]⟩

@[rocq_alias iriswasm.ct_compat_mutual]
theorem ct_compat_mutual (ts1 ts2 tsMutual : List CheckerTypeAux) (ts : List ValueType) :
    tsMutual = toCtList ts → ts1.length ≤ tsMutual.length → ts2.length ≤ tsMutual.length →
      ctListCompat (tsMutual.drop (tsMutual.length - ts1.length)) ts1 = true →
      ctListCompat (tsMutual.drop (tsMutual.length - ts2.length)) ts2 = true →
      ts1.length ≤ ts2.length → ctListCompat (ts2.drop (ts2.length - ts1.length)) ts1 = true := by
  rintro rfl hs1 hs2 h1 h2 hs
  simp only [ctListCompat_iff, List.length_drop, List.getElem_drop, toCtList_length,
    getElem_toCtList] at h1 h2 ⊢ hs1 hs2
  refine ⟨by omega, fun i hi hi' => ?_⟩
  have a1 := h1.2 i (by omega) hi'
  have a2 := h2.2 (ts2.length - ts1.length + i) (by omega) (by omega)
  have e : ts.length - ts2.length + (ts2.length - ts1.length + i) = ts.length - ts1.length + i := by
    omega
  simp only [e] at a2
  exact ctCompat_trans_some _ _ _ a2 a1

@[rocq_alias iriswasm.ct_suffix_mutual_compat]
theorem ct_suffix_mutual_compat (ts1 ts2 tsMutual : List CheckerTypeAux) (ts : List ValueType) :
    tsMutual = toCtList ts → ctSuffix ts1 tsMutual = true → ctSuffix ts2 tsMutual = true →
      ts1.length ≤ ts2.length → ctListCompat (ts2.drop (ts2.length - ts1.length)) ts1 = true := by
  intro hm h1 h2 hs
  simp only [ctSuffix, Bool.and_eq_true, decide_eq_true_eq] at h1 h2
  exact ct_compat_mutual ts1 ts2 tsMutual ts hm h1.1 h2.1 h1.2 h2.2 hs

@[rocq_alias iriswasm.ct_suffix_mutual_suffix]
theorem ct_suffix_mutual_suffix (ts1 ts2 tsMutual : List CheckerTypeAux) (ts : List ValueType) :
    tsMutual = toCtList ts → ctSuffix ts1 tsMutual = true → ctSuffix ts2 tsMutual = true →
      ts1.length ≤ ts2.length → ctSuffix ts1 ts2 = true := by
  intro hm h1 h2 hs
  simp only [ctSuffix, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hs, ct_suffix_mutual_compat ts1 ts2 tsMutual ts hm h1 h2 hs⟩

@[rocq_alias iriswasm.le_neq_lt]
theorem le_neq_lt (a b : Nat) : a ≤ b → a ≠ b → a < b := by
  omega

@[rocq_alias iriswasm.sub_if]
theorem sub_if (a b : Nat) : (if a - b < a then a - b else a) = a - b := by
  split <;> omega

@[simp] theorem cTypesAgree_type (a b : List ValueType) :
    cTypesAgree (.type a) b = true ↔ a = b := by simp [cTypesAgree]
@[simp] theorem cTypesAgree_top (l : List CheckerTypeAux) (b : List ValueType) :
    cTypesAgree (.topType l) b = ctSuffix l (toCtList b) := rfl
@[simp] theorem cTypesAgree_bot (b : List ValueType) : cTypesAgree .bot b = false := rfl
theorem toCtList_take (n : Nat) (l : List ValueType) :
    toCtList (l.take n) = (toCtList l).take n := by simp [toCtList, List.map_take]
theorem toCtList_drop (n : Nat) (l : List ValueType) :
    toCtList (l.drop n) = (toCtList l).drop n := by simp [toCtList, List.map_drop]

theorem ctSuffix_app_toCt (X : List CheckerTypeAux) (a b : List ValueType) :
    ctSuffix (X ++ toCtList a) (toCtList b) = true →
      ∃ lp, b = lp ++ a ∧ ctSuffix X (toCtList lp) = true := by
  rw [ctSuffix_iff]
  simp only [List.length_append, toCtList_length]
  rintro ⟨hl, h⟩
  refine ⟨b.take (b.length - a.length), ?_, ?_⟩
  · have hd : b.drop (b.length - a.length) = a := by
      apply List.ext_getElem (by simp; omega)
      intro i h1 h2
      have := h (X.length + i) (by omega) (by omega)
      simp only [getElem_toCtList, List.getElem_append_right (by omega : X.length ≤ X.length + i),
        toCtList_length] at this
      simp only [Nat.add_sub_cancel_left, getElem_toCtList, ctCompat_some_some,
        decide_eq_true_eq] at this
      simp only [List.getElem_drop]
      rw [← this]; congr 1; omega
    conv => lhs; rw [← List.take_append_drop (b.length - a.length) b]
    rw [hd]
  · rw [ctSuffix_iff]
    simp only [toCtList_length, List.length_take]
    refine ⟨by omega, fun i hi hi' => ?_⟩
    have := h i (by omega) (by omega)
    rw [List.getElem_append_left hi] at this
    simp only [getElem_toCtList, List.getElem_take] at this ⊢
    have e : min (b.length - a.length) b.length - X.length + i =
        b.length - (X.length + a.length) + i := by omega
    simp only [e]; exact this

@[rocq_alias iriswasm.ct_suffix_any_take_2]
theorem ct_suffix_any_take_2 (ts : List ValueType) :
    2 < ts.length → ctSuffix [.any] (toCtList (ts.take (ts.length - 2))) = true := by
  intro h; apply ct_suffix_any_1; simp; omega

@[rocq_alias iriswasm.ct_suffix_compat_index]
theorem ct_suffix_compat_index (l1 l2 : List CheckerTypeAux) (n : Nat) (t1 t2 : CheckerTypeAux) :
    ctSuffix l1 l2 = true → 1 ≤ n → n ≤ l1.length → l1[l1.length - n]? = some t1 →
      l2[l2.length - n]? = some t2 → ctCompat t1 t2 = true := by
  rw [ctSuffix_iff]
  rintro ⟨hl, h⟩ hn1 hn2 h1 h2
  rw [List.getElem?_eq_some_iff] at h1 h2
  obtain ⟨_, rfl⟩ := h1
  obtain ⟨_, rfl⟩ := h2
  have := h (l1.length - n) (by omega) (by omega)
  have e : l2.length - l1.length + (l1.length - n) = l2.length - n := by omega
  simp only [e] at this
  rw [ctCompat_comm]; exact this

@[rocq_alias iriswasm.ct_suffix_append_compat]
theorem ct_suffix_append_compat (l1 l2 l3 l4 : List CheckerTypeAux) :
    ctSuffix l1 l2 = true → ctListCompat l3 l4 = true → ctSuffix (l1 ++ l3) (l2 ++ l4) = true := by
  rw [ctSuffix_iff, ctSuffix_iff, ctListCompat_iff]
  rintro ⟨hl, h⟩ ⟨hl', h'⟩
  simp only [List.length_append]
  refine ⟨by omega, fun i hi hi' => ?_⟩
  by_cases hi1 : i < l1.length
  · rw [List.getElem_append_left hi1, List.getElem_append_left (by omega)]
    have := h i hi1 (by omega)
    have e : l2.length + l4.length - (l1.length + l3.length) + i = l2.length - l1.length + i := by
      omega
    simp only [e]; exact this
  · rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
    have := h' (i - l1.length) (by omega) (by omega)
    rw [ctCompat_comm]
    have e : l2.length + l4.length - (l1.length + l3.length) + i - l2.length = i - l1.length := by
      omega
    simp only [e]; exact this

@[rocq_alias iriswasm.nth_to_ct_list]
theorem nth_to_ct_list (ts : List ValueType) (n : Nat) (x : ValueType) :
    ts[n]? = some x → (toCtList ts)[n]? = some (.some x) := by
  intro h; simp [toCtList, h]

@[rocq_alias iriswasm.ct_list_compat_to_ct]
theorem ct_list_compat_to_ct (tn tm : List ValueType) :
    ctListCompat (toCtList tn) (toCtList tm) = true → tn = tm := by
  unfold ctListCompat toCtList
  induction tn generalizing tm with
  | nil => cases tm <;> simp
  | cons a tn ih =>
    cases tm with
    | nil => simp
    | cons b tm => simp only [List.map_cons, List.all2_cons, ctCompat_some_some, Bool.and_eq_true,
        decide_eq_true_eq]; rintro ⟨rfl, h⟩; rw [ih _ h]

@[rocq_alias iriswasm.ct_list_compat_symmetry]
theorem ct_list_compat_symmetry (l1 l2 : List CheckerTypeAux) :
    ctListCompat l1 l2 = true → ctListCompat l2 l1 = true := by
  simp only [ctListCompat_iff]
  rintro ⟨h1, h2⟩
  exact ⟨h1.symm, fun i a b => by rw [ctCompat_comm]; exact h2 i b a⟩

@[rocq_alias iriswasm.ct_list_compat_cat1]
theorem ct_list_compat_cat1 (l1 l2 l3 : List CheckerTypeAux) :
    ctListCompat (l2 ++ l3) l1 = true ↔
      ctListCompat l2 (l1.take l2.length) = true ∧ ctListCompat l3 (l1.drop l2.length) = true := by
  unfold ctListCompat
  induction l2 generalizing l1 with
  | nil => simp
  | cons a l2 ih => cases l1 <;> simp_all [and_assoc]

@[rocq_alias iriswasm.ct_list_compat_cat2]
theorem ct_list_compat_cat2 (l1 l2 l3 : List CheckerTypeAux) :
    ctListCompat l1 (l2 ++ l3) = true ↔
      ctListCompat (l1.take l2.length) l2 = true ∧ ctListCompat (l1.drop l2.length) l3 = true := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := (ct_list_compat_cat1 _ _ _).1 (ct_list_compat_symmetry _ _ h)
    exact ⟨ct_list_compat_symmetry _ _ h1, ct_list_compat_symmetry _ _ h2⟩
  · rintro ⟨h1, h2⟩
    exact ct_list_compat_symmetry _ _ ((ct_list_compat_cat1 _ _ _).2
      ⟨ct_list_compat_symmetry _ _ h1, ct_list_compat_symmetry _ _ h2⟩)

@[rocq_alias iriswasm.consume_top_not_bot]
theorem consume_top_not_bot (cts tn : List CheckerTypeAux) :
    tn.length ≤ cts.length → consume (.topType cts) tn ≠ .bot →
      ctListCompat (cts.drop (cts.length - tn.length)) tn = true := by
  intro hl h
  simp only [consume] at h
  split at h
  next hs => simp only [ctSuffix, Bool.and_eq_true] at hs; exact hs.2
  next =>
    split at h
    next hs =>
      simp only [ctSuffix, Bool.and_eq_true, decide_eq_true_eq] at hs
      have e : tn.length - cts.length = 0 := by omega
      have e' : cts.length - tn.length = 0 := by omega
      rw [e] at hs; rw [e']
      exact ct_list_compat_symmetry _ _ (by simpa using hs.2)
    next => exact absurd rfl h

@[rocq_alias iriswasm.consume_top_not_bot_short]
theorem consume_top_not_bot_short (cts tn : List CheckerTypeAux) :
    cts.length ≤ tn.length → consume (.topType cts) tn ≠ .bot →
      ctListCompat cts (tn.drop (tn.length - cts.length)) = true := by
  intro hl h
  simp only [consume] at h
  split at h
  next hs =>
    simp only [ctSuffix, Bool.and_eq_true, decide_eq_true_eq] at hs
    have e : tn.length - cts.length = 0 := by omega
    have e' : cts.length - tn.length = 0 := by omega
    rw [e]; rw [e'] at hs
    simpa using hs.2
  next =>
    split at h
    next hs =>
      simp only [ctSuffix, Bool.and_eq_true] at hs
      exact ct_list_compat_symmetry _ _ hs.2
    next => exact absurd rfl h

@[rocq_alias iriswasm.consume_type_not_bot]
theorem consume_type_not_bot (cts : List ValueType) (tn : List CheckerTypeAux) :
    consume (.type cts) tn ≠ .bot →
      ctListCompat ((toCtList cts).drop (cts.length - tn.length)) tn = true := by
  intro h
  simp only [consume] at h
  split at h
  next hs => simp only [ctSuffix, Bool.and_eq_true, toCtList_length] at hs; exact hs.2
  next => exact absurd rfl h

@[rocq_alias iriswasm.type_update_type_agree]
theorem type_update_type_agree (tm tn' tm' : List ValueType) (cts : CheckerType) :
    cTypesAgree (typeUpdate cts (toCtList tn') (.type tm')) tm = true →
      ∃ lp, cTypesAgree cts (lp ++ tn') = true ∧ tm = lp ++ tm' := by
  intro h
  cases cts with
  | type c =>
    simp only [typeUpdate, consume] at h
    split at h
    next hs =>
      simp only [produce, cTypesAgree_type] at h
      obtain ⟨lp, hc, -⟩ := ctSuffix_app_toCt [] tn' c (by simpa using hs)
      subst hc; subst h
      refine ⟨lp, by simp, ?_⟩
      simp
    next => simp [produce] at h
  | topType c =>
    simp only [typeUpdate, consume] at h
    split at h
    next hs =>
      simp only [produce, cTypesAgree_top] at h
      obtain ⟨lp, rfl, hlp⟩ := ctSuffix_app_toCt _ tm' tm h
      refine ⟨lp, ?_, rfl⟩
      simp only [cTypesAgree_top, toCtList_append]
      simp only [ctSuffix, Bool.and_eq_true] at hs
      have key := ct_suffix_append_compat _ _ _ _ hlp hs.2
      rwa [List.take_append_drop] at key
    next =>
      split at h
      next hs =>
        simp only [produce, cTypesAgree_top] at h
        obtain ⟨lp, rfl, -⟩ := ctSuffix_app_toCt [] tm' tm (by simpa using h)
        exact ⟨lp, by simpa using ct_suffix_extend _ _ (toCtList lp) hs, rfl⟩
      next => simp [produce] at h
  | bot => simp [typeUpdate, consume, produce] at h

@[rocq_alias iriswasm.consume_type_agree]
theorem consume_type_agree (tm tn' : List ValueType) (cts : CheckerType) :
    cTypesAgree (consume cts (toCtList tn')) tm = true → cTypesAgree cts (tm ++ tn') = true := by
  intro h
  rw [← type_update_empty_prod] at h
  obtain ⟨lp, h1, h2⟩ := type_update_type_agree tm tn' [] cts h
  simp at h2; subst h2; exact h1

@[rocq_alias iriswasm.check_single_top_top]
theorem check_single_top_top (C : TContext) (cts : List CheckerTypeAux) (e : BasicInstruction) :
    checkSingle C (.topType cts) e ≠ .bot →
      ∃ cts', checkSingle C (.topType cts) e = .topType cts' := by
  intro h
  rcases checkSingle_top C cts e with h' | h'
  · exact absurd h' h
  · exact h'

@[rocq_alias iriswasm.ct_suffix_1_impl]
theorem ct_suffix_1_impl (tm : List ValueType) :
    ctSuffix [.any] (toCtList tm) = true → ∃ v tm', tm = tm' ++ [v] := by
  intro h
  have := ct_suffix_size _ _ h
  simp at this
  exact ⟨tm.getLast (by intro h; simp [h] at this), tm.dropLast,
    (List.dropLast_concat_getLast _).symm⟩

@[rocq_alias iriswasm.tc_to_bet_br]
theorem tc_to_bet_br (cts : CheckerType) (l : List ValueType) :
    consume cts (toCtList l) ≠ .bot → ∃ tn, cTypesAgree cts (tn ++ l) = true := by
  intro h
  cases cts with
  | type c =>
    simp only [consume] at h
    split at h
    next hs =>
      obtain ⟨lp, rfl, -⟩ := ctSuffix_app_toCt [] l c (by simpa using hs)
      exact ⟨lp, by simp⟩
    next => exact absurd rfl h
  | topType c =>
    simp only [consume] at h
    split at h
    next hs =>
      refine ⟨populateCtAux (c.take (c.length - (toCtList l).length)), ?_⟩
      simp only [cTypesAgree_top, toCtList_append]
      simp only [ctSuffix, Bool.and_eq_true] at hs
      have key := ct_suffix_append_compat _ _ _ _
        (populate_ct_aux_suffix (c.take (c.length - (toCtList l).length))) hs.2
      rwa [List.take_append_drop] at key
    next =>
      split at h
      next hs => exact ⟨[], by simpa using hs⟩
      next => exact absurd rfl h
  | bot => exact absurd rfl h

@[rocq_alias iriswasm.type_update_agree_suffix]
theorem type_update_agree_suffix (ts : List ValueType) (cons : List CheckerTypeAux)
    (prod : CheckerType) (ts2 : List ValueType) (topt : List CheckerTypeAux) :
    cTypesAgree (typeUpdate (.type ts) cons prod) ts2 = true → ctSuffix topt (toCtList ts) = true →
      cTypesAgree (typeUpdate (.topType topt) cons prod) ts2 = true := by
  intro h hsuf
  simp only [typeUpdate, consume] at h ⊢
  split at h
  next hs =>
    have hl := ct_suffix_size _ _ hs
    simp only [toCtList_length] at hl
    by_cases hc : cons.length ≤ topt.length
    · have hs' : ctSuffix cons topt = true :=
        ct_suffix_mutual_suffix _ _ _ ts rfl hs hsuf hc
      simp only [hs', ↓reduceIte]
      cases prod with
      | type p =>
        simp only [produce, cTypesAgree_type, cTypesAgree_top] at h ⊢
        subst h
        rw [toCtList_append]
        apply ct_suffix_append_compat _ _ _ _ _ (ct_list_compat_self _)
        rw [toCtList_take]
        have := ct_suffix_take _ _ cons.length hsuf hc
        simpa [Nat.sub_sub, Nat.add_comm] using this
      | topType p => simpa [produce] using h
      | bot => simp [produce] at h
    · have hs' : ctSuffix topt cons = true :=
        ct_suffix_mutual_suffix _ _ _ ts rfl hsuf hs (by omega)
      have hn : ctSuffix cons topt = false := by
        cases h' : ctSuffix cons topt
        · rfl
        · have := ct_suffix_size _ _ h'; omega
      simp only [hn, hs', ↓reduceIte, Bool.false_eq_true]
      cases prod with
      | type p =>
        simp only [produce, cTypesAgree_type, cTypesAgree_top] at h ⊢
        subst h
        simpa using ct_suffix_suffix (ts.take (ts.length - cons.length)) p
      | topType p => simpa [produce] using h
      | bot => simp [produce] at h
  next => simp [produce] at h

@[rocq_alias iriswasm.c_types_agree_weakening]
theorem c_types_agree_weakening (C : TContext) (es : List BasicInstruction)
    (ts ts' ts2 : List ValueType) :
    cTypesAgree (check C es (.type ts)) ts2 = true →
      cTypesAgree (check C es (.type (ts' ++ ts))) (ts' ++ ts2) = true := by
  intro h
  cases hc : check C es (.type ts) with
  | type l =>
    rw [hc, cTypesAgree_type] at h; subst h
    rw [check_weaken C es ts ts' l hc]; simp
  | topType l =>
    rw [hc, cTypesAgree_top] at h
    rw [check_weaken_top C es ts ts' l hc, cTypesAgree_top, toCtList_append]
    exact ct_suffix_extend _ _ _ h
  | bot => rw [hc] at h; simp at h

theorem suf_idx {l : List CheckerTypeAux} {ts : List ValueType} (h : ctSuffix l (toCtList ts) = true)
    (k : Nat) (hk1 : 1 ≤ k) (hk : k ≤ l.length) (hts : k ≤ ts.length) :
    ctCompat l[l.length - k] (.some ts[ts.length - k]) = true :=
  ct_suffix_compat_index _ _ k _ _ h hk1 hk (by simp)
    (by simp [toCtList, List.getElem?_eq_getElem (show ts.length - k < ts.length by omega)])

theorem sel_c (l : List CheckerTypeAux) (c2 c3 : CheckerTypeAux) (v : ValueType)
    (r : List CheckerTypeAux) (h : selectReturnTop l c2 c3 = .topType r)
    (h2 : ctCompat c2 (.some v) = true) (h3 : ctCompat c3 (.some v) = true) :
    ∃ c, r = l.take (l.length - 3) ++ [c] ∧ ctCompat c (.some v) = true ∧
      (ctCompat c (.some v) = true → ctCompat c2 (.some v) = true ∧
        ctCompat c3 (.some v) = true) := by
  simp only [selectReturnTop] at h
  split at h
  · cases h; exact ⟨_, rfl, h2, fun _ => ⟨h2, h3⟩⟩
  · cases h; exact ⟨_, rfl, h3, fun _ => ⟨h2, h3⟩⟩
  · split at h
    · cases h; exact ⟨_, rfl, h2, fun _ => ⟨h2, h3⟩⟩
    · cases h

theorem consume_top_last (l c : List CheckerTypeAux) (x y : CheckerTypeAux) :
    consume (.topType (l ++ [x])) (c ++ [y]) ≠ .bot → ctCompat x y = true := by
  simp only [consume]
  split
  next hs => intro; rw [ctCompat_comm]; exact ((ct_suffix_rcons _ _ _ _).1 hs).1
  next =>
    split
    next hs => intro; exact ((ct_suffix_rcons _ _ _ _).1 hs).1
    next => intro h; exact absurd rfl h

theorem typeUpdate_top_top (l c p : List CheckerTypeAux) :
    typeUpdate (.topType l) c (.topType p) = .bot ∨
      typeUpdate (.topType l) c (.topType p) = .topType p := by
  simp only [typeUpdate, consume]
  split
  · simp [produce]
  · split <;> simp [produce]

@[rocq_alias iriswasm.select_return_top_suffix]
theorem select_return_top_suffix (c2 c3 : CheckerTypeAux) (ts : List ValueType)
    (topt topts : List CheckerTypeAux) :
    selectReturnTop topt c2 c3 = .topType topts → ctSuffix topt (toCtList ts) = true →
      topt[topt.length - 2]? = some c2 → topt[topt.length - 3]? = some c3 →
      ts[ts.length - 2]? = ts[ts.length - 3]? → 2 < topt.length → 2 < ts.length →
      ctSuffix topts (toCtList (ts.take (ts.length - 2))) = true := by
  intro hsel hs h2 h3 hts hm hn
  have hl := ct_suffix_size _ _ hs
  simp only [toCtList_length] at hl
  rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega),
    Option.some.injEq] at hts
  rw [List.getElem?_eq_getElem (by omega), Option.some.injEq] at h2 h3
  have hc2 := suf_idx hs 2 (by omega) (by omega) (by omega)
  have hc3 := suf_idx hs 3 (by omega) (by omega) (by omega)
  rw [h2, hts] at hc2
  rw [h3] at hc3
  obtain ⟨c, rfl, hc, -⟩ := sel_c _ _ _ _ _ hsel hc2 hc3
  have et : ts.take (ts.length - 2) = ts.take (ts.length - 3) ++ [ts[ts.length - 3]] := by
    rw [show ts.length - 2 = ts.length - 3 + 1 by omega, List.take_add_one,
      List.getElem?_eq_getElem (by omega)]; rfl
  rw [et, toCtList_append]
  refine (ct_suffix_rcons _ _ _ _).2 ⟨hc, ?_⟩
  have := ct_suffix_take _ _ 3 hs (by omega)
  simpa [toCtList_take] using this

@[rocq_alias iriswasm.type_update_select_agree]
theorem type_update_select_agree (topt : List CheckerTypeAux) (ts : List ValueType) :
    ctSuffix [.any, .some .i32] (toCtList ts) = true → ctSuffix topt (toCtList ts) = true →
      2 < ts.length → ts[ts.length - 2]? = ts[ts.length - 3]? →
      cTypesAgree (typeUpdateSelect (.topType topt)) (ts.take (ts.length - 2)) = true := by
  intro hs1 hs2 hn hts
  have hl := ct_suffix_size _ _ hs2
  simp only [toCtList_length] at hl
  have hlast := suf_idx hs1 1 (by omega) (by simp) (by omega)
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_one_sub_one,
    List.getElem_cons_succ, List.getElem_cons_zero, ctCompat_some_some,
    decide_eq_true_eq] at hlast
  have hts' := hts
  rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega),
    Option.some.injEq] at hts'
  simp only [typeUpdateSelect]
  split
  · simp only [cTypesAgree_top]; exact ct_suffix_any_take_2 ts hn
  · rename_i heq
    obtain ⟨x1, rfl⟩ : ∃ x1, topt = [x1] := by
      rcases topt with _ | ⟨x1, _ | _⟩ <;> simp at heq; exact ⟨x1, rfl⟩
    rcases typeUpdate_top_top [x1] [.some .i32] [.any] with h | h <;> rw [h]
    · simp only [cTypesAgree_bot]
      have := suf_idx hs2 1 (by simp) (by simp) (by omega)
      simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.sub_self,
        List.getElem_cons_zero, ← hlast] at this
      exfalso; revert h
      simp [typeUpdate, consume, produce, ctSuffix, ctListCompat, this, ctCompat_comm x1]
    · exact ct_suffix_any_take_2 ts hn
  · rename_i heq
    obtain ⟨x2, x1, rfl⟩ : ∃ x2 x1, topt = [x2, x1] := by
      rcases topt with _ | ⟨x2, _ | ⟨x1, _ | _⟩⟩ <;> simp at heq; exact ⟨x2, x1, rfl⟩
    have a1 := suf_idx hs2 1 (by simp) (by simp) (by omega)
    have a2 := suf_idx hs2 2 (by simp) (by simp) (by omega)
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_one_sub_one,
      Nat.sub_self, List.getElem_cons_succ, List.getElem_cons_zero, ← hlast] at a1 a2
    have hsx : ctSuffix [.some .i32] [x2, x1] = true := by
      rw [ctSuffix_iff]; simp [ctCompat_comm, a1]
    simp only [consume, hsx, ↓reduceIte, cTypesAgree_top]
    rw [ctSuffix_iff]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.sub_self, List.take_succ_cons,
      List.take_zero, toCtList_length, List.length_take]
    refine ⟨by omega, fun i hi _ => ?_⟩
    obtain rfl : i = 0 := by simp at hi; omega
    simp only [getElem_toCtList, List.getElem_take, List.getElem_cons_zero]
    have e : min (ts.length - 2) ts.length - 1 + 0 = ts.length - 3 := by omega
    simp only [e, ← hts']; rw [ctCompat_comm]; exact a2
  · have hm : 3 ≤ topt.length := by
      rcases Nat.lt_or_ge topt.length 3 with hc | hc
      · rcases (by omega : topt.length = 0 ∨ topt.length = 1 ∨ topt.length = 2) with h | h | h <;>
          simp_all
      · exact hc
    split
    next c2 c3 h2 h3 =>
      have a1 := suf_idx hs2 1 (by simp) (by omega) (by omega)
      have b2 := suf_idx hs2 2 (by simp) (by omega) (by omega)
      have b3 := suf_idx hs2 3 (by simp) (by omega) (by omega)
      rw [List.getElem?_eq_getElem (by omega), Option.some.injEq] at h2 h3
      rw [h2, hts'] at b2
      rw [h3] at b3
      rw [← hlast] at a1
      obtain ⟨c, hr, -⟩ : ∃ c, selectReturnTop topt c2 c3 =
          .topType (topt.take (topt.length - 3) ++ [c]) ∧ True := by
        simp only [selectReturnTop]
        split
        · exact ⟨_, rfl, trivial⟩
        · exact ⟨_, rfl, trivial⟩
        · rename_i t1 t2
          simp only [ctCompat_some_some, decide_eq_true_eq] at b2 b3
          subst b2; subst b3
          exact ⟨_, by simp only [beq_self_eq_true, ↓reduceIte]; rfl, trivial⟩
      have hsel := select_return_top_suffix c2 c3 ts topt _ hr hs2
        (by rw [List.getElem?_eq_getElem (by omega), h2])
        (by rw [List.getElem?_eq_getElem (by omega), h3]) hts (by omega) hn
      have hc3 : ctSuffix [.any, .any, .some .i32] topt = true := by
        rw [ctSuffix_iff]
        refine ⟨by simp; omega, fun i hi _ => ?_⟩
        simp at hi
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
        · simp
        · simp
        · have e : topt.length - 3 + 2 = topt.length - 1 := by omega
          simp only [List.length_cons, List.length_nil, Nat.reduceAdd, e, List.getElem_cons_succ,
            List.getElem_cons_zero]
          exact a1
      simp only [typeUpdate, consume, hc3, ↓reduceIte, hr, produce, cTypesAgree_top]
      exact hsel
    next h2 =>
      exfalso
      apply h2 (topt[topt.length - 2]'(by omega)) (topt[topt.length - 3]'(by omega)) <;>
        simp [List.getElem?_eq_getElem (show topt.length - 2 < topt.length by omega),
          List.getElem?_eq_getElem (show topt.length - 3 < topt.length by omega)]

theorem select_suffix_single (l : List CheckerTypeAux) (ts ts2 : List ValueType)
    (h : cTypesAgree (typeUpdateSelect (.type ts)) ts2 = true)
    (hs : ctSuffix l (toCtList ts) = true) :
    cTypesAgree (typeUpdateSelect (.topType l)) ts2 = true := by
  simp only [typeUpdateSelect.eq_1] at h
  split at h
  next hc =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
    simp only [consume] at h
    split at h
    next hsuf =>
      simp only [cTypesAgree_type, List.length_cons, List.length_nil] at h
      subst h
      exact type_update_select_agree l ts hsuf hs (by omega) hc.2
    next => simp at h
  next => simp at h

@[rocq_alias iriswasm.c_types_agree_suffix_single]
theorem c_types_agree_suffix_single (l : List CheckerTypeAux) (C : TContext)
    (ts ts2 : List ValueType) (e : BasicInstruction) :
    cTypesAgree (checkSingle C (.type ts) e) ts2 = true → ctSuffix l (toCtList ts) = true →
      cTypesAgree (checkSingle C (.topType l) e) ts2 = true := by
  intro h hs
  cases e <;> (try (rename_i c _ _; cases c)) <;>
    simp only [checkSingle.eq_def, beq_iff_eq, reduceCtorEq, ite_false] at h ⊢ <;>
    (repeat' split at h) <;>
    (try simp only [*, ↓reduceIte] at ⊢) <;>
    first
    | exact type_update_agree_suffix _ _ _ _ _ h hs
    | exact select_suffix_single _ _ _ h hs
    | (simp only [cTypesAgree_type] at h; subst h; exact hs)
    | simp at h

theorem exists_last3 {α : Type} (l : List α) (h : 3 ≤ l.length) :
    ∃ pre a b c, l = pre ++ [a, b, c] := by
  obtain ⟨c, b, a, rest, hr⟩ : ∃ c b a rest, l.reverse = c :: b :: a :: rest := by
    match hr : l.reverse with
    | c :: b :: a :: rest => exact ⟨c, b, a, rest, rfl⟩
    | [] | [_] | [_, _] =>
      have := congrArg List.length hr
      simp only [List.length_reverse, List.length_nil, List.length_cons] at this; omega
  exact ⟨rest.reverse, a, b, c, by rw [← List.reverse_reverse l, hr]; simp⟩

theorem select_bet (C : TContext) (pre : List ValueType) (v : ValueType) :
    BeTyping C [.select] (.tf (pre ++ [v, v, .i32]) (pre ++ [v])) := .weakening .select

theorem produce_bot (x : CheckerType) : produce x .bot = .bot := by cases x <;> rfl

theorem selectReturnTop_ne_type (l : List CheckerTypeAux) (c2 c3 : CheckerTypeAux)
    (r : List ValueType) : selectReturnTop l c2 c3 ≠ .type r := by
  simp only [selectReturnTop]; split
  · simp
  · simp
  · split <;> simp

theorem sel_shape (l : List CheckerTypeAux) (c2 c3 : CheckerTypeAux) (r : List CheckerTypeAux)
    (h : selectReturnTop l c2 c3 = .topType r) :
    ∃ c, r = l.take (l.length - 3) ++ [c] ∧ ∀ v, ctCompat c (.some v) = true →
      ctCompat c2 (.some v) = true ∧ ctCompat c3 (.some v) = true := by
  simp only [selectReturnTop] at h
  split at h
  · cases h; exact ⟨_, rfl, fun v hv => ⟨hv, by simp⟩⟩
  · cases h; exact ⟨_, rfl, fun v hv => ⟨by simp, hv⟩⟩
  · split at h
    · cases h; rename_i heq; simp only [beq_iff_eq] at heq; subst heq
      exact ⟨_, rfl, fun v hv => ⟨hv, hv⟩⟩
    · cases h

@[rocq_alias iriswasm.type_update_select_agree_bet]
theorem type_update_select_agree_bet (C : TContext) (cts : CheckerType) (tm : List ValueType) :
    cTypesAgree (typeUpdateSelect cts) tm = true →
      ∃ tn, cTypesAgree cts tn = true ∧ BeTyping C [.select] (.tf tn tm) := by
  intro h
  cases cts with
  | type ts =>
    simp only [typeUpdateSelect] at h
    split at h
    next hc =>
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
      simp only [consume] at h
      split at h
      next hsuf =>
        simp only [cTypesAgree_type] at h
        subst h
        obtain ⟨pre, a, b, c, rfl⟩ := exists_last3 ts hc.1
        have hb : b = a := by simpa using hc.2
        have hcc := suf_idx hsuf 1 (by simp) (by simp) (by simp)
        simp at hcc
        subst hb; subst hcc
        refine ⟨_, (cTypesAgree_type _ _).2 rfl, ?_⟩
        have e : ∀ k, k = pre.length + 1 → (pre ++ [b, b, .i32]).take k = pre ++ [b] := by
          rintro k rfl; rw [List.take_append, List.take_of_length_le (by omega)]; simp
        rw [e _ (by simp)]
        exact select_bet C pre b
      next => simp at h
    next => simp at h
  | topType l =>
    simp only [typeUpdateSelect] at h
    split at h
    · simp only [cTypesAgree_top] at h
      obtain ⟨v, tm', rfl⟩ := ct_suffix_1_impl tm h
      rename_i heq
      obtain rfl : l = [] := List.eq_nil_of_length_eq_zero heq
      exact ⟨tm' ++ [v, v, .i32], ct_suffix_empty _, select_bet C tm' v⟩
    · rename_i heq
      obtain ⟨x1, rfl⟩ : ∃ x1, l = [x1] := by
        rcases l with _ | ⟨x1, _ | _⟩ <;> simp at heq; exact ⟨x1, rfl⟩
      rcases typeUpdate_top_top [x1] [.some .i32] [.any] with h' | h' <;> rw [h'] at h
      · simp at h
      · have hx := consume_top_last [] [] x1 (.some .i32) (by
          intro hb; simp only [List.nil_append] at hb; simp [typeUpdate, hb, produce] at h')
        have hx' : ctCompat (.some .i32) x1 = true := by rw [ctCompat_comm]; exact hx
        simp only [cTypesAgree_top] at h
        obtain ⟨v, tm', rfl⟩ := ct_suffix_1_impl tm h
        refine ⟨tm' ++ [v, v, .i32], ?_, select_bet C tm' v⟩
        simp only [cTypesAgree_top, toCtList_append]
        rw [ctSuffix_iff]; simp [toCtList, hx']
    · rename_i heq
      obtain ⟨x2, x1, rfl⟩ : ∃ x2 x1, l = [x2, x1] := by
        rcases l with _ | ⟨x2, _ | ⟨x1, _ | _⟩⟩ <;> simp at heq; exact ⟨x2, x1, rfl⟩
      have hx : ctCompat x1 (.some .i32) = true := consume_top_last [x2] [] x1 (.some .i32) (by
        intro hb; simp only [List.cons_append, List.nil_append] at hb; simp [hb] at h)
      have hsx : ctSuffix [.some .i32] [x2, x1] = true := by
        rw [ctSuffix_iff]; simp [ctCompat_comm, hx]
      simp only [consume, hsx, ↓reduceIte, cTypesAgree_top] at h
      simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_one_sub_one,
        List.take_succ_cons, List.take_zero] at h
      obtain ⟨v, tm', rfl⟩ := ct_suffix_1_impl tm (by
        rw [ctSuffix_iff] at h ⊢; simp_all)
      have hv := ((ct_suffix_rcons [] (toCtList tm') x2 (.some v)).1 (by simpa [toCtList] using h)).1
      refine ⟨tm' ++ [v, v, .i32], ?_, select_bet C tm' v⟩
      simp only [cTypesAgree_top, toCtList_append]
      have := ct_suffix_append_compat [] (toCtList tm' ++ [.some v]) [x2, x1]
        [.some v, .some .i32] (ct_suffix_empty _) (by simp [ctListCompat, hv, hx])
      simpa [toCtList] using this
    · have hm : 3 ≤ l.length := by
        rcases Nat.lt_or_ge l.length 3 with hc | hc
        · rcases (by omega : l.length = 0 ∨ l.length = 1 ∨ l.length = 2) with h | h | h <;>
            simp_all
        · exact hc
      split at h
      next c2 c3 h2 h3 =>
        rw [List.getElem?_eq_getElem (by omega), Option.some.injEq] at h2 h3
        cases hsel : selectReturnTop l c2 c3 with
        | topType r =>
          rw [hsel] at h
          rcases typeUpdate_top_top l [.any, .any, .some .i32] r with h' | h' <;> rw [h'] at h
          · simp at h
          · obtain ⟨c, hr, hcv⟩ := sel_shape _ _ _ _ hsel
            obtain ⟨pre, x3, x2, x1, rfl⟩ := exists_last3 l hm
            have hx : ctCompat x1 (.some .i32) = true :=
              consume_top_last (pre ++ [x3, x2]) [.any, .any] x1 (.some .i32) (by
                intro hb; simp only [List.append_assoc, List.cons_append, List.nil_append] at hb
                simp [typeUpdate, hb, produce] at h')
            have e2 : x2 = c2 := by
              rw [← h2]; simp [List.getElem_append_right]
            have e3 : x3 = c3 := by
              rw [← h3]; simp [List.getElem_append_right]
            subst e2 e3
            simp at hr
            subst hr
            simp only [cTypesAgree_top] at h
            obtain ⟨v, tm', rfl⟩ := ct_suffix_1_impl tm (by
              have := ct_suffix_size _ _ h
              apply ct_suffix_any_1; simp only [List.length_append, List.length_cons,
                List.length_nil] at this; omega)
            obtain ⟨hcv', hpre⟩ := (ct_suffix_rcons pre (toCtList tm') c (.some v)).1
              (by simpa [toCtList] using h)
            obtain ⟨h2v, h3v⟩ := hcv v hcv'
            refine ⟨tm' ++ [v, v, .i32], ?_, select_bet C tm' v⟩
            simp only [cTypesAgree_top, toCtList_append]
            have := ct_suffix_append_compat pre (toCtList tm') [x3, x2, x1]
              [.some v, .some v, .some .i32] hpre (by simp [ctListCompat, h2v, h3v, hx])
            simpa [toCtList] using this
        | type r => exact absurd hsel (selectReturnTop_ne_type _ _ _ _)
        | bot => rw [hsel] at h; simp [typeUpdate, produce_bot] at h
      next => simp at h
  | bot => simp [typeUpdateSelect] at h

@[rocq_alias iriswasm.be_size_single]
def beSizeSingle (be : BasicInstruction) : Nat :=
  match be with
  | .block _ l => 1 + (l.map beSizeSingle).foldl (· + ·) 1 + l.length
  | .loop _ l => 1 + (l.map beSizeSingle).foldl (· + ·) 1 + l.length
  | .if_ _ l1 l2 =>
    1 + ((l1.map beSizeSingle).foldl (· + ·) 1 + l1.length) +
      ((l2.map beSizeSingle).foldl (· + ·) 1 + l2.length)
  | _ => 1

@[rocq_alias iriswasm.be_size_list]
def beSizeList (bes : List BasicInstruction) : Nat :=
  (bes.map beSizeSingle).foldl (· + ·) 1 + bes.length

@[rocq_alias iriswasm.fold_left_rcons]
theorem fold_left_rcons {A B : Type} (f : A → B → A) (l : List B) (x : B) (acc : A) :
    (l ++ [x]).foldl f acc = f (l.foldl f acc) x := by
  simp

@[rocq_alias iriswasm.be_size_list_rcons]
theorem be_size_list_rcons (bes : List BasicInstruction) (e : BasicInstruction) :
    beSizeList (bes ++ [e]) = beSizeSingle e + beSizeList bes + 1 := by
  simp only [beSizeList, List.map_append, List.map_cons, List.map_nil, fold_left_rcons,
    List.length_append, List.length_singleton]
  omega

theorem foldl_add_ge (l : List Nat) (a : Nat) : a ≤ l.foldl (· + ·) a := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => simp only [List.foldl_cons]; exact Nat.le_trans (Nat.le_add_right _ _) (ih _)

theorem beSizeList_pos (bes : List BasicInstruction) : 1 ≤ beSizeList bes := by
  unfold beSizeList; have := foldl_add_ge (bes.map beSizeSingle) 1; omega

theorem beSizeSingle_pos (e : BasicInstruction) : 1 ≤ beSizeSingle e := by
  cases e <;> simp [beSizeSingle] <;> omega

theorem beSizeSingle_block (tf : FunctionType) (l : List BasicInstruction) :
    beSizeSingle (.block tf l) = 1 + beSizeList l := by
  simp [beSizeSingle, beSizeList]; omega

theorem beSizeSingle_loop (tf : FunctionType) (l : List BasicInstruction) :
    beSizeSingle (.loop tf l) = 1 + beSizeList l := by
  simp [beSizeSingle, beSizeList]; omega

theorem beSizeSingle_if (tf : FunctionType) (l1 l2 : List BasicInstruction) :
    beSizeSingle (.if_ tf l1 l2) = 1 + beSizeList l1 + beSizeList l2 := by
  simp [beSizeSingle, beSizeList]

theorem tu_bet {C : TContext} {cts : CheckerType} {tm : List ValueType} {e : BasicInstruction}
    (tn0 tm0 : List ValueType) (hb : BeTyping C [e] (.tf tn0 tm0))
    (h : cTypesAgree (typeUpdate cts (toCtList tn0) (.type tm0)) tm = true) :
    ∃ tn, cTypesAgree cts tn = true ∧ BeTyping C [e] (.tf tn tm) := by
  obtain ⟨lp, h1, rfl⟩ := type_update_type_agree _ _ _ _ h
  exact ⟨_, h1, .weakening hb⟩

theorem tu_bet_top {C : TContext} {cts : CheckerType} {tm : List ValueType}
    {e : BasicInstruction} (tn0 : List ValueType)
    (hb : ∀ t1s, BeTyping C [e] (.tf (t1s ++ tn0) tm))
    (h : cTypesAgree (typeUpdate cts (toCtList tn0) (.topType [])) tm = true) :
    ∃ tn, cTypesAgree cts tn = true ∧ BeTyping C [e] (.tf tn tm) := by
  have hc : consume cts (toCtList tn0) ≠ .bot := by
    intro hb'; simp [typeUpdate, hb', produce] at h
  obtain ⟨tn, htn⟩ := tc_to_bet_br cts tn0 hc
  exact ⟨_, htn, hb tn⟩

theorem tu_any (cts : CheckerType) (tm : List ValueType)
    (h : cTypesAgree (typeUpdate cts [.any] (.type [])) tm = true) :
    ∃ x, cTypesAgree cts (tm ++ [x]) = true := by
  rw [type_update_empty_prod] at h
  cases cts with
  | type ts =>
    simp only [consume] at h
    split at h
    next hs =>
      obtain ⟨v, ts', rfl⟩ := ct_suffix_1_impl ts hs
      simp at h; subst h
      exact ⟨v, by simp⟩
    next => simp at h
  | topType l =>
    simp only [consume] at h
    split at h
    next hs =>
      have hl := ct_suffix_size _ _ hs
      obtain ⟨l', y, rfl⟩ : ∃ l' y, l = l' ++ [y] := by
        simp at hl
        exact ⟨l.dropLast, l.getLast (by intro h; simp [h] at hl),
          (List.dropLast_concat_getLast _).symm⟩
      simp only [cTypesAgree_top, List.length_append, List.length_singleton,
        Nat.add_sub_cancel, List.take_left'] at h
      refine ⟨populateCtAuxSingle y, ?_⟩
      simp only [cTypesAgree_top, toCtList_append]
      refine (ct_suffix_rcons _ _ _ _).2 ⟨?_, h⟩
      cases y <;> simp [populateCtAuxSingle]
    next =>
      split at h
      next hs =>
        have hl := ct_suffix_size _ _ hs
        obtain rfl : l = [] := by
          cases l with
          | nil => rfl
          | cons y l' =>
            simp at hl; subst hl; rename_i hn; exfalso; apply hn
            rw [ctSuffix_iff]; simp
        exact ⟨.i32, ct_suffix_empty _⟩
      next => simp at h
  | bot => simp [consume] at h


theorem tc_to_bet_single (d : Nat)
    (ihL : ∀ C cts bes tm cts', beSizeList bes ≤ d → check C bes cts = cts' →
      cTypesAgree cts' tm = true →
      ∃ tn, cTypesAgree cts tn = true ∧ BeTyping C bes (.tf tn tm))
    (C : TContext) (cts : CheckerType) (tm : List ValueType) (e : BasicInstruction)
    (hs : beSizeSingle e ≤ d + 1) (h : cTypesAgree (checkSingle C cts e) tm = true) :
    ∃ tn, cTypesAgree cts tn = true ∧ BeTyping C [e] (.tf tn tm) := by
  by_cases hb : cts = .bot
  · subst hb; rw [check_single_bot] at h; simp at h
  have hnb : (cts == .bot) = false := by simpa using hb
  cases e
  all_goals (rw [checkSingle.eq_def] at h; simp only [hnb, Bool.false_eq_true, ↓reduceIte] at h)
  case const v => exact tu_bet [] [typeof v] .const h
  case unop t op =>
    cases op <;> simp only at h <;> split at h <;> (try simp at h) <;> rename_i hc <;>
      exact tu_bet [t] [t] (.unop (by cases t <;> simp [isInt, isFloat] at hc <;> constructor)) h
  case binop t op =>
    cases op <;> simp only at h <;> split at h <;> (try simp at h) <;> rename_i hc <;>
      exact tu_bet [t, t] [t] (.binop (by cases t <;> simp [isInt, isFloat] at hc <;> constructor)) h
  case testop t op =>
    split at h
    · rename_i hc; exact tu_bet [t] [.i32] (.testop hc) h
    · simp at h
  case relop t op =>
    cases op <;> simp only at h <;> split at h <;> (try simp at h) <;> rename_i hc <;>
      exact tu_bet [t, t] [.i32] (.relop (by cases t <;> simp [isInt, isFloat] at hc <;> constructor)) h
  case cvtop t1 c t2 sx =>
    cases c <;> simp only at h <;> split at h <;> (try simp at h) <;> rename_i hc
    · simp only [convertCond, Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
      exact tu_bet [t2] [t1] (.convert hc.1 hc.2) h
    · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hc
      obtain ⟨⟨h1, h2⟩, rfl⟩ := hc
      exact tu_bet [t2] [t1] (.reinterpret h1 (by simp [h2])) h
  case unreachable =>
    exact ⟨populateCt cts, populate_ct_agree cts hb, .unreachable⟩
  case nop =>
    exact ⟨tm, h, bet_weakening_empty_both tm .nop⟩
  case drop =>
    obtain ⟨x, hx⟩ := tu_any cts tm h
    exact ⟨tm ++ [x], hx, bet_weakening_empty_2 tm .drop⟩
  case select => exact type_update_select_agree_bet C cts tm h
  case block tf es =>
    obtain ⟨tn, tm0⟩ := tf
    simp only at h
    split at h
    next hc =>
      have hd : beSizeList es ≤ d := by rw [beSizeSingle_block] at hs; omega
      obtain ⟨tn', h1, h2⟩ := ihL _ _ es tm0 _ hd rfl hc
      simp only [cTypesAgree_type] at h1; rw [← h1] at h2
      exact tu_bet tn tm0 (.block h2) h
    next => simp at h
  case loop tf es =>
    obtain ⟨tn, tm0⟩ := tf
    simp only at h
    split at h
    next hc =>
      have hd : beSizeList es ≤ d := by rw [beSizeSingle_loop] at hs; omega
      obtain ⟨tn', h1, h2⟩ := ihL _ _ es tm0 _ hd rfl hc
      simp only [cTypesAgree_type] at h1; rw [← h1] at h2
      exact tu_bet tn tm0 (.loop h2) h
    next => simp at h
  case if_ tf es1 es2 =>
    obtain ⟨tn, tm0⟩ := tf
    simp only at h
    split at h
    next hc =>
      simp only [Bool.and_eq_true] at hc
      rw [beSizeSingle_if] at hs
      obtain ⟨tn1, h11, h12⟩ := ihL _ _ es1 tm0 _ (by omega) rfl hc.1
      obtain ⟨tn2, h21, h22⟩ := ihL _ _ es2 tm0 _ (by omega) rfl hc.2
      simp only [cTypesAgree_type] at h11 h21; rw [← h11] at h12; rw [← h21] at h22
      have hb' : BeTyping C [.if_ (.tf tn tm0) es1 es2] (.tf (tn ++ [ValueType.i32]) tm0) := by
        apply BeTyping.ifWasm
        · exact h12
        · exact h22
      exact tu_bet (tn ++ [ValueType.i32]) tm0 hb' h
    next => simp at h
  case br i =>
    split at h
    next hi =>
      split at h
      next xx hxx =>
        exact tu_bet_top xx (fun t1s => .br hi (by simp [plop2, hxx])) h
      next => simp at h
    next => simp at h
  case brIf i =>
    split at h
    next hi =>
      split at h
      next xx hxx => exact tu_bet (xx ++ [ValueType.i32]) xx (.brIf hi (by simp [plop2, hxx])) h
      next => simp at h
    next => simp at h
  case brTable iss i =>
    split at h
    next => simp at h
    next tls htls =>
      exact tu_bet_top (tls ++ [ValueType.i32])
        (fun t1s => .brTable (same_lab_h_all C tls _ (same_lab_same_lab_h _ _ _ htls))) h
  case return_ =>
    split at h
    next => simp at h
    next tls htls => exact tu_bet_top tls (fun t1s => .return_ htls) h
  case call i =>
    split at h
    next hi =>
      split at h
      next => simp at h
      next tn0 tm0 htf => exact tu_bet tn0 tm0 (.call hi htf) h
    next => simp at h
  case callIndirect i =>
    split at h
    next hi =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hi
      split at h
      next => simp at h
      next tn0 tm0 htf =>
        exact tu_bet (tn0 ++ [ValueType.i32]) tm0
          (.callIndirect hi.2 htf (by intro h'; simp [h'] at hi)) h
    next => simp at h
  case getLocal i =>
    split at h
    next hi =>
      split at h
      next => simp at h
      next xx hxx => exact tu_bet [] [xx] (.getLocal hi hxx) h
    next => simp at h
  case setLocal i =>
    split at h
    next hi =>
      split at h
      next => simp at h
      next xx hxx => exact tu_bet [xx] [] (.setLocal hi hxx) h
    next => simp at h
  case teeLocal i =>
    split at h
    next hi =>
      split at h
      next => simp at h
      next xx hxx => exact tu_bet [xx] [xx] (.teeLocal hi hxx) h
    next => simp at h
  case getGlobal i =>
    split at h
    next hi =>
      split at h
      next => simp at h
      next xx hxx => exact tu_bet [] [xx.t] (.getGlobal hi (by simp [hxx])) h
    next => simp at h
  case setGlobal i =>
    split at h
    next hi =>
      split at h
      next => simp at h
      next xx hxx =>
        split at h
        next hm => exact tu_bet [xx.t] [] (.setGlobal hi hxx rfl hm) h
        next => simp at h
    next => simp at h
  case load t tp a off =>
    split at h
    next hc =>
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
      exact tu_bet [.i32] [t] (.load hc.1 hc.2) h
    next => simp at h
  case store t tp a off =>
    split at h
    next hc =>
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
      exact tu_bet [.i32, t] [] (.store hc.1 hc.2) h
    next => simp at h
  case currentMemory =>
    split at h
    next hc =>
      simp only [bne_iff_ne, ne_eq] at hc
      exact tu_bet [] [.i32] (.currentMemory hc) h
    next => simp at h
  case growMemory =>
    split at h
    next hc =>
      simp only [bne_iff_ne, ne_eq] at hc
      exact tu_bet [.i32] [.i32] (.growMemory hc) h
    next => simp at h

@[rocq_alias iriswasm.tc_to_bet_conj]
theorem tc_to_bet_conj (d : Nat) :
    (∀ C cts bes tm cts', beSizeList bes ≤ d → check C bes cts = cts' →
      cTypesAgree cts' tm = true →
      ∃ tn, cTypesAgree cts tn = true ∧ BeTyping C bes (.tf tn tm)) ∧
    (∀ C cts tm e cts', beSizeSingle e ≤ d → checkSingle C cts e = cts' →
      cTypesAgree cts' tm = true →
      ∃ tn, cTypesAgree cts tn = true ∧ BeTyping C [e] (.tf tn tm)) := by
  induction d with
  | zero =>
    exact ⟨fun _ _ bes _ _ hs => absurd hs (by have := beSizeList_pos bes; omega),
      fun _ _ _ e _ hs => absurd hs (by have := beSizeSingle_pos e; omega)⟩
  | succ d ih =>
    obtain ⟨ihL, -⟩ := ih
    refine ⟨?_, fun C cts tm e cts' hs hc ha => ?_⟩
    · intro C cts bes
      obtain ⟨l, rfl⟩ : ∃ l, bes = l.reverse := ⟨bes.reverse, by simp⟩
      induction l with
      | nil =>
        intro tm cts' _ hc ha; subst hc
        exact ⟨tm, ha, bet_weakening_empty_both tm .empty⟩
      | cons e l ihb =>
        intro tm cts' hs hc ha; subst hc
        rw [List.reverse_cons] at hs ha ⊢
        generalize l.reverse = bes at hs ha ihb ⊢
        rw [be_size_list_rcons] at hs
        rw [check_rcons] at ha
        have := beSizeList_pos bes
        obtain ⟨tn', h1, h2⟩ := tc_to_bet_single d ihL C _ tm e (by omega) ha
        obtain ⟨tn, h3, h4⟩ := ihb tn' _ (by omega) rfl h1
        exact ⟨tn, h3, .composition h4 h2⟩
    · subst hc; exact tc_to_bet_single d ihL C cts tm e hs ha

@[rocq_alias iriswasm.tc_to_bet_list]
theorem tc_to_bet_list (C : TContext) (cts : CheckerType) (bes : List BasicInstruction)
    (tm : List ValueType) (cts' : CheckerType) :
    check C bes cts = cts' → cTypesAgree cts' tm = true →
      ∃ tn, cTypesAgree cts tn = true ∧ BeTyping C bes (.tf tn tm) :=
  (tc_to_bet_conj (beSizeList bes)).1 C cts bes tm cts' (Nat.le_refl _)

theorem consume_app (a b : List ValueType) : consume (.type (a ++ b)) (toCtList b) = .type a := by
  simp only [consume, ct_suffix_suffix, ↓reduceIte, List.length_append, Nat.add_sub_cancel,
    List.take_left', toCtList_length]

theorem tu_app_type (a b c : List ValueType) :
    typeUpdate (.type (a ++ b)) (toCtList b) (.type c) = .type (a ++ c) := by
  simp [typeUpdate, consume_app, produce]

theorem tu_self_type (b c : List ValueType) :
    typeUpdate (.type b) (toCtList b) (.type c) = .type c := by
  simpa using tu_app_type [] b c

theorem tu_app_top (a b : List ValueType) (c : List CheckerTypeAux) :
    typeUpdate (.type (a ++ b)) (toCtList b) (.topType c) = .topType c := by
  simp [typeUpdate, consume_app, produce]

theorem consume_self (b : List ValueType) : consume (.type b) (toCtList b) = .type [] := by
  simpa using consume_app [] b

theorem sameLab_of_all (C : TContext) (ts : List ValueType) (l : List Nat) (hne : l ≠ [])
    (h : l.all (fun i => decide (i < C.label.length) && plop2 C i ts) = true) :
    sameLab l C.label = some ts := by
  cases l with
  | nil => contradiction
  | cons n l =>
    have h2 := same_lab_h_condition C ts _ h
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq, plop2, beq_iff_eq] at h
    simp only [sameLab, show ¬ C.label.length ≤ n by omega, ↓reduceIte, h.1.2]
    exact same_lab_h_rec n l C ts h2

@[rocq_alias iriswasm.b_e_type_checker_reflects_typing]
theorem b_e_type_checker_reflects_typing (C : TContext) (bes : List BasicInstruction)
    (tf : FunctionType) : bETypeChecker C bes tf = true ↔ BeTyping C bes tf := by
  constructor
  · obtain ⟨tn, tm⟩ := tf
    intro h
    simp only [bETypeChecker, ← check_eq_foldl] at h
    obtain ⟨tn', h1, h2⟩ := tc_to_bet_list C (.type tn) bes tm _ rfl h
    simp only [cTypesAgree_type] at h1; rw [← h1] at h2; exact h2
  · intro hb
    induction hb with
    | unop h | binop h | relop h =>
      cases h <;> simp [bETypeChecker, checkSingle.eq_def, typeUpdate, consume, produce, ctSuffix,
        ctListCompat, toCtList, isInt, isFloat]
    | testop h =>
      simp [bETypeChecker, checkSingle.eq_def, typeUpdate, consume, produce, ctSuffix,
        ctListCompat, toCtList, h]
    | convert h1 h2 =>
      simp [bETypeChecker, checkSingle.eq_def, typeUpdate, consume, produce, ctSuffix,
        ctListCompat, toCtList, convertCond, h1, h2]
    | reinterpret h1 h2 =>
      simp [bETypeChecker, checkSingle.eq_def, typeUpdate, consume, produce, ctSuffix,
        ctListCompat, toCtList, h1, Nat.beq_eq_true_eq] at h2 ⊢
      simp [h2]
    | block _ ih | loop _ ih =>
      simp only [bETypeChecker, ← check_eq_foldl, List.singleton_append] at ih
      simp [bETypeChecker, checkSingle.eq_def, ih, typeUpdate, consume_self, produce,
        -toCtList_append]
    | ifWasm _ _ ih1 ih2 =>
      simp only [bETypeChecker, ← check_eq_foldl, List.singleton_append] at ih1 ih2
      simp [bETypeChecker, checkSingle.eq_def, ih1, ih2, typeUpdate, consume_self, produce,
        -toCtList_append]
    | br hi hp =>
      simp only [plop2, beq_iff_eq, List.getElem?_eq_some_iff] at hp
      simp [-toCtList_append, hp.2, bETypeChecker, checkSingle.eq_def, hi, hp, typeUpdate, consume_app, produce,
        ct_suffix_empty]
    | brIf hi hp =>
      simp only [plop2, beq_iff_eq, List.getElem?_eq_some_iff] at hp
      simp [-toCtList_append, hp.2, bETypeChecker, checkSingle.eq_def, hi, hp, typeUpdate, consume_self, produce]
    | brTable h =>
      have := sameLab_of_all _ _ _ (by simp) h
      simp [-toCtList_append, bETypeChecker, checkSingle.eq_def, this, typeUpdate, consume_app, produce,
        ct_suffix_empty]
    | return_ h =>
      simp [-toCtList_append, bETypeChecker, checkSingle.eq_def, h, typeUpdate, consume_app, produce,
        ct_suffix_empty]
    | call hi h =>
      rename_i tf
      obtain ⟨tn, tm⟩ := tf
      obtain ⟨_, h⟩ := List.getElem?_eq_some_iff.1 h
      simp [bETypeChecker, checkSingle.eq_def, hi, h, tu_self_type]
    | callIndirect hi h ht =>
      have : 1 ≤ _ := List.length_pos_iff.2 ht
      obtain ⟨_, h⟩ := List.getElem?_eq_some_iff.1 h
      simp [-toCtList_append, bETypeChecker, checkSingle.eq_def, hi, h, this, tu_self_type]
    | getLocal hi h | setLocal hi h | teeLocal hi h =>
      obtain ⟨_, h⟩ := List.getElem?_eq_some_iff.1 h
      simp [bETypeChecker, checkSingle.eq_def, hi, h, typeUpdate, consume, produce, ctSuffix,
        ctListCompat, toCtList]
    | getGlobal hi h =>
      obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨_, h⟩ := List.getElem?_eq_some_iff.1 hg
      simp [bETypeChecker, checkSingle.eq_def, hi, h, typeUpdate, consume, produce,
        ctSuffix, ctListCompat, toCtList]
    | setGlobal hi h ht hm =>
      subst ht
      obtain ⟨_, h⟩ := List.getElem?_eq_some_iff.1 h
      simp [bETypeChecker, checkSingle.eq_def, hi, h, hm, typeUpdate, consume, produce, ctSuffix,
        ctListCompat, toCtList]
    | load hm hb | store hm hb =>
      simp [bETypeChecker, checkSingle.eq_def, hm, hb, typeUpdate, consume, produce, ctSuffix,
        ctListCompat, toCtList]
    | currentMemory hm | growMemory hm =>
      simp [bETypeChecker, checkSingle.eq_def, hm, typeUpdate, consume, produce, ctSuffix,
        ctListCompat, toCtList]
    | empty => rfl
    | unreachable =>
      have (ts : List ValueType) : (ts.map CheckerTypeAux.some).drop ts.length = [] :=
        List.drop_eq_nil_of_le (by simp)
      simp [this, bETypeChecker, checkSingle.eq_def, typeUpdate, consume, produce, ctSuffix, toCtList,
        cTypesAgree, ctListCompat]
    | composition _ _ ih1 ih2 =>
      rename_i C es e t1s t2s t3s _ _
      simp only [bETypeChecker, List.foldl_append, List.foldl_cons, List.foldl_nil] at ih1 ih2 ⊢
      cases hc : es.foldl (checkSingle C) (.type t1s) with
      | type l =>
        rw [hc, cTypesAgree_type] at ih1; subst ih1; exact ih2
      | topType l =>
        rw [hc, cTypesAgree_top] at ih1
        exact c_types_agree_suffix_single l C t2s t3s e ih2 ih1
      | bot => rw [hc] at ih1; simp at ih1
    | weakening _ ih =>
      simp only [bETypeChecker, ← check_eq_foldl] at ih ⊢
      exact c_types_agree_weakening _ _ _ _ _ ih
    | _ =>
      simp [bETypeChecker, checkSingle.eq_def, typeUpdate, consume, produce, ctSuffix,
        ctListCompat, toCtList, typeUpdateSelect]

instance (C : TContext) (bes : List BasicInstruction) (tf : FunctionType) :
    Decidable (BeTyping C bes tf) :=
  decidable_of_iff _ (b_e_type_checker_reflects_typing C bes tf)

end Wasm
