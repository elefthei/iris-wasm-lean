/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import Wasm.Common
import Wasm.ListExtra
import Wasm.Opsem
import Wasm.Typing

/-! Port of `theories/properties.v`: miscellaneous properties of Wasm operations.
Arguments determined by a hypothesis are implicit (as Coq's `Set Implicit Arguments`). -/

namespace Wasm

/-! ### Basic lemmas -/

@[rocq_alias iriswasm.app_app]
theorem app_app {es1 es2 es3 es4 : List AdministrativeInstruction}
    (h : es1 ++ es2 = es3 ++ es4) (hlen : es1.length = es3.length) : (es1, es2) = (es3, es4) := by
  obtain ⟨rfl, rfl⟩ := List.append_inj h hlen; rfl

@[rocq_alias iriswasm.combine_app]
theorem combine_app {T1 T2 : Type} {l1 : List T1} (l3 : List T1) {l2 : List T2} (l4 : List T2)
    (h : l1.length = l2.length) : (l1 ++ l3).zip (l2 ++ l4) = l1.zip l2 ++ l3.zip l4 := by
  exact List.zip_append h

@[rocq_alias iriswasm.const_list_concat]
theorem const_list_concat {vs1 vs2 : List AdministrativeInstruction}
    (h1 : constList vs1 = true) (h2 : constList vs2 = true) : constList (vs1 ++ vs2) = true := by
  simp_all [constList]

@[rocq_alias iriswasm.const_list_split]
theorem const_list_split {vs1 vs2 : List AdministrativeInstruction}
    (h : constList (vs1 ++ vs2) = true) : constList vs1 = true ∧ constList vs2 = true := by
  simpa [constList] using h

private theorem isConst_iff {e : AdministrativeInstruction} :
    isConst e = true ↔ ∃ v, e = .basic (.const v) := by
  rcases e with b | _ | _ | _ | _ | _ <;> simp [isConst]
  cases b <;> simp

/-- Justifies the computation "to the first non-`constList`". -/
@[rocq_alias iriswasm.const_list_concat_inv]
theorem const_list_concat_inv {vs1 vs2 : List AdministrativeInstruction}
    {e1 e2 : AdministrativeInstruction} {es1 es2 : List AdministrativeInstruction}
    (hc1 : constList vs1 = true) (hc2 : constList vs2 = true)
    (hn1 : ¬ isConst e1 = true) (hn2 : ¬ isConst e2 = true)
    (h : vs1 ++ e1 :: es1 = vs2 ++ e2 :: es2) : vs1 = vs2 ∧ e1 = e2 ∧ es1 = es2 := by
  induction vs1 generalizing vs2 with
  | nil =>
    cases vs2 with
    | nil => simpa using h
    | cons b vs2 =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      simp_all [constList]
  | cons a vs1 ih =>
    cases vs2 with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, -⟩ := h
      simp_all [constList]
    | cons b vs2 =>
      simp only [List.cons_append, List.cons.injEq] at h
      simp only [constList, List.all_cons, Bool.and_eq_true] at hc1 hc2
      obtain ⟨rfl, h⟩ := h
      obtain ⟨rfl, rfl, rfl⟩ := ih hc1.2 hc2.2 h
      exact ⟨rfl, rfl, rfl⟩

@[rocq_alias iriswasm.const_list_take]
theorem const_list_take {vs : List AdministrativeInstruction} (l : Nat)
    (h : constList vs = true) : constList (vs.take l) = true := by
  simp only [constList, List.all_eq_true] at *
  exact fun x hx => h x (List.mem_of_mem_take hx)

@[rocq_alias iriswasm.v_to_e_is_const_list]
theorem v_to_e_is_const_list (vs : List Value) : constList (vToEList vs) = true := by
  simp [constList, vToEList, isConst]

@[rocq_alias iriswasm.v_to_e_cat]
theorem v_to_e_cat (vs1 vs2 : List Value) :
    vToEList vs1 ++ vToEList vs2 = vToEList (vs1 ++ vs2) := by
  simp [vToEList]

@[rocq_alias iriswasm.v_to_e_inj]
theorem v_to_e_inj {vs1 vs2 : List Value} (h : vToEList vs1 = vToEList vs2) : vs1 = vs2 := by
  exact (List.map_inj_right (by intro x y h; simpa using h)).1 h

@[rocq_alias iriswasm.split_vals_e_v_to_e_duality]
theorem split_vals_e_v_to_e_duality {es : List AdministrativeInstruction} {vs : List Value}
    {es' : List AdministrativeInstruction} (h : splitValsE es = (vs, es')) :
    es = vToEList vs ++ es' := by
  induction es generalizing vs es' with
  | nil => simp only [splitValsE, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | cons a es ih =>
    rcases a with b | _ | _ | _ | _ | _
    · cases b
      case const v =>
        rcases hs : splitValsE es with ⟨vs0, es0⟩
        simp only [splitValsE, hs, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [ih hs, vToEList]
      all_goals simp only [splitValsE, Prod.mk.injEq] at h; simp [← h.1, ← h.2, vToEList]
    all_goals simp only [splitValsE, Prod.mk.injEq] at h; simp [← h.1, ← h.2, vToEList]

@[rocq_alias iriswasm.const_list_cons]
theorem const_list_cons (a : AdministrativeInstruction) (l : List AdministrativeInstruction) :
    constList (a :: l) = (isConst a && constList l) := by
  rfl

@[rocq_alias iriswasm.v_to_e_list0]
theorem v_to_e_list0 : vToEList [] = [] := by
  rfl

@[rocq_alias iriswasm.v_to_e_list1]
theorem v_to_e_list1 (v : Value) : vToEList [v] = [.basic (.const v)] := by
  rfl

@[rocq_alias iriswasm.e_is_trapP]
theorem e_is_trapP (e : AdministrativeInstruction) : eIsTrap e = true ↔ e = .trap := by
  cases e <;> simp [eIsTrap]

@[rocq_alias iriswasm.es_is_trapP]
theorem es_is_trapP (l : List AdministrativeInstruction) : esIsTrap l = true ↔ l = [.trap] := by
  match l with
  | [] => simp [esIsTrap]
  | [e] => simp [esIsTrap, e_is_trapP]
  | _ :: _ :: _ => simp [esIsTrap]

@[rocq_alias iriswasm.split_n_is_take_drop]
theorem split_n_is_take_drop (es : List Value) (n : Nat) :
    splitN es n = (es.take n, es.drop n) := by
  induction es generalizing n with
  | nil => simp [splitN]
  | cons e es ih => cases n <;> simp_all [splitN]

@[rocq_alias iriswasm.update_list_at_is_set_nth]
theorem update_list_at_is_set_nth {X : Type} {l : List X} {n : Nat} (x : X) (h : n < l.length) :
    l.set n x = updateListAt l n x := by
  simp [updateListAt, List.set_eq_take_append_cons_drop, h]

@[rocq_alias iriswasm.length_is_size]
theorem length_is_size {X : Type} (l : List X) : l.length = l.length := rfl

@[rocq_alias iriswasm.v_to_e_take_exchange]
theorem v_to_e_take_exchange (vs : List Value) (n : Nat) :
    vToEList (vs.take n) = (vToEList vs).take n := by
  simp [vToEList, List.map_take]

@[rocq_alias iriswasm.v_to_e_drop_exchange]
theorem v_to_e_drop_exchange (vs : List Value) (n : Nat) :
    vToEList (vs.drop n) = (vToEList vs).drop n := by
  simp [vToEList, List.map_drop]

@[rocq_alias iriswasm.v_to_e_size]
theorem v_to_e_size (vs : List Value) : (vToEList vs).length = vs.length := by
  simp [vToEList]

/-- Splits the stack into the values consumed by an instruction and the rest. -/
@[rocq_alias iriswasm.v_to_e_take_drop_split]
theorem v_to_e_take_drop_split (l : List Value) (n : Nat) :
    vToEList l = vToEList (l.take n) ++ vToEList (l.drop n) := by
  rw [v_to_e_cat, List.take_append_drop]

@[rocq_alias iriswasm.v_to_e_take]
theorem v_to_e_take (l : List Value) (n : Nat) : vToEList (l.take n) = (vToEList l).take n := by
  exact v_to_e_take_exchange l n

@[rocq_alias iriswasm.v_to_e_drop]
theorem v_to_e_drop (l : List Value) (n : Nat) : vToEList (l.drop n) = (vToEList l).drop n := by
  exact v_to_e_drop_exchange l n

@[rocq_alias iriswasm.v_to_e_rev]
theorem v_to_e_rev (l : List Value) : vToEList l.reverse = (vToEList l).reverse := by
  simp [vToEList, List.map_reverse]

@[rocq_alias iriswasm.to_b_list_concat]
theorem to_b_list_concat (es1 es2 : List AdministrativeInstruction) :
    toBList (es1 ++ es2) = toBList es1 ++ toBList es2 := by
  simp [toBList]

@[rocq_alias iriswasm.to_e_list_basic]
theorem to_e_list_basic (bes : List BasicInstruction) : EsIsBasic (toEList bes) := by
  induction bes <;> simp_all [toEList, EsIsBasic, EIsBasic]

@[rocq_alias iriswasm.basic_concat]
theorem basic_concat {es1 es2 : List AdministrativeInstruction} (h : EsIsBasic (es1 ++ es2)) :
    EsIsBasic es1 ∧ EsIsBasic es2 := by
  induction es1 <;> simp_all [EsIsBasic]

@[rocq_alias iriswasm.basic_split]
theorem basic_split {es1 es2 : List AdministrativeInstruction} (h1 : EsIsBasic es1)
    (h2 : EsIsBasic es2) : EsIsBasic (es1 ++ es2) := by
  induction es1 <;> simp_all [EsIsBasic]

@[rocq_alias iriswasm.const_list_is_basic]
theorem const_list_is_basic {es : List AdministrativeInstruction} (h : constList es = true) :
    EsIsBasic es := by
  induction es with
  | nil => trivial
  | cons a es ih =>
    simp only [constList, List.all_cons, Bool.and_eq_true] at h
    obtain ⟨v, rfl⟩ := isConst_iff.1 h.1
    exact ⟨⟨_, rfl⟩, ih h.2⟩

@[rocq_alias iriswasm.to_b_list_rev]
theorem to_b_list_rev (es : List AdministrativeInstruction) :
    (toBList es).reverse = toBList es.reverse := by
  simp [toBList, List.map_reverse]

@[rocq_alias iriswasm.vs_to_vts_cat]
theorem vs_to_vts_cat (vs1 vs2 : List Value) :
    vsToVts (vs1 ++ vs2) = vsToVts vs1 ++ vsToVts vs2 := by
  simp [vsToVts]

@[rocq_alias iriswasm.vs_to_vts_rev]
theorem vs_to_vts_rev (vs : List Value) : vsToVts vs.reverse = (vsToVts vs).reverse := by
  simp [vsToVts, List.map_reverse]

@[rocq_alias iriswasm.const_es_exists]
theorem const_es_exists {es : List AdministrativeInstruction} (h : constList es = true) :
    ∃ vs, es = vToEList vs := by
  induction es with
  | nil => exact ⟨[], rfl⟩
  | cons a es ih =>
    simp only [constList, List.all_cons, Bool.and_eq_true] at h
    obtain ⟨v, rfl⟩ := isConst_iff.1 h.1
    obtain ⟨vs, rfl⟩ := ih h.2
    exact ⟨v :: vs, rfl⟩

@[rocq_alias iriswasm.properties.b_e_elim]
theorem b_e_elim {bes : List BasicInstruction} {es : List AdministrativeInstruction}
    (h : toEList bes = es) : bes = toBList es ∧ EsIsBasic es := by
  subst h
  exact ⟨by simp [toBList, toEList, Function.comp_def, toBSingle], to_e_list_basic bes⟩

@[rocq_alias iriswasm.e_b_elim]
theorem e_b_elim {bes : List BasicInstruction} {es : List AdministrativeInstruction}
    (h1 : bes = toBList es) (h2 : EsIsBasic es) : es = toEList bes := by
  subst h1
  induction es with
  | nil => rfl
  | cons a es ih =>
    obtain ⟨⟨b, rfl⟩, h2⟩ := h2
    simp [toEList, toBList, toBSingle] at ih ⊢
    exact ih h2

@[rocq_alias iriswasm.to_e_list_injective]
theorem to_e_list_injective {bes bes' : List BasicInstruction} (h : toEList bes = toEList bes') :
    bes = bes' := by
  exact (List.map_inj_right (by intro x y h; simpa using h)).1 h

@[rocq_alias iriswasm.properties.to_e_list_cat]
theorem to_e_list_cat (bes1 bes2 : List BasicInstruction) :
    toEList (bes1 ++ bes2) = toEList bes1 ++ toEList bes2 := by
  simp [toEList]

@[rocq_alias iriswasm.concat_cancel_last]
theorem concat_cancel_last {X : Type} {l1 l2 : List X} {e1 e2 : X}
    (h : l1 ++ [e1] = l2 ++ [e2]) : l1 = l2 ∧ e1 = e2 := by
  obtain ⟨h1, h2⟩ := List.append_inj' h rfl
  exact ⟨h1, by simpa using h2⟩

/-- Coq concludes `(l1 == l3) && (l2 == l4)`; stated with `∧` of equalities (eqType mapping). -/
@[rocq_alias iriswasm.concat_cancel_last_n]
theorem concat_cancel_last_n {l1 l2 l3 l4 : List ValueType} (h : l1 ++ l2 = l3 ++ l4)
    (hs : l2.length = l4.length) : l1 = l3 ∧ l2 = l4 := by
  exact List.append_inj' h hs

@[rocq_alias iriswasm.extract_list1]
theorem extract_list1 {X : Type} {es : List X} {e1 e2 : X} (h : es ++ [e1] = [e2]) :
    es = [] ∧ e1 = e2 := by
  exact concat_cancel_last (l2 := []) h

@[rocq_alias iriswasm.extract_list2]
theorem extract_list2 {X : Type} {es : List X} {e1 e2 e3 : X} (h : es ++ [e1] = [e2, e3]) :
    es = [e2] ∧ e1 = e3 := by
  exact concat_cancel_last (l2 := [e2]) h

@[rocq_alias iriswasm.extract_list3]
theorem extract_list3 {X : Type} {es : List X} {e1 e2 e3 e4 : X}
    (h : es ++ [e1] = [e2, e3, e4]) : es = [e2, e3] ∧ e1 = e4 := by
  exact concat_cancel_last (l2 := [e2, e3]) h

@[rocq_alias iriswasm.extract_list4]
theorem extract_list4 {X : Type} {es : List X} {e1 e2 e3 e4 e5 : X}
    (h : es ++ [e1] = [e2, e3, e4, e5]) : es = [e2, e3, e4] ∧ e1 = e5 := by
  exact concat_cancel_last (l2 := [e2, e3, e4]) h

@[rocq_alias iriswasm.list_nth_prefix]
theorem list_nth_prefix {X : Type} (l1 l2 : List X) (x : X) :
    (l1 ++ [x] ++ l2)[l1.length]? = some x := by
  simp

/-! ### Tactics
The Coq `gen_ind` family generalises indices before induction; Lean's `induction`/`cases` do this
natively. The other Ltacs are only used by base-file proofs, which are redone with Lean automation. -/

#rocq_ignore iriswasm.gen_ind_pre "Lean's induction generalises indices natively"
#rocq_ignore iriswasm.gen_ind_gen "Lean's induction generalises indices natively"
#rocq_ignore iriswasm.gen_ind_post "Lean's induction generalises indices natively"
#rocq_ignore iriswasm.gen_ind "Lean's induction generalises indices natively"
#rocq_ignore iriswasm.gen_ind_subst "Lean's induction generalises indices natively"
#rocq_ignore iriswasm.call_unfold "Ltac helper; not used by theories/iris"
#rocq_ignore iriswasm.basic_inversion "Ltac helper; not used by theories/iris (use basic_concat)"
#rocq_ignore iriswasm.extract_listn "Ltac helper; not used by theories/iris (use extract_list*)"
#rocq_ignore iriswasm.fold_upd_context "Ltac helper; not used by theories/iris"
#rocq_ignore iriswasm.auto_prove_bet "Ltac helper local to composition_typing_single's proof"

/-! ### More advanced lemmas -/

@[rocq_alias iriswasm.lfilled_swap]
theorem lfilled_swap {i : Nat} {lh : Lholed} {es LI : List AdministrativeInstruction}
    (es' : List AdministrativeInstruction) (h : lfilled i lh es LI = true) :
    ∃ LI', lfilled i lh es' LI' = true := by
  rw [lfilled_Ind_Equivalent] at h
  simp only [lfilled_Ind_Equivalent]
  induction h with
  | lfilledBase vs _ es'' hc => exact ⟨_, .lfilledBase vs es' es'' hc⟩
  | lfilledRec k vs n es0 lh' es'' _ _ hc _ ih =>
    obtain ⟨LI', h'⟩ := ih
    exact ⟨_, .lfilledRec k vs n es0 lh' es'' es' LI' hc h'⟩

@[rocq_alias iriswasm.lfilled_inj]
theorem lfilled_inj {i : Nat} {lh : Lholed} {es LI LI' : List AdministrativeInstruction}
    (h1 : lfilled i lh es LI = true) (h2 : lfilled i lh es LI' = true) : LI = LI' := by
  rw [lfilled_Ind_Equivalent] at h1 h2
  induction h1 generalizing LI' with
  | lfilledBase => cases h2; rfl
  | lfilledRec _ _ _ _ _ _ _ _ _ _ ih =>
    cases h2 with
    | lfilledRec _ _ _ _ _ _ _ _ _ h2' => rw [ih h2']

@[rocq_alias iriswasm.lfilled_collapse1]
theorem lfilled_collapse1 {n : Nat} {lh : Lholed} {vs es LI : List AdministrativeInstruction}
    (l : Nat) (h : LfilledInd n lh (vs ++ es) LI) (hc : constList vs = true)
    (_hl : vs.length ≥ l) : ∃ lh', LfilledInd n lh' (vs.drop (vs.length - l) ++ es) LI := by
  generalize hE : vs ++ es = X at h
  induction h with
  | lfilledBase vs0 X' es'' hc0 =>
    subst hE
    have e : vs0 ++ (vs ++ es) ++ es'' =
        (vs0 ++ vs.take (vs.length - l)) ++ (vs.drop (vs.length - l) ++ es) ++ es'' := by
      conv => lhs; rw [← List.take_append_drop (vs.length - l) vs]
      simp only [List.append_assoc]
    rw [e]
    exact ⟨_, .lfilledBase _ _ _ (const_list_concat hc0 (const_list_take _ hc))⟩
  | lfilledRec _ vs0 n0 es0 _ es'' _ _ hc0 _ ih =>
    obtain ⟨lh2, h2⟩ := ih hE
    exact ⟨.rec_ vs0 n0 es0 lh2 es'', .lfilledRec _ _ _ _ _ _ _ _ hc0 h2⟩

@[rocq_alias iriswasm.lfilled_collapse2]
theorem lfilled_collapse2 {n : Nat} {lh : Lholed} {es es' LI : List AdministrativeInstruction}
    (h : LfilledInd n lh (es ++ es') LI) : ∃ lh', LfilledInd n lh' es LI := by
  generalize hE : es ++ es' = X at h
  induction h with
  | lfilledBase vs0 X' es'' hc0 =>
    subst hE
    exact ⟨.base vs0 (es' ++ es''), by simpa using LfilledInd.lfilledBase vs0 es (es' ++ es'') hc0⟩
  | lfilledRec _ vs0 n0 es0 _ es'' _ _ hc0 _ ih =>
    obtain ⟨lh2, h2⟩ := ih hE
    exact ⟨.rec_ vs0 n0 es0 lh2 es'', .lfilledRec _ _ _ _ _ _ _ _ hc0 h2⟩

@[rocq_alias iriswasm.lfilled_collapse3]
theorem lfilled_collapse3 {k : Nat} {lh : Lholed} {n : Nat}
    {les es LI : List AdministrativeInstruction} (h : LfilledInd k lh [.label n les es] LI) :
    ∃ lh', LfilledInd (k + 1) lh' es LI := by
  generalize hE : [AdministrativeInstruction.label n les es] = X at h
  induction h with
  | lfilledBase vs0 X' es'' hc0 =>
    subst hE
    have hb : LfilledInd 0 (.base [] []) es es := by
      simpa using LfilledInd.lfilledBase [] es [] rfl
    exact ⟨_, .lfilledRec 0 vs0 n les _ es'' es es hc0 hb⟩
  | lfilledRec _ vs0 n0 es0 _ es'' _ _ hc0 _ ih =>
    obtain ⟨lh2, h2⟩ := ih hE
    exact ⟨.rec_ vs0 n0 es0 lh2 es'', .lfilledRec _ _ _ _ _ _ _ _ hc0 h2⟩

@[rocq_alias iriswasm.lfilled_deterministic]
theorem lfilled_deterministic {k : Nat} {lh : Lholed} {es les les' : List AdministrativeInstruction}
    (h1 : LfilledInd k lh es les) (h2 : LfilledInd k lh es les') : les = les' := by
  exact lfilled_inj ((lfilled_Ind_Equivalent ..).2 h1) ((lfilled_Ind_Equivalent ..).2 h2)

@[rocq_alias iriswasm.all_projection]
theorem all_projection {X : Type} {f : X → Bool} {l : List X} {n : Nat} {x : X}
    (h : l.all f = true) (hn : l[n]? = some x) : f x = true := by
  exact List.all_eq_true.1 h x (List.mem_of_getElem? hn)

@[rocq_alias iriswasm.all2_projection]
theorem all2_projection {X Y : Type} {f : X → Y → Bool} {l1 : List X} {l2 : List Y} {n : Nat}
    {x1 : X} {x2 : Y} (h : List.all2 f l1 l2 = true) (h1 : l1[n]? = some x1)
    (h2 : l2[n]? = some x2) : f x1 x2 = true := by
  induction l1 generalizing l2 n with
  | nil => simp at h1
  | cons a l1 ih =>
    cases l2 with
    | nil => simp at h2
    | cons b l2 =>
      simp only [List.all2_cons, Bool.and_eq_true] at h
      cases n with
      | zero => simp at h1 h2; subst h1 h2; exact h.1
      | succ n => simp at h1 h2; exact ih h.2 h1 h2

@[rocq_alias iriswasm.all2_Forall2]
theorem all2_Forall2 {T1 T2 : Type} (r : T1 → T2 → Bool) (l1 : List T1) (l2 : List T2) :
    List.all2 r l1 l2 = true ↔ List.Forall₂ (fun x y => r x y = true) l1 l2 := by
  exact List.all2_Forall₂ r l1 l2

/-- `f` is a functional relation. -/
@[rocq_alias iriswasm.function]
def Function {X Y : Type} (f : X → Y → Prop) : Prop :=
  ∀ x y1 y2, (f x y1 ∧ f x y2) → y1 = y2

@[rocq_alias iriswasm.all2_function_unique]
theorem all2_function_unique {X Y : Type} {f : X → Y → Bool} {l1 : List X} {l2 l3 : List Y}
    (h1 : List.all2 f l1 l2 = true) (h2 : List.all2 f l1 l3 = true)
    (hf : Function (fun x y => f x y = true)) : l2 = l3 := by
  induction l1 generalizing l2 l3 with
  | nil => cases l2 <;> cases l3 <;> simp_all
  | cons a l1 ih =>
    match l2, l3, h1, h2 with
    | b :: l2, c :: l3, h1, h2 =>
      simp only [List.all2_cons, Bool.and_eq_true] at h1 h2
      rw [hf a b c ⟨h1.1, h2.1⟩, ih h1.2 h2.2]
    | [], _, h1, _ => simp at h1
    | _, [], _, h2 => simp at h2

#rocq_ignore iriswasm.lfilled_pickable_rec_gen_measure_single
  "termination measure of the pickability proof; pickability replaced by classical Decidable"
#rocq_ignore iriswasm.lfilled_pickable_rec_gen_measure
  "termination measure of the pickability proof; pickability replaced by classical Decidable"
#rocq_ignore iriswasm.fold_left_max_rem "only used by the pickability measure"
#rocq_ignore iriswasm.fold_left_max_app_cons "only used by the pickability measure"
#rocq_ignore iriswasm.lfilled_pickable_rec_gen_measure_cons "only used by the pickability measure"
#rocq_ignore iriswasm.lfilled_pickable_rec_gen_measure_concat_l
  "only used by the pickability measure"
#rocq_ignore iriswasm.lfilled_pickable_rec_gen_measure_concat_r
  "only used by the pickability measure"
#rocq_ignore iriswasm.lfilled_pickable_rec_gen_measure_label_r
  "only used by the pickability measure"
#rocq_ignore iriswasm.lfilledInd_pickable_rec_gen "pickability replaced by classical Decidable"
#rocq_ignore iriswasm.lfilled_pickable_rec_gen "pickability replaced by classical Decidable"
#rocq_ignore iriswasm.lfilled_decidable_base "lfilled is Bool-valued, hence decidable"
#rocq_ignore iriswasm.lfilled_pickable_base "pickability replaced by classical Decidable"
#rocq_ignore iriswasm.lfilled_pickable_rec "pickability replaced by classical Decidable"

/-! ### Framing lemmas: focus on parts of the stack, ignoring the context. -/

@[rocq_alias iriswasm.r_eliml]
theorem r_eliml {s : StoreRecord} {f : Frame} {es : List AdministrativeInstruction}
    {s' : StoreRecord} {f' : Frame} {es' lconst : List AdministrativeInstruction}
    (hc : constList lconst = true) (h : Reduce s f es s' f' es') :
    Reduce s f (lconst ++ es) s' f' (lconst ++ es') := by
  exact .label es es' 0 (.base lconst []) h (by simp [lfilled, lfill, hc])
    (by simp [lfilled, lfill, hc])

@[rocq_alias iriswasm.r_elimr]
theorem r_elimr {s : StoreRecord} {f : Frame} {es : List AdministrativeInstruction}
    {s' : StoreRecord} {f' : Frame} {es' : List AdministrativeInstruction}
    (les : List AdministrativeInstruction) (h : Reduce s f es s' f' es') :
    Reduce s f (es ++ les) s' f' (es' ++ les) := by
  exact .label es es' 0 (.base [] les) h (by simp [lfilled, lfill, constList])
    (by simp [lfilled, lfill, constList])

@[rocq_alias iriswasm.r_eliml_empty]
theorem r_eliml_empty {s : StoreRecord} {f : Frame} {es : List AdministrativeInstruction}
    {s' : StoreRecord} {f' : Frame} {lconst : List AdministrativeInstruction}
    (hc : constList lconst = true) (h : Reduce s f es s' f' []) :
    Reduce s f (lconst ++ es) s' f' lconst := by
  simpa using r_eliml hc h

@[rocq_alias iriswasm.r_elimr_empty]
theorem r_elimr_empty {s : StoreRecord} {f : Frame} {es : List AdministrativeInstruction}
    {s' : StoreRecord} {f' : Frame} (les : List AdministrativeInstruction)
    (h : Reduce s f es s' f' []) : Reduce s f (es ++ les) s' f' les := by
  simpa using r_elimr les h

/-! ### Typing -/

/-- A reformulation of `ETyping.a` that is easier to use. -/
@[rocq_alias iriswasm.ety_a']
theorem ety_a' (s : StoreRecord) {C : TContext} {es : List AdministrativeInstruction}
    {ts : FunctionType} (hb : EsIsBasic es) (h : BeTyping C (toBList es) ts) :
    ETyping s C es ts := by
  have := ETyping.a (s := s) h
  rwa [← e_b_elim rfl hb] at this

@[rocq_alias iriswasm.bet_weakening_empty_1]
theorem bet_weakening_empty_1 {C : TContext} {es : List BasicInstruction} (ts : List ValueType)
    {t2s : List ValueType} (h : BeTyping C es (.tf [] t2s)) :
    BeTyping C es (.tf ts (ts ++ t2s)) := by
  simpa using BeTyping.weakening (ts := ts) h

@[rocq_alias iriswasm.et_weakening_empty_1]
theorem et_weakening_empty_1 {s : StoreRecord} {C : TContext} {es : List AdministrativeInstruction}
    (ts : List ValueType) {t2s : List ValueType} (h : ETyping s C es (.tf [] t2s)) :
    ETyping s C es (.tf ts (ts ++ t2s)) := by
  simpa using ETyping.weakening (ts := ts) h

@[rocq_alias iriswasm.bet_weakening_empty_2]
theorem bet_weakening_empty_2 {C : TContext} {es : List BasicInstruction} (ts : List ValueType)
    {t1s : List ValueType} (h : BeTyping C es (.tf t1s [])) :
    BeTyping C es (.tf (ts ++ t1s) ts) := by
  simpa using BeTyping.weakening (ts := ts) h

@[rocq_alias iriswasm.bet_weakening_empty_both]
theorem bet_weakening_empty_both {C : TContext} {es : List BasicInstruction}
    (ts : List ValueType) (h : BeTyping C es (.tf [] [])) : BeTyping C es (.tf ts ts) := by
  simpa using BeTyping.weakening (ts := ts) h

@[rocq_alias iriswasm.empty_typing]
theorem empty_typing {C : TContext} {t1s t2s : List ValueType} (h : BeTyping C [] (.tf t1s t2s)) :
    t1s = t2s := by
  generalize hes : ([] : List BasicInstruction) = es at h
  generalize htf : FunctionType.tf t1s t2s = tf at h
  induction h generalizing t1s t2s
  case empty => cases htf; rfl
  case weakening _ _ _ _ _ _ ih => cases htf; rw [ih hes rfl]
  all_goals simp at hes

/-- Inverts `ETyping` back to `BeTyping`. -/
@[rocq_alias iriswasm.et_to_bet]
theorem et_to_bet {s : StoreRecord} {C : TContext} {es : List AdministrativeInstruction}
    {ts : FunctionType} (hb : EsIsBasic es) (h : ETyping s C es ts) :
    BeTyping C (toBList es) ts := by
  match h with
  | .a h' => simpa [toBList, toEList, Function.comp_def, toBSingle] using h'
  | .composition h1 h2 =>
    obtain ⟨hb1, hb2⟩ := basic_concat hb
    rw [to_b_list_concat]
    exact .composition (et_to_bet hb1 h1) (et_to_bet hb2 h2)
  | .weakening h1 => exact .weakening (et_to_bet hb h1)
  | .trap | .local .. | .invoke .. | .label .. | .callHost .. =>
    simp [EsIsBasic, EIsBasic] at hb

@[rocq_alias iriswasm.composition_typing_single]
theorem composition_typing_single {C : TContext} {es1 : List BasicInstruction}
    {e : BasicInstruction} {t1s t2s : List ValueType} (h : BeTyping C (es1 ++ [e]) (.tf t1s t2s)) :
    ∃ ts t1s' t2s' t3s, t1s = ts ++ t1s' ∧ t2s = ts ++ t2s' ∧
      BeTyping C es1 (.tf t1s' t3s) ∧ BeTyping C [e] (.tf t3s t2s') := by
  suffices key : ∀ {es tf}, BeTyping C es tf → ∀ {es1 : List BasicInstruction}
      {e : BasicInstruction} {t1s t2s : List ValueType},
      es = es1 ++ [e] → tf = .tf t1s t2s → BeTyping C es tf →
      ∃ ts t1s' t2s' t3s, t1s = ts ++ t1s' ∧ t2s = ts ++ t2s' ∧
        BeTyping C es1 (.tf t1s' t3s) ∧ BeTyping C [e] (.tf t3s t2s') from key h rfl rfl h
  clear h
  intro es tf hty
  induction hty
  case empty => intro _ _ _ _ hes; simp at hes
  case composition h1 h2 _ _ =>
    intro es1 e t1s t2s hes htf _
    obtain ⟨rfl, rfl⟩ := concat_cancel_last hes
    cases htf
    exact ⟨[], _, _, _, rfl, rfl, h1, h2⟩
  case weakening ts _ _ h1 ih =>
    intro es1 e a b hes htf _
    obtain ⟨ts', t1s', t2s', t3s', rfl, rfl, H3, H4⟩ := ih hes rfl h1
    cases htf
    exact ⟨ts ++ ts', t1s', t2s', t3s', by simp, by simp, H3, H4⟩
  all_goals
    intro es1 e t1s t2s hes htf h0
    obtain ⟨rfl, rfl⟩ := extract_list1 hes.symm
    cases htf
    exact ⟨[], _, _, _, rfl, rfl, bet_weakening_empty_both _ .empty, h0⟩

@[rocq_alias iriswasm.composition_typing]
theorem composition_typing {C : TContext} {es1 es2 : List BasicInstruction}
    {t1s t2s : List ValueType} (h : BeTyping C (es1 ++ es2) (.tf t1s t2s)) :
    ∃ ts t1s' t2s' t3s, t1s = ts ++ t1s' ∧ t2s = ts ++ t2s' ∧
      BeTyping C es1 (.tf t1s' t3s) ∧ BeTyping C es2 (.tf t3s t2s') := by
  obtain ⟨l, rfl⟩ : ∃ l, es2 = l.reverse := ⟨es2.reverse, by simp⟩
  induction l generalizing t1s t2s with
  | nil =>
    simp only [List.reverse_nil, List.append_nil] at h
    exact ⟨[], t1s, t2s, t2s, rfl, rfl, h, bet_weakening_empty_both _ .empty⟩
  | cons a l ih =>
    rw [List.reverse_cons, ← List.append_assoc] at h
    obtain ⟨ts', t1s', t2s', t3s', rfl, rfl, H3, H4⟩ := composition_typing_single h
    obtain ⟨ts2, t1s2, t2s2, t3s2, rfl, rfl, H7, H8⟩ := ih H3
    refine ⟨ts', ts2 ++ t1s2, t2s', ts2 ++ t3s2, rfl, rfl, .weakening H7, ?_⟩
    rw [List.reverse_cons]
    exact .composition (.weakening H8) H4

private theorem e_comp_single_aux {s : StoreRecord} {C : TContext}
    {es : List AdministrativeInstruction} {tf : FunctionType} (h : ETyping s C es tf) :
    ∀ {es1 : List AdministrativeInstruction} {e : AdministrativeInstruction}
      {t1s t2s : List ValueType}, es = es1 ++ [e] → tf = .tf t1s t2s →
    ∃ ts t1s' t2s' t3s, t1s = ts ++ t1s' ∧ t2s = ts ++ t2s' ∧
      ETyping s C es1 (.tf t1s' t3s) ∧ ETyping s C [e] (.tf t3s t2s') := by
  match h with
  | .a hb =>
    intro es1 e t1s t2s hes htf
    obtain ⟨rfl, hbasic⟩ := b_e_elim hes
    rw [to_b_list_concat] at hb
    subst htf
    obtain ⟨ts, t1s', t2s', t3s, rfl, rfl, H3, H4⟩ := composition_typing hb
    obtain ⟨hb1, hb2⟩ := basic_concat hbasic
    exact ⟨ts, t1s', t2s', t3s, rfl, rfl, ety_a' s hb1 H3, ety_a' s hb2 H4⟩
  | .composition h1 h2 =>
    intro es1 e t1s t2s hes htf
    obtain ⟨rfl, rfl⟩ := concat_cancel_last hes
    cases htf
    exact ⟨[], _, _, _, rfl, rfl, h1, h2⟩
  | .weakening (ts := ts) h1 =>
    intro es1 e a b hes htf
    obtain ⟨ts', t1s', t2s', t3s', rfl, rfl, H3, H4⟩ := e_comp_single_aux h1 hes rfl
    cases htf
    exact ⟨ts ++ ts', t1s', t2s', t3s', by simp, by simp, H3, H4⟩
  | .trap =>
    intro es1 e t1s t2s hes htf
    obtain ⟨rfl, rfl⟩ := extract_list1 hes.symm
    cases htf
    exact ⟨[], _, _, _, rfl, rfl, ety_a' s trivial (bet_weakening_empty_both _ .empty), .trap⟩
  | .local h1 h2 =>
    intro es1 e t1s t2s hes htf
    obtain ⟨rfl, rfl⟩ := extract_list1 hes.symm
    cases htf
    exact ⟨[], _, _, _, rfl, rfl, ety_a' s trivial (bet_weakening_empty_both _ .empty),
      .local h1 h2⟩
  | .invoke h1 h2 =>
    intro es1 e t1s t2s hes htf
    obtain ⟨rfl, rfl⟩ := extract_list1 hes.symm
    cases htf
    exact ⟨[], _, _, _, rfl, rfl, ety_a' s trivial (bet_weakening_empty_both _ .empty),
      .invoke h1 h2⟩
  | .label h1 h2 h3 =>
    intro es1 e t1s t2s hes htf
    obtain ⟨rfl, rfl⟩ := extract_list1 hes.symm
    cases htf
    exact ⟨[], _, _, _, rfl, rfl, ety_a' s trivial (bet_weakening_empty_both _ .empty),
      .label h1 h2 h3⟩
  | .callHost h1 =>
    intro es1 e t1s t2s hes htf
    obtain ⟨rfl, rfl⟩ := extract_list1 hes.symm
    cases htf
    exact ⟨[], _, _, _, rfl, rfl, ety_a' s trivial (bet_weakening_empty_both _ .empty),
      .callHost h1⟩

@[rocq_alias iriswasm.e_composition_typing_single]
theorem e_composition_typing_single {s : StoreRecord} {C : TContext}
    {es1 : List AdministrativeInstruction} {e : AdministrativeInstruction}
    {t1s t2s : List ValueType} (h : ETyping s C (es1 ++ [e]) (.tf t1s t2s)) :
    ∃ ts t1s' t2s' t3s, t1s = ts ++ t1s' ∧ t2s = ts ++ t2s' ∧
      ETyping s C es1 (.tf t1s' t3s) ∧ ETyping s C [e] (.tf t3s t2s') := by
  exact e_comp_single_aux h rfl rfl

@[rocq_alias iriswasm.e_composition_typing]
theorem e_composition_typing {s : StoreRecord} {C : TContext}
    {es1 es2 : List AdministrativeInstruction} {t1s t2s : List ValueType}
    (h : ETyping s C (es1 ++ es2) (.tf t1s t2s)) :
    ∃ ts t1s' t2s' t3s, t1s = ts ++ t1s' ∧ t2s = ts ++ t2s' ∧
      ETyping s C es1 (.tf t1s' t3s) ∧ ETyping s C es2 (.tf t3s t2s') := by
  obtain ⟨l, rfl⟩ : ∃ l, es2 = l.reverse := ⟨es2.reverse, by simp⟩
  induction l generalizing t1s t2s with
  | nil =>
    simp only [List.reverse_nil, List.append_nil] at h
    exact ⟨[], t1s, t2s, t2s, rfl, rfl, h,
      ety_a' s trivial (bet_weakening_empty_both _ .empty)⟩
  | cons a l ih =>
    rw [List.reverse_cons, ← List.append_assoc] at h
    obtain ⟨ts', t1s', t2s', t3s', rfl, rfl, H3, H4⟩ := e_composition_typing_single h
    obtain ⟨ts2, t1s2, t2s2, t3s2, rfl, rfl, H7, H8⟩ := ih H3
    refine ⟨ts', ts2 ++ t1s2, t2s', ts2 ++ t3s2, rfl, rfl, .weakening H7, ?_⟩
    rw [List.reverse_cons]
    exact .composition (.weakening H8) H4

@[rocq_alias iriswasm.bet_composition']
theorem bet_composition' {C : TContext} {es1 es2 : List BasicInstruction}
    {t1s t2s t3s : List ValueType} (h1 : BeTyping C es1 (.tf t1s t2s))
    (h2 : BeTyping C es2 (.tf t2s t3s)) : BeTyping C (es1 ++ es2) (.tf t1s t3s) := by
  obtain ⟨l, rfl⟩ : ∃ l, es2 = l.reverse := ⟨es2.reverse, by simp⟩
  induction l generalizing t3s with
  | nil =>
    have := empty_typing h2
    subst this
    simpa using h1
  | cons a l ih =>
    rw [List.reverse_cons] at h2 ⊢
    obtain ⟨ts, t1s', t2s', t3s', rfl, rfl, H5, H6⟩ := composition_typing h2
    rw [← List.append_assoc]
    exact .composition (ih (.weakening H5)) (.weakening H6)

@[rocq_alias iriswasm.bet_composition_front]
theorem bet_composition_front {C : TContext} {e : BasicInstruction} {es : List BasicInstruction}
    {t1s t2s t3s : List ValueType} (h1 : BeTyping C [e] (.tf t1s t2s))
    (h2 : BeTyping C es (.tf t2s t3s)) : BeTyping C (e :: es) (.tf t1s t3s) := by
  exact bet_composition' (es1 := [e]) h1 h2

@[rocq_alias iriswasm.et_composition']
theorem et_composition' {s : StoreRecord} {C : TContext} {es1 es2 : List AdministrativeInstruction}
    {t1s t2s t3s : List ValueType} (h1 : ETyping s C es1 (.tf t1s t2s))
    (h2 : ETyping s C es2 (.tf t2s t3s)) : ETyping s C (es1 ++ es2) (.tf t1s t3s) := by
  obtain ⟨l, rfl⟩ : ∃ l, es2 = l.reverse := ⟨es2.reverse, by simp⟩
  induction l generalizing t3s with
  | nil =>
    have := empty_typing (et_to_bet (es := []) trivial h2)
    subst this
    simpa using h1
  | cons a l ih =>
    rw [List.reverse_cons] at h2 ⊢
    obtain ⟨ts, t1s', t2s', t3s', rfl, rfl, H5, H6⟩ := e_composition_typing h2
    rw [← List.append_assoc]
    exact .composition (ih (.weakening H5)) (.weakening H6)

/-! ### Reductions of empty stacks -/

@[rocq_alias iriswasm.cat_cons_not_nil]
theorem cat_cons_not_nil {T : Type} (xs : List T) (y : T) (ys : List T) : xs ++ y :: ys ≠ [] := by
  simp

@[rocq_alias iriswasm.properties.lfill_cons_not_Some_nil]
theorem lfill_cons_not_Some_nil {i : Nat} {lh : Lholed} {es : List AdministrativeInstruction}
    {es' : Option (List AdministrativeInstruction)} {e : AdministrativeInstruction}
    {es0 : List AdministrativeInstruction} (h1 : lfill i lh es = es') (h2 : es = e :: es0) :
    es' ≠ some [] := by
  subst h1 h2
  cases i <;> cases lh <;> simp only [lfill]
  all_goals (repeat' split); all_goals simp

@[rocq_alias iriswasm.properties.lfilled_not_nil]
theorem lfilled_not_nil {i : Nat} {lh : Lholed} {es es' : List AdministrativeInstruction}
    (h : lfilled i lh es es' = true) (hes : es ≠ []) : es' ≠ [] := by
  rintro rfl
  obtain ⟨e, es0, rfl⟩ := List.exists_cons_of_ne_nil hes
  unfold lfilled at h
  split at h
  · rename_i es'' heq
    simp at h
    subst h
    exact lfill_cons_not_Some_nil heq rfl rfl
  · simp at h

@[rocq_alias iriswasm.not_reduce_simple_nil]
theorem not_reduce_simple_nil (es' : List AdministrativeInstruction) : ¬ ReduceSimple [] es' := by
  intro h
  generalize he : ([] : List AdministrativeInstruction) = es at h
  cases h
  case trap hne hlf => exact lfilled_not_nil hlf (by simp) he.symm
  all_goals simp at he

@[rocq_alias iriswasm.reduce_not_nil]
theorem reduce_not_nil {σ1 : StoreRecord} {f : Frame} {es : List AdministrativeInstruction}
    {σ2 : StoreRecord} {f' : Frame} {es' : List AdministrativeInstruction}
    (h : Reduce σ1 f es σ2 f' es') : es ≠ [] := by
  induction h
  case simple hs => rintro rfl; exact not_reduce_simple_nil _ hs
  case label hl _ ih => exact lfilled_not_nil hl ih
  all_goals simp

end Wasm
