/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Helpers.LfillPrelude.LfillPrelude
import Iris.ProgramLogic.Language

/-! Port of `theories/iris/language/iris/iris.v`: Wasm as an Iris language. -/

namespace IrisWasm

open Wasm Iris Iris.ProgramLogic

@[rocq_alias iriswasm.iris.expr]
abbrev Expr := List AdministrativeInstruction

/-- A value can be an immediate, a trap, a `br i` if it is in a context shallow enough, i.e. a
`ValidHoled i`; or a return, in any context. `ValidHoled`/`SimpleValidHoled` are used instead of
`Lholed` so that the fill operations are total. -/
@[rocq_alias iriswasm.val]
inductive Val where
  | immV : List Value → Val
  | trapV : Val
  | brV {i : Nat} (lh : ValidHoled i) : Val
  | retV : SimpleValidHoled → Val
  | callHostV : FunctionType → Hostfuncidx → List Value → Llholed → Val
  deriving DecidableEq

#rocq_ignore iriswasm.val_eq_dec "Val derives DecidableEq"
#rocq_ignore iriswasm.val_eqb "use decide (v1 = v2)"
#rocq_ignore iriswasm.eqvalP "eqType glue; Val derives DecidableEq"
#rocq_ignore iriswasm.val_eqMixin "eqType glue; Val derives DecidableEq"
#rocq_ignore iriswasm.val_eqType "eqType glue; Val derives DecidableEq"

@[rocq_alias iriswasm.iris.state]
abbrev State := StoreRecord × List Value × Instance

@[rocq_alias iriswasm.observation]
abbrev Observation := Unit

@[rocq_alias iriswasm.of_val]
def ofVal : Val → Expr
  | .immV l => vToEList l
  | .trapV => [.trap]
  | .brV (i := i) vh => vfill vh [.basic (.br i)]
  | .retV sh => sfill sh [.basic .return_]
  | .callHostV tf h vcs sh => llfill sh [.callHost tf h vcs]

@[rocq_alias iriswasm.of_val_imm]
theorem of_val_imm (vs : List Value) : vToEList vs = ofVal (.immV vs) := rfl

/-- Mirrors the opsem of `trap` (a trap swallows all other stack values) and of `br`/`return`
(which skip over all subsequent expressions). -/
@[rocq_alias iriswasm.val_combine]
def valCombine (v1 v2 : Val) : Val :=
  match v1 with
  | .immV l => match v2 with
    | .immV l' => .immV (l ++ l')
    | .trapV => .trapV
    | .brV vh => .brV (vhPushConst vh l)
    | .retV lh => .retV (shPushConst lh l)
    | .callHostV tf h cvs sh => .callHostV tf h cvs (llhPushConst sh l)
  | .trapV => .trapV
  | .brV vh => .brV (vhAppend vh (ofVal v2))
  | .retV lh => .retV (shAppend lh (ofVal v2))
  | .callHostV tf h vcs sh => .callHostV tf h vcs (llhAppend sh (ofVal v2))

/-- Intuitively, `.notVal e` means `e` is not a value; this is not enforced by the syntax. -/
@[rocq_alias iriswasm.ValNotVal]
inductive ValNotVal where
  | val : Val → ValNotVal
  | notVal : Expr → ValNotVal

@[rocq_alias iriswasm.expr_of_val_not_val]
def exprOfValNotVal : ValNotVal → Expr
  | .val v => ofVal v
  | .notVal e => e

@[rocq_alias iriswasm.expr_of_val_of_val_not_val]
theorem expr_of_val_of_val_not_val (v : Val) : ofVal v = exprOfValNotVal (.val v) := rfl

@[rocq_alias iriswasm.val_of_val_not_val]
def valOfValNotVal : ValNotVal → Option Val
  | .val v => some v
  | .notVal _ => none

/-- Combining a `Val` and a `ValNotVal`, keeping the invariant that `.notVal e` is only used when
`e` is not a value. -/
@[rocq_alias iriswasm.val_not_val_combine]
def valNotValCombine (v1 : Val) (v2 : ValNotVal) : ValNotVal :=
  match v1 with
  | .immV l => match v2 with
    | .val (.immV l') => .val (.immV (l ++ l'))
    | .val .trapV => match l with
      | [] => .val .trapV
      | _ => .notVal (vToEList l ++ [.trap])
    | .val (.brV vh) => .val (.brV (vhPushConst vh l))
    | .val (.retV lh) => .val (.retV (shPushConst lh l))
    | .val (.callHostV tf h vcs lh) => .val (.callHostV tf h vcs (llhPushConst lh l))
    | .notVal e => .notVal (vToEList l ++ e)
  | .trapV => match exprOfValNotVal v2 with
    | [] => .val .trapV
    | _ => .notVal (.trap :: exprOfValNotVal v2)
  | .brV vh => .val (.brV (vhAppend vh (exprOfValNotVal v2)))
  | .retV lh => .val (.retV (shAppend lh (exprOfValNotVal v2)))
  | .callHostV tf h vcs lh => .val (.callHostV tf h vcs (llhAppend lh (exprOfValNotVal v2)))

/-- A `foldl` of `valNotValCombine` over a list; aborts at the first `.notVal`. -/
@[rocq_alias iriswasm.merge_values]
def mergeValues (v : Val) : List ValNotVal → ValNotVal
  | [] => .val v
  | a :: vs => match valNotValCombine v a with
    | .val v => mergeValues v vs
    | .notVal e => .notVal (e ++ (vs.map exprOfValNotVal).flatten)

@[rocq_alias iriswasm.merge_values_list]
def mergeValuesList : List ValNotVal → ValNotVal
  | .val v :: vs => mergeValues v vs
  | [] => .val (.immV [])
  | vs => .notVal (vs.map exprOfValNotVal).flatten

@[rocq_alias iriswasm.to_val_instr]
def toValInstr (instr : AdministrativeInstruction) : ValNotVal :=
  match instr with
  | .trap => .val .trapV
  | .basic (.br i) => .val (.brV (ValidHoled.base (n := i) [] []))
  | .basic .return_ => .val (.retV (.base [] []))
  | .basic (.const v) => .val (.immV [v])
  | .label n labe es =>
    match mergeValuesList (es.map toValInstr) with
    | .val (.brV vh) =>
      match vhDecrease (.rec_ [] n labe vh []) with
      | some vh' => .val (.brV vh')
      | none => .notVal [instr]
    | .val (.retV lh) => .val (.retV (.rec_ [] n labe lh []))
    | .val (.callHostV tf h cvs lh) => .val (.callHostV tf h cvs (.label [] n labe lh []))
    | _ => .notVal [instr]
  | .local n f es =>
    match mergeValuesList (es.map toValInstr) with
    | .val (.callHostV tf h cvs sh) => .val (.callHostV tf h cvs (.local [] n f sh []))
    | _ => .notVal [instr]
  | .callHost tf h cvs => .val (.callHostV tf h cvs (.base [] []))
  | _ => .notVal [instr]

@[rocq_alias iriswasm.to_val]
def toVal (e : Expr) : Option Val :=
  match mergeValuesList (e.map toValInstr) with
  | .val v => some v
  | _ => none

@[rocq_alias iriswasm.prim_step]
def primStep : Expr × State → List Observation → Expr × State × List Expr → Prop
  | (e, (s, locs, inst)), os, (e', (s', locs', inst'), forkEs') =>
    Reduce s ⟨locs, inst⟩ e s' ⟨locs', inst'⟩ e' ∧ os = [] ∧ forkEs' = []

/-! ### Local helpers on total fills (one-step unfoldings) -/

section helpers
variable {n : Nat}

private theorem vfill_push (vh : ValidHoled n) (vs : List Value) (es : Expr) :
    vfill (vhPushConst vh vs) es = vToEList vs ++ vfill vh es := by
  cases vh <;> simp [vhPushConst, vfill, vToEList]

private theorem sfill_push (sh : SimpleValidHoled) (vs : List Value) (es : Expr) :
    sfill (shPushConst sh vs) es = vToEList vs ++ sfill sh es := by
  cases sh <;> simp [shPushConst, sfill, vToEList]

private theorem llfill_push (lh : Llholed) (vs : List Value) (es : Expr) :
    llfill (llhPushConst lh vs) es = vToEList vs ++ llfill lh es := by
  cases lh <;> simp [llhPushConst, llfill, vToEList]

private theorem vfill_app (vh : ValidHoled n) (es' es : Expr) :
    vfill (vhAppend vh es') es = vfill vh es ++ es' := by
  cases vh <;> simp [vhAppend, vfill]

private theorem sfill_app (sh : SimpleValidHoled) (es' es : Expr) :
    sfill (shAppend sh es') es = sfill sh es ++ es' := by
  cases sh <;> simp [shAppend, sfill]

private theorem llfill_app (lh : Llholed) (es' es : Expr) :
    llfill (llhAppend lh es') es = llfill lh es ++ es' := by
  cases lh <;> simp [llhAppend, llfill]

private theorem vfill_ne_nil (vh : ValidHoled n) (e : AdministrativeInstruction) (es : Expr) :
    vfill vh (e :: es) ≠ [] := by
  cases vh <;> simp [vfill]

private theorem sfill_ne_nil (sh : SimpleValidHoled) (e : AdministrativeInstruction) (es : Expr) :
    sfill sh (e :: es) ≠ [] := by
  cases sh <;> simp [sfill]

private theorem llfill_ne_nil (lh : Llholed) (e : AdministrativeInstruction) (es : Expr) :
    llfill lh (e :: es) ≠ [] := by
  cases lh <;> simp [llfill]

end helpers

attribute [local simp] vfill_push sfill_push llfill_push vfill_app sfill_app llfill_app
  vh_append_nil sh_append_nil llh_append_nil vh_push_const_nil sh_push_const_nil llh_push_const_nil
  vh_push_const_append sh_push_const_append llh_push_const_append
attribute [local simp ←] vh_append_app sh_append_app llh_append_app
  vh_push_const_app sh_push_const_app llh_push_const_app

private theorem vToEList_eq_nil (l : List Value) : vToEList l = [] ↔ l = [] := by
  simp [vToEList]

private theorem vToEList_append' (l1 l2 : List Value) :
    vToEList (l1 ++ l2) = vToEList l1 ++ vToEList l2 := by
  simp [vToEList]

attribute [local simp] vfill_ne_nil sfill_ne_nil llfill_ne_nil vToEList_eq_nil vToEList_append'

section combine
variable (l l' : List Value) (x : ValNotVal) {i : Nat} (vh : ValidHoled i) (sh : SimpleValidHoled)
  (tf : FunctionType) (h : Hostfuncidx) (cvs : List Value) (lh : Llholed) (e : Expr)

private theorem c_ii : valNotValCombine (.immV l) (.val (.immV l')) = .val (.immV (l ++ l')) := rfl
private theorem c_it : valNotValCombine (.immV l) (.val .trapV) =
    if l = [] then .val .trapV else .notVal (vToEList l ++ [.trap]) := by
  cases l <;> rfl
private theorem c_ib : valNotValCombine (.immV l) (.val (.brV vh)) =
    .val (.brV (vhPushConst vh l)) := rfl
private theorem c_ir : valNotValCombine (.immV l) (.val (.retV sh)) =
    .val (.retV (shPushConst sh l)) := rfl
private theorem c_ic : valNotValCombine (.immV l) (.val (.callHostV tf h cvs lh)) =
    .val (.callHostV tf h cvs (llhPushConst lh l)) := rfl
private theorem c_in : valNotValCombine (.immV l) (.notVal e) = .notVal (vToEList l ++ e) := rfl
private theorem c_t : valNotValCombine .trapV x =
    if exprOfValNotVal x = [] then .val .trapV else .notVal (.trap :: exprOfValNotVal x) := by
  simp only [valNotValCombine]; split <;> simp_all
private theorem c_b : valNotValCombine (.brV vh) x =
    .val (.brV (vhAppend vh (exprOfValNotVal x))) := rfl
private theorem c_r : valNotValCombine (.retV sh) x =
    .val (.retV (shAppend sh (exprOfValNotVal x))) := rfl
private theorem c_c : valNotValCombine (.callHostV tf h cvs lh) x =
    .val (.callHostV tf h cvs (llhAppend lh (exprOfValNotVal x))) := rfl

private theorem m_nil : mergeValuesList [] = .val (.immV []) := rfl
private theorem m_val (v : Val) (vs : List ValNotVal) :
    mergeValuesList (.val v :: vs) = mergeValues v vs := rfl
private theorem m_notVal (vs : List ValNotVal) :
    mergeValuesList (.notVal e :: vs) = .notVal (e ++ (vs.map exprOfValNotVal).flatten) := rfl

end combine

attribute [local simp] m_nil m_val m_notVal c_ii c_it c_ib c_ir c_ic c_in c_t c_b c_r c_c
  exprOfValNotVal.eq_1 exprOfValNotVal.eq_2
  ofVal.eq_1 ofVal.eq_2 ofVal.eq_3 ofVal.eq_4 ofVal.eq_5

@[rocq_alias iriswasm.val_not_val_combine_app]
theorem val_not_val_combine_app (v1 : Val) (v2 : ValNotVal) :
    exprOfValNotVal (valNotValCombine v1 v2) = ofVal v1 ++ exprOfValNotVal v2 := by
  rcases v1 with l | _ | _ | _ | _ <;> rcases v2 with (_ | _ | _ | _ | _) | e <;>
    (try rcases l with _ | ⟨_, _⟩) <;> (try rcases e with _ | ⟨_, _⟩) <;> simp [vToEList] <;> split <;> simp_all

/-- If we write `valNotValCombine v1 v2` as `v1 + v2`, this is plain associativity
`v1 + (v2 + x) = (v1 + v2) + x`; typing makes the phrasing more complicated. -/
@[rocq_alias iriswasm.val_not_val_combine_assoc]
theorem val_not_val_combine_assoc (v1 v2 : Val) (x : ValNotVal) :
    valNotValCombine v1 (valNotValCombine v2 x) =
      match valNotValCombine v1 (.val v2) with
      | .val v3 => valNotValCombine v3 x
      | .notVal es => .notVal (es ++ exprOfValNotVal x) := by
  rcases v1 with l1 | _ | _ | _ | _ <;> rcases v2 with l2 | _ | _ | _ | _ <;>
    rcases x with (l0 | _ | _ | _ | _) | e0 <;>
    (try rcases l1 with _ | ⟨_, _⟩) <;> (try rcases l2 with _ | ⟨_, _⟩) <;>
    (try rcases l0 with _ | ⟨_, _⟩) <;> (try rcases e0 with _ | ⟨_, _⟩) <;> simp [vToEList]

@[rocq_alias iriswasm.merge_br]
theorem merge_br {i : Nat} (vh : ValidHoled i) (es : List ValNotVal) :
    mergeValues (.brV vh) es = .val (.brV (vhAppend vh (es.map exprOfValNotVal).flatten)) := by
  induction es generalizing vh with
  | nil => simp [mergeValues]
  | cons a es ih => simp [mergeValues, valNotValCombine, ih]

@[rocq_alias iriswasm.merge_return]
theorem merge_return (sh : SimpleValidHoled) (es : List ValNotVal) :
    mergeValues (.retV sh) es = .val (.retV (shAppend sh (es.map exprOfValNotVal).flatten)) := by
  induction es generalizing sh with
  | nil => simp [mergeValues]
  | cons a es ih => simp [mergeValues, valNotValCombine, ih]

@[rocq_alias iriswasm.merge_call_host]
theorem merge_call_host (tf : FunctionType) (h : Hostfuncidx) (cvs : List Value) (sh : Llholed)
    (es : List ValNotVal) :
    mergeValues (.callHostV tf h cvs sh) es =
      .val (.callHostV tf h cvs (llhAppend sh (es.map exprOfValNotVal).flatten)) := by
  induction es generalizing sh with
  | nil => simp [mergeValues]
  | cons a es ih => simp [mergeValues, valNotValCombine, ih]

@[rocq_alias iriswasm.merge_trap]
theorem merge_trap (es : List ValNotVal) :
    mergeValues .trapV es = valNotValCombine .trapV (.notVal (es.map exprOfValNotVal).flatten) := by
  induction es with
  | nil => rfl
  | cons a es ih =>
    by_cases ha : exprOfValNotVal a = [] <;> simp [mergeValues, ha, ih]

/-- Two identities that have to be proven mutually. -/
@[rocq_alias iriswasm.merge_prepend_flatten]
theorem merge_prepend_flatten (vs : List ValNotVal) :
    (∀ v0, mergeValues v0 vs = valNotValCombine v0 (mergeValuesList vs)) ∧
      (vs.map exprOfValNotVal).flatten = exprOfValNotVal (mergeValuesList vs) := by
  induction vs with
  | nil =>
    refine ⟨fun v0 => ?_, rfl⟩
    rcases v0 with _ | _ | _ | _ | _ <;> simp [mergeValues, mergeValuesList, vToEList]
  | cons a vs ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rcases a with v | e
    · simp only [m_val, ih1]
      refine ⟨fun v0 => ?_, ?_⟩
      · rw [val_not_val_combine_assoc, mergeValues]
        split <;> simp [ih1, ih2]
      · rw [val_not_val_combine_app]; simp [ih2]
    · refine ⟨fun v0 => ?_, by simp⟩
      simp only [m_notVal]
      rcases v0 with l | _ | _ | _ | _
      · simp [mergeValues]
      · by_cases he : e = [] <;> simp [mergeValues, he, merge_trap]
      · simp [mergeValues, merge_br]
      · simp [mergeValues, merge_return]
      · simp [mergeValues, merge_call_host]

@[rocq_alias iriswasm.merge_prepend]
theorem merge_prepend (v0 : Val) (vs : List ValNotVal) :
    mergeValues v0 vs = valNotValCombine v0 (mergeValuesList vs) :=
  (merge_prepend_flatten vs).1 v0

@[rocq_alias iriswasm.merge_flatten]
theorem merge_flatten (vs : List ValNotVal) :
    (vs.map exprOfValNotVal).flatten = exprOfValNotVal (mergeValuesList vs) :=
  (merge_prepend_flatten vs).2

private theorem flatten_of_forall (es : Expr)
    (h : ∀ e ∈ es, exprOfValNotVal (toValInstr e) = [e]) :
    ((es.map toValInstr).map exprOfValNotVal).flatten = es := by
  induction es with
  | nil => rfl
  | cons a es ih =>
    simp only [List.map_cons, List.flatten_cons, h a (by simp)]
    rw [ih fun e he => h e (by simp [he])]; rfl

@[rocq_alias iriswasm.of_to_val_instr]
theorem of_to_val_instr (e : AdministrativeInstruction) : exprOfValNotVal (toValInstr e) = [e] := by
  match e with
  | .label n labe es =>
    have hm : exprOfValNotVal (mergeValuesList (es.map toValInstr)) = es := by
      rw [← merge_flatten, flatten_of_forall es fun e _ => of_to_val_instr e]
    rw [toValInstr]
    rcases h : mergeValuesList (es.map toValInstr) with (_ | _ | @⟨k, vh⟩ | _ | _) | _ <;>
      simp only [h, exprOfValNotVal.eq_1, ofVal] at hm ⊢
    case val.brV =>
      rcases hd : vhDecrease (.rec_ [] n labe vh []) with _ | vh'
      · rfl
      · rw [exprOfValNotVal.eq_1, ofVal, ← vfill_decrease _ _ _ hd]; simp [vfill, hm]
    all_goals first | rfl | simp [sfill, llfill, hm]
  | .local n f es =>
    have hm : exprOfValNotVal (mergeValuesList (es.map toValInstr)) = es := by
      rw [← merge_flatten, flatten_of_forall es fun e _ => of_to_val_instr e]
    rw [toValInstr]
    rcases h : mergeValuesList (es.map toValInstr) with (_ | _ | _ | _ | _) | _ <;>
      simp only [h, exprOfValNotVal.eq_1, ofVal] at hm ⊢
    all_goals first | rfl | simp [llfill, hm]
  | .basic b => cases b <;> simp [toValInstr, vToEList, vfill, sfill]
  | .trap | .invoke _ | .callHost _ _ _ => simp [toValInstr, llfill]
termination_by sizeOf e

@[rocq_alias iriswasm.flatten_simplify]
theorem flatten_simplify (es : Expr) : ((es.map toValInstr).map exprOfValNotVal).flatten = es := by
  induction es with
  | nil => rfl
  | cons a es ih => simp only [List.map_cons, List.flatten_cons, of_to_val_instr]; rw [ih]; rfl

@[rocq_alias iriswasm.merge_to_val]
theorem merge_to_val (es : Expr) : exprOfValNotVal (mergeValuesList (es.map toValInstr)) = es := by
  rw [← merge_flatten, flatten_simplify]

@[rocq_alias iriswasm.of_to_val]
theorem of_to_val (es : Expr) (v : Val) : toVal es = some v → ofVal v = es := by
  have h := merge_to_val es
  unfold toVal
  split <;> simp_all [exprOfValNotVal]
  rintro rfl; exact h

@[rocq_alias iriswasm.merge_app]
theorem merge_app (vs1 vs2 : List ValNotVal) :
    mergeValuesList (vs1 ++ vs2) =
      match mergeValuesList vs1 with
      | .val v1 => valNotValCombine v1 (mergeValuesList vs2)
      | .notVal e1 => .notVal (e1 ++ exprOfValNotVal (mergeValuesList vs2)) := by
  induction vs1 with
  | nil =>
    simp only [List.nil_append, m_nil]
    rcases mergeValuesList vs2 with (_ | _ | _ | _ | _) | _ <;> simp [vToEList]
  | cons a vs1 ih =>
    rcases a with v | e
    · simp only [List.cons_append, m_val, merge_prepend, ih]
      rcases h : mergeValuesList vs1 with v1 | e1
      · simp only [val_not_val_combine_assoc]
      · rcases v with l | _ | _ | _ | _
        · simp
        · by_cases he : e1 = [] <;> simp [he]
        all_goals simp
    · simp [merge_flatten]

private theorem toVal_eq_some {e : Expr} {v : Val} :
    toVal e = some v ↔ mergeValuesList (e.map toValInstr) = .val v := by
  unfold toVal; split <;> simp_all

private theorem toVal_eq_none {e : Expr} :
    toVal e = none ↔ mergeValuesList (e.map toValInstr) = .notVal e := by
  have := merge_to_val e
  unfold toVal
  rcases h : mergeValuesList (e.map toValInstr) with v | e' <;> simp_all

private theorem toVal_of_notVal {e : Expr} (h : ∀ v, mergeValuesList (e.map toValInstr) ≠ .val v) :
    toVal e = none := by
  unfold toVal; split <;> simp_all

private theorem merge_cons_val {a : AdministrativeInstruction} {v : Val} (es : Expr)
    (h : toValInstr a = .val v) :
    mergeValuesList ((a :: es).map toValInstr) =
      valNotValCombine v (mergeValuesList (es.map toValInstr)) := by
  rw [List.map_cons, h, m_val, merge_prepend]

private theorem merge_vToEList (l : List Value) :
    mergeValuesList ((vToEList l).map toValInstr) = .val (.immV l) := by
  induction l with
  | nil => rfl
  | cons v l ih =>
    exact (merge_cons_val (vToEList l) (by rw [toValInstr])).trans (by rw [ih]; simp)

private theorem merge_vToEList_app (l : List Value) (es : Expr) :
    mergeValuesList ((vToEList l ++ es).map toValInstr) =
      valNotValCombine (.immV l) (mergeValuesList (es.map toValInstr)) := by
  rw [List.map_append, merge_app, merge_vToEList]

private theorem vhIncreaseRepeat_base {m : Nat} (bef : List Value) (aft : Expr) (j : Nat) :
    vhIncreaseRepeat (ValidHoled.base (n := m) bef aft) j = .base bef aft := by
  induction j with
  | zero => rfl
  | succ j ih => simp [vhIncreaseRepeat, ih, vhIncrease]

private theorem brV_cast {a b : Nat} (h : a = b) (x : ValidHoled a) :
    Val.brV (h ▸ x) = Val.brV x := by
  subst h; rfl

@[rocq_alias iriswasm.to_of_val]
theorem to_of_val (v : Val) : toVal (ofVal v) = some v := by
  rw [toVal_eq_some]
  rcases v with l | _ | @⟨i, vh⟩ | sh | ⟨tf, h, cvs, lh⟩
  · exact merge_vToEList l
  · simp [toValInstr, mergeValues]
  · -- Coq indexes `vh_increase_repeat vh j` by `j + i`; Lean's is `i + j`, so `br (i + j)`.
    have H : ∀ i (vh : ValidHoled i) j,
        mergeValuesList ((vfill vh [.basic (.br (i + j))]).map toValInstr) =
          .val (.brV (vhIncreaseRepeat vh j)) := by
      intro i vh
      induction vh with
      | base bef aft =>
        intro j
        rw [vhIncreaseRepeat_base, vfill, List.append_assoc, List.singleton_append,
          merge_vToEList_app, merge_cons_val _ (by rw [toValInstr])]
        simp [merge_to_val, vhPushConst, vhAppend]
      | @rec_ m bef n es vh aft ih =>
        intro j
        have hj : m + 1 + j = m + (j + 1) := by omega
        rw [vh_increase_repeat_rec, brV_cast, vfill, hj, merge_vToEList_app]
        rw [merge_cons_val (v := .brV (.rec_ [] n es (vhIncreaseRepeat vh j) [])) _
          (by
            rw [toValInstr, ih (j + 1)]
            simp [vhIncreaseRepeat, vhDecrease, vh_decrease_increase])]
        simp [merge_to_val, vhPushConst, vhAppend]
    exact H i vh 0
  · induction sh with
    | base bef aft =>
      rw [ofVal, sfill, List.append_assoc, List.singleton_append, merge_vToEList_app,
        merge_cons_val _ (by rw [toValInstr])]
      simp [merge_to_val, shPushConst, shAppend]
    | rec_ bef n es sh aft ih =>
      rw [ofVal] at ih
      rw [ofVal, sfill, merge_vToEList_app,
        merge_cons_val (v := .retV (.rec_ [] n es sh [])) _ (by rw [toValInstr, ih])]
      simp [merge_to_val, shPushConst, shAppend]
  · induction lh with
    | base bef aft =>
      rw [ofVal, llfill, List.append_assoc, List.singleton_append, merge_vToEList_app,
        merge_cons_val _ (by rw [toValInstr])]
      simp [merge_to_val, llhPushConst, llhAppend]
    | label bef n es lh aft ih =>
      rw [ofVal] at ih
      rw [ofVal, llfill, merge_vToEList_app,
        merge_cons_val (v := .callHostV tf h cvs (.label [] n es lh [])) _ (by rw [toValInstr, ih])]
      simp [merge_to_val, llhPushConst, llhAppend]
    | «local» bef n f lh aft ih =>
      rw [ofVal] at ih
      rw [ofVal, llfill, merge_vToEList_app,
        merge_cons_val (v := .callHostV tf h cvs (.local [] n f lh [])) _ (by rw [toValInstr, ih])]
      simp [merge_to_val, llhPushConst, llhAppend]

@[rocq_alias iriswasm.to_val_cons_is_none_or_cons]
theorem to_val_cons_is_none_or_cons (e0 : AdministrativeInstruction) (e : Expr) (r : Option Val) :
    toVal (e0 :: e) = r →
      isNoneOr (fun l => match l with | .immV v => v != [] | _ => true) r = true := by
  rintro rfl
  rcases h : toVal (e0 :: e) with _ | v
  · rfl
  · have := of_to_val _ _ h
    rcases v with l | _ | _ | _ | _ <;> simp [isNoneOr]
    rintro rfl; simp [ofVal, vToEList] at this

@[rocq_alias iriswasm.to_val_trap_is_singleton]
theorem to_val_trap_is_singleton (e : Expr) : toVal e = some .trapV → e = [.trap] := by
  intro h; simpa [ofVal] using (of_to_val e _ h).symm

@[rocq_alias iriswasm.flatten_map_expr_of_val_not_val]
theorem flatten_map_expr_of_val_not_val (vs : List ValNotVal) :
    (vs.map exprOfValNotVal).flatten = exprOfValNotVal (mergeValuesList vs) :=
  merge_flatten vs

@[rocq_alias iriswasm.to_val_is_immV]
theorem to_val_is_immV (es : Expr) (vs : List Value) :
    toVal es = some (.immV vs) → es = vs.map fun x => .basic (.const x) := by
  intro h; simpa [ofVal, vToEList] using (of_to_val es _ h).symm

@[rocq_alias iriswasm.merge_is_not_val]
theorem merge_is_not_val (es es' : Expr) :
    mergeValuesList (es.map toValInstr) = .notVal es' → es = es' := by
  intro h; have := merge_to_val es; rw [h] at this; exact this.symm

@[rocq_alias iriswasm.extend_retV]
theorem extend_retV (sh : SimpleValidHoled) (es : Expr) :
    toVal (ofVal (.retV sh) ++ es) = some (.retV (shAppend sh es)) := by
  rw [toVal_eq_some, List.map_append, merge_app, toVal_eq_some.1 (to_of_val _)]
  simp [merge_to_val]

@[rocq_alias iriswasm.splits_vals_e_to_val_hd]
theorem splits_vals_e_to_val_hd (e1 : Expr) (e : AdministrativeInstruction) (es : Expr)
    (vs : List Value) :
    splitValsE e1 = (vs, e :: es) →
      toVal e1 = none ∨
      (vs = [] ∧ toVal e1 = some .trapV) ∨
      (∃ i, e = .basic (.br i) ∧ toVal e1 = some (.brV (ValidHoled.base (n := i) vs es))) ∨
      (e = .basic .return_ ∧ toVal e1 = some (.retV (.base vs es))) ∨
      (∃ tf h vcs, e = .callHost tf h vcs ∧ toVal e1 = some (.callHostV tf h vcs (.base vs es))) ∨
      (∃ i n es' LI, ∃ vh : ValidHoled i,
        e = .label n es' LI ∧ toVal e1 = some (.brV (.rec_ vs n es' vh es)) ∧
        vfill vh [.basic (.br (i + 1))] = LI) ∨
      (∃ n es' LI sh, e = .label n es' LI ∧ toVal e1 = some (.retV (.rec_ vs n es' sh es)) ∧
        sfill sh [.basic .return_] = LI) ∨
      (∃ tf h vcs n es' LI sh, e = .label n es' LI ∧
        toVal e1 = some (.callHostV tf h vcs (.label vs n es' sh es)) ∧
        llfill sh [.callHost tf h vcs] = LI) ∨
      (∃ tf h vcs n f LI sh, e = .local n f LI ∧
        toVal e1 = some (.callHostV tf h vcs (.local vs n f sh es)) ∧
        llfill sh [.callHost tf h vcs] = LI) := by
  intro hs
  have hnc := split_vals_e_not_const e1 vs e es hs
  obtain rfl := split_vals_e_v_to_e_duality hs
  have key := merge_vToEList_app vs (e :: es)
  -- every non-value head instruction leaves a `.notVal`
  have hnv : toValInstr e = .notVal [e] → toVal (vToEList vs ++ e :: es) = none := fun h =>
    toVal_of_notVal (fun _ => by rw [key, List.map_cons, h]; simp)
  rcases e with b | _ | _ | ⟨n, es', LI⟩ | ⟨n, f, LI⟩ | ⟨tf, h, cvs⟩
  · cases b
    case br i =>
      refine .inr (.inr (.inl ⟨i, rfl, ?_⟩))
      rw [toVal_eq_some, key, merge_cons_val _ (by rw [toValInstr])]
      simp [merge_to_val, vhPushConst, vhAppend]
    case return_ =>
      refine .inr (.inr (.inr (.inl ⟨rfl, ?_⟩)))
      rw [toVal_eq_some, key, merge_cons_val _ (by rw [toValInstr])]
      simp [merge_to_val, shPushConst, shAppend]
    case const => simp [isConst] at hnc
    all_goals exact .inl (hnv (by simp [toValInstr]))
  · rw [merge_cons_val _ (by rw [toValInstr])] at key
    rcases es with _ | ⟨a, es⟩
    · rcases vs with _ | ⟨v, vs⟩
      · exact .inr (.inl ⟨rfl, toVal_eq_some.2 (by rw [key]; simp)⟩)
      · exact .inl (toVal_of_notVal (fun _ => by rw [key]; simp))
    · exact .inl (toVal_of_notVal (fun _ => by rw [key]; simp only [c_t, merge_to_val]; simp))
  · exact .inl (hnv (by simp [toValInstr]))
  · rcases hm : mergeValuesList (LI.map toValInstr) with
      (_ | _ | @⟨k, vh⟩ | sh | ⟨tf, h, cvs, lh⟩) | _
    case val.brV =>
      have hLI := of_to_val LI _ (toVal_eq_some.2 hm)
      cases k with
      | zero => exact .inl (hnv (by rw [toValInstr, hm]; rfl))
      | succ k =>
        rcases hd : vhDecrease vh with _ | vh''
        · exact .inl (hnv (by rw [toValInstr, hm]; simp [vhDecrease, hd]))
        · refine .inr (.inr (.inr (.inr (.inr (.inl ⟨k, n, es', LI, vh'', rfl, ?_, ?_⟩)))))
          · rw [toVal_eq_some, key, merge_cons_val (v := .brV (.rec_ [] n es' vh'' [])) _
              (by rw [toValInstr, hm]; simp [vhDecrease, hd])]
            simp [merge_to_val, vhPushConst, vhAppend]
          · rw [← vfill_decrease _ _ _ hd]; exact hLI
    case val.retV =>
      refine .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨n, es', LI, sh, rfl, ?_, ?_⟩))))))
      · rw [toVal_eq_some, key, merge_cons_val (v := .retV (.rec_ [] n es' sh [])) _
          (by rw [toValInstr, hm])]
        simp [merge_to_val, shPushConst, shAppend]
      · exact of_to_val LI _ (toVal_eq_some.2 hm)
    case val.callHostV =>
      refine .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
        ⟨tf, h, cvs, n, es', LI, lh, rfl, ?_, ?_⟩)))))))
      · rw [toVal_eq_some, key, merge_cons_val (v := .callHostV tf h cvs (.label [] n es' lh [])) _
          (by rw [toValInstr, hm])]
        simp [merge_to_val, llhPushConst, llhAppend]
      · exact of_to_val LI _ (toVal_eq_some.2 hm)
    all_goals exact .inl (hnv (by rw [toValInstr, hm]))
  · rcases hm : mergeValuesList (LI.map toValInstr) with (_ | _ | _ | _ | ⟨tf, h, cvs, lh⟩) | _
    case val.callHostV =>
      refine .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
        ⟨tf, h, cvs, n, f, LI, lh, rfl, ?_, ?_⟩)))))))
      · rw [toVal_eq_some, key, merge_cons_val (v := .callHostV tf h cvs (.local [] n f lh [])) _
          (by rw [toValInstr, hm])]
        simp [merge_to_val, llhPushConst, llhAppend]
      · exact of_to_val LI _ (toVal_eq_some.2 hm)
    all_goals exact .inl (hnv (by rw [toValInstr, hm]))
  · refine .inr (.inr (.inr (.inr (.inl ⟨tf, h, cvs, rfl, ?_⟩))))
    rw [toVal_eq_some, key, merge_cons_val _ (by rw [toValInstr])]
    simp [merge_to_val, llhPushConst, llhAppend]

@[rocq_alias iriswasm.to_val_None_append]
theorem to_val_None_append (es1 es2 : Expr) : toVal es1 = none → toVal (es1 ++ es2) = none := by
  intro h; apply toVal_of_notVal; intro v; rw [List.map_append, merge_app, toVal_eq_none.1 h]
  simp

@[rocq_alias iriswasm.to_val_None_prepend]
theorem to_val_None_prepend (es1 es2 : Expr) :
    toVal es2 = none →
      toVal (es1 ++ es2) = none ∨
      (∃ i, ∃ vh : ValidHoled i, toVal es1 = some (.brV vh)) ∨
      (∃ sh, toVal es1 = some (.retV sh)) ∨
      (∃ tf h cvs sh, toVal es1 = some (.callHostV tf h cvs sh)) := by
  intro h2
  have h2' := toVal_eq_none.1 h2
  rcases h1 : toVal es1 with _ | v
  · exact .inl (to_val_None_append _ _ h1)
  · have hm := toVal_eq_some.1 h1
    rcases v with l | _ | @⟨i, vh⟩ | sh | ⟨tf, h, cvs, lh⟩
    · left; apply toVal_of_notVal; intro v; rw [List.map_append, merge_app, hm, h2']; simp
    · have hne : es2 ≠ [] := by rintro rfl; simp [toVal, mergeValuesList] at h2
      left; apply toVal_of_notVal; intro v; rw [List.map_append, merge_app, hm, h2']; simp [hne]
    · exact .inr (.inl ⟨i, vh, rfl⟩)
    · exact .inr (.inr (.inl ⟨sh, rfl⟩))
    · exact .inr (.inr (.inr ⟨tf, h, cvs, lh, rfl⟩))

@[rocq_alias iriswasm.to_val_None_prepend_const]
theorem to_val_None_prepend_const (es1 es2 : Expr) :
    constList es1 = true → toVal es2 = none → toVal (es1 ++ es2) = none := by
  intro hc h2
  obtain ⟨vs, rfl⟩ := const_es_exists hc
  apply toVal_of_notVal; intro v; rw [merge_vToEList_app, toVal_eq_none.1 h2]; simp

@[rocq_alias iriswasm.to_val_not_trap_interweave]
theorem to_val_not_trap_interweave (es es' : Expr) :
    constList es = true → es ≠ [] ∨ es' ≠ [] → toVal (es ++ [.trap] ++ es') = none := by
  intro hc hne
  obtain ⟨vs, rfl⟩ := const_es_exists hc
  apply toVal_of_notVal; intro v
  rw [List.append_assoc, merge_vToEList_app, List.singleton_append,
    merge_cons_val _ (by rw [toValInstr])]
  rcases es' with _ | ⟨a, es'⟩
  · have : vs ≠ [] := by simpa [vToEList] using hne
    simp [this]
  · simp only [c_t, merge_to_val]; simp

@[rocq_alias iriswasm.const_list_to_val]
theorem const_list_to_val (es : Expr) : constList es = true → ∃ vs, toVal es = some (.immV vs) := by
  intro hc
  obtain ⟨vs, rfl⟩ := const_es_exists hc
  exact ⟨vs, to_of_val (.immV vs)⟩

@[rocq_alias iriswasm.to_val_const_list]
theorem to_val_const_list (es : Expr) (vs : List Value) :
    toVal es = some (.immV vs) → constList es = true := by
  intro h; rw [to_val_is_immV es vs h]; simp [constList, isConst]

private theorem toVal_label_none {n : Nat} {es0 LI : Expr}
    (hbr : ∀ k (vh : ValidHoled k) vh', vhDecrease (.rec_ [] n es0 vh []) = some vh' →
      toVal LI ≠ some (.brV vh))
    (hret : ∀ sh, toVal LI ≠ some (.retV sh))
    (hch : ∀ tf h cvs lh, toVal LI ≠ some (.callHostV tf h cvs lh)) :
    toVal [.label n es0 LI] = none := by
  apply toVal_of_notVal; intro v
  rw [List.map_cons, List.map_nil, toValInstr]
  rcases hm : mergeValuesList (LI.map toValInstr) with
    (_ | _ | @⟨k, vh⟩ | sh | ⟨tf, h, cvs, lh⟩) | _
  case val.brV =>
    rcases hd : vhDecrease (.rec_ [] n es0 vh []) with _ | vh'
    · simp [hd]
    · exact absurd (toVal_eq_some.2 hm) (hbr k vh vh' hd)
  case val.retV => exact absurd (toVal_eq_some.2 hm) (hret sh)
  case val.callHostV => exact absurd (toVal_eq_some.2 hm) (hch _ _ _ _)
  all_goals simp

private theorem toVal_local_none {n : Nat} {f : Frame} {LI : Expr}
    (hch : ∀ tf h cvs lh, toVal LI ≠ some (.callHostV tf h cvs lh)) :
    toVal [.local n f LI] = none := by
  apply toVal_of_notVal; intro v
  rw [List.map_cons, List.map_nil, toValInstr]
  rcases hm : mergeValuesList (LI.map toValInstr) with (_ | _ | _ | _ | ⟨tf, h, cvs, lh⟩) | _
  case val.callHostV => exact absurd (toVal_eq_some.2 hm) (hch _ _ _ _)
  all_goals simp

@[rocq_alias iriswasm.val_head_stuck_reduce]
theorem val_head_stuck_reduce {s1 : StoreRecord} {f1 : Frame} {e1 : Expr} {s2 : StoreRecord}
    {f2 : Frame} {e2 : Expr} : Reduce s1 f1 e1 s2 f2 e2 → toVal e1 = none := by
  intro h
  induction h with
  | simple hs =>
    cases hs with
    | labelConst hc =>
      obtain ⟨vs, hv⟩ := const_list_to_val _ hc
      exact toVal_label_none (by simp [hv]) (by simp [hv]) (by simp [hv])
    | labelTrap =>
      have hv : toVal [.trap] = some .trapV := to_of_val .trapV
      exact toVal_label_none (by simp [hv]) (by simp [hv]) (by simp [hv])
    | br i lh hc _ hfill =>
      refine toVal_label_none (fun k vh vh' hd hv => ?_) (fun sh hv => ?_)
        (fun tf h cvs lh' hv => ?_)
      · have hLI := of_to_val _ _ hv
        cases k with
        | zero => simp [vhDecrease] at hd
        | succ k =>
          simp only [vhDecrease, Option.map_eq_some_iff] at hd
          obtain ⟨vh'', hd'', -⟩ := hd
          rw [ofVal, vfill_decrease _ _ _ hd''] at hLI
          obtain ⟨hk, hf⟩ := vfill_to_lfilled vh'' [.basic (.br (k + 1))]
          rw [hLI, ← List.nil_append [_]] at hf
          obtain ⟨he, hi, -⟩ := lfilled_first_values hfill hf hc rfl rfl rfl
            (by simp) (by simp)
          simp only [AdministrativeInstruction.basic.injEq, BasicInstruction.br.injEq] at he
          have he' : (i : Nat) = k + 1 := he
          omega
      · have hLI := of_to_val _ _ hv
        have hf := sfill_to_lfilled sh [.basic .return_]
        rw [ofVal] at hLI
        rw [hLI, ← List.nil_append [_]] at hf
        obtain ⟨he, -, -⟩ := lfilled_first_values hfill hf hc rfl rfl rfl (by simp) (by simp)
        simp at he
      · have hLI := of_to_val _ _ hv
        rw [ofVal, ← List.nil_append [_]] at hLI
        obtain ⟨he, -⟩ := lfilled_llfill_first_values hfill hLI hc rfl rfl rfl (by simp)
          (by simp) (by simp)
        simp at he
    | localConst hc _ =>
      obtain ⟨vs, hv⟩ := const_list_to_val _ hc
      exact toVal_local_none (by simp [hv])
    | localTrap =>
      have hv : toVal [.trap] = some .trapV := to_of_val .trapV
      exact toVal_local_none (by simp [hv])
    | return_ i lh hc _ hfill =>
      refine toVal_local_none (fun tf h cvs lh' hv => ?_)
      have hLI := of_to_val _ _ hv
      rw [ofVal, ← List.nil_append [_]] at hLI
      obtain ⟨he, -⟩ := lfilled_llfill_first_values hfill hLI hc rfl rfl rfl (by simp)
        (by simp) (by simp)
      simp at he
    | @teeLocal _ v hv =>
      rcases v with b | _ | _ | _ | _ | _ <;> simp [isConst] at hv
      cases b <;> simp at hv
      simp [toVal, toValInstr, mergeValues]
    | trap lh hne hfill =>
      rw [lfilled_Ind_Equivalent] at hfill
      cases hfill with
      | lfilledBase bef _ aft hc =>
        refine to_val_not_trap_interweave bef aft hc ?_
        cases bef <;> cases aft <;> simp_all
    | _ => simp [toVal, toValInstr, mergeValues]
  | block _ hc _ | loop _ hc _ =>
    exact to_val_None_prepend_const _ _ hc (by simp [toVal, toValInstr])
  | invokeNative _ _ _ _ _ _ _ _ _ _ hves =>
    subst hves
    exact to_val_None_prepend_const _ _ (v_to_e_is_const_list _) (by simp [toVal, toValInstr])
  | invokeHost _ _ _ _ _ hves =>
    subst hves
    exact to_val_None_prepend_const _ _ (v_to_e_is_const_list _) (by simp [toVal, toValInstr])
  | label es es' k lh hred hfill _ ih =>
    rw [lfilled_Ind_Equivalent] at hfill
    cases hfill with
    | lfilledBase bef _ aft hc =>
      rw [List.append_assoc]
      exact to_val_None_prepend_const _ _ hc (to_val_None_append _ _ ih)
    | lfilledRec k bef n es0 lh0 aft _ LI hc hLI =>
      have hLI' := (lfilled_Ind_Equivalent _ _ _ _).2 hLI
      rw [List.append_assoc]
      refine to_val_None_prepend_const _ _ hc (to_val_None_append _ _ ?_)
      refine toVal_label_none (fun j vh _ _ hv => ?_) (fun sh hv => ?_)
        (fun tf h cvs lh' hv => ?_)
      · have hLI2 : vfill vh [.basic (.br j)] = LI := of_to_val _ _ hv
        obtain ⟨hk, hf⟩ := vfill_to_lfilled vh [.basic (.br j)]
        rw [hLI2, ← List.nil_append [_]] at hf
        exact lfilled_br_and_reduce hred rfl hk hf hLI'
      · have hLI2 := of_to_val _ _ hv
        have hf := sfill_to_lfilled sh [.basic .return_]
        rw [ofVal] at hLI2
        rw [hLI2, ← List.nil_append [_]] at hf
        exact lfilled_return_and_reduce hred rfl hf hLI'
      · have hLI2 := of_to_val _ _ hv
        rw [ofVal, ← List.nil_append [_]] at hLI2
        exact llfill_call_host_and_reduce hred rfl hLI2 (lfilled_implies_llfill hLI').choose_spec
  | «local» _ ih =>
    exact toVal_local_none (by simp [ih])
  | _ => simp [toVal, toValInstr, mergeValues]

@[rocq_alias iriswasm.val_head_stuck]
theorem val_head_stuck (e1 : Expr) (s1 : State) (κ : List Observation) (e2 : Expr) (s2 : State)
    (efs : List Expr) : primStep (e1, s1) κ (e2, s2, efs) → toVal e1 = none := by
  obtain ⟨_, _, _⟩ := s1; obtain ⟨_, _, _⟩ := s2
  exact fun h => val_head_stuck_reduce h.1

/-- Coq's `wasm_mixin : LanguageMixin of_val to_val prim_step` and the canonical structure
`wasm_lang` are this instance. -/
@[rocq_alias iriswasm.wasm_mixin, rocq_alias iriswasm.wasm_lang]
instance wasmLanguage : Language Expr State Observation Val where
  toVal := toVal
  ofVal := ofVal
  coe_of_toVal_eq_some := of_to_val _ _
  toVal_coe := to_of_val
  primStep := primStep
  val_stuck := val_head_stuck _ _ _ _ _ _

end IrisWasm
