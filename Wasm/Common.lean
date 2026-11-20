/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import Iris.Std.RocqPorting

/-! Port of `theories/common.v`. -/

#rocq_ignore iriswasm.nat_eqP "Lean DecidableEq Nat"
#rocq_ignore iriswasm.nat_eqMixin "Lean DecidableEq Nat"
#rocq_ignore iriswasm.nat_eqType "Lean DecidableEq Nat"
#rocq_ignore iriswasm.Z_eqP "Lean DecidableEq Int"
#rocq_ignore iriswasm.Z_eqMixin "Lean DecidableEq Int"
#rocq_ignore iriswasm.Pos_eqP "positive maps to Nat"
#rocq_ignore iriswasm.Pos_eqMixin "positive maps to Nat"
#rocq_ignore iriswasm.eq_dec_Equality_axiom "eqType machinery; deriving DecidableEq"
#rocq_ignore iriswasm.Equality_axiom_eq_dec "eqType machinery; deriving DecidableEq"
#rocq_ignore iriswasm.BoolSpec_reflect "reflect machinery; unused"
#rocq_ignore iriswasm.reflect_BoolSpec "reflect machinery; unused"
#rocq_ignore iriswasm.gtb_spec0 "reflect machinery; Int decide"
#rocq_ignore iriswasm.geb_spec0 "reflect machinery; Int decide"
#rocq_ignore iriswasm.curry "unused"
#rocq_ignore iriswasm.uncurry "unused"
#rocq_ignore iriswasm.curry_uncurry "unused"
#rocq_ignore iriswasm.uncurry_curry "unused"
#rocq_ignore iriswasm.List_In_in_mem "eqType mem; Lean List.Mem is used directly"
#rocq_ignore iriswasm.inP "eqType mem; Lean List.Mem is used directly"
#rocq_ignore iriswasm.filter_notin "unused"
#rocq_ignore iriswasm.filter_out_zlt "CompCert numerics proof helper; BitVec replaces it"
#rocq_ignore iriswasm.filter_for_all "CompCert numerics proof helper; BitVec replaces it"
#rocq_ignore iriswasm.list_all_forall "CompCert numerics proof helper; BitVec replaces it"
#rocq_ignore iriswasm.filter_none "CompCert numerics proof helper; BitVec replaces it"
#rocq_ignore iriswasm.filter_and "CompCert numerics proof helper; BitVec replaces it"
#rocq_ignore iriswasm.split3 "unused"
#rocq_ignore iriswasm.rev_move "unused"
#rocq_ignore iriswasm.rev0 "unused"
#rocq_ignore iriswasm.nil_rcons "unused"
#rocq_ignore iriswasm.last_error_rcons "unused"
#rocq_ignore iriswasm.rcons_last_error "unused"
#rocq_ignore iriswasm.last_error_nil "unused"
#rocq_ignore iriswasm.last_error_last "unused"
#rocq_ignore iriswasm.all2_eq "unused"
#rocq_ignore iriswasm.map_all2 "unused"
#rocq_ignore iriswasm.cat0_inv "unused; core List.append_eq_nil_iff"
#rocq_ignore iriswasm.maxn_nat_max "ssreflect maxn is Nat.max"
#rocq_ignore iriswasm.maxn_congruence_l "unused"
#rocq_ignore iriswasm.maxn_congruence_r "unused"
#rocq_ignore iriswasm.TProp.sum "unused"
#rocq_ignore iriswasm.TProp.map "unused"
#rocq_ignore iriswasm.TProp.from_list "unused"
#rocq_ignore iriswasm.TProp.Concat "unused"
#rocq_ignore iriswasm.TProp.Forall_forall "unused"
#rocq_ignore iriswasm.TProp.forall_Forall "unused"
#rocq_ignore iriswasm.TProp.Forall_List_Forall "unused"
#rocq_ignore iriswasm.TProp.List_Forall_Forall "unused"
#rocq_ignore iriswasm.TProp.Forall_cat "unused"
#rocq_ignore iriswasm.TProp.Forall_catrev "unused"
#rocq_ignore iriswasm.TProp.Forall_rev "unused"
#rocq_ignore iriswasm.TProp.sum_to_list "unused"
#rocq_ignore iriswasm.TProp.to_list_size "unused"
#rocq_ignore iriswasm.TProp.Forall_forall_eq_dec "unused; deriving DecidableEq"
#rocq_ignore iriswasm.list_search_prefix_pickable "pickability replaced by classical Decidable"
#rocq_ignore iriswasm.list_search_suffix_pickable "pickability replaced by classical Decidable"
#rocq_ignore iriswasm.list_split_pickable2_gen "pickability replaced by classical Decidable"
#rocq_ignore iriswasm.list_split_pickable2 "pickability replaced by classical Decidable"
#rocq_ignore iriswasm.list_search_split_pickable2 "pickability replaced by classical Decidable"
#rocq_ignore iriswasm.list_split_pickable3_gen "pickability replaced by classical Decidable"
#rocq_ignore iriswasm.list_split_pickable3 "pickability replaced by classical Decidable"

namespace Wasm

/-- ssreflect `all2`: `false` on length mismatch. -/
def List.all2 {A B : Type} (f : A → B → Bool) : List A → List B → Bool
  | [], [] => true
  | a :: as, b :: bs => f a b && all2 f as bs
  | _, _ => false

/-- Coq `Forall2`. -/
inductive List.Forall₂ {A B : Type} (R : A → B → Prop) : List A → List B → Prop
  | nil : Forall₂ R [] []
  | cons {a b l₁ l₂} : R a b → Forall₂ R l₁ l₂ → Forall₂ R (a :: l₁) (b :: l₂)

namespace List

@[simp] theorem all2_nil {A B : Type} (f : A → B → Bool) : all2 f [] [] = true := rfl

@[simp] theorem all2_cons {A B : Type} (f : A → B → Bool) (a : A) (b : B) as bs :
    all2 f (a :: as) (b :: bs) = (f a b && all2 f as bs) := rfl

@[simp] theorem all2_nil_cons {A B : Type} (f : A → B → Bool) (b : B) bs :
    all2 f [] (b :: bs) = false := rfl

@[simp] theorem all2_cons_nil {A B : Type} (f : A → B → Bool) (a : A) as :
    all2 f (a :: as) [] = false := rfl

/-- `all2` agrees with `Forall₂` on the boolean predicate. -/
theorem all2_Forall₂ {A B : Type} (f : A → B → Bool) :
    ∀ (l₁ : List A) (l₂ : List B), all2 f l₁ l₂ = true ↔ Forall₂ (fun a b => f a b = true) l₁ l₂
  | [], [] => ⟨fun _ => .nil, fun _ => rfl⟩
  | [], _ :: _ => ⟨by simp, fun h => by cases h⟩
  | _ :: _, [] => ⟨by simp, fun h => by cases h⟩
  | a :: as, b :: bs => by
    rw [all2_cons, Bool.and_eq_true, all2_Forall₂ f as bs]
    exact ⟨fun ⟨h1, h2⟩ => .cons h1 h2, fun h => by cases h; exact ⟨‹_›, ‹_›⟩⟩

theorem Forall₂.length_eq {A B : Type} {R : A → B → Prop} {l₁ : List A} {l₂ : List B}
    (h : Forall₂ R l₁ l₂) : l₁.length = l₂.length := by
  induction h <;> simp [*]

end List


@[rocq_alias iriswasm.firstn_is_take_n]
theorem firstn_is_take_n {X : Type} (l : List X) (n : Nat) : l.take n = l.take n := rfl

@[rocq_alias iriswasm.seq_nth_eq]
theorem seq_nth_eq {A : Type} (d : A) (l1 l2 : List A) (hs : l1.length = l2.length)
    (h : ∀ n, n < l1.length → l1.getD n d = l2.getD n d) : l1 = l2 := by
  apply List.ext_getElem hs
  intro n h1 h2
  have := h n h1
  simp_all [List.getD_eq_getElem?_getD]

@[rocq_alias iriswasm.last_error]
def lastError {A : Type} : List A → Option A
  | [] => none
  | [x] => some x
  | _ :: l => lastError l

@[rocq_alias iriswasm.all2_swap]
theorem all2_swap {A B : Type} (f : A → B → Bool) :
    ∀ (l1 : List A) (l2 : List B), List.all2 f l1 l2 = List.all2 (fun x y => f y x) l2 l1
  | [], [] | [], _ :: _ | _ :: _, [] => rfl
  | a :: as, b :: bs => by simp [all2_swap f as bs]

@[rocq_alias iriswasm.all2_size]
theorem all2_size {X Y : Type} (f : X → Y → Bool) :
    ∀ (l1 : List X) (l2 : List Y), List.all2 f l1 l2 = true → l1.length = l2.length
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [List.all2_cons, Bool.and_eq_true] at h
    simp [all2_size f as bs h.2]

@[rocq_alias iriswasm.all2_map_left]
theorem all2_map_left {A B : Type} [DecidableEq B] (f : A → B) :
    ∀ (l1 : List A) (l2 : List B), List.all2 (fun a1 a2 => decide (f a1 = a2)) l1 l2 = true →
      l1.map f = l2
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [List.all2_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    simp [h.1, all2_map_left f as bs h.2]

@[rocq_alias iriswasm.all2_map_right]
theorem all2_map_right {A B : Type} [DecidableEq B] (f : A → B) (l1 : List B) (l2 : List A)
    (h : List.all2 (fun a1 a2 => decide (a1 = f a2)) l1 l2 = true) : l1 = l2.map f := by
  rw [all2_swap] at h
  have e : (fun (x : A) (y : B) => decide (y = f x)) = fun x y => decide (f x = y) := by
    funext x y; exact decide_eq_decide.mpr ⟨Eq.symm, Eq.symm⟩
  exact (all2_map_left f l2 l1 (e ▸ h)).symm

/-- Coq `reflect`, stated as `↔`. -/
@[rocq_alias iriswasm.all2_mapP]
theorem all2_mapP {A B : Type} [DecidableEq B] (f : A → B) (l1 : List A) (l2 : List B) :
    List.all2 (fun a1 a2 => decide (f a1 = a2)) l1 l2 = true ↔ l1.map f = l2 := by
  refine ⟨all2_map_left f l1 l2, ?_⟩
  rintro rfl
  induction l1 <;> simp_all

namespace TProp

/-- `List.Forall` in `Type`. -/
@[rocq_alias iriswasm.TProp.Forall]
inductive Forall {A : Type} (P : A → Type) : List A → Type
  | nil : Forall P []
  | cons (e : A) (l : List A) : P e → Forall P l → Forall P (e :: l)

@[rocq_alias iriswasm.TProp.max]
def max {A : Type} {l : List A} : Forall (fun _ => Nat) l → Nat
  | .nil => 0
  | .cons _ _ n F => Nat.max n (max F)

@[rocq_alias iriswasm.TProp.to_list]
def toList {A B : Type} {l : List A} : Forall (fun _ => B) l → List B
  | .nil => []
  | .cons _ _ p F => p :: toList F

@[rocq_alias iriswasm.TProp.max_to_list]
theorem max_to_list {A : Type} {l : List A} (F : Forall (fun _ => Nat) l) :
    max F = (toList F).foldr Nat.max 0 := by
  induction F <;> simp_all [max, toList]

end TProp

end Wasm
