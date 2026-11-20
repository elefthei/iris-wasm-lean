/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import Wasm.Common

/-! Port of `theories/list_extra.v`. -/

#rocq_ignore iriswasm.bind_list0 "ITree monad helper; only the interpreter uses it"
#rocq_ignore iriswasm.bind_list_aux "ITree monad helper; only the interpreter uses it"
#rocq_ignore iriswasm.bind_list "ITree monad helper; only the interpreter uses it"
#rocq_ignore iriswasm.mapi_aux "folded into mapi"

namespace Wasm

/-- All options are `some`: collect the values. -/
@[rocq_alias iriswasm.those0]
def those0 {A : Type} : List (Option A) → Option (List A)
  | [] => some []
  | none :: _ => none
  | some y :: xs => (those0 xs).map (y :: ·)

@[rocq_alias iriswasm.length_repeat]
theorem length_repeat {A : Type} (x : A) (n : Nat) : (List.replicate n x).length = n :=
  List.length_replicate

/-- Tail-recursive variant of `those0`. -/
def thoseAux {A : Type} : List A → List (Option A) → Option (List A)
  | acc, [] => some acc
  | _, none :: _ => none
  | acc, some y :: xs => thoseAux (y :: acc) xs

@[rocq_alias iriswasm.those]
def those {A : Type} (l : List (Option A)) : Option (List A) :=
  (thoseAux [] l).map List.reverse

theorem thoseAux_eq {A : Type} :
    ∀ (acc : List A) (l : List (Option A)),
      thoseAux acc l = (those0 l).map (fun r => r.reverse ++ acc)
  | acc, [] => by simp [thoseAux, those0]
  | acc, none :: _ => by simp [thoseAux, those0]
  | acc, some y :: xs => by
    simp only [thoseAux, those0, thoseAux_eq _ xs, Option.map_map]
    congr 1; funext r; simp

@[rocq_alias iriswasm.those_those0]
theorem those_those0 {A : Type} (l : List (Option A)) : those0 l = those l := by
  simp [those, thoseAux_eq, Option.map_map, Function.comp_def]

theorem those0_app {A : Type} (l1 l2 : List (Option A)) :
    those0 (l1 ++ l2) = (those0 l1).bind fun t1 => (those0 l2).map (t1 ++ ·) := by
  induction l1 with
  | nil => simp [those0]
  | cons a l1 ih =>
    rcases a with _ | a
    · simp [those0]
    · simp only [List.cons_append, those0, ih]
      cases those0 l1 <;> cases those0 l2 <;> simp

@[rocq_alias iriswasm.those_app]
theorem those_app {A : Type} (l1 l2 : List (Option A)) (tl1 tl2 : List A)
    (h1 : those l1 = some tl1) (h2 : those l2 = some tl2) :
    those (l1 ++ l2) = some (tl1 ++ tl2) := by
  rw [← those_those0] at *
  simp [those0_app, h1, h2]

@[rocq_alias iriswasm.those_app_inv]
theorem those_app_inv {A : Type} (l1 l2 : List (Option A)) (tl : List A)
    (h : those (l1 ++ l2) = some tl) :
    ∃ tl1 tl2, those l1 = some tl1 ∧ those l2 = some tl2 ∧ tl1 ++ tl2 = tl := by
  rw [← those_those0] at *
  simp only [those_those0] at *
  rw [← those_those0, those0_app] at h
  rw [← those_those0, ← those_those0]
  cases h1 : those0 l1 <;> cases h2 : those0 l2 <;> simp_all

@[rocq_alias iriswasm.mapi]
def mapi {A B : Type} (f : Nat → A → B) (xs : List A) : List B :=
  xs.zipIdx.map fun (x, i) => f i x

@[rocq_alias iriswasm.fold_lefti]
def foldLefti {A B : Type} (f : Nat → A → B → A) (xs : List B) (acc0 : A) : A :=
  (xs.foldl (fun (k, acc) x => (k + 1, f k acc x)) (0, acc0)).2

end Wasm
