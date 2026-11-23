/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import Std

universe u
variable {α : Type u}

namespace Wasm
namespace RunTable

-- The first component stores length minus one, ruling out empty runs by construction.
private abbrev Runs (α : Type u) := List (Nat × α)

private def apart (a : α) : Runs α → Prop
  | [] => True
  | (_, b) :: _ => a ≠ b

private def separated : Runs α → Prop
  | [] => True
  | (_, a) :: rs => apart a rs ∧ separated rs

private def expand : Runs α → List α
  | [] => []
  | (k, a) :: rs => List.replicate (k + 1) a ++ expand rs

end RunTable

/-- Finite table represented by its logical size and maximal, nonempty constant runs. -/
structure RunTable (α : Type u) where
  private mk ::
  size : Nat
  runs : List (Nat × α)
  private canonical : RunTable.separated runs
  private sized : (RunTable.expand runs).length = size
  deriving Repr, DecidableEq

namespace RunTable

/-- The extensional view is for specification, not for runtime indexing or updating. -/
def toList (t : RunTable α) := expand t.runs

@[simp] theorem length_toList (t : RunTable α) : t.toList.length = t.size := t.sized

private def empty : RunTable α := ⟨0, [], trivial, rfl⟩

instance : Inhabited (RunTable α) := ⟨empty⟩

private def push [DecidableEq α] : Nat → α → Runs α → Runs α
  | 0, _, rs => rs
  | k+1, a, [] => [(k, a)]
  | k+1, a, (l, b) :: rs =>
    if a = b then (k + 1 + l, a) :: rs else (k, a) :: (l, b) :: rs

private theorem separated_push [DecidableEq α] (n : Nat) (a : α) (rs : Runs α)
    (h : separated rs) : separated (push n a rs) := by
  cases n with
  | zero => exact h
  | succ k =>
    cases rs with
    | nil => exact ⟨trivial, trivial⟩
    | cons p rs =>
      obtain ⟨l, b⟩ := p
      by_cases e : a = b
      · subst b; simpa [push, separated] using h
      · simp only [push, ite_eq_right e]; exact ⟨e, h⟩

private theorem expand_push [DecidableEq α] (n : Nat) (a : α) (rs : Runs α) :
    expand (push n a rs) = List.replicate n a ++ expand rs := by
  cases n with
  | zero => simp [push]
  | succ k =>
    cases rs with
    | nil => simp [expand, push]
    | cons p rs =>
      obtain ⟨l, b⟩ := p
      by_cases e : a = b
      · subst b
        simp [push, expand, ← List.append_assoc, List.replicate_append_replicate, Nat.add_assoc]
      · simp [push, e, expand]

private def prepend [DecidableEq α] (n : Nat) (a : α) (t : RunTable α) : RunTable α :=
  ⟨n + t.size, push n a t.runs, separated_push _ _ _ t.canonical,
    by simp [expand_push, t.sized]⟩

private theorem view_prepend [DecidableEq α] (n : Nat) (a : α) (t : RunTable α) :
    (prepend n a t).toList = List.replicate n a ++ t.toList := expand_push ..

def uniform [DecidableEq α] (n : Nat) (a : α) := prepend n a empty

@[simp] theorem size_uniform [DecidableEq α] (n : Nat) (a : α) : (uniform n a).size = n := by
  simp [uniform, prepend, empty]

@[simp] theorem toList_uniform [DecidableEq α] (n : Nat) (a : α) :
    (uniform n a).toList = List.replicate n a := by
  rw [uniform, view_prepend]; exact List.append_nil _

private def consList [DecidableEq α] (xs : List α) (t : RunTable α) :=
  xs.foldr (prepend 1) t

private theorem view_consList [DecidableEq α] (xs : List α) (t : RunTable α) :
    (consList xs t).toList = xs ++ t.toList := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simpa [consList, view_prepend] using congrArg (a :: ·) ih

def ofList [DecidableEq α] (xs : List α) := consList xs empty

@[simp] theorem toList_ofList [DecidableEq α] (xs : List α) : (ofList xs).toList = xs := by
  rw [ofList, view_consList]; exact List.append_nil _

@[simp] theorem size_ofList [DecidableEq α] (xs : List α) : (ofList xs).size = xs.length := by
  rw [← length_toList, toList_ofList]

private theorem push_one_push [DecidableEq α] (n : Nat) (a : α) (rs : Runs α) :
    push 1 a (push n a rs) = push (n + 1) a rs := by
  cases n with
  | zero => rfl
  | succ k =>
    cases rs with
    | nil => simp [push, Nat.add_comm]
    | cons p rs =>
      obtain ⟨l, b⟩ := p
      by_cases e : a = b <;> simp [push, e, Nat.add_left_comm, Nat.add_comm]

private theorem pack_run [DecidableEq α] (n : Nat) (a : α) (t : RunTable α) :
    (consList (List.replicate n a) t).runs = push n a t.runs := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ]
    change push 1 a (consList (List.replicate n a) t).runs = _
    rw [ih, push_one_push]

private theorem pack_expand [DecidableEq α] (rs : Runs α) (h : separated rs) :
    (ofList (expand rs)).runs = rs := by
  induction rs with
  | nil => rfl
  | cons p rs ih =>
    obtain ⟨k, a⟩ := p
    change (List.foldr (prepend 1) empty (List.replicate (k + 1) a ++ expand rs)).runs = _
    rw [List.foldr_append]
    change (consList (List.replicate (k + 1) a) (ofList (expand rs))).runs = _
    rw [pack_run, ih h.2]
    cases rs with
    | nil => rfl
    | cons q qs =>
      obtain ⟨l, b⟩ := q
      exact ite_eq_right (show a ≠ b from h.1)

@[simp] theorem ofList_toList [DecidableEq α] (t : RunTable α) : ofList t.toList = t := by
  have hr := pack_expand t.runs t.canonical
  have hs : (ofList t.toList).size = t.size := by rw [← length_toList, toList_ofList, length_toList]
  have same : ∀ {x y : RunTable α}, x.size = y.size → x.runs = y.runs → x = y := by
    rintro ⟨_, _, _, _⟩ ⟨_, _, _, _⟩ rfl rfl; rfl
  exact same hs hr

private def lookup (i : Nat) : Runs α → Option α
  | [] => none
  | (k, a) :: rs => if i ≤ k then some a else lookup (i - (k + 1)) rs

def get? (t : RunTable α) (i : Nat) := lookup i t.runs

private theorem lookup_expand (rs : Runs α) (i : Nat) : (expand rs)[i]? = lookup i rs := by
  induction rs generalizing i with
  | nil => rfl
  | cons p rs ih =>
    obtain ⟨k, a⟩ := p
    by_cases h : i ≤ k <;>
      simp [expand, lookup, List.getElem?_append, ih, h,
        show (i < k + 1) ↔ i ≤ k by omega]

@[simp] theorem toList_getElem? (t : RunTable α) (i : Nat) : t.toList[i]? = t.get? i :=
  lookup_expand ..

@[simp] theorem get?_ofList [DecidableEq α] (xs : List α) (i : Nat) : (ofList xs).get? i = xs[i]? := by
  rw [← toList_getElem?, toList_ofList]

@[simp] theorem get?_uniform [DecidableEq α] (n : Nat) (a : α) (i : Nat) :
    (uniform n a).get? i = if i < n then some a else none := by
  rw [← toList_getElem?, toList_uniform, List.getElem?_replicate]

theorem get?_eq_none_iff (t : RunTable α) (i : Nat) : t.get? i = none ↔ t.size ≤ i := by
  rw [← toList_getElem?, List.getElem?_eq_none_iff, length_toList]

theorem ext_toList [DecidableEq α] {t u : RunTable α} (h : t.toList = u.toList) : t = u := by
  simpa using congrArg ofList h

@[ext] theorem ext [DecidableEq α] {t u : RunTable α} (h : ∀ i, t.get? i = u.get? i) : t = u := by
  exact ext_toList (List.ext_getElem? (fun i ↦ by simpa using h i))

theorem ext_of_size_get? [DecidableEq α] {t u : RunTable α} (hs : t.size = u.size)
    (h : ∀ i < t.size, t.get? i = u.get? i) : t = u := by
  apply ext; intro i
  by_cases hi : i < t.size
  · exact h i hi
  · rw [(get?_eq_none_iff t i).2 (by omega), (get?_eq_none_iff u i).2 (by omega)]

-- Copy only runs intersecting the prefix, merging its last run with the supplied suffix.
private def takeOnto [DecidableEq α] (n : Nat) (t : RunTable α) : Runs α → RunTable α
  | [] => t
  | (k, a) :: rs => if n ≤ k + 1 then prepend n a t
    else prepend (k + 1) a (takeOnto (n - (k + 1)) t rs)

private theorem view_takeOnto [DecidableEq α] (n : Nat) (t : RunTable α) (rs : Runs α) :
    (takeOnto n t rs).toList = (expand rs).take n ++ t.toList := by
  induction rs generalizing n with
  | nil => simp [takeOnto, expand]
  | cons p rs ih =>
    obtain ⟨k, a⟩ := p
    by_cases h : n ≤ k + 1
    · simp [takeOnto, h, view_prepend, expand, List.take_append, Nat.min_eq_left h,
        Nat.sub_eq_zero_of_le h]
    · simp [takeOnto, h, view_prepend, expand, List.take_append, ih, List.append_assoc,
        Nat.min_eq_right (Nat.le_of_not_ge h)]

private def skipRuns (i : Nat) : Runs α → Runs α
  | [] => []
  | (k, a) :: rs => if i ≤ k then (k - i, a) :: rs else skipRuns (i - (k + 1)) rs

private theorem separated_skip (i : Nat) (rs : Runs α) (h : separated rs) :
    separated (skipRuns i rs) := by
  induction rs generalizing i with
  | nil => trivial
  | cons p rs ih =>
    obtain ⟨k, a⟩ := p
    simp only [skipRuns]; split
    · exact h
    · exact ih _ h.2

private theorem expand_skip (i : Nat) (rs : Runs α) : expand (skipRuns i rs) = (expand rs).drop i := by
  induction rs generalizing i with
  | nil => simp [expand, skipRuns]
  | cons p rs ih =>
    obtain ⟨k, a⟩ := p
    by_cases h : i ≤ k
    · have hs : i - (k + 1) = 0 := by omega
      have hk : k + 1 - i = k - i + 1 := by omega
      simp [skipRuns, expand, h, List.drop_append, hs, hk]
    · have hs : k + 1 - i = 0 := by omega
      simp [skipRuns, expand, h, ih, List.drop_append, hs]

private def suffix (i : Nat) (t : RunTable α) : RunTable α :=
  ⟨t.size - i, skipRuns i t.runs, separated_skip _ _ t.canonical, by simp [expand_skip, t.sized]⟩

/-- Unchecked element-segment splice. An offset past the end appends without padding. -/
def overwrite [DecidableEq α] (t : RunTable α) (i : Nat) (xs : List α) : RunTable α :=
  match xs with
  | [] => t
  | _ :: _ => takeOnto i (consList xs (suffix (i + xs.length) t)) t.runs

@[simp] theorem toList_overwrite [DecidableEq α] (t : RunTable α) (i : Nat) (xs : List α) :
    (t.overwrite i xs).toList = t.toList.take i ++ xs ++ t.toList.drop (i + xs.length) := by
  cases xs with
  | nil => simp [overwrite]
  | cons a xs =>
    rw [overwrite, view_takeOnto, view_consList]
    simp [suffix, toList, expand_skip, List.append_assoc]

theorem size_overwrite_of_le [DecidableEq α] (t : RunTable α) (i : Nat) (xs : List α)
    (h : i + xs.length ≤ t.size) : (t.overwrite i xs).size = t.size := by
  rw [← length_toList, toList_overwrite]
  simp; omega

def set? [DecidableEq α] (t : RunTable α) (i : Nat) (a : α) : Option (RunTable α) :=
  if i < t.size then some (t.overwrite i [a]) else none

@[simp] theorem set?_eq_none_iff [DecidableEq α] (t : RunTable α) (i : Nat) (a : α) :
    t.set? i a = none ↔ t.size ≤ i := by simp [set?]

theorem toList_set [DecidableEq α] {t t' : RunTable α} {i : Nat} {a : α}
    (h : t.set? i a = some t') : t'.toList = t.toList.set i a := by
  unfold set? at h
  split at h
  next hi =>
    cases h
    simp [List.set_eq_take_append_cons_drop, hi, List.append_assoc]
  next => contradiction

theorem size_set [DecidableEq α] {t t' : RunTable α} {i : Nat} {a : α}
    (h : t.set? i a = some t') : t'.size = t.size := by
  rw [← length_toList, toList_set h, List.length_set, length_toList]

theorem get?_set [DecidableEq α] {t t' : RunTable α} {i : Nat} {a : α}
    (h : t.set? i a = some t') (j : Nat) : t'.get? j = if i = j then some a else t.get? j := by
  have hi : i < t.size := by
    by_cases hi : i < t.size
    · exact hi
    · simp [set?, hi] at h
  rw [← toList_getElem?, toList_set h, List.getElem?_set]
  simp [hi]

theorem set?_of_lt [DecidableEq α] (t : RunTable α) (i : Nat) (a : α) (h : i < t.size) :
    ∃ t', t.set? i a = some t' ∧ t'.toList = t.toList.set i a := by
  have hs : t.set? i a = some (t.overwrite i [a]) := ite_eq_left h
  exact ⟨_, hs, toList_set hs⟩

def grow [DecidableEq α] (t : RunTable α) (n : Nat) (a : α) : RunTable α :=
  if n = 0 then t else takeOnto t.size (uniform n a) t.runs

@[simp] theorem toList_grow [DecidableEq α] (t : RunTable α) (n : Nat) (a : α) :
    (t.grow n a).toList = t.toList ++ List.replicate n a := by
  by_cases h : n = 0
  · simp [grow, h]
  · rw [grow, ite_eq_right h, view_takeOnto, toList_uniform, ← t.sized, List.take_length]
    rfl

@[simp] theorem size_grow [DecidableEq α] (t : RunTable α) (n : Nat) (a : α) :
    (t.grow n a).size = t.size + n := by rw [← length_toList, toList_grow]; simp

theorem get?_grow [DecidableEq α] (t : RunTable α) (n : Nat) (a : α) (i : Nat) :
    (t.grow n a).get? i =
      if i < t.size then t.get? i else if i < t.size + n then some a else none := by
  rw [← toList_getElem?, toList_grow, List.getElem?_append, length_toList]
  split
  · exact toList_getElem? ..
  · simp [List.getElem?_replicate, show (i - t.size < n) ↔ i < t.size + n by omega]

end RunTable
end Wasm
