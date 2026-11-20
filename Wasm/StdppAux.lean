/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import Wasm.ListExtra
import Iris.Std.PartialMap

/-! Port of `theories/stdpp_aux.v` (lemmas are added as later files need them, in `.v` order). -/

namespace Wasm

#rocq_ignore iriswasm.forward "Ltac `assert`/`specialize` helper; Lean uses `have`"
#rocq_ignore iriswasm.remember_lookup "stdpp finmap automation; Lean proofs rewrite with `get?` lemmas"
#rocq_ignore iriswasm.resolve_finmap "stdpp finmap automation; Lean proofs rewrite with `get?` lemmas"

/-- `imap` is `List.mapIdx`. -/
@[rocq_alias iriswasm.nodup_imap_inj1]
theorem nodup_imap_inj1 {T X : Type} (l : List T) (f : Nat → T → X)
    (h : ∀ n1 n2 t1 t2, f n1 t1 = f n2 t2 → n1 = n2) : (l.mapIdx f).Nodup := by
  induction l generalizing f with
  | nil => simp
  | cons a l ih =>
    rw [List.mapIdx_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, ih _ fun n1 n2 t1 t2 he => Nat.succ.inj (h _ _ _ _ he)⟩
    obtain ⟨i, _, he⟩ := List.mem_mapIdx.1 hm
    exact Nat.succ_ne_zero _ (h _ _ _ _ he)

/-- Every binding of `m1` has a binding of `m2` at the same key, related by `r`. -/
@[rocq_alias iriswasm.map_related]
def mapRelated {K : Type _} {M : Type _ → Type _} [Iris.Std.PartialMap M K] {A : Type _}
    (r : A → A → Prop) (m1 m2 : M A) : Prop :=
  ∀ (i : K) (x : A), Iris.Std.get? m1 i = some x → ∃ y, Iris.Std.get? m2 i = some y ∧ r x y

@[rocq_alias iriswasm.fold_left_preserve]
theorem fold_left_preserve {A B : Type} (P : A → Prop) (f : A → B → A) (l : List B) (acc : A)
    (hacc : P acc) (hf : ∀ (x : A) (act : B), P x → P (f x act)) : P (l.foldl f acc) := by
  induction l generalizing acc with
  | nil => exact hacc
  | cons a l ih => exact ih _ (hf _ _ hacc)

@[rocq_alias iriswasm.gen_index]
def genIndex (offset len : Nat) : List Nat :=
  (List.replicate len 0).mapIdx fun i x => i + offset + x

@[rocq_alias iriswasm.gen_index_lookup]
theorem gen_index_lookup (offset len k : Nat) (h : k < len) :
    (genIndex offset len)[k]? = some (offset + k) := by
  simp [genIndex, h]; omega

@[rocq_alias iriswasm.gen_index_lookup_Some]
theorem gen_index_lookup_Some {n l i x : Nat} (h : (genIndex n l)[i]? = some x) :
    x = n + i ∧ i < l := by
  simp only [genIndex, List.getElem?_mapIdx, List.getElem?_replicate] at h
  split at h <;> simp at h; omega

@[rocq_alias iriswasm.gen_index_NoDup]
theorem gen_index_NoDup (n l : Nat) : (genIndex n l).Nodup := by
  have : genIndex n l = List.range' n l := by
    apply List.ext_getElem <;> simp [genIndex]; intros; omega
  rw [this]; exact List.nodup_range'

@[rocq_alias iriswasm.gen_index_length]
theorem gen_index_length (n len : Nat) : (genIndex n len).length = len := by
  simp [genIndex]

@[rocq_alias iriswasm.gen_index_extend]
theorem gen_index_extend (offset len : Nat) :
    genIndex offset (len + 1) = genIndex offset len ++ [offset + len] := by
  simp only [genIndex, List.replicate_succ', List.mapIdx_append, List.length_replicate]
  simp; omega

@[rocq_alias iriswasm.those_projection_backward]
theorem those_projection_backward {T : Type} (l0 : List (Option T)) (l1 : List T)
    (h : ∀ k : Nat, (match l0[k]? with | some (x : Option T) => x | none => none) = l1[k]?)
    (hlen : l0.length = l1.length) : those l0 = some l1 := by
  rw [← those_those0]
  induction l0 generalizing l1 with
  | nil => cases l1 with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons a l0 ih =>
    cases l1 with
    | nil => simp at hlen
    | cons b l1 =>
      have h0 := h 0
      simp only [List.getElem?_cons_zero] at h0
      subst h0
      simp [those0, ih l1 (fun k => h (k + 1)) (by simpa using hlen)]

/-- Coq's unused map argument `m` is dropped. -/
@[rocq_alias iriswasm.list_to_map_zip_lookup]
theorem list_to_map_zip_lookup {X Y : Type _} {M : Type _ → Type _}
    [Iris.Std.LawfulFiniteMap M X] [DecidableEq X] (l1 : List X) (l2 : List Y) (k : X) (v : Y)
    (hnd : l1.Nodup) (hlen : l1.length = l2.length) :
    Iris.Std.get? (Iris.Std.PartialMap.ofList (M := M) (l1.zip l2)) k = some v ↔
      ∃ k' : Nat, l1[k']? = some k ∧ l2[k']? = some v := by
  rw [← Iris.Std.LawfulFiniteMap.mem_ofList (by simpa [List.map_fst_zip, hlen] using hnd),
    List.mem_iff_getElem?]
  simp [List.getElem?_zip_eq_some]

open Iris.Std in
@[rocq_alias iriswasm.list_to_map_zip_insert]
theorem list_to_map_zip_insert {X Y : Type _} {M : Type _ → Type _} [LawfulFiniteMap M X]
    [DecidableEq X] (l1 : List X) (l2 : List Y) (k : X) (k' : Nat) (v : Y) (m : M Y)
    (hnd : l1.Nodup) (hm : m = PartialMap.ofList (l1.zip l2)) (hlen : l1.length = l2.length)
    (hk : l1[k']? = some k) :
    insert m k v = PartialMap.ofList (M := M) (l1.zip (l2.set k' v)) := by
  subst hm
  have hlen' : l1.length = (l2.set k' v).length := by simpa using hlen
  have hlt : k' < l1.length := (List.getElem?_eq_some_iff.1 hk).1
  apply equiv_iff_eq.1
  intro i
  apply Option.ext
  intro w
  rw [LawfulPartialMap.get?_insert_some_iff, list_to_map_zip_lookup l1 _ i w hnd hlen',
    list_to_map_zip_lookup l1 l2 i w hnd hlen]
  -- positions of `l1` are determined by their entries
  have inj : ∀ j, l1[j]? = some i → (k = i ↔ j = k') := fun j hj => by
    have hjl : j < l1.length := (List.getElem?_eq_some_iff.1 hj).1
    constructor
    · rintro rfl; exact (hnd.getElem?_inj hjl).1 (hj.trans hk.symm)
    · rintro rfl; simpa [hk] using hj
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨hne, j, hj1, hj2⟩)
    · exact ⟨k', hk, by simp [show k' < l2.length by omega]⟩
    · refine ⟨j, hj1, ?_⟩
      have : j ≠ k' := fun h => hne ((inj j hj1).2 h)
      simpa [List.getElem?_set, Ne.symm this] using hj2
  · rintro ⟨j, hj1, hj2⟩
    by_cases hjk : j = k'
    · subst hjk
      left
      refine ⟨(inj j hj1).2 rfl, ?_⟩
      simpa [List.getElem?_set, show j < l2.length by omega] using hj2
    · right
      exact ⟨fun h => hjk ((inj j hj1).1 h), j, hj1,
        by simpa [List.getElem?_set, Ne.symm hjk] using hj2⟩

@[rocq_alias iriswasm.length_those]
theorem length_those {A B : Type} (f : A → Option B) (l : List A) (l' : List B)
    (h : those (l.map f) = some l') : l.length = l'.length := by
  rw [← those_those0] at h
  induction l generalizing l' with
  | nil => cases l' <;> simp_all [those0]
  | cons a l ih =>
    cases hfa : f a with
    | none => simp [those0, hfa] at h
    | some b =>
      cases ht : those0 (l.map f) with
      | none => simp [those0, hfa, ht] at h
      | some t =>
        simp [those0, hfa, ht] at h
        subst h
        simp [ih _ ht]

end Wasm
