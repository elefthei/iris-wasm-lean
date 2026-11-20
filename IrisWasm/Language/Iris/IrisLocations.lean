/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import Wasm.Operations
import Wasm.StdppAux
import Iris.Std.HeapInstances

/-! Port of `theories/iris/language/iris/iris_locations.v`: the finite maps (over the store's
function, table and memory lists) that back the Iris state interpretation.

Coq `gmap N T` / `gmap (N*N) T` become `NatMap T` / `NatPairMap T` (`Std.ExtTreeMap … compare`),
used through iris-lean's `Iris.Std.PartialMap` API: `get? m k` (Coq `m !! k`), `insert m k v`
(Coq `<[k:=v]> m`), `∅`, `m₁ ∪ m₂` (left-biased), `m₁ ##ₘ m₂` (`open scoped Iris.Std.PartialMap`). -/

namespace IrisWasm

open Iris Iris.Std Wasm
open Iris.Std.LawfulPartialMap (get?_insert get?_union)
open scoped Iris.Std.PartialMap

/-! ## Orders for the map keys -/

/-- Lexicographic order on `Nat × Nat` keys (table and memory heaps). -/
instance instOrdNatProd : Ord (Nat × Nat) := lexOrd

instance instOrdUnit : Ord Unit := ⟨fun _ _ => .eq⟩

instance instTransOrdUnit : Std.TransOrd Unit where
  eq_swap := rfl
  isLE_trans := by intros; rfl

instance instLawfulEqOrdUnit : Std.LawfulEqOrd Unit where
  eq_of_compare := by intros; rfl

/-- Finite maps with `Nat` keys (Coq `gmap N`). -/
abbrev NatMap : Type → Type := fun V => Std.ExtTreeMap Nat V compare

/-- Finite maps with `Nat × Nat` keys (Coq `gmap (N*N)`). -/
abbrev NatPairMap : Type → Type := fun V => Std.ExtTreeMap (Nat × Nat) V compare

example : LawfulFiniteMap NatMap Nat := inferInstance
example : LawfulFiniteMap NatPairMap (Nat × Nat) := inferInstance
example : LawfulFiniteMap (Std.ExtTreeMap Unit · compare) Unit := inferInstance

/-- `m₁ ∪ m₂` on `ExtTreeMap`s is iris-lean's left-biased `PartialMap.union` (as stdpp's `∪`),
overriding core's right-biased `Std.ExtTreeMap.union`, so iris-lean map/big-op lemmas apply.
Scoped: active inside `namespace IrisWasm` only. -/
scoped instance (priority := high) instUnionExtTreeMap {K V : Type} [Ord K] [Std.TransOrd K]
    [Std.LawfulEqOrd K] : Union (Std.ExtTreeMap K V compare) :=
  ⟨PartialMap.union (M := (Std.ExtTreeMap K · compare))⟩

/-! ## Generic `ofList` lookup -/

/-- Lookup in `ofList L` is determined by membership in `L` alone (no `NoDup` needed). -/
private theorem get?_ofList_of_mem_iff {K V : Type} {M : Type → Type} [LawfulPartialMap M K]
    {L : List (K × V)} {k : K} {o : Option V} (h : ∀ v, (k, v) ∈ L ↔ o = some v) :
    get? (PartialMap.ofList (M := M) L) k = o := by
  induction L with
  | nil =>
    rw [PartialMap.ofList, List.foldr_nil, LawfulPartialMap.get?_empty]
    cases o with
    | none => rfl
    | some v => simp at h
  | cons p L ih =>
    obtain ⟨k', v'⟩ := p
    rw [PartialMap.ofList, List.foldr_cons]
    by_cases hk : k' = k
    · subst hk
      rw [LawfulPartialMap.get?_insert_eq rfl]
      exact ((h v').1 (List.mem_cons_self ..)).symm
    · rw [LawfulPartialMap.get?_insert_ne hk]
      exact ih fun v => by
        rw [← h v, List.mem_cons]
        simp [Prod.ext_iff, Ne.symm hk]

private theorem mem_mapIdx_pair {K T : Type} (f : Nat → K) (l : List T) (k : K) (v : T) :
    (k, v) ∈ l.mapIdx (fun i x => (f i, x)) ↔ ∃ i, f i = k ∧ l[i]? = some v := by
  rw [List.mem_mapIdx]
  constructor
  · rintro ⟨i, hi, he⟩
    cases he
    exact ⟨i, rfl, by simp [hi]⟩
  · rintro ⟨i, rfl, hv⟩
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hv
    exact ⟨i, hi, rfl⟩

/-! ## Definitions -/

@[rocq_alias iriswasm.create_table]
def createTable (len : Nat) : Tableinst :=
  { data := List.replicate len none, maxOpt := some len }

@[rocq_alias iriswasm.create_memory]
def createMemory (sz szLim : Nat) (initB : Byte) : Memory :=
  { data := MemoryList.memMake initB sz, maxOpt := some szLim }

#rocq_ignore iriswasm.inhabited_table "`Tableinst` derives `Inhabited`"
#rocq_ignore iriswasm.inhabited_memory "`Memory` derives `Inhabited`"

@[rocq_alias iriswasm.lookup_2d]
def lookup2d {T : Type} (l : List (List T)) (n i : Nat) : Option T :=
  match l[n]? with
  | some x => x[i]?
  | none => none

/-- Coq `imap` is `List.mapIdx`. -/
@[rocq_alias iriswasm.flatten_list]
def flattenList {T : Type} (l : List T) : List (Nat × T) :=
  l.mapIdx fun n x => (n, x)

@[rocq_alias iriswasm.flatten_list_nodup]
theorem flatten_list_nodup {T : Type} (l : List T) : (flattenList l).Nodup :=
  nodup_imap_inj1 l _ fun _ _ _ _ h => (Prod.mk.inj h).1

@[rocq_alias iriswasm.flatten_list_lookup_Some]
theorem flatten_list_lookup_Some {T : Type} (l : List T) (i : Nat) (x : T) (h : l[i]? = some x) :
    (flattenList l)[i]? = some (i, x) := by
  simp [flattenList, List.getElem?_mapIdx, h]

private theorem mem_flattenList {T : Type} (l : List T) (n : Nat) (x : T) :
    (n, x) ∈ flattenList l ↔ l[n]? = some x := by
  rw [flattenList, mem_mapIdx_pair (fun n => n)]
  exact ⟨fun ⟨_, h1, h2⟩ => h1 ▸ h2, fun h => ⟨n, rfl, h⟩⟩

@[rocq_alias iriswasm.gmap_of_list]
def gmapOfList {T : Type} (l : List T) : NatMap T :=
  PartialMap.ofList (flattenList l)

@[rocq_alias iriswasm.flatten_2d_list_i]
def flatten2dListI {T : Type} : List (List T) → Nat → List ((Nat × Nat) × T)
  | [], _ => []
  | l1 :: l', i => (flattenList l1).map (fun (n, b) => ((i, n), b)) ++ flatten2dListI l' (i + 1)

@[rocq_alias iriswasm.flatten_2d_list]
def flatten2dList {T : Type} (l : List (List T)) : List ((Nat × Nat) × T) :=
  flatten2dListI l 0

@[rocq_alias iriswasm.gmap_of_list_2d]
def gmapOfList2d {T : Type} (l : List (List T)) : NatPairMap T :=
  PartialMap.ofList (flatten2dList l)

@[rocq_alias iriswasm.gmap_of_list_2d_offset]
def gmapOfList2dOffset {T : Type} (l : List (List T)) (offset : Nat) : NatPairMap T :=
  PartialMap.ofList ((flatten2dList l).map fun ((i, j), x) => ((i + offset, j), x))

@[rocq_alias iriswasm.memory_to_list]
def memoryToList (m : Memory) : List Byte :=
  m.data.data

@[rocq_alias iriswasm.gmap_of_memory]
def gmapOfMemory (l : List Memory) : NatPairMap Byte :=
  gmapOfList2d (l.map memoryToList)

@[rocq_alias iriswasm.table_to_list]
def tableToList (tab : Tableinst) : List Funcelem :=
  tab.data

@[rocq_alias iriswasm.gmap_of_table]
def gmapOfTable (l : List Tableinst) : NatPairMap Funcelem :=
  gmapOfList2d (l.map tableToList)

/-! ## Lemmas -/

@[rocq_alias iriswasm.gmap_of_list_lookup]
theorem gmap_of_list_lookup {T : Type} (l : List T) (n : Nat) :
    get? (gmapOfList l) n = l[n]? :=
  get?_ofList_of_mem_iff fun _ => mem_flattenList l n _

/-- Commutativity between `gmapOfList` and list insertion. -/
@[rocq_alias iriswasm.gmap_of_list_insert]
theorem gmap_of_list_insert {T : Type} (l : List T) (v : T) (n : Nat) (h : n < l.length) :
    gmapOfList (l.set n v) = insert (gmapOfList l) n v := by
  apply LawfulPartialMap.equiv_iff_eq.1
  intro i
  rw [gmap_of_list_lookup, get?_insert, gmap_of_list_lookup, List.getElem?_set]
  split <;> simp_all

@[rocq_alias iriswasm.gmap_of_list_append]
theorem gmap_of_list_append {T : Type} (l : List T) (v : T) :
    gmapOfList (l ++ [v]) = insert (gmapOfList l) l.length v := by
  apply LawfulPartialMap.equiv_iff_eq.1
  intro i
  rw [gmap_of_list_lookup, get?_insert, gmap_of_list_lookup, List.getElem?_append]
  split <;> split
  · omega
  · rfl
  · subst_vars; simp
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

@[rocq_alias iriswasm.flatten_2d_list_i_acc_shift_spec]
theorem flatten_2d_list_i_acc_shift_spec {T : Type} (l : List (List T)) (acc : Nat) :
    flatten2dListI l (acc + 1) =
      (flatten2dListI l acc).map (fun ((n, i), t) => ((n + 1, i), t)) := by
  induction l generalizing acc with
  | nil => rfl
  | cons a l ih =>
    simp only [flatten2dListI, List.map_append, List.map_map, ih]
    congr 1

private theorem mem_flatten2dListI {T : Type} (l : List (List T)) (acc n i : Nat) (t : T) :
    ((n, i), t) ∈ flatten2dListI l acc ↔ acc ≤ n ∧ lookup2d l (n - acc) i = some t := by
  induction l generalizing acc with
  | nil => simp [flatten2dListI, lookup2d]
  | cons a l ih =>
    simp only [flatten2dListI, List.mem_append, List.mem_map, ih]
    constructor
    · rintro (⟨⟨j, b⟩, hm, he⟩ | ⟨h1, h2⟩)
      · simp only [Prod.mk.injEq] at he
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := he
        simpa [lookup2d] using (mem_flattenList ..).1 hm
      · refine ⟨by omega, ?_⟩
        rw [show n - acc = n - (acc + 1) + 1 by omega]
        simpa [lookup2d] using h2
    · rintro ⟨h1, h2⟩
      rcases Nat.eq_or_lt_of_le h1 with rfl | h
      · exact .inl ⟨(i, t), (mem_flattenList ..).2 (by simpa [lookup2d] using h2), rfl⟩
      · rw [show n - acc = n - (acc + 1) + 1 by omega] at h2
        exact .inr ⟨h, by simpa [lookup2d] using h2⟩

@[rocq_alias iriswasm.flatten_2d_list_i_acc_shift]
theorem flatten_2d_list_i_acc_shift {T : Type} (l : List (List T)) (n i : Nat) (t : T)
    (acc : Nat) :
    ((n + 1, i), t) ∈ flatten2dListI l (acc + 1) ↔ ((n, i), t) ∈ flatten2dListI l acc := by
  simp only [mem_flatten2dListI, Nat.add_sub_add_right, Nat.add_le_add_iff_right]

@[rocq_alias iriswasm.flatten_2d_list_i_acc_domain1]
theorem flatten_2d_list_i_acc_domain1 {T : Type} (l : List (List T)) (n i : Nat) (t : T)
    (acc : Nat) (h : ((n, i), t) ∈ flatten2dListI l acc) : n ≥ acc :=
  ((mem_flatten2dListI ..).1 h).1

@[rocq_alias iriswasm.flatten_2d_list_lookup]
theorem flatten_2d_list_lookup {T : Type} (l : List (List T)) (n i : Nat) (t : T) :
    ((n, i), t) ∈ flatten2dList l ↔
      (match l[n]? with
       | some l' => l'[i]?
       | none => none) = some t := by
  simp only [flatten2dList, mem_flatten2dListI, Nat.zero_le, true_and, Nat.sub_zero]
  rfl

@[rocq_alias iriswasm.flatten_2d_list_inj12]
theorem flatten_2d_list_inj12 {T : Type} (l : List (List T)) (x1 x2 : Nat) (p : Nat × Nat)
    (t1 t2 : T) (h1 : (flatten2dList l)[x1]? = some (p, t1))
    (h2 : (flatten2dList l)[x2]? = some (p, t2)) : t1 = t2 := by
  obtain ⟨n, i⟩ := p
  have e1 := (flatten_2d_list_lookup ..).1 (List.mem_of_getElem? h1)
  have e2 := (flatten_2d_list_lookup ..).1 (List.mem_of_getElem? h2)
  exact Option.some.inj (e1.symm.trans e2)

@[rocq_alias iriswasm.flatten_2d_list_nodup]
theorem flatten_2d_list_nodup {T : Type} (l : List (List T)) : (flatten2dList l).Nodup := by
  suffices ∀ acc, (flatten2dListI l acc).Nodup from this 0
  induction l with
  | nil => intro; exact List.nodup_nil
  | cons a l ih =>
    intro acc
    rw [flatten2dListI, List.nodup_append]
    refine ⟨List.nodup_map_of_injective ?_ (flatten_list_nodup a), ih _, ?_⟩
    · rintro ⟨_, _⟩ ⟨_, _⟩ h
      simp_all
    · rintro ⟨⟨n, i⟩, t⟩ ha ⟨⟨n', i'⟩, t'⟩ hb he
      obtain ⟨⟨_, _⟩, _, he'⟩ := List.mem_map.1 ha
      cases he'
      cases he
      have := flatten_2d_list_i_acc_domain1 _ _ _ _ _ hb
      omega

private theorem get?_gmapOfList2dOffset {T : Type} (l : List (List T)) (off n i : Nat) :
    get? (gmapOfList2dOffset l off) (n, i) = if off ≤ n then lookup2d l (n - off) i else none := by
  apply get?_ofList_of_mem_iff
  intro t
  simp only [List.mem_map]
  constructor
  · rintro ⟨⟨⟨n', i'⟩, t'⟩, hm, he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := he
    rw [ite_eq_left (Nat.le_add_left _ _), Nat.add_sub_cancel]
    exact (flatten_2d_list_lookup ..).1 hm
  · intro h
    split at h
    · exact ⟨((n - off, i), t), (flatten_2d_list_lookup ..).2 h, by simp; omega⟩
    · cases h

@[rocq_alias iriswasm.gmap_of_list_2d_offset_lookup]
theorem gmap_of_list_2d_offset_lookup {T : Type} (l : List (List T)) (off n i : Nat)
    (h : n ≥ off) :
    get? (gmapOfList2dOffset l off) (n, i) =
      match l[n - off]? with
      | some l' => l'[i]?
      | none => none := by
  rw [get?_gmapOfList2dOffset, ite_eq_left h]
  rfl

@[rocq_alias iriswasm.gmap_of_list_2d_offset_lookup_None]
theorem gmap_of_list_2d_offset_lookup_None {T : Type} (l : List (List T)) (off n i : Nat)
    (h : n < off) : get? (gmapOfList2dOffset l off) (n, i) = none := by
  rw [get?_gmapOfList2dOffset, ite_eq_right (by omega)]

@[rocq_alias iriswasm.gmap_of_list_2d_offset_0]
theorem gmap_of_list_2d_offset_0 {T : Type} (l : List (List T)) :
    gmapOfList2d l = gmapOfList2dOffset l 0 := by
  rw [gmapOfList2d, gmapOfList2dOffset]
  congr 1
  conv => lhs; rw [← List.map_id (flatten2dList l)]
  apply List.map_congr_left
  rintro ⟨⟨_, _⟩, _⟩ _
  rfl

@[rocq_alias iriswasm.gmap_of_list_2d_lookup]
theorem gmap_of_list_2d_lookup {T : Type} (l : List (List T)) (n i : Nat) :
    get? (gmapOfList2d l) (n, i) =
      match l[n]? with
      | some l' => l'[i]?
      | none => none := by
  rw [gmap_of_list_2d_offset_0, gmap_of_list_2d_offset_lookup _ _ _ _ (Nat.zero_le _),
    Nat.sub_zero]

private theorem lookup2d_eq {T : Type} (l : List (List T)) (n i : Nat) :
    lookup2d l n i = l[n]?.bind (·[i]?) := by
  unfold lookup2d
  cases l[n]? <;> rfl

private theorem get?_gmapOfList2d {T : Type} (l : List (List T)) (n i : Nat) :
    get? (gmapOfList2d l) (n, i) = l[n]?.bind (·[i]?) := by
  rw [gmap_of_list_2d_lookup]
  cases l[n]? <;> rfl

private theorem get?_gmapOfList2dOffset' {T : Type} (l : List (List T)) (off n i : Nat) :
    get? (gmapOfList2dOffset l off) (n, i) =
      if off ≤ n then l[n - off]?.bind (·[i]?) else none := by
  rw [get?_gmapOfList2dOffset, lookup2d_eq]

@[rocq_alias iriswasm.new_2d_gmap_at_n]
def new2dGmapAtN {T : Type} (n : Nat) (l : List T) : NatPairMap T :=
  PartialMap.ofList (l.mapIdx fun i x => ((n, i), x))

private theorem get?_new2dGmapAtN {T : Type} (n m i : Nat) (l : List T) :
    get? (new2dGmapAtN n l) (m, i) = if m = n then l[i]? else none := by
  apply get?_ofList_of_mem_iff
  intro t
  rw [mem_mapIdx_pair (fun i => (n, i))]
  constructor
  · rintro ⟨j, he, h⟩
    cases he
    simpa using h
  · intro h
    split at h
    · exact ⟨i, by simp_all, h⟩
    · cases h

@[rocq_alias iriswasm.new_2d_gmap_at_n_lookup]
theorem new_2d_gmap_at_n_lookup {T : Type} (n i : Nat) (l : List T) :
    get? (new2dGmapAtN n l) (n, i) = l[i]? := by
  rw [get?_new2dGmapAtN, ite_eq_left rfl]

@[rocq_alias iriswasm.new_2d_gmap_at_n_lookup_None]
theorem new_2d_gmap_at_n_lookup_None {T : Type} (n m i : Nat) (l : List T) (h : n ≠ m) :
    get? (new2dGmapAtN n l) (m, i) = none := by
  rw [get?_new2dGmapAtN, ite_eq_right (Ne.symm h)]

@[rocq_alias iriswasm.gmap_of_list_2d_offset_append_disjoint]
theorem gmap_of_list_2d_offset_append_disjoint {T : Type} (l : List (List T)) (l' : List T)
    (off k : Nat) (h : k ≥ l.length + off) :
    new2dGmapAtN k l' ##ₘ gmapOfList2dOffset l off := by
  refine (PartialMap.disjoint_iff _ _).2 fun ⟨n, i⟩ => ?_
  rw [get?_new2dGmapAtN, get?_gmapOfList2dOffset]
  by_cases hn : n = k
  · right
    rw [ite_eq_left (by omega), lookup2d, List.getElem?_eq_none (by omega)]
  · left
    rw [ite_eq_right hn]

@[rocq_alias iriswasm.gmap_of_list_2d_append_disjoint]
theorem gmap_of_list_2d_append_disjoint {T : Type} (l : List (List T)) (l' : List T) :
    new2dGmapAtN l.length l' ##ₘ gmapOfList2d l := by
  rw [gmap_of_list_2d_offset_0]
  exact gmap_of_list_2d_offset_append_disjoint _ _ _ _ (by omega)

@[rocq_alias iriswasm.gmap_of_list_2d_offset_append_general]
theorem gmap_of_list_2d_offset_append_general {T : Type} (l : List (List T)) (x : List T)
    (off : Nat) :
    gmapOfList2dOffset (l ++ [x]) off =
      new2dGmapAtN (l.length + off) x ∪ gmapOfList2dOffset l off := by
  apply LawfulPartialMap.equiv_iff_eq.1
  rintro ⟨n, i⟩
  rw [get?_union, get?_gmapOfList2dOffset', get?_new2dGmapAtN, get?_gmapOfList2dOffset']
  by_cases hn : n = l.length + off
  · subst hn
    cases hx : x[i]? <;> simp [hx]
  · rw [ite_eq_right hn]
    show _ = (if off ≤ n then l[n - off]?.bind (·[i]?) else none)
    split
    · rw [List.getElem?_append]
      split
      · rfl
      · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]
    · rfl

@[rocq_alias iriswasm.gmap_of_list_2d_append_general]
theorem gmap_of_list_2d_append_general {T : Type} (l : List (List T)) (x : List T) :
    gmapOfList2d (l ++ [x]) = new2dGmapAtN l.length x ∪ gmapOfList2d l := by
  rw [gmap_of_list_2d_offset_0, gmap_of_list_2d_offset_0, gmap_of_list_2d_offset_append_general,
    Nat.add_zero]

@[rocq_alias iriswasm.gmap_of_list_2d_append]
theorem gmap_of_list_2d_append {T : Type} (l : List (List T)) (len : Nat) (x : T) :
    gmapOfList2d (l ++ [List.replicate len x]) =
      new2dGmapAtN l.length (List.replicate len x) ∪ gmapOfList2d l :=
  gmap_of_list_2d_append_general _ _

@[rocq_alias iriswasm.gmap_of_list_2d_insert]
theorem gmap_of_list_2d_insert {T : Type} (n i : Nat) (x : T) (l : List (List T)) (t : List T)
    (hl : l[n]? = some t) (hlen : i < t.length) :
    insert (gmapOfList2d l) (n, i) x = gmapOfList2d (l.set n (t.set i x)) := by
  apply LawfulPartialMap.equiv_iff_eq.1
  rintro ⟨m, j⟩
  rw [get?_insert, gmap_of_list_2d_lookup, gmap_of_list_2d_lookup, List.getElem?_set]
  have hn : n < l.length := (List.getElem?_eq_some_iff.1 hl).1
  by_cases hm : n = m
  · subst hm
    simp only [hn, ite_true, hl, List.getElem?_set, hlen, Prod.mk.injEq, true_and]
  · simp [hm]

@[rocq_alias iriswasm.gmap_of_table_append_disjoint]
theorem gmap_of_table_append_disjoint (l : List Tableinst) (len : Nat) :
    new2dGmapAtN l.length (List.replicate len (none : Funcelem)) ##ₘ gmapOfTable l := by
  rw [gmapOfTable, ← List.length_map (f := tableToList)]
  exact gmap_of_list_2d_append_disjoint _ _

@[rocq_alias iriswasm.gmap_of_memory_append_disjoint]
theorem gmap_of_memory_append_disjoint (l : List Memory) (len : Nat) (initB : Byte) :
    new2dGmapAtN l.length (List.replicate len initB) ##ₘ gmapOfMemory l := by
  rw [gmapOfMemory, ← List.length_map (f := memoryToList)]
  exact gmap_of_list_2d_append_disjoint _ _

@[rocq_alias iriswasm.gmap_of_table_append]
theorem gmap_of_table_append (l : List Tableinst) (len : Nat) :
    gmapOfTable (l ++ [createTable len]) =
      new2dGmapAtN l.length (List.replicate len (none : Funcelem)) ∪ gmapOfTable l := by
  rw [gmapOfTable, gmapOfTable, ← List.length_map (f := tableToList), List.map_append]
  exact gmap_of_list_2d_append _ _ _

@[rocq_alias iriswasm.gmap_of_memory_append]
theorem gmap_of_memory_append (l : List Memory) (sz szLim : Nat) (initB : Byte) :
    gmapOfMemory (l ++ [createMemory sz szLim initB]) =
      new2dGmapAtN l.length (List.replicate sz initB) ∪ gmapOfMemory l := by
  rw [gmapOfMemory, gmapOfMemory, ← List.length_map (f := memoryToList), List.map_append]
  exact gmap_of_list_2d_append _ _ _

@[rocq_alias iriswasm.gmap_of_table_insert]
theorem gmap_of_table_insert (n i : Nat) (x : Funcelem) (l : List Tableinst) (t : Tableinst)
    (hl : l[n]? = some t) (hlen : i < t.data.length) :
    insert (gmapOfTable l) (n, i) x =
      gmapOfTable (l.set n { data := t.data.set i x, maxOpt := t.maxOpt }) := by
  rw [gmapOfTable, gmapOfTable, List.map_set]
  exact gmap_of_list_2d_insert _ _ _ _ t.data (by simp [hl, tableToList]) hlen

@[rocq_alias iriswasm.insert_take_drop]
theorem insert_take_drop {T : Type} (i : Nat) (l : List T) (x : T) (h : i < l.length) :
    l.set i x = l.take i ++ [x] ++ l.drop (i + 1) := by
  simp [List.set_eq_take_append_cons_drop, h]

@[rocq_alias iriswasm.gmap_of_memory_insert]
theorem gmap_of_memory_insert (n i : Nat) (x : Byte) (l : List Memory) (m : Memory)
    (md' : MemoryList) (hl : l[n]? = some m) (hlen : i < m.data.data.length)
    (hupd : MemoryList.memUpdate i x m.data = some md') :
    insert (gmapOfMemory l) (n, i) x =
      gmapOfMemory (l.set n { data := md', maxOpt := m.maxOpt }) := by
  simp only [MemoryList.memUpdate, hlen, ite_true, Option.some.injEq] at hupd
  subst hupd
  rw [gmapOfMemory, gmapOfMemory, List.map_set]
  rw [gmap_of_list_2d_insert _ _ _ _ m.data.data (by simp [hl, memoryToList]) hlen,
    insert_take_drop _ _ _ hlen]
  rfl

@[rocq_alias iriswasm.gmap_of_memory_insert_block]
theorem gmap_of_memory_insert_block (n : Nat) (m mem : Memory) (l : List Memory)
    (hmem : l[n]? = some mem) (hlen : m.data.data.length ≥ mem.data.data.length) :
    gmapOfMemory (l.set n m) = new2dGmapAtN n m.data.data ∪ gmapOfMemory l := by
  apply LawfulPartialMap.equiv_iff_eq.1
  rintro ⟨i, j⟩
  rw [gmapOfMemory, gmapOfMemory, get?_union, get?_gmapOfList2d, get?_gmapOfList2d,
    get?_new2dGmapAtN, List.map_set, List.getElem?_set]
  have hn : n < l.length := (List.getElem?_eq_some_iff.1 hmem).1
  by_cases hi : n = i
  · subst hi
    simp only [List.length_map, hn, ite_true, List.getElem?_map, hmem, Option.map_some,
      Option.bind_some, memoryToList]
    cases h : m.data.data[j]? with
    | some _ => rfl
    | none =>
      rw [List.getElem?_eq_none_iff] at h
      simp [List.getElem?_eq_none_iff.2 (Nat.le_trans hlen h)]
  · rw [ite_eq_right hi, ite_eq_right (Ne.symm hi)]
    rfl

@[rocq_alias iriswasm.length_mem_divisible]
theorem length_mem_divisible (m : MemoryList) (h : MlValid m) :
    m.lengthMem / pageSize * pageSize = m.lengthMem :=
  Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h)

@[rocq_alias iriswasm.mem_grow_data]
theorem mem_grow_data (m : Memory) (n : Nat) (m' : Memory) (h : memGrow m n = some m') :
    m'.data.data = m.data.data ++ List.replicate (n * pageSize) 0 := by
  unfold memGrow at h
  dsimp only at h
  split at h
  · split at h
    · split at h
      · cases h; rfl
      · cases h
    · cases h; rfl
  · cases h

@[rocq_alias iriswasm.mem_grow_length]
theorem mem_grow_length (m : Memory) (n : Nat) (m' : Memory) (h : memGrow m n = some m') :
    lengthMem m' = lengthMem m + n * pageSize := by
  simp [lengthMem, MemoryList.lengthMem, mem_grow_data m n m' h]

@[rocq_alias iriswasm.mem_grow_appendix]
def memGrowAppendix (m : Memory) (mn : Nat) (n : Nat) : NatPairMap Byte :=
  PartialMap.ofList ((List.replicate (n * pageSize) (0 : Byte)).mapIdx
    fun i x => ((mn, i + memSize m * pageSize), x))

private theorem get?_memGrowAppendix (m : Memory) (mn n i j : Nat) :
    get? (memGrowAppendix m mn n) (i, j) =
      if i = mn ∧ memSize m * pageSize ≤ j ∧ j < memSize m * pageSize + n * pageSize then
        some 0 else none := by
  apply get?_ofList_of_mem_iff
  intro b
  rw [mem_mapIdx_pair (fun k => (mn, k + memSize m * pageSize))]
  constructor
  · rintro ⟨k, he, hk⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    simp only [List.getElem?_replicate] at hk
    split at hk
    · cases hk; rw [ite_eq_left (by omega)]
    · cases hk
  · intro h
    split at h
    · cases h
      exact ⟨j - memSize m * pageSize, by simp; omega, by simp [List.getElem?_replicate]; omega⟩
    · cases h

private theorem memSize_mul_pageSize (m : Memory) (h : MlValid m.data) :
    memSize m * pageSize = m.data.data.length :=
  length_mem_divisible m.data h

@[rocq_alias iriswasm.mem_grow_appendix_disjoint]
theorem mem_grow_appendix_disjoint (m : Memory) (n : Nat) (mn : Nat) (m' : Memory)
    (mems : List Memory) (hlen : mn < mems.length) (hmem : mems[mn]? = some m)
    (hvalid : MlValid m.data) (_hgrow : memGrow m n = some m') :
    memGrowAppendix m mn n ##ₘ gmapOfMemory mems := by
  refine (PartialMap.disjoint_iff _ _).2 fun ⟨i, j⟩ => ?_
  rw [get?_memGrowAppendix, memSize_mul_pageSize m hvalid]
  split
  · right
    rename_i hc
    obtain ⟨rfl, hj, _⟩ := hc
    rw [gmapOfMemory, gmap_of_list_2d_lookup, List.getElem?_map, hmem]
    exact List.getElem?_eq_none hj
  · left; rfl

@[rocq_alias iriswasm.gmap_of_memory_grow]
theorem gmap_of_memory_grow (m : Memory) (n : Nat) (m' : Memory) (mn : Nat) (mems : List Memory)
    (hlen : mn < mems.length) (hmem : mems[mn]? = some m) (hvalid : MlValid m.data)
    (hgrow : memGrow m n = some m') :
    memGrowAppendix m mn n ∪ gmapOfMemory mems = gmapOfMemory (mems.set mn m') := by
  apply LawfulPartialMap.equiv_iff_eq.1
  rintro ⟨i, j⟩
  rw [get?_union, get?_memGrowAppendix, memSize_mul_pageSize m hvalid, gmapOfMemory,
    gmapOfMemory, get?_gmapOfList2d, get?_gmapOfList2d, List.map_set, List.getElem?_set]
  by_cases hi : mn = i
  · subst hi
    simp only [List.length_map, hlen, ite_true, true_and, List.getElem?_map, hmem,
      Option.map_some, Option.bind_some, memoryToList, mem_grow_data m n m' hgrow,
      List.getElem?_append, List.getElem?_replicate]
    by_cases hj : j < m.data.data.length
    · rw [ite_eq_right (by omega), ite_eq_left hj]; rfl
    · rw [ite_eq_right hj, show m.data.data[j]? = none from List.getElem?_eq_none (by omega)]
      split <;> split <;> first | rfl | omega
  · rw [ite_eq_right hi, ite_eq_right (by omega)]
    rfl

@[rocq_alias iriswasm.gmap_of_list_append_big]
theorem gmap_of_list_append_big {T : Type} (l1 l2 : List T) :
    let gtmap : NatMap T := PartialMap.ofList (l2.mapIdx fun i x => (l1.length + i, x))
    gmapOfList (l1 ++ l2) = gmapOfList l1 ∪ gtmap ∧ gmapOfList l1 ##ₘ gtmap := by
  intro gtmap
  have hg : ∀ k, get? gtmap k = if l1.length ≤ k then l2[k - l1.length]? else none := by
    intro k
    apply get?_ofList_of_mem_iff
    intro v
    rw [mem_mapIdx_pair (fun i => l1.length + i)]
    constructor
    · rintro ⟨i, rfl, h⟩
      simpa using h
    · intro h
      split at h
      · exact ⟨k - l1.length, by omega, h⟩
      · cases h
  constructor
  · apply LawfulPartialMap.equiv_iff_eq.1
    intro k
    rw [get?_union, hg, gmap_of_list_lookup, gmap_of_list_lookup, List.getElem?_append]
    by_cases hk : k < l1.length
    · rw [ite_eq_left hk, List.getElem?_eq_getElem hk]; rfl
    · rw [ite_eq_right hk, ite_eq_left (by omega), List.getElem?_eq_none (l := l1) (by omega)]
      rfl
  · refine (PartialMap.disjoint_iff _ _).2 fun k => ?_
    rw [hg, gmap_of_list_lookup]
    by_cases hk : l1.length ≤ k
    · left; exact List.getElem?_eq_none hk
    · right; rw [ite_eq_right hk]

@[rocq_alias iriswasm.gmap_of_list_2d_append_big]
theorem gmap_of_list_2d_append_big {T : Type} (l1 l2 : List (List T)) :
    let gtmap := gmapOfList2dOffset l2 l1.length
    gmapOfList2d (l1 ++ l2) = gmapOfList2d l1 ∪ gtmap ∧ gmapOfList2d l1 ##ₘ gtmap := by
  intro gtmap
  constructor
  · apply LawfulPartialMap.equiv_iff_eq.1
    rintro ⟨n, i⟩
    rw [get?_union, get?_gmapOfList2d, get?_gmapOfList2d, get?_gmapOfList2dOffset',
      List.getElem?_append]
    by_cases hk : n < l1.length
    · rw [ite_eq_left hk, ite_eq_right (by omega), List.getElem?_eq_getElem hk, Option.bind_some]
      cases l1[n][i]? <;> rfl
    · rw [ite_eq_right hk, ite_eq_left (by omega), List.getElem?_eq_none (l := l1) (by omega)]
      rfl
  · refine (PartialMap.disjoint_iff _ _).2 fun ⟨n, i⟩ => ?_
    rw [get?_gmapOfList2d, get?_gmapOfList2dOffset']
    by_cases hk : l1.length ≤ n
    · left; rw [List.getElem?_eq_none hk]; rfl
    · right; rw [ite_eq_right hk]

@[rocq_alias iriswasm.no_memory_no_memories]
theorem no_memory_no_memories (ws : StoreRecord) (n : Nat) (h : ws.mems[n]? = none) :
    ∀ k, get? (gmapOfMemory ws.mems) (n, k) = none := by
  intro k
  rw [gmapOfMemory, gmap_of_list_2d_lookup, List.getElem?_map, h]
  rfl

/-- Rewrite `get?` lookups of the store maps in hypotheses into list lookups. -/
@[rocq_alias iriswasm.simplify_lookup]
macro "simplify_lookup" : tactic =>
  `(tactic| simp only [gmapOfTable, gmapOfMemory, gmap_of_list_2d_lookup, gmap_of_list_lookup,
    List.getElem?_map] at *)

end IrisWasm
