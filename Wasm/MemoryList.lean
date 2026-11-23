/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import Wasm.Bytes
import Std.Data.ExtTreeMap.Lemmas

/-! Sparse linear memory. The list view is for specifications, not execution. -/

namespace Wasm

@[rocq_alias iriswasm.page_size]
def pageSize : Nat := 64 * 1024

namespace MemoryList

/-- Only deviations from the default are represented, at both levels of the page map. -/
abbrev SparseMap {α : Type} (z : α) := Std.ExtTreeMap Nat {v : α // v ≠ z}

variable {α : Type}

private def readMap {z : α} (t : SparseMap z) (i : Nat) : α :=
  match t[i]? with
  | some v => v.val
  | none => z

private def setMap {z : α} (t : SparseMap z) (i : Nat) (v : α) [Decidable (v = z)] :
    SparseMap z :=
  if h : v = z then t.erase i else t.insert i ⟨v, h⟩

private theorem readMap_setMap {z : α} (t : SparseMap z) (i j : Nat) (v : α)
    [Decidable (v = z)] : readMap (setMap t i v) j = if i = j then v else readMap t j := by
  by_cases hij : i = j <;> by_cases hv : v = z <;>
    simp [setMap, readMap, hv, hij, Std.ExtTreeMap.getElem?_erase, Std.ExtTreeMap.getElem?_insert]

private theorem sparseMap_ext {z : α} {s t : SparseMap z}
    (h : ∀ i, readMap s i = readMap t i) : s = t := by
  apply Std.ExtTreeMap.ext_getElem?
  intro i
  specialize h i
  unfold readMap at h
  cases hs : s[i]? <;> cases ht : t[i]? <;> simp_all [Subtype.ext_iff] <;>
    rename_i v <;> first | exact v.property h | exact v.property h.symm

abbrev Page := SparseMap (0 : Byte)
abbrev Pages := SparseMap (∅ : Page)

private instance (p : Page) : Decidable (p = ∅) := decidable_of_iff _ Std.ExtTreeMap.isEmpty_iff

private def cell (pages : Pages) (p k : Nat) : Byte := readMap (readMap pages p) k

private def byteAt (pages : Pages) (i : Nat) : Byte := cell pages (i / pageSize) (i % pageSize)

private def setByte (pages : Pages) (i : Nat) (b : Byte) : Pages :=
  let p := i / pageSize
  let pg := setMap (readMap pages p) (i % pageSize) b
  setMap pages p pg

private theorem cell_setByte (pages : Pages) (i p k : Nat) (b : Byte) :
    cell (setByte pages i b) p k =
      if i / pageSize = p ∧ i % pageSize = k then b else cell pages p k := by
  unfold cell setByte
  rw [readMap_setMap]
  split <;> rename_i h
  · subst p; simp [readMap_setMap]
  · simp [h]

private theorem byteAt_setByte (pages : Pages) (i j : Nat) (b : Byte) :
    byteAt (setByte pages i b) j = if i = j then b else byteAt pages j := by
  simp only [byteAt, cell_setByte]
  have e : (i / pageSize = j / pageSize ∧ i % pageSize = j % pageSize) ↔ i = j := by
    change (i / 65536 = j / 65536 ∧ i % 65536 = j % 65536) ↔ _; omega
  simp only [e]

private def Valid (pages : Pages) (len : Nat) : Prop :=
  ∀ p k, cell pages p k ≠ 0 → k < pageSize ∧ p * pageSize + k < len

private theorem valid_empty (n : Nat) : Valid ∅ n := by simp [Valid, cell, readMap]

private theorem Valid.weaken {pg : Pages} {n m : Nat} (h : Valid pg n) (hle : n ≤ m) :
    Valid pg m := fun p k hn ↦ ⟨(h p k hn).1, Nat.lt_of_lt_of_le (h p k hn).2 hle⟩

private theorem Valid.set {pg : Pages} {len i : Nat} (h : Valid pg len) (hi : i < len) (b : Byte) :
    Valid (setByte pg i b) len := by
  intro p k hn
  rw [cell_setByte] at hn
  split at hn
  · obtain ⟨rfl, rfl⟩ := ‹_ ∧ _›
    simp only [pageSize] at *; omega
  · exact h p k hn

end MemoryList

@[rocq_alias iriswasm.memory_list]
structure MemoryList where
  lengthMem : Nat
  pages : MemoryList.Pages
  private valid : MemoryList.Valid pages lengthMem
  deriving DecidableEq, Repr

attribute [rocq_alias iriswasm.memory_list.length_mem] MemoryList.lengthMem

#rocq_ignore iriswasm.memory_list_eq_dec "deriving DecidableEq"
#rocq_ignore iriswasm.memory_list_eqb "deriving DecidableEq"
#rocq_ignore iriswasm.eqmemory_listP "deriving DecidableEq"

namespace MemoryList

private def zeros (n : Nat) : MemoryList := ⟨n, ∅, valid_empty n⟩

instance : Inhabited MemoryList := ⟨zeros 0⟩

@[rocq_alias iriswasm.memory_list.mem_grow]
def memGrow (lenDelta : Nat) (ml : MemoryList) : MemoryList :=
  ⟨ml.lengthMem + lenDelta, ml.pages, ml.valid.weaken (by omega)⟩

@[rocq_alias iriswasm.mem_lookup]
def memLookup (i : Nat) (ml : MemoryList) : Option Byte :=
  if i < ml.lengthMem then some (byteAt ml.pages i) else none

@[rocq_alias iriswasm.mem_update]
def memUpdate (i : Nat) (v : Byte) (ml : MemoryList) : Option MemoryList :=
  if h : i < ml.lengthMem then some ⟨ml.lengthMem, setByte ml.pages i v, ml.valid.set h v⟩
  else none

/-- The extensional list view; its length is independent of the number of allocated pages. -/
def data (ml : MemoryList) : List Byte := List.ofFn (n := ml.lengthMem) fun i ↦ byteAt ml.pages i

@[simp] theorem length_data (ml : MemoryList) : ml.data.length = ml.lengthMem := by simp [data]

@[simp] theorem data_getElem? (ml : MemoryList) (i : Nat) : ml.data[i]? = ml.memLookup i := by
  simp [data, memLookup, List.getElem?_ofFn]

private theorem byteAt_oob (ml : MemoryList) (i : Nat) (h : ml.lengthMem ≤ i) :
    byteAt ml.pages i = 0 := by
  apply Classical.byContradiction; intro hn
  have := (ml.valid _ _ hn).2
  simp only [pageSize] at *; omega

private theorem lookup_pageOffset (ml : MemoryList) (p k : Nat) (hk : k < pageSize) :
    (ml.memLookup (p * pageSize + k)).getD 0 = cell ml.pages p k := by
  unfold memLookup
  split <;> rename_i h
  · simp only [Option.getD_some, byteAt]
    rw [show (p * pageSize + k) / pageSize = p by simp only [pageSize] at *; omega,
      show (p * pageSize + k) % pageSize = k by simp only [pageSize] at *; omega]
  · symm; apply Classical.byContradiction; intro hb; exact h (ml.valid _ _ hb).2

theorem stored_byte_bounds (ml : MemoryList) {p k : Nat} {pg b}
    (hp : ml.pages[p]? = some pg) (hk : pg.val[k]? = some b) :
    k < pageSize ∧ p * pageSize + k < ml.lengthMem :=
  ml.valid p k (by simpa [cell, readMap, hp, hk] using b.property)

theorem page_absent_iff (ml : MemoryList) (p : Nat) :
    ml.pages[p]? = none ↔ ∀ k < pageSize, (ml.memLookup (p * pageSize + k)).getD 0 = 0 := by
  constructor
  · intro hp k hk; rw [lookup_pageOffset _ _ _ hk]; simp [cell, readMap, hp]
  · intro h
    cases hp : ml.pages[p]? with
    | none => rfl
    | some pg =>
      exfalso; apply pg.property
      apply sparseMap_ext; intro k
      have e : cell ml.pages p k = 0 := by
        by_cases hk : k < pageSize
        · rw [← lookup_pageOffset _ _ _ hk]; exact h k hk
        · apply Classical.byContradiction; intro hb; exact hk (ml.valid _ _ hb).1
      simpa [cell, readMap, hp] using e

@[ext] theorem ext {m n : MemoryList} (hlen : m.lengthMem = n.lengthMem)
    (h : ∀ i, m.memLookup i = n.memLookup i) : m = n := by
  have hp : m.pages = n.pages := by
    apply sparseMap_ext; intro p
    apply sparseMap_ext; intro k
    change cell m.pages p k = cell n.pages p k
    by_cases hk : k < pageSize
    · rw [← lookup_pageOffset m p k hk, ← lookup_pageOffset n p k hk, h]
    · have hm : cell m.pages p k = 0 := by
        apply Classical.byContradiction; intro hb; exact hk (m.valid _ _ hb).1
      have hn : cell n.pages p k = 0 := by
        apply Classical.byContradiction; intro hb; exact hk (n.valid _ _ hb).1
      rw [hm, hn]
  cases m; cases n; cases hlen; cases hp; rfl

theorem ext_data {m n : MemoryList} (h : m.data = n.data) : m = n := by
  apply ext
  · simpa using congrArg List.length h
  · intro i; simpa using congrArg (fun bs : List Byte ↦ bs[i]?) h

theorem ext_lookup {m n : MemoryList} (h : ∀ i, m.memLookup i = n.memLookup i) : m = n :=
  ext_data (List.ext_getElem? fun i ↦ by simpa only [data_getElem?] using h i)

theorem data_grow (ml : MemoryList) (n : Nat) :
    (ml.memGrow n).data = ml.data ++ List.replicate n 0 := by
  apply List.ext_getElem?; intro i
  by_cases hi : i < ml.lengthMem
  · rw [List.getElem?_append_left (by simpa using hi)]
    rw [data_getElem?, data_getElem?]
    simp [memLookup, memGrow, hi, show i < ml.lengthMem + n by omega]
  · rw [List.getElem?_append_right (by simp; omega)]
    simp [memLookup, memGrow, byteAt_oob ml i (by omega), List.getElem?_replicate]
    split <;> split <;> first | rfl | omega

theorem data_update {ml ml' : MemoryList} {i : Nat} {b : Byte} (h : ml.memUpdate i b = some ml') :
    ml'.data = ml.data.set i b := by
  unfold memUpdate at h
  split at h <;> simp_all only [Option.some.injEq, reduceCtorEq]
  subst ml'
  apply List.ext_getElem?; intro j
  by_cases he : i = j
  · subst j
    rw [data_getElem?, List.getElem?_set_self (by simpa using ‹i < ml.lengthMem›)]
    simp [memLookup, byteAt_setByte, *]
  · rw [List.getElem?_set_ne he]
    simp [memLookup, byteAt_setByte, he]

private def writeFrom (pg : Pages) (i : Nat) : List Byte → Pages
  | [] => pg
  | b :: bs => writeFrom (setByte pg i b) (i + 1) bs

private theorem Valid.writeFrom {pg : Pages} {len : Nat} (bs : List Byte) (i : Nat)
    (h : Valid pg len) (hi : i + bs.length ≤ len) : Valid (writeFrom pg i bs) len := by
  induction bs generalizing pg i with
  | nil => exact h
  | cons b bs ih =>
    simp only [List.length_cons] at hi
    exact ih (i + 1) (h.set (by omega) b) (by omega)

private theorem byteAt_writeFrom (bs : List Byte) (pg : Pages) (i j : Nat) :
    byteAt (writeFrom pg i bs) j =
      if i ≤ j then bs[j - i]?.getD (byteAt pg j) else byteAt pg j := by
  induction bs generalizing pg i with
  | nil => simp [writeFrom]
  | cons b bs ih =>
    rw [writeFrom, ih, byteAt_setByte]
    by_cases he : i = j
    · subst j; simp [show ¬i + 1 ≤ i by omega]
    · by_cases h : i < j
      · have e : j - i = (j - (i + 1)) + 1 := by omega
        simp [Nat.le_of_lt h, show i + 1 ≤ j by omega, he, e]
      · simp [show ¬i ≤ j by omega, show ¬i + 1 ≤ j by omega, he]

/-- The original list splice clamps starts past the end and extends only by the overhang. -/
def splice (ml : MemoryList) (off : Nat) (bs : List Byte) : MemoryList :=
  let start := min off ml.lengthMem
  let len := max ml.lengthMem (start + bs.length)
  ⟨len, writeFrom ml.pages start bs,
    (ml.valid.weaken (Nat.le_max_left ..)).writeFrom bs start (Nat.le_max_right ..)⟩

theorem data_splice (ml : MemoryList) (off : Nat) (bs : List Byte) :
    (ml.splice off bs).data = ml.data.take off ++ bs ++ ml.data.drop (off + bs.length) := by
  apply List.ext_getElem?; intro i
  simp only [List.getElem?_append, List.length_append, List.length_take, length_data,
    List.getElem?_take, List.getElem?_drop, data_getElem?, splice, memLookup, byteAt_writeFrom]
  let start := min off ml.lengthMem
  change (if i < max ml.lengthMem (start + bs.length) then
      some (if start ≤ i then bs[i - start]?.getD (byteAt ml.pages i) else byteAt ml.pages i)
      else none) = _
  by_cases ha : i < start
  · have ho : i < off := Nat.lt_of_lt_of_le ha (Nat.min_le_left ..)
    have hm : i < ml.lengthMem := Nat.lt_of_lt_of_le ha (Nat.min_le_right ..)
    have ht : i < min off ml.lengthMem + bs.length := by omega
    simp only [ite_eq_left ht, ite_eq_left (show i < min off ml.lengthMem from ha),
      ite_eq_left ho, ite_eq_left hm, ite_eq_right (show ¬start ≤ i by omega),
      ite_eq_left (show i < max ml.lengthMem (start + bs.length) by omega)]
  · by_cases hb : i < start + bs.length
    · have hj : i - start < bs.length := by omega
      rw [ite_eq_left (by omega), ite_eq_left (by omega), List.getElem?_eq_getElem hj]
      simp only [Option.getD_some]
      simp only [ite_eq_left (show i < min off ml.lengthMem + bs.length from hb),
        ite_eq_right (show ¬i < min off ml.lengthMem from ha)]
    · have hj : bs[i - start]? = none := List.getElem?_eq_none (by omega)
      rw [ite_eq_right (show ¬i < min off ml.lengthMem + bs.length from hb)]
      simp only [show start ≤ i by omega, ↓reduceIte, hj, Option.getD_none]
      by_cases ho : off ≤ ml.lengthMem
      · have he : start = off := Nat.min_eq_left ho
        have ei : off + bs.length + (i - (min off ml.lengthMem + bs.length)) = i := by
          rw [Nat.min_eq_left ho]; omega
        rw [ei]
        by_cases hm : i < ml.lengthMem <;> simp [hm] <;> omega
      · have he : start = ml.lengthMem := Nat.min_eq_right (by omega)
        have hi : ¬i < max ml.lengthMem (start + bs.length) := by omega
        rw [ite_eq_right hi, ite_eq_right (by omega)]

def ofBytes (bs : List Byte) : MemoryList := (zeros 0).splice 0 bs

@[simp] theorem data_ofBytes (bs : List Byte) : (ofBytes bs).data = bs := by
  rw [ofBytes, data_splice]
  simp [data, zeros]

@[simp] theorem ofBytes_data (ml : MemoryList) : ofBytes ml.data = ml := ext_data (by simp)

@[simp] theorem length_ofBytes (bs : List Byte) : (ofBytes bs).lengthMem = bs.length := by
  rw [← length_data, data_ofBytes]

theorem update_eq (ml : MemoryList) (i : Nat) (b : Byte) :
    ml.memUpdate i b = if i < ml.lengthMem then some (ofBytes (ml.data.set i b)) else none := by
  by_cases hi : i < ml.lengthMem
  · rw [ite_eq_left hi]
    generalize he : ml.memUpdate i b = o
    cases o with
    | none => simp [memUpdate, hi] at he
    | some m => exact congrArg some (ext_data (by rw [data_ofBytes, data_update he]))
  · simp [memUpdate, hi]

variable {α : Type}

private def fillKeys {z : α} (v : {v : α // v ≠ z}) (t : SparseMap z) : Nat → SparseMap z
  | 0 => t
  | n + 1 => fillKeys v (t.insert n v) n

private theorem readMap_fillKeys {z : α} (v : {v : α // v ≠ z}) (t : SparseMap z) (n i : Nat) :
    readMap (fillKeys v t n) i = if i < n then v.val else readMap t i := by
  induction n generalizing t with
  | zero => simp [fillKeys]
  | succ n ih =>
    rw [fillKeys, ih]
    by_cases hl : i < n
    · simp [hl, show i < n + 1 by omega]
    · by_cases he : n = i
      · subst i; simp [readMap]
      · simp [hl, he, show ¬i < n + 1 by omega, readMap, Std.ExtTreeMap.getElem?_insert]

private def filledMap {z : α} (n : Nat) (v : α) [Decidable (v = z)] : SparseMap z :=
  if h : v = z then ∅ else fillKeys ⟨v, h⟩ ∅ n

private theorem readMap_filledMap {z : α} (n i : Nat) (v : α) [Decidable (v = z)] :
    readMap (filledMap n v : SparseMap z) i = if i < n then v else z := by
  by_cases h : v = z
  · simp [filledMap, h, readMap]
  · simp only [filledMap, dite_eq_right h, readMap_fillKeys]; simp [readMap]

-- All complete nonzero pages share one immutable byte map.
private def fullPages (b : Byte) : Nat → Pages
  | 0 => ∅
  | n + 1 => filledMap (n + 1) (filledMap pageSize b)

private theorem readMap_fullPages (b : Byte) (n p : Nat) :
    readMap (fullPages b n) p = if p < n then (filledMap pageSize b : Page) else ∅ := by
  cases n with
  | zero => simp [fullPages, readMap]
  | succ n => exact readMap_filledMap ..

private def makePages (b : Byte) (n : Nat) : Pages :=
  setMap (fullPages b (n / pageSize)) (n / pageSize) (filledMap (n % pageSize) b)

private theorem cell_makePages (b : Byte) (n p k : Nat) :
    cell (makePages b n) p k = if k < pageSize ∧ p * pageSize + k < n then b else 0 := by
  simp only [cell, makePages, readMap_setMap, readMap_fullPages]
  split <;> rename_i he
  · rw [readMap_filledMap]
    split <;> split <;> first | rfl | (simp only [pageSize] at *; omega)
  · split <;> rename_i hl
    · rw [readMap_filledMap]
      split <;> split <;> first | rfl | (simp only [pageSize] at *; omega)
    · simp [readMap, show ¬(k < pageSize ∧ p * pageSize + k < n) by simp only [pageSize] at *; omega]

@[rocq_alias iriswasm.mem_make]
def memMake (v : Byte) (len : Nat) : MemoryList :=
  if v = 0 then zeros len else
    ⟨len, makePages v len, fun p k hn ↦ by
      rw [cell_makePages] at hn; split at hn <;> simp_all⟩

@[simp] theorem length_make (b : Byte) (n : Nat) : (memMake b n).lengthMem = n := by
  unfold memMake; split <;> rfl

@[simp] theorem length_grow (ml : MemoryList) (n : Nat) :
    (ml.memGrow n).lengthMem = ml.lengthMem + n := rfl

theorem data_make (b : Byte) (n : Nat) : (memMake b n).data = List.replicate n b := by
  apply List.ext_getElem?; intro i
  rw [data_getElem?, memLookup, length_make, List.getElem?_replicate]
  split <;> rename_i hi
  · unfold memMake
    split <;> rename_i hb
    · subst b; simp [zeros, byteAt, cell, readMap]
    · simp [byteAt, cell_makePages, show i % pageSize < pageSize by exact Nat.mod_lt _ (by decide),
        show i / pageSize * pageSize + i % pageSize < n by simp only [pageSize] at *; omega]
  · rfl

@[rocq_alias iriswasm.nth_repeat]
theorem nth_repeat {A : Type _} (b : A) (i len : Nat) (h : i < len) :
    (List.replicate len b)[i]? = some b := by
  simp [h]

@[rocq_alias iriswasm.lookup_split]
theorem lookup_split {A : Type _} (l : List A) (i : Nat) (b : A) (h : i < l.length) :
    (l.take i ++ b :: l.drop (i + 1))[i]? = some b := by
  rw [List.getElem?_append_right] <;> simp [Nat.min_eq_left (Nat.le_of_lt h)]

@[rocq_alias iriswasm.bar]
theorem bar {A : Type _} (n n' : Nat) (l : List A) (v : A) (hne : n ≠ n')
    (h : n' < l.length) : (l.take n' ++ v :: l.drop (n' + 1))[n]? = l[n]? := by
  have : l.take n' ++ v :: l.drop (n' + 1) = l.set n' v := by
    rw [List.set_eq_take_append_cons_drop]; simp [h]
  rw [this, List.getElem?_set_ne (Ne.symm hne)]

@[rocq_alias iriswasm.split_preserves_length]
theorem split_preserves_length {A : Type _} (i : Nat) (b : A) (l : List A) (h : i < l.length) :
    (l.take i ++ b :: l.drop (i + 1)).length = l.length := by
  simp; omega

@[rocq_alias iriswasm.memory_list_ax_lookup_out_of_bounds]
theorem memory_list_ax_lookup_out_of_bounds (mem : MemoryList) (i : Nat) (h : i ≥ mem.lengthMem) :
    mem.memLookup i = none := by
  simp [memLookup, Nat.not_lt_of_ge h]

@[rocq_alias iriswasm.memory_list_ax_lookup_make]
theorem memory_list_ax_lookup_make (i len : Nat) (b : Byte) (h : i < len) :
    (memMake b len).memLookup i = some b := by
  rw [← data_getElem?, data_make, List.getElem?_replicate_of_lt h]

@[rocq_alias iriswasm.memory_list_ax_lookup_update]
theorem memory_list_ax_lookup_update (mem mem' : MemoryList) (i : Nat) (b : Byte)
    (h : i < mem.lengthMem) (h' : some mem' = mem.memUpdate i b) : mem'.memLookup i = some b := by
  rw [← data_getElem?, data_update h'.symm, List.getElem?_set_self (by simpa using h)]

@[rocq_alias iriswasm.memory_list_ax_lookup_skip]
theorem memory_list_ax_lookup_skip (mem mem' : MemoryList) (i i' : Nat) (b : Byte) (hne : i ≠ i')
    (h' : some mem' = mem.memUpdate i' b) : mem'.memLookup i = mem.memLookup i := by
  rw [← data_getElem?, data_update h'.symm, List.getElem?_set_ne hne.symm, data_getElem?]

@[rocq_alias iriswasm.memory_list_ax_length_constant_update]
theorem memory_list_ax_length_constant_update (i : Nat) (b : Byte) (mem mem' : MemoryList)
    (h' : some mem' = mem.memUpdate i b) : mem'.lengthMem = mem.lengthMem := by
  rw [← length_data, data_update h'.symm, List.length_set, length_data]

end MemoryList

end Wasm
