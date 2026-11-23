/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import Wasm.TypePreservation
import IrisWasm.Language.IrisWpDef
import IrisWasm.Language.IrisAtomicity
import IrisWasm.Helpers.IrisWasmDeterm
import IrisWasm.Helpers.Prelude.FirstInstr

/-! Port of `theories/iris/rules/iris_rules_resources.v`: rules for locals, globals and linear
memory, plus the memory-list lemmas they rely on. -/

namespace IrisWasm

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm

#rocq_ignore iriswasm.iris_rules_resources.those_app "re-export of list_extra.v's `those_app`; use `Wasm.those_app`"
#rocq_ignore iriswasm.iris_rules_resources.those_app_inv "re-export of list_extra.v's `those_app_inv`; use `Wasm.those_app_inv`"
#rocq_ignore iriswasm.iris_rules_resources.reducible "use `Language.Reducible`"

/-! ## Memory-list lemmas -/

/-- Pointwise proof of a list equation built from `take`/`drop`/`++`. -/
local macro "list_ext" : tactic => `(tactic| (
  apply List.ext_getElem?; intro j
  simp only [List.getElem?_append, List.getElem?_take, List.getElem?_drop, List.length_append,
    List.length_take, List.length_drop, List.length_cons, List.length_nil, List.getElem?_cons]
  grind))

private theorem foldl_memUpdate {F : Nat × Option MemoryList → Byte → Nat × Option MemoryList}
    (start : Nat)
    (hF : ∀ k o x, F (k, o) x =
      (k + 1, match o with | none => none | some dat => dat.memUpdate (start + k) x)) :
    ∀ (bs : Bytes) (i : Nat) (d : MemoryList), start + i + bs.length ≤ d.data.length →
      bs.foldl F (i, some d) = (i + bs.length, some (MemoryList.ofBytes
        (d.data.take (start + i) ++ bs ++ d.data.drop (start + i + bs.length))))
  | [], i, d, _ => by simp
  | b :: bs, i, d, h => by
    simp only [List.length_cons] at h
    rw [List.foldl_cons, hF]
    have hi : start + i < d.data.length := by omega
    dsimp only
    rw [MemoryList.update_eq, if_pos (by simpa only [MemoryList.length_data] using hi)]
    rw [foldl_memUpdate start hF bs (i + 1) _ (by
      simp only [MemoryList.data_ofBytes, List.length_set]; omega)]
    simp only [List.length_cons, Option.some.injEq, Prod.mk.injEq, MemoryList.data_ofBytes]
    refine ⟨by omega, congrArg MemoryList.ofBytes ?_⟩
    rw [List.set_eq_take_append_cons_drop]
    simp only [hi, ↓reduceIte]
    rw [← Nat.add_assoc]
    list_ext

theorem writeBytes_eq (m : Memory) (start : Nat) (bs : Bytes)
    (h : start + bs.length ≤ m.data.data.length) :
    writeBytes m start bs = some ⟨MemoryList.ofBytes (m.data.data.take start ++ bs ++
      m.data.data.drop (start + bs.length)), m.type⟩ := by
  unfold writeBytes foldLefti
  rw [foldl_memUpdate start (fun _ _ _ => rfl) bs 0 m.data (by simpa using h)]
  simp

/-- `store` in closed form. -/
theorem store_eq (m : Memory) (n : Nat) (off : StaticOffset) (bs : Bytes) (l : Nat) :
    store m n off bs l = if n + off + l ≤ lengthMem m then
      some ⟨MemoryList.ofBytes (m.data.data.take (n + off) ++ bytesTakefill 0 l bs ++
        m.data.data.drop (n + off + l)), m.type⟩ else none := by
  unfold store
  split
  · rename_i hb
    rw [writeBytes_eq _ _ _ (by simpa only [length_bytesTakefill, lengthMem_eq_data_length] using hb)]
    simp [length_bytesTakefill]
  · rfl

private theorem those_map_some {A : Type} (l : List A) : those (l.map some) = some l := by
  rw [← those_those0]
  induction l with
  | nil => rfl
  | cons a l ih => simp [those0, ih]

/-- `load` in closed form. -/
theorem load_eq (m : Memory) (n : Nat) (off : StaticOffset) (l : Nat) :
    load m n off l = if n + (off + l) ≤ lengthMem m then
      some ((m.data.data.drop (n + off)).take l) else none := by
  unfold load
  split
  · rename_i h
    rw [lengthMem_eq_data_length] at h
    unfold readBytes
    rw [← those_map_some]
    congr 1
    apply List.ext_getElem? ; intro j
    simp only [List.getElem?_map, List.getElem?_take, List.getElem?_drop, ← MemoryList.data_getElem?]
    grind
  · rfl


@[rocq_alias iriswasm.mem_update_length]
theorem mem_update_length (dat dat' : MemoryList) (k : Nat) (b : Byte)
    (h : MemoryList.memUpdate k b dat = some dat') : dat.data.length = dat'.data.length := by
  have hd : dat'.data = dat.data.set k b := by apply MemoryList.data_update; exact h
  simp only [hd, List.length_set]

@[rocq_alias iriswasm.length_store]
theorem length_store (m m' : Memory) (n : Nat) (off : StaticOffset) (bs : Bytes)
    (h : store m n off bs bs.length = some m') : m.data.data.length = m'.data.data.length := by
  rw [store_eq] at h
  split at h
  · cases h; simp only [MemoryList.data_ofBytes, lengthMem_eq_data_length, List.length_append,
      List.length_take, List.length_drop, length_bytesTakefill] at *; omega
  · cases h

#rocq_ignore iriswasm.store_mem_max_opt "writes preserve the complete memory type"
theorem store_mem_type (m m' : Memory) (n : Nat) (off : StaticOffset) (bs : Bytes) (l : Nat)
    (h : store m n off bs l = some m') : m.type = m'.type := by
  rw [store_eq] at h
  split at h
  · cases h; rfl
  · cases h

@[rocq_alias iriswasm.map_iota_lift]
theorem map_iota_lift {A : Type} (f g : Nat → A) (n len : Nat) (h : ∀ x, f (x + 1) = g x) :
    (List.range' (n + 1) len).map f = (List.range' n len).map g := by
  induction len generalizing n with
  | zero => rfl
  | succ len ih => simp [List.range'_succ, h, ← ih]

@[rocq_alias iriswasm.load_append]
theorem load_append (m : Memory) (k : Nat) (off : StaticOffset) (b : Byte) (bs : Bytes)
    (h : load m k off (b :: bs).length = some (b :: bs)) :
    load m k (off + 1) bs.length = some bs := by
  rw [load_eq] at h ⊢
  simp only [List.length_cons] at h
  split at h
  · simp only [Option.some.injEq] at h
    rw [ite_eq_left (by omega)]
    have h2 := congrArg (List.drop 1) h
    rw [List.drop_take, List.drop_drop] at h2
    simpa [Nat.add_assoc, Nat.add_comm 1] using h2
  · cases h

@[rocq_alias iriswasm.list_trivial_replace]
theorem list_trivial_replace {A : Type} (l : List A) (x : A) (k : Nat) (h : l[k]? = some x) :
    l.take k ++ ([x] ++ l.drop (k + 1)) = l := by
  obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.1 h
  rw [List.singleton_append, ← List.drop_eq_getElem_cons hk, List.take_append_drop]

@[rocq_alias iriswasm.trivial_update]
theorem trivial_update (m : Memory) (k : Nat) (b : Byte) (h : readBytes m k 1 = some [b]) :
    MemoryList.memUpdate k b m.data = some m.data := by
  simp only [readBytes, List.range_one, List.map_cons, List.map_nil, Nat.add_zero] at h
  rw [← those_those0] at h
  rw [← MemoryList.data_getElem?] at h
  cases hk : m.data.data[k]? with
  | none => simp [hk, those0] at h
  | some x =>
    simp only [hk, those0, Option.map_some, Option.some.injEq, List.cons.injEq, and_true] at h
    subst h
    have hlt : k < m.data.data.length := (List.getElem?_eq_some_iff.1 hk).1
    rw [MemoryList.update_eq, if_pos (by simpa only [MemoryList.length_data] using hlt),
      insert_take_drop _ _ _ hlt, List.append_assoc, list_trivial_replace _ _ _ hk,
      MemoryList.ofBytes_data]

@[rocq_alias iriswasm.incr_fst]
def incrFst {A : Type} (a : Nat × A) : Nat × A := (a.1 + 1, a.2)

@[rocq_alias iriswasm.incr_fst_equals]
theorem incr_fst_equals {A : Type} (x : Nat × A) (n : Nat) (o : A) (h : incrFst x = (n, o)) :
    x = (n - 1, o) := by
  obtain ⟨a, b⟩ := x
  simp only [incrFst, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp

@[rocq_alias iriswasm.fold_left_lift]
theorem fold_left_lift {A B : Type} (f g : Nat × A → B → Nat × A) (l : List B) (i : Nat)
    (acc : A) (h : ∀ i acc x, f (i + 1, acc) x = incrFst (g (i, acc) x)) :
    l.foldl f (i + 1, acc) = incrFst (l.foldl g (i, acc)) := by
  induction l generalizing i acc with
  | nil => rfl
  | cons x l ih =>
    simp only [List.foldl_cons, h]
    exact ih _ _

@[rocq_alias iriswasm.store_append1]
theorem store_append1 (m : Memory) (k : Nat) (off : StaticOffset) (b : Byte) (bs : Bytes)
    (m' : Memory) (h : store m k off (b :: bs) (b :: bs).length = some m') :
    ∃ m'', store m'' k (off + 1) bs bs.length = some m' ∧ store m k off [b] 1 = some m'' := by
  rw [store_eq] at h
  split at h
  · rename_i hle
    cases h
    simp only [lengthMem_eq_data_length, List.length_cons] at hle
    refine ⟨_, ?_, by rw [store_eq, ite_eq_left (by rw [lengthMem_eq_data_length]; omega)]⟩
    rw [store_eq, ite_eq_left (by
      simp only [lengthMem_eq_data_length, MemoryList.data_ofBytes, List.length_take,
        List.length_append, List.length_drop, length_bytesTakefill]; omega)]
    simp only [bytesTakefill, bytesTakefill_of_length, List.length_cons, Option.some.injEq,
      Memory.mk.injEq, and_true, MemoryList.data_ofBytes]
    apply congrArg MemoryList.ofBytes
    list_ext
  · cases h


theorem store_some_iff {m m' : Memory} {n : Nat} {off : StaticOffset} {bs : Bytes} {l : Nat} :
    store m n off bs l = some m' ↔ n + off + l ≤ m.data.data.length ∧
      m' = ⟨MemoryList.ofBytes (m.data.data.take (n + off) ++ bytesTakefill 0 l bs ++
        m.data.data.drop (n + off + l)), m.type⟩ := by
  rw [store_eq, lengthMem_eq_data_length]
  split <;> simp_all [eq_comm] <;> omega

theorem load_some_iff {m : Memory} {n : Nat} {off : StaticOffset} {l : Nat} {bs : Bytes} :
    load m n off l = some bs ↔ n + (off + l) ≤ m.data.data.length ∧
      (m.data.data.drop (n + off)).take l = bs := by
  rw [load_eq, lengthMem_eq_data_length]
  split <;> simp_all <;> omega

@[rocq_alias iriswasm.enough_space_to_store]
theorem enough_space_to_store (m : Memory) (k : Nat) (off : StaticOffset) (bs : Bytes)
    (h : k + off + bs.length ≤ lengthMem m) : ∃ mf, store m k off bs bs.length = some mf :=
  ⟨_, store_some_iff.2 ⟨by rwa [← lengthMem_eq_data_length], rfl⟩⟩

private theorem memUpdate_eq_set {i : Nat} {v : Byte} {ml : MemoryList} (h : i < ml.data.length) :
    MemoryList.memUpdate i v ml = some (MemoryList.ofBytes (ml.data.set i v)) := by
  rw [MemoryList.update_eq, if_pos (by simpa only [MemoryList.length_data] using h)]

@[rocq_alias iriswasm.mem_update_insert]
theorem mem_update_insert (k : Nat) (b : Byte) (dat dat' : MemoryList)
    (h : MemoryList.memUpdate k b dat = some dat') :
    dat' = MemoryList.ofBytes (dat.data.set k b) ∧ k < dat.data.length := by
  rw [MemoryList.update_eq] at h
  split at h
  · exact ⟨(Option.some.inj h).symm, by simpa only [MemoryList.length_data] using ‹k < _›⟩
  · cases h

@[rocq_alias iriswasm.update_swap]
theorem update_swap (k : Nat) (b : Byte) (dat : MemoryList) (k' : Nat) (b' : Byte)
    (dat' dat'' : MemoryList) (hne : k ≠ k') (h : MemoryList.memUpdate k b dat = some dat')
    (h' : MemoryList.memUpdate k' b' dat' = some dat'') :
    ∃ dat0, MemoryList.memUpdate k' b' dat = some dat0 ∧ MemoryList.memUpdate k b dat0 = some dat'' := by
  obtain ⟨rfl, hk⟩ := mem_update_insert _ _ _ _ h
  obtain ⟨rfl, hk'⟩ := mem_update_insert _ _ _ _ h'
  simp only [MemoryList.data_ofBytes, List.length_set] at hk'
  refine ⟨_, memUpdate_eq_set hk', ?_⟩
  rw [memUpdate_eq_set (by simpa only [MemoryList.data_ofBytes, List.length_set] using hk)]
  simp only [MemoryList.data_ofBytes, List.set_comm _ _ hne]

@[rocq_alias iriswasm.swap_stores]
theorem swap_stores (m m' m'' : Memory) (k : Nat) (off : StaticOffset) (b : Byte) (bs : Bytes)
    (h : store m k off [b] 1 = some m') (h' : store m' k (off + 1) bs bs.length = some m'') :
    ∃ m0, store m k (off + 1) bs bs.length = some m0 ∧ store m0 k off [b] 1 = some m'' := by
  obtain ⟨h1, rfl⟩ := store_some_iff.1 h
  obtain ⟨h2, rfl⟩ := store_some_iff.1 h'
  simp only [MemoryList.data_ofBytes, List.length_append, List.length_take, List.length_drop, bytesTakefill,
    bytesTakefill_of_length, List.length_cons, List.length_nil] at h1 h2 ⊢
  refine ⟨_, store_some_iff.2 ⟨by omega, rfl⟩,
    store_some_iff.2 ⟨by simp only [MemoryList.data_ofBytes, List.length_append, List.length_take,
      List.length_drop, length_bytesTakefill]; omega, ?_⟩⟩
  simp only [bytesTakefill, bytesTakefill_of_length, Memory.mk.injEq, MemoryList.data_ofBytes, and_true]
  apply congrArg MemoryList.ofBytes
  list_ext

@[rocq_alias iriswasm.store_trivial]
theorem store_trivial (m : Memory) (k : Nat) (off : StaticOffset) (bs : Bytes)
    (h : load m k off bs.length = some bs) : store m k off bs bs.length = some m := by
  obtain ⟨h1, h2⟩ := load_some_iff.1 h
  refine store_some_iff.2 ⟨by omega, ?_⟩
  apply MemEquiv.eq
  refine ⟨rfl, ?_⟩
  simp only [bytesTakefill_of_length, MemoryList.data_ofBytes]
  have e := List.take_append_drop bs.length (List.drop (k + off) m.data.data)
  rw [h2, List.drop_drop] at e
  rw [List.append_assoc, e, List.take_append_drop]

@[rocq_alias iriswasm.store_append]
theorem store_append (m : Memory) (k : Nat) (off : StaticOffset) (b : Byte) (bs : Bytes)
    (m' : Memory) (h : store m k off (b :: bs) (b :: bs).length = some m') :
    ∃ m'', store m k (off + 1) bs bs.length = some m'' ∧ store m'' k off [b] 1 = some m' := by
  obtain ⟨m0, hm0, hm0'⟩ := store_append1 m k off b bs m' h
  exact swap_stores m m0 m' k off b bs hm0' hm0

#rocq_ignore iriswasm.mem_grow_max "growth preserves the maximum of the stored memory type"
theorem mem_grow_max (m : Memory) (n : Nat) (m' : Memory) (h : memGrow m n = some m') :
    m.type.limits.max = m'.type.limits.max := by
  rw [(memGrow_spec h).2.1]

@[rocq_alias iriswasm.length_bits]
theorem length_bits (v : Value) (t : ValueType) (h : typesAgree t v = true) :
    (bits v).length = lengthT t := by
  cases v <;> cases t <;> simp_all [typesAgree, typeof, bits, serialiseI32, serialiseI64,
    serialiseF32, serialiseF64, length_encodeInt, lengthT]

@[rocq_alias iriswasm.memory_in_bounds]
theorem memory_in_bounds (m : Memory) (i : Nat) (b : Byte) (h : m.data.data[i]? = some b) :
    i < lengthMem m := by
  rw [lengthMem_eq_data_length]
  exact (List.getElem?_eq_some_iff.1 h).1

@[rocq_alias iriswasm.iris_rules_resources.take_drop]
theorem take_drop {A : Type} (n : Nat) (l : List A) : l = l.take n ++ l.drop n :=
  (List.take_append_drop n l).symm

@[rocq_alias iriswasm.those_map_Some]
theorem those_map_Some (f : Nat → Option Byte) (l : List Byte)
    (h : ∀ x, x < l.length → f x = l[x]?) : those ((List.range' 0 l.length).map f) = some l := by
  rw [← those_map_some]
  congr 1
  apply List.ext_getElem?; intro j
  simp only [List.getElem?_map]
  grind

@[rocq_alias iriswasm.length_iota]
theorem length_iota (len i : Nat) : (List.range' i len).length = len := List.length_range'

@[rocq_alias iriswasm.load_prefix]
theorem load_prefix (m : Memory) (k : Nat) (off : StaticOffset) (bs : Bytes) (len : Nat)
    (hlen : len < bs.length) (h : load m k off bs.length = some bs) :
    ∃ tl1 tl2, bs = tl1 ++ tl2 ∧ load m k off len = some tl1 := by
  obtain ⟨h1, h2⟩ := load_some_iff.1 h
  refine ⟨bs.take len, bs.drop len, (List.take_append_drop _ _).symm,
    load_some_iff.2 ⟨by omega, ?_⟩⟩
  rw [← h2, List.take_take, Nat.min_eq_left (by omega)]

@[rocq_alias iriswasm.if_load_then_store]
theorem if_load_then_store (bs bs' : Bytes) (m : Memory) (k : Nat) (off : StaticOffset)
    (hlen : bs.length = bs'.length) (h : load m k off bs.length = some bs) :
    ∃ m', store m k off bs' bs'.length = some m' :=
  ⟨_, store_some_iff.2 ⟨by have := (load_some_iff.1 h).1; omega, rfl⟩⟩

@[rocq_alias iriswasm.length_load]
theorem length_load (m : Memory) (k : Nat) (off : StaticOffset) (len : Nat) (tl1 : Bytes)
    (h : load m k off len = some tl1) : tl1.length = len := by
  obtain ⟨h1, rfl⟩ := load_some_iff.1 h
  simp only [List.length_take, List.length_drop]; omega

@[rocq_alias iriswasm.if_load_then_store_weak]
theorem if_load_then_store_weak (bs bs' : Bytes) (m : Memory) (k : Nat) (off : StaticOffset)
    (hlen : bs'.length ≤ bs.length) (h : load m k off bs.length = some bs) :
    ∃ m', store m k off bs' bs'.length = some m' :=
  ⟨_, store_some_iff.2 ⟨by have := (load_some_iff.1 h).1; omega, rfl⟩⟩

@[rocq_alias iriswasm.length_bytes_takefill]
theorem length_bytes_takefill (b : Byte) (len : Nat) (bytes : Bytes) :
    (bytesTakefill b len bytes).length = len :=
  length_bytesTakefill b len bytes

@[rocq_alias iriswasm.drop_S_inv]
theorem drop_S_inv {A : Type} (n : Nat) (bs : List A) (b : A) (l : List A)
    (h : bs.drop n = b :: l) : bs.drop (n + 1) = l := by
  rw [← List.drop_drop, h]; rfl

@[rocq_alias iriswasm.enough_space_to_store']
theorem enough_space_to_store' (m : Memory) (k : Nat) (off : StaticOffset) (bs : Bytes) (len : Nat)
    (_hlen : len < bs.length) (h : k + off + len ≤ lengthMem m) :
    ∃ mf, store m k off bs len = some mf :=
  ⟨_, store_some_iff.2 ⟨by rwa [← lengthMem_eq_data_length], rfl⟩⟩

@[rocq_alias iriswasm.store_weak]
theorem store_weak (m : Memory) (k : Nat) (off : StaticOffset) (bs : Bytes) (m' : Memory)
    (len' : Nat) (hlt : len' < bs.length) (h : store m k off bs bs.length = some m') :
    ∃ m'', store m k off bs len' = some m'' :=
  ⟨_, store_some_iff.2 ⟨by have := (store_some_iff.1 h).1; omega, rfl⟩⟩

theorem if_load_then_store_packed (bs bs' : Bytes) (m : Memory) (k : Nat) (off : StaticOffset)
    (packedLen len : Nat) (sx : Sx) (hlen : bs'.length ≤ packedLen)
    (h : loadPacked sx m k off packedLen len = some bs) :
    ∃ m', storePacked m k off bs' bs'.length = some m' := by
  obtain ⟨_, hl, _⟩ := Option.map_eq_some_iff.mp h
  have := (load_some_iff.mp hl).1
  exact ⟨_, store_some_iff.2 ⟨by omega, rfl⟩⟩

@[rocq_alias iriswasm.bytes_takefill_idem]
theorem bytes_takefill_idem (len : Nat) (bs : Bytes) :
    bytesTakefill 0 len (bytesTakefill 0 len bs) = bytesTakefill 0 len bs := by
  induction len generalizing bs with
  | zero => rfl
  | succ len ih => cases bs <;> simp only [bytesTakefill, ih]

@[rocq_alias iriswasm.store_bytes_takefill_eq]
theorem store_bytes_takefill_eq (m : Memory) (k : Nat) (off : StaticOffset) (len : Nat)
    (bs : Bytes) : store m k off (bytesTakefill 0 len bs) len = store m k off bs len := by
  simp only [store, bytes_takefill_idem]

#rocq_ignore iriswasm.store_mem_len_eq "writes preserve address width, byte length, and declared minimum"
theorem store_mem_meta_eq (m : Memory) (k : Nat) (off : StaticOffset) (bv : Bytes) (mf : Memory)
    (n : Nat) (mem : List Memory) (hm : mem[n]? = some m)
    (h : store m k off bv bv.length = some mf) :
    (updateListAt mem n mf).map memLengthMeta = mem.map memLengthMeta := by
  have hn := (List.getElem?_eq_some_iff.1 hm).1
  have hl : lengthMem mf = lengthMem m := by
    simpa only [lengthMem_eq_data_length] using (length_store _ _ _ _ _ h).symm
  have hmeta : memLengthMeta mf = memLengthMeta m := by
    simp only [memLengthMeta, hl, store_mem_type m mf k off bv _ h]
  have hu : updateListAt mem n mf = mem.set n mf := by
    simp [updateListAt, List.set_eq_take_append_cons_drop, hn]
  rw [hu, List.map_set]
  apply List.ext_getElem?; intro j
  simp only [List.getElem?_set, List.getElem?_map, List.length_map]
  grind


private theorem encode_decode_int (bs : Bytes) : encodeInt bs.length (decodeInt bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have hb := b.isLt
    have hd := decodeInt_nonneg bs
    simp only [List.length_cons, encodeInt, decodeInt, List.cons.injEq]
    constructor
    · apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofInt, Nat.reducePow, Int.cast_ofNat_Int, Int.add_mul_emod_self_right]
      omega
    · rw [Int.add_mul_ediv_right _ _ (by decide)]
      rw [show ((b.toNat : Int) / 256) = 0 by omega, Int.zero_add, ih]

private theorem ofInt_decodeInt_toNat {w : Nat} (bs : Bytes) (h : bs.length * 8 = w) :
    (((BitVec.ofInt w (decodeInt bs)).toNat : Nat) : Int) = decodeInt bs := by
  have h1 := decodeInt_nonneg bs
  have h2 := decodeInt_lt bs
  have h3 : 0 < 2 ^ w := Nat.two_pow_pos w
  rw [BitVec.toNat_ofInt, Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega)),
    Int.emod_eq_of_lt h1 (by subst h; rw [Nat.mul_comm]; exact_mod_cast h2)]

private theorem ofInt_encodeInt (n : Nat) {w : Nat} (a : BitVec w) (h : w = 8 * n) :
    BitVec.ofInt w (decodeInt (encodeInt n a.toNat)) = a := by
  rw [decode_encode_int_of_lt (by omega) (by subst h; exact_mod_cast a.isLt)]
  simp

@[rocq_alias iriswasm.deserialise_bits]
theorem deserialise_bits (v : Value) (t : ValueType) (h : typesAgree t v = true) :
    wasmDeserialise (bits v) t = v := by
  cases v <;> cases t <;> simp_all [typesAgree, typeof] <;>
    simp [bits, serialiseI32, serialiseI64, serialiseF32, serialiseF64, wasmDeserialise,
      ofInt_encodeInt]

@[rocq_alias iriswasm.bits_deserialise]
theorem bits_deserialise (bs : Bytes) (t : ValueType) (h : bs.length = lengthT t) :
    bits (wasmDeserialise bs t) = bs := by
  cases t <;> simp only [lengthT] at h <;>
    simp only [wasmDeserialise, bits, serialiseI32, serialiseI64, serialiseF32, serialiseF64] <;>
    rw [ofInt_decodeInt_toNat bs _, ← h, encode_decode_int] <;> omega

@[rocq_alias iriswasm.deserialise_type]
theorem deserialise_type (bs : Bytes) (t : ValueType) : typesAgree t (wasmDeserialise bs t) = true := by
  cases t <;> rfl

#rocq_ignore iriswasm.mem_in_bound "the page limit depends on the memory's address width"
def MemInBound (aw : AddrType) (c : Nat) : Prop := c ≤ aw.pageLimit


/-! ## Separation-logic rules -/

section iris
variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF]

private theorem get?_gmapOfMemory {mems : List Memory} {n : Nat} {m : Memory} (hm : mems[n]? = some m)
    (j : Nat) : get? (gmapOfMemory mems) (n, j) = m.data.data[j]? := by
  rw [gmapOfMemory, gmap_of_list_2d_lookup, List.getElem?_map, hm]; rfl

private theorem frame_lookup {locs : List Value} {inst : Instance} {f : Frame} {q : DFrac} :
    ⊢ (ghost_map_auth (WasmG.frameGName GF) (DFrac.own 1)
      (insert (PartialMap.empty : UnitMapF Frame) () ⟨locs, inst⟩) -∗ ↪[frame]{ q } f -∗
      ⌜f = ⟨locs, inst⟩⌝ : IProp GF) := by
  unfold frameOwn
  iintro Ha Hf
  ihave %h := ghost_map_lookup $$ Ha Hf
  ipureintro
  rw [get?_insert_eq rfl] at h
  exact (Option.some.inj h).symm

private theorem reduce_det_of {ws f es ws1 f1 es1 ws2 f2 es2}
    (h1 : Reduce ws f es ws1 f1 es1) (h2 : Reduce ws f es ws2 f2 es2)
    (hgrow : ∀ x i, firstInstr es ≠ some (.basic (.growMemory x), i) := by
      simp [firstInstr_cons, firstInstrInstr])
    (htrap : ∀ i, firstInstr es ≠ some (.trap, i) := by
      simp [firstInstr_cons, firstInstrInstr]) :
    ws2 = ws1 ∧ f2 = f1 ∧ es2 = es1 := by
  rcases reduce_det h1 h2 with h | ⟨x, i, h⟩ | ⟨i, -, -, h, -⟩
  · simp only [Prod.mk.injEq] at h; exact ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩
  · exact absurd h (hgrow x i)
  · exact absurd h (htrap i)

/-- `genHeap_valid` without the update modality (and without consuming the resources). -/
private theorem heap_lookup {L V : Type _} {H : Type _ → Type _} [LawfulFiniteMap H L]
    {G : genHeapGS L V GF H} {σ : H V} {l : L} {dq : DFrac} {v : V} :
    ⊢ (genHeapInterp (G := G) σ -∗ pointsTo (G := G) l dq v -∗ ⌜get? σ l = some v⌝ : IProp GF) := by
  unfold genHeapInterp pointsTo
  iintro ⟨%m, -, Hσ, -⟩ Hl
  iapply ghost_map_lookup $$ Hσ Hl

/-- Every points-to of a big separating conjunction is backed by the heap. -/
private theorem bigSep_valid {L V : Type _} {H : Type _ → Type _} [LawfulFiniteMap H L]
    {G : genHeapGS L V GF H} {g : Nat → L} {l : List V} {dq : DFrac} {σ : H V} :
    ⊢ (([∗list] i ↦ x ∈ l, pointsTo (G := G) (g i) dq x) -∗ genHeapInterp (G := G) σ -∗
      ⌜∀ i x, l[i]? = some x → get? σ (g i) = some x⌝ : IProp GF) := by
  iintro Hl Hσ
  iapply pure_forall.2; iintro %i
  iapply pure_forall.2; iintro %x
  iapply pure_wand.1; iintro %hx
  ihave Hx := BigSepL.bigSepL_lookup hx $$ Hl
  iapply heap_lookup $$ Hσ Hx

private theorem get?_gmapOfTable {tabs : List Tableinst} {n : Nat} {t : Tableinst}
    (ht : tabs[n]? = some t) (j : Nat) : get? (gmapOfTable tabs) (n, j) = t.data[j]? := by
  rw [gmapOfTable, gmap_of_list_2d_lookup, List.getElem?_map, ht]; rfl

/-- Two lists agree if they have the same length and the second one contains the first. -/
private theorem list_eq_of_lookup {A : Type} {l l' : List A} (hlen : l'.length = l.length)
    (h : ∀ (i : Nat) x, l[i]? = some x → l'[i]? = some x) : l' = l := by
  apply List.ext_getElem?; intro i
  by_cases hi : i < l.length
  · obtain ⟨x, hx⟩ : ∃ x, l[i]? = some x := ⟨_, List.getElem?_eq_getElem hi⟩
    rw [hx, h i x hx]
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

private theorem load_of_bytes {m : Memory} {k off : Nat} {bv : Bytes} (hlen : bv.length > 0)
    (h : ∀ i b, bv[i]? = some b → m.data.data[k + off + i]? = some b) :
    load m k off bv.length = some bv := by
  have hb : k + off + bv.length ≤ m.data.data.length := by
    have := h _ _ (List.getElem?_eq_getElem (l := bv) (i := bv.length - 1) (by omega))
    have := (List.getElem?_eq_some_iff.1 this).1
    omega
  rw [load_some_iff]
  refine ⟨by omega, List.ext_getElem? fun i => ?_⟩
  by_cases hi : i < bv.length
  · obtain ⟨b, hbi⟩ : ∃ b, bv[i]? = some b := ⟨_, List.getElem?_eq_getElem hi⟩
    rw [hbi, List.getElem?_take_of_lt hi, List.getElem?_drop, ← h i b hbi]
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

/-- The Wasm state interpretation, unfolded. -/
private theorem stateInterp_wasm {ws : StoreRecord} {locs : List Value} {inst : Instance} {ns : Nat}
    {obs : List Observation} {nt : Nat} :
    @Iris.stateInterp State Observation GF (wasmIrisGS (hlc := hlc)).toStateInterp
      (ws, locs, inst) ns obs nt ⊣⊢ iprop(
    genHeapInterp (G := WasmG.funcHs) (gmapOfList ws.funcs) ∗
    genHeapInterp (G := WasmG.tabHs) (gmapOfTable ws.tables) ∗
    genHeapInterp (G := WasmG.memHs) (gmapOfMemory ws.mems) ∗
    genHeapInterp (G := WasmG.globHs) (gmapOfList ws.globals) ∗
    ghost_map_auth (WasmG.frameGName GF) (DFrac.own 1)
      (insert (PartialMap.empty : UnitMapF Frame) () ⟨locs, inst⟩) ∗
    genHeapInterp (G := WasmG.memsizeHs) (gmapOfList (ws.mems.map memLengthMeta)) ∗
    genHeapInterp (G := WasmG.tabsizeHs) (gmapOfList (ws.tables.map tabSize)) ∗
    genHeapInterp (G := WasmG.memlimitHs) (gmapOfList (ws.mems.map (·.type.limits.max))) ∗
    genHeapInterp (G := WasmG.tablimitHs) (gmapOfList (ws.tables.map (·.maxOpt)))) := .rfl

/-- `toVal` of an explicit instruction list. -/
local macro "solve_toVal" : tactic => `(tactic| (
  show IrisWasm.toVal _ = _
  simp [toVal, mergeValuesList, toValInstr, mergeValues, valNotValCombine, valCombine]))

/-- Lifting skeleton shared by the resource rules (not in Coq, whose proofs inline it): from
frame `f`, the resources `R` together with the heaps of any store `ws` show that `es` reduces,
and turn every reduction `ws, f, es ↦ ws2, f2, es2` into the heaps of `ws2`, a value of `es2`
satisfying `Φ`, and the new frame `f2 = f'`. -/
private theorem wp_wasm_step {s : Stuckness} {E : CoPset} {es : Expr} {f f' : Frame}
    {Φ : Val → IProp GF} {R : IProp GF} (hnv : toVal es = none)
    (H : ∀ ws, R ∗ genHeapWasmStore ws ⊢ ⌜∃ ws' f'' es', Reduce ws f es ws' f'' es'⌝ ∗
      ▷ ∀ ws2 f2 es2, ⌜Reduce ws f es ws2 f2 es2⌝ -∗
        |==> (⌜f2 = f'⌝ ∗ genHeapWasmStore ws2 ∗ ∃ v, ⌜toVal es2 = some v⌝ ∗ Φ v)) :
    ⊢ iprop(R -∗ ↪[frame] f -∗ WP es @ s ; E {{ w, Φ w ∗ ↪[frame] f' }}) := by
  let := @WasmG.invGS hlc GF _
  iintro HR Hf
  iapply IrisWp.wp_lift_atomic_step (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) hnv f'
  iintro %σ %ns %obs %obs' %nt Hσ
  rcases σ with ⟨ws, locs, inst⟩
  icases stateInterp_wasm.1 $$ Hσ with ⟨Hfn, Htb, Hm, Hg, Hframe, Hms, Hts, Hml, Htl⟩
  ihave %hf := frame_lookup $$ Hframe Hf
  subst hf
  icases H ws $$ [HR Hfn Htb Hm Hg Hms Hts Hml Htl] with ⟨%hred, Hnext⟩
  · unfold genHeapWasmStore; iframe
  imodintro
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    obtain ⟨ws', f'', es', h⟩ := hred
    exact ⟨[], es', (ws', f''.locs, f''.inst), [], h, rfl, rfl⟩
  iintro !> %e₂ %σ₂ %eₜ %Hstep -
  rcases σ₂ with ⟨ws2, locs2, inst2⟩
  obtain ⟨Hred, rfl, rfl⟩ := Hstep
  imod Hnext $$ %_ %_ %_ %Hred with ⟨%hf2, Hws2, HΦ⟩
  iunfold frameOwn at Hf
  imod ghost_map_update (H := UnitMapF) f' $$ Hframe Hf with ⟨Hframe, Hf⟩
  rw [LawfulPartialMap.insert_insert_same, ← hf2]
  unfold genHeapWasmStore
  icases Hws2 with ⟨Hfn, Htb, Hm, Hg, Hms, Hts, Hml, Htl⟩
  imodintro
  isplitl [Hfn Htb Hm Hg Hframe Hms Hts Hml Htl]
  · iapply stateInterp_wasm.2; iframe
  isplitl [HΦ]
  · icases HΦ with ⟨%v, %hv, HΦ⟩
    iexists v
    isplit
    · ipureintro; exact hv
    · iexact HΦ
  isplitl [Hf]
  · iunfold frameOwn; iexact Hf
  · simp; exact .rfl

@[rocq_alias iriswasm.mem_block_lookup_data]
theorem mem_block_lookup_data (wms : List Memory) (n : Nat) (mem : Memory) :
    ⊢ (genHeapInterp (G := WasmG.memHs) (gmapOfMemory wms) -∗
      genHeapInterp (G := WasmG.memsizeHs) (gmapOfList (wms.map memLengthMeta)) -∗
      n ↦[wmblock] mem -∗
      ⌜∃ m, wms[n]? = some m ∧ m.data.data = mem.data.data⌝ : IProp GF) := by
  unfold memBlock
  iintro Hm Hms ⟨-, Hbytes, Hlen, -⟩
  ihave %hlen := heap_lookup $$ Hms Hlen
  ihave %hb := bigSep_valid $$ Hbytes Hm
  ipureintro
  rw [gmap_of_list_lookup, List.getElem?_map] at hlen
  obtain ⟨m, hm, he⟩ := Option.map_eq_some_iff.1 hlen
  have hl : lengthMem m = lengthMem mem := congrArg (fun p => p.2.1) he
  refine ⟨m, hm, list_eq_of_lookup (by simpa only [lengthMem_eq_data_length] using hl) fun i b hbi => ?_⟩
  rw [← get?_gmapOfMemory hm, hb i b hbi]

#rocq_ignore iriswasm.mem_block_lookup "ownership determines the complete stored memory type"
theorem mem_block_lookup (wms : List Memory) (n : Nat) (mem : Memory) :
    ⊢ (genHeapInterp (G := WasmG.memHs) (gmapOfMemory wms) -∗
      genHeapInterp (G := WasmG.memsizeHs) (gmapOfList (wms.map memLengthMeta)) -∗
      genHeapInterp (G := WasmG.memlimitHs) (gmapOfList (wms.map (·.type.limits.max))) -∗
      n ↦[wmblock] mem -∗
      ⌜∃ m, wms[n]? = some m ∧ m.data.data = mem.data.data ∧ m.type = mem.type⌝ : IProp GF) := by
  unfold memBlock
  iintro Hm Hms Hml ⟨%ha, Hbytes, Hlen, Hlim⟩
  ihave %hlen := heap_lookup $$ Hms Hlen
  ihave %hlim := heap_lookup $$ Hml Hlim
  ihave %hb := bigSep_valid $$ Hbytes Hm
  ipureintro
  rw [gmap_of_list_lookup, List.getElem?_map] at hlen hlim
  obtain ⟨m, hm, he⟩ := Option.map_eq_some_iff.1 hlen
  have hl : lengthMem m = lengthMem mem := congrArg (fun p => p.2.1) he
  have hw : m.type.address = mem.type.address := congrArg Prod.fst he
  have hmin : m.type.limits.min = lengthMem mem / pageSize := congrArg (fun p => p.2.2) he
  have hmineq : m.type.limits.min = mem.type.limits.min := hmin.trans ha.min_eq.symm
  rw [hm] at hlim
  have hmax : m.type.limits.max = mem.type.limits.max := Option.some.inj hlim
  have htype : m.type = mem.type := by
    change MemoryType.mk m.type.address ⟨m.type.limits.min, m.type.limits.max⟩ = mem.type
    rw [hw, hmineq, hmax]
  refine ⟨m, hm, list_eq_of_lookup (by simpa only [lengthMem_eq_data_length] using hl)
    fun i b hbi => ?_, htype⟩
  rw [← get?_gmapOfMemory hm, hb i b hbi]

@[rocq_alias iriswasm.tab_block_lookup_data]
theorem tab_block_lookup_data (wts : List Tableinst) (n : Nat) (tab : Tableinst) :
    ⊢ (genHeapInterp (G := WasmG.tabHs) (gmapOfTable wts) -∗
      genHeapInterp (G := WasmG.tabsizeHs) (gmapOfList (wts.map tabSize)) -∗
      n ↦[wtblock] tab -∗
      ⌜∃ t, wts[n]? = some t ∧ t.data = tab.data⌝ : IProp GF) := by
  unfold tabBlock
  iintro Ht Hts ⟨Hdata, Hsize, -⟩
  ihave %hsize := heap_lookup $$ Hts Hsize
  ihave %hb := bigSep_valid $$ Hdata Ht
  ipureintro
  rw [gmap_of_list_lookup, List.getElem?_map] at hsize
  obtain ⟨t, ht, hl⟩ := Option.map_eq_some_iff.1 hsize
  refine ⟨t, ht, list_eq_of_lookup (by simpa [tabSize] using hl) fun i x hx => ?_⟩
  rw [← get?_gmapOfTable ht, hb i x hx]

@[rocq_alias iriswasm.tab_block_lookup]
theorem tab_block_lookup (wts : List Tableinst) (n : Nat) (tab : Tableinst) :
    ⊢ (genHeapInterp (G := WasmG.tabHs) (gmapOfTable wts) -∗
      genHeapInterp (G := WasmG.tabsizeHs) (gmapOfList (wts.map tabSize)) -∗
      genHeapInterp (G := WasmG.tablimitHs) (gmapOfList (wts.map (·.maxOpt))) -∗
      n ↦[wtblock] tab -∗
      ⌜wts[n]? = some tab⌝ : IProp GF) := by
  unfold tabBlock
  iintro Ht Hts Htl ⟨Hdata, Hsize, Hlim⟩
  ihave %hsize := heap_lookup $$ Hts Hsize
  ihave %hlim := heap_lookup $$ Htl Hlim
  ihave %hb := bigSep_valid $$ Hdata Ht
  ipureintro
  rw [gmap_of_list_lookup, List.getElem?_map] at hsize hlim
  obtain ⟨t, ht, hl⟩ := Option.map_eq_some_iff.1 hsize
  rw [ht] at hlim ⊢
  have hdata : t.data = tab.data := list_eq_of_lookup (by simpa [tabSize] using hl)
    fun i x hx => by rw [← get?_gmapOfTable ht, hb i x hx]
  have he : t.entries = tab.entries := RunTable.ext_toList hdata
  obtain ⟨d, o⟩ := t
  obtain ⟨d', o'⟩ := tab
  simp_all

@[rocq_alias iriswasm.wp_get_local]
theorem wp_get_local (s : Stuckness) (E : CoPset) (v : Value) (i : Nat) (Φ : Val → IProp GF)
    (f : Frame) (hlook : f.locs[i]? = some v) :
    ⊢ iprop(▷ Φ (.immV [v]) -∗ ↪[frame] f -∗
      WP ([.basic (.getLocal i)] : Expr) @ s ; E {{ w, Φ w ∗ ↪[frame] f }}) := by
  refine wp_wasm_step (by solve_toVal) fun ws => ?_
  iintro ⟨HΦ, Hws⟩
  isplitr
  · ipureintro; exact ⟨_, _, _, .getLocal hlook⟩
  iintro !> %ws2 %f2 %es2 %Hred
  obtain ⟨rfl, rfl, rfl⟩ := reduce_det_of (.getLocal hlook) Hred
  imodintro
  iframe
  ipureintro
  exact ⟨rfl, by solve_toVal⟩

@[rocq_alias iriswasm.wp_set_local]
theorem wp_set_local (s : Stuckness) (E : CoPset) (v : Value) (i : Nat) (Φ : Val → IProp GF)
    (f : Frame) (hi : i < f.locs.length) :
    ⊢ iprop(▷ Φ (.immV []) -∗ ↪[frame] f -∗
      WP ([.basic (.const v), .basic (.setLocal i)] : Expr) @ s ; E
        {{ w, Φ w ∗ ↪[frame] (⟨f.locs.set i v, f.inst⟩ : Frame) }}) := by
  refine wp_wasm_step (by solve_toVal) fun ws => ?_
  iintro ⟨HΦ, Hws⟩
  have hred : Reduce ws f [.basic (.const v), .basic (.setLocal i)] ws ⟨f.locs.set i v, f.inst⟩ [] :=
    .setLocal rfl hi rfl
  isplitr
  · ipureintro; exact ⟨_, _, _, hred⟩
  iintro !> %ws2 %f2 %es2 %Hred
  obtain ⟨rfl, rfl, rfl⟩ := reduce_det_of hred Hred
  imodintro
  iframe
  ipureintro
  exact ⟨rfl, by solve_toVal⟩

@[rocq_alias iriswasm.wp_tee_local]
theorem wp_tee_local (s : Stuckness) (E : CoPset) (v : Value) (i : Nat) (Φ : Val → IProp GF)
    (f : Frame) :
    ⊢ iprop(↪[frame] f -∗
      ▷ (↪[frame] f -∗
        WP ([.basic (.const v), .basic (.const v), .basic (.setLocal i)] : Expr) @ s ; E {{ Φ }}) -∗
      WP ([.basic (.const v), .basic (.teeLocal i)] : Expr) @ s ; E {{ Φ }}) := by
  have hred : ∀ ws fr, Reduce ws fr [.basic (.const v), .basic (.teeLocal i)] ws fr
      [.basic (.const v), .basic (.const v), .basic (.setLocal i)] :=
    fun _ _ => .simple (.teeLocal rfl)
  have hpd : ∀ {σ₁ : State} {obs e₂' σ₂ eₜ'},
      primStep (([.basic (.const v), .basic (.teeLocal i)] : Expr), σ₁) obs (e₂', σ₂, eₜ') →
      obs = [] ∧ σ₂ = σ₁ ∧ e₂' = [.basic (.const v), .basic (.const v), .basic (.setLocal i)] ∧
        eₜ' = [] := by
    intro ⟨ws, locs, inst⟩ obs e₂' ⟨ws', locs', inst'⟩ eₜ' ⟨h, ho, he⟩
    obtain ⟨rfl, hf, rfl⟩ := reduce_det_of (hred ws ⟨locs, inst⟩) h
    cases hf
    exact ⟨ho, rfl, rfl, he⟩
  have key := IrisWp.wp_lift_pure_det_step_no_fork (fun f : Frame => iprop(↪[frame] f))
    (ι := wasmIrisGS) (s := s) (Φ := Φ) (E := E) E f (by
      intro ⟨ws, locs, inst⟩
      cases s
      · exact ⟨[], _, (ws, locs, inst), [], hred ws ⟨locs, inst⟩, rfl, rfl⟩
      · exact val_head_stuck_reduce (hred ws ⟨locs, inst⟩)) hpd
  let := @WasmG.invGS hlc GF _
  iintro Hf H
  iapply key $$ [H] Hf
  iapply step_fupd_intro (Std.LawfulSet.subset_refl)
  inext
  iintro _ Hf
  iapply H $$ Hf

@[rocq_alias iriswasm.wp_get_global]
theorem wp_get_global (s : Stuckness) (E : CoPset) (v : Value) (f : Frame) (n : Nat)
    (Φ : Val → IProp GF) (g : Global) (k : Nat) (hn : f.inst.globs[n]? = some k)
    (hg : g.val = v) :
    ⊢ iprop(▷ Φ (.immV [v]) -∗ ↪[frame] f -∗ k ↦[wg] g -∗
      WP ([.basic (.getGlobal n)] : Expr) @ s ; E {{ w, Φ w ∗ k ↦[wg] g ∗ ↪[frame] f }}) := by
  have key := wp_wasm_step (s := s) (E := E) (f := f) (f' := f)
    (Φ := fun w => iprop(Φ w ∗ k ↦[wg] g)) (R := iprop(▷ Φ (.immV [v]) ∗ k ↦[wg] g))
    (es := [.basic (.getGlobal n)]) (by solve_toVal) fun ws => by
      unfold genHeapWasmStore
      iintro ⟨⟨HΦ, Hg⟩, Hfn, Htb, Hm, Hgl, Hms, Hts, Hml, Htl⟩
      ihave %hgl := heap_lookup $$ [$Hgl] [$Hg]
      rw [gmap_of_list_lookup] at hgl
      have hred : Reduce ws f [.basic (.getGlobal n)] ws f [.basic (.const v)] :=
        .getGlobal (by simp [sglobVal, sglob, sglobInd, optionBind, hn, hgl, hg])
      isplitr
      · ipureintro; exact ⟨_, _, _, hred⟩
      iintro !> %ws2 %f2 %es2 %Hred
      obtain ⟨rfl, rfl, rfl⟩ := reduce_det_of hred Hred
      imodintro
      iframe
      ipureintro
      exact ⟨rfl, by solve_toVal⟩
  iintro HΦ Hf Hg
  iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ [HΦ Hg Hf]
  · iapply key $$ [HΦ Hg] Hf
    iframe
  · iintro %w ⟨⟨HΦ, Hg⟩, Hf⟩
    iframe

@[rocq_alias iriswasm.wp_set_global]
theorem wp_set_global (s : Stuckness) (E : CoPset) (v : Value) (f : Frame) (n : Nat)
    (Φ : Val → IProp GF) (g : Global) (k : Nat) (hn : f.inst.globs[n]? = some k) :
    ⊢ iprop(▷ Φ (.immV []) -∗ ↪[frame] f -∗ k ↦[wg] g -∗
      WP ([.basic (.const v), .basic (.setGlobal n)] : Expr) @ s ; E
        {{ w, Φ w ∗ k ↦[wg] (⟨g.mut_, v⟩ : Global) ∗ ↪[frame] f }}) := by
  have key := wp_wasm_step (s := s) (E := E) (f := f) (f' := f)
    (Φ := fun w => iprop(Φ w ∗ k ↦[wg] (⟨g.mut_, v⟩ : Global)))
    (R := iprop(▷ Φ (.immV []) ∗ k ↦[wg] g))
    (es := [.basic (.const v), .basic (.setGlobal n)]) (by solve_toVal) fun ws => by
      unfold genHeapWasmStore
      iintro ⟨⟨HΦ, Hg⟩, Hfn, Htb, Hm, Hgl, Hms, Hts, Hml, Htl⟩
      ihave %hgl := heap_lookup $$ [$Hgl] [$Hg]
      rw [gmap_of_list_lookup] at hgl
      have hk : k < ws.globals.length := (List.getElem?_eq_some_iff.1 hgl).1
      have hred : Reduce ws f [.basic (.const v), .basic (.setGlobal n)]
          ⟨ws.funcs, ws.tables, ws.mems, updateListAt ws.globals k ⟨g.mut_, v⟩⟩ f [] :=
        .setGlobal (by simp [supdateGlob, supdateGlobS, sglobInd, optionBind, hn, hgl])
      isplitr
      · ipureintro; exact ⟨_, _, _, hred⟩
      iintro !> %ws2 %f2 %es2 %Hred
      obtain ⟨rfl, rfl, rfl⟩ := reduce_det_of hred Hred
      imod @genHeap_update _ _ _ _ _ WasmG.globHs _ _ _ _ (⟨g.mut_, v⟩ : Global) $$ [$Hgl $Hg]
        with ⟨Hgl, Hg⟩
      rw [← gmap_of_list_insert _ _ _ hk, update_list_at_is_set_nth _ hk]
      imodintro
      iframe
      ipureintro
      exact ⟨rfl, by solve_toVal⟩
  iintro HΦ Hf Hg
  iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ [HΦ Hg Hf]
  · iapply key $$ [HΦ Hg] Hf
    iframe
  · iintro %w ⟨⟨HΦ, Hg⟩, Hf⟩
    iframe

@[rocq_alias iriswasm.wms_append]
theorem wms_append (n k : Nat) (b : Byte) (bs : Bytes) :
    ⊢ (n ↦[wms][ k ] (b :: bs) ∗-∗ (n ↦[wm][ k ] b ∗ n ↦[wms][ k + 1 ] bs) : IProp GF) := by
  apply equiv_wandIff
  unfold memBlockAtPos
  refine BigSepL.bigSepL_cons.trans ?_
  simp only [Nat.add_zero, ← Nat.add_assoc, Nat.add_right_comm _ _ 1]
  exact .rfl

private theorem set_take_drop {A : Type} (d bs' : List A) (b' : A) (p len : Nat) (hp : p + (len + 1) ≤ d.length) :
    (d.set p b').take (p + 1) ++ bs' ++ (d.set p b').drop (p + 1 + len)
      = d.take p ++ b' :: bs' ++ d.drop (p + (len + 1)) := by
  have h1 : (d.set p b').take (p + 1) = d.take p ++ [b'] := by
    apply List.ext_getElem?; intro j
    simp only [List.getElem?_take, List.getElem?_append, List.getElem?_set, List.length_take,
      List.getElem?_singleton]
    by_cases hj : j < p
    · simp [hj, show j < p + 1 by omega, show p ≠ j by omega, Nat.min_eq_left (by omega : p ≤ d.length)]
    · by_cases hj' : j = p
      · subst hj'; simp [Nat.min_eq_left (by omega : j ≤ d.length), show j < d.length by omega]
      · simp [show ¬ j < p + 1 by omega, Nat.min_eq_left (by omega : p ≤ d.length), hj,
          show j - p ≠ 0 by omega]
  have h2 : (d.set p b').drop (p + 1 + len) = d.drop (p + (len + 1)) := by
    rw [List.drop_set_of_lt (by omega)]; congr 1; omega
  rw [h1, h2]; simp

/-- Overwrite the bytes `bs` at position `p` of the memory `n` (data `d`) with `bs'`. -/
private theorem heap_update_bytes (n : Nat) (o : MemoryType) (bs : Bytes) : ∀ (bs' : Bytes) (p : Nat)
    (d : List Byte) (mems : List Memory), mems[n]? = some ⟨MemoryList.ofBytes d, o⟩ → bs.length = bs'.length →
    p + bs.length ≤ d.length →
    ⊢ (genHeapInterp (G := WasmG.memHs) (gmapOfMemory mems) -∗ n ↦[wms][ p ] bs ==∗
      genHeapInterp (G := WasmG.memHs)
        (gmapOfMemory (mems.set n ⟨MemoryList.ofBytes (d.take p ++ bs' ++ d.drop (p + bs.length)), o⟩)) ∗
      n ↦[wms][ p ] bs' : IProp GF) := by
  induction bs with
  | nil =>
    intro bs' p d mems hm hlen _
    cases bs' with
    | cons => simp at hlen
    | nil =>
      obtain ⟨hn, hm⟩ := List.getElem?_eq_some_iff.1 hm
      simp only [List.append_nil, List.length_nil, Nat.add_zero, List.take_append_drop]
      rw [← hm, List.set_getElem_self hn]
      iintro Hσ Hbs
      imodintro
      iframe
  | cons b bs ih =>
    intro bs' p d mems hm hlen hp
    cases bs' with
    | nil => simp at hlen
    | cons b' bs' =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen hp
      have hpd : p < d.length := by omega
      have hn : n < mems.length := (List.getElem?_eq_some_iff.1 hm).1
      have key := ih bs' (p + 1) (d.set p b') (mems.set n ⟨MemoryList.ofBytes (d.set p b'), o⟩)
        (by rw [List.getElem?_set_self hn]) hlen (by simp; omega)
      rw [List.set_set, set_take_drop d bs' b' p bs.length (by omega)] at key
      iintro Hσ Hbs
      icases (wandIff_equiv (wms_append (GF := GF) n p b bs)).1 $$ Hbs with ⟨Hb, Hbs⟩
      imod @genHeap_update _ _ _ _ _ WasmG.memHs _ _ _ _ b' $$ [$Hσ $Hb] with ⟨Hσ, Hb⟩
      rw [gmap_of_memory_insert n p b' mems ⟨MemoryList.ofBytes d, o⟩
        (MemoryList.ofBytes (d.set p b')) hm (by simpa only [MemoryList.data_ofBytes] using hpd)
        (by simp only [MemoryList.update_eq, MemoryList.length_ofBytes, hpd, ↓reduceIte,
              MemoryList.data_ofBytes])]
      imod key $$ Hσ Hbs with ⟨Hσ, Hbs⟩
      imodintro
      isplitl [Hσ]
      · iexact Hσ
      iapply (wandIff_equiv (wms_append (GF := GF) n p b' bs')).2
      isplitl [Hb]
      · iexact Hb
      · iexact Hbs

@[rocq_alias iriswasm.gen_heap_update_big_wm]
theorem gen_heap_update_big_wm (bs bs' : Bytes) (k off n : Nat) (mems mems' : List Memory)
    (m m' : Memory) (hlen : bs.length = bs'.length) (hload : load m k off bs.length = some bs)
    (hstore : store m k off bs' bs'.length = some m') (hupd : updateListAt mems n m' = mems')
    (hm : mems[n]? = some m) :
    ⊢ (genHeapInterp (G := WasmG.memHs) (gmapOfMemory mems) -∗ n ↦[wms][ k + off ] bs ==∗
      genHeapInterp (G := WasmG.memHs) (gmapOfMemory mems') ∗ n ↦[wms][ k + off ] bs' : IProp GF) := by
  have hb := (load_some_iff.1 hload).1
  obtain ⟨-, rfl⟩ := store_some_iff.1 hstore
  subst hupd
  rw [← update_list_at_is_set_nth _ (List.getElem?_eq_some_iff.1 hm).1, bytesTakefill_of_length, ← hlen]
  exact heap_update_bytes n m.type bs bs' (k + off) m.data.data mems
    (by simpa only [MemoryList.ofBytes_data] using hm) hlen (by omega)

@[rocq_alias iriswasm.wms_is_load]
theorem wms_is_load (n k off : Nat) (bv : Bytes) (m : Memory) (ws : StoreRecord)
    (hlen : bv.length > 0) (hm : ws.mems[n]? = some m) :
    ⊢ (n ↦[wms][ k + off ] bv -∗ genHeapInterp (G := WasmG.memHs) (gmapOfMemory ws.mems) -∗
      ⌜load m k off bv.length = some bv⌝ : IProp GF) := by
  unfold memBlockAtPos
  iintro Hwms Hm
  ihave %h := bigSep_valid $$ Hwms Hm
  ipureintro
  exact load_of_bytes hlen fun i b hb => by rw [← get?_gmapOfMemory hm]; exact h i b hb

theorem wms_is_load_packed (n k off : Nat) (bv : Bytes) (m : Memory) (len : Nat) (ws : StoreRecord)
    (sx : Sx) (hlen : bv.length > 0) (hm : ws.mems[n]? = some m) :
    ⊢ (n ↦[wms][ k + off ] bv -∗ genHeapInterp (G := WasmG.memHs) (gmapOfMemory ws.mems) -∗
      ⌜loadPacked sx m k off bv.length len = some (signExtend sx len bv)⌝ : IProp GF) := by
  iintro Hwms Hm
  ihave %h := wms_is_load n k off bv m ws hlen hm $$ Hwms Hm
  ipureintro
  simp [loadPacked, h]

@[rocq_alias iriswasm.wms_implies_bounds]
theorem wms_implies_bounds (n k off : Nat) (bv : Bytes) (ws : StoreRecord) (m : Memory)
    (hlen : bv.length > 0) (hm : ws.mems[n]? = some m) :
    ⊢ (n ↦[wms][ k + off ] bv -∗ genHeapInterp (G := WasmG.memHs) (gmapOfMemory ws.mems) -∗
      ⌜k + off + bv.length ≤ lengthMem m⌝ : IProp GF) := by
  iintro Hwms Hm
  ihave %h := wms_is_load n k off bv m ws hlen hm $$ Hwms Hm
  ipureintro
  have := (load_some_iff.1 h).1
  rw [lengthMem_eq_data_length]
  omega

variable {aw : AddrType}

#rocq_ignore iriswasm.wms_is_not_load "out-of-bounds reads use width-indexed extents"
theorem wms_is_not_load (n k off len : Nat) (m : Memory) (ws : StoreRecord) (llen : Nat)
    (ht : k + off + llen > len) (hm : ws.mems[n]? = some m) :
    ⊢ (n ↦[wmlength] (aw, len) -∗
      genHeapInterp (G := WasmG.memsizeHs) (gmapOfList (ws.mems.map memLengthMeta)) -∗
      ⌜load m k off llen = none⌝ : IProp GF) := by
  iintro Hlen Hms
  ihave %h := heap_lookup $$ Hms Hlen
  ipureintro
  rw [gmap_of_list_lookup, List.getElem?_map, hm, Option.map_some, Option.some.injEq] at h
  have hlen : lengthMem m = len := congrArg (fun p => p.2.1) h
  rw [load_eq]; split
  · omega
  · rfl

#rocq_ignore iriswasm.wms_is_not_load_packed "packed reads use width-indexed extents"
theorem wms_is_not_load_packed (n k off len : Nat) (m : Memory) (ws : StoreRecord) (llen len' : Nat)
    (sx : Sx) (ht : k + off + llen > len) (hm : ws.mems[n]? = some m) :
    ⊢ (n ↦[wmlength] (aw, len) -∗
      genHeapInterp (G := WasmG.memsizeHs) (gmapOfList (ws.mems.map memLengthMeta)) -∗
      ⌜loadPacked sx m k off llen len' = none⌝ : IProp GF) := by
  iintro Hlen Hms
  ihave %h := wms_is_not_load n k off len m ws llen ht hm $$ Hlen Hms
  ipureintro
  simp [loadPacked, h]

#rocq_ignore iriswasm.wms_is_not_store "out-of-bounds writes use width-indexed extents"
theorem wms_is_not_store (n k off len : Nat) (m : Memory) (ws : StoreRecord) (llen : Nat)
    (bv : Bytes) (ht : k + off + llen > len) (hm : ws.mems[n]? = some m) :
    ⊢ (n ↦[wmlength] (aw, len) -∗
      genHeapInterp (G := WasmG.memsizeHs) (gmapOfList (ws.mems.map memLengthMeta)) -∗
      ⌜store m k off bv llen = none⌝ : IProp GF) := by
  iintro Hlen Hms
  ihave %h := heap_lookup $$ Hms Hlen
  ipureintro
  rw [gmap_of_list_lookup, List.getElem?_map, hm, Option.map_some, Option.some.injEq] at h
  have hlen : lengthMem m = len := congrArg (fun p => p.2.1) h
  rw [store_eq]; split
  · omega
  · rfl

#rocq_ignore iriswasm.wms_is_not_store_packed "packed writes use width-indexed extents"
theorem wms_is_not_store_packed (n k off len : Nat) (m : Memory) (ws : StoreRecord) (llen : Nat)
    (bv : Bytes) (ht : k + off + llen > len) (hm : ws.mems[n]? = some m) :
    ⊢ (n ↦[wmlength] (aw, len) -∗
      genHeapInterp (G := WasmG.memsizeHs) (gmapOfList (ws.mems.map memLengthMeta)) -∗
      ⌜storePacked m k off bv llen = none⌝ : IProp GF) :=
  wms_is_not_store n k off len m ws llen bv ht hm

@[rocq_alias iriswasm.wms_implies_smems_is_Some]
theorem wms_implies_smems_is_Some (ws : StoreRecord) (n k : Nat) (b : Byte) (bs : Bytes) :
    ⊢ (genHeapInterp (G := WasmG.memHs) (gmapOfMemory ws.mems) -∗
      ([∗list] i ↦ b ∈ (b :: bs), n ↦[wm][ k + i ] b) -∗
      ([∗list] i ↦ b ∈ (b :: bs), n ↦[wm][ k + i ] b) ∗
        genHeapInterp (G := WasmG.memHs) (gmapOfMemory ws.mems) ∗
        ⌜∃ m, ws.mems[n]? = some m⌝ : IProp GF) := by
  iintro Hσ Hbs
  ihave %h := bigSep_valid $$ [$Hbs] [$Hσ]
  iframe
  ipureintro
  have h0 := h 0 b rfl
  rw [gmapOfMemory, gmap_of_list_2d_lookup, List.getElem?_map] at h0
  cases hm : ws.mems[n]? <;> simp_all

private theorem wms_mems_some {n p : Nat} {bv : Bytes} {mems : List Memory} (hpos : bv.length > 0) :
    ⊢ (n ↦[wms][ p ] bv -∗ genHeapInterp (G := WasmG.memHs) (gmapOfMemory mems) -∗
      ⌜∃ m, mems[n]? = some m⌝ : IProp GF) := by
  unfold memBlockAtPos
  iintro Hwms Hm
  ihave %h := bigSep_valid $$ Hwms Hm
  ipureintro
  obtain ⟨b, hb⟩ : ∃ b, bv[0]? = some b := ⟨_, List.getElem?_eq_getElem hpos⟩
  have h0 := h 0 b hb
  rw [gmapOfMemory, gmap_of_list_2d_lookup, List.getElem?_map] at h0
  cases hm : mems[n]? <;> simp_all

private theorem map_updateListAt {A B : Type} (g : A → B) {l : List A} {i : Nat} {a a' : A}
    (hl : l[i]? = some a) (h : g a' = g a) : (updateListAt l i a').map g = l.map g := by
  have hi := (List.getElem?_eq_some_iff.1 hl).1
  rw [← update_list_at_is_set_nth _ hi, List.map_set, h]
  apply List.ext_getElem?; intro j
  rw [List.getElem?_set]
  split <;> simp_all

variable {x : Nat}

theorem wp_load_deserialize (Φ : Val → IProp GF) (s : Stuckness) (E : CoPset) (t : ValueType)
    (bv : Bytes) (off : StaticOffset) (a : AlignmentExponent) (k : AddressOperand) (n : Nat) (f0 : Frame)
    (hlen : bv.length = lengthT t) (hn : f0.inst.memory[x]? = some n) :
    iprop(▷ Φ (.immV [wasmDeserialise bv t]) ∗ ↪[frame] f0 ∗
      n ↦[wms][ k.unsigned + off ] bv) ⊢
    WP ([.basic (.const k.value), .basic (.load t none ⟨x, a, off⟩)] : Expr) @ s ; E
      {{ w, (Φ w ∗ n ↦[wms][ k.unsigned + off ] bv) ∗ ↪[frame] f0 }} := by
  have hpos : bv.length > 0 := by rw [hlen]; cases t <;> decide
  have key := wp_wasm_step (s := s) (E := E) (f := f0) (f' := f0)
    (Φ := fun w => iprop(Φ w ∗ n ↦[wms][ k.unsigned + off ] bv))
    (R := iprop(▷ Φ (.immV [wasmDeserialise bv t]) ∗ n ↦[wms][ k.unsigned + off ] bv))
    (es := [.basic (.const k.value), .basic (.load t none ⟨x, a, off⟩)]) (by solve_toVal) fun ws => by
      unfold genHeapWasmStore
      iintro ⟨⟨HΦ, Hwms⟩, Hfn, Htb, Hm, Hgl, Hms, Hts, Hml, Htl⟩
      ihave %hm := wms_mems_some hpos $$ [$Hwms] [$Hm]
      obtain ⟨m, hm⟩ := hm
      ihave %hload := wms_is_load n k.unsigned off bv m ws hpos hm $$ [$Hwms] [$Hm]
      have hred : Reduce ws f0 [.basic (.const k.value), .basic (.load t none ⟨x, a, off⟩)] ws f0
          [.basic (.const (wasmDeserialise bv t))] :=
        .loadSuccess n m hn hm (by rw [← hlen]; exact hload)
      isplitr
      · ipureintro; exact ⟨_, _, _, hred⟩
      iintro !> %ws2 %f2 %es2 %Hred
      obtain ⟨rfl, rfl, rfl⟩ := reduce_det_of hred Hred
      imodintro
      iframe
      ipureintro
      exact ⟨rfl, by solve_toVal⟩
  iintro ⟨HΦ, Hf, Hwms⟩
  iapply key $$ [HΦ Hwms] Hf
  iframe

theorem wp_load (Φ : Val → IProp GF) (s : Stuckness) (E : CoPset) (t : ValueType) (v : Value)
    (off : StaticOffset) (a : AlignmentExponent) (k : AddressOperand) (n : Nat) (f : Frame)
    (ht : typesAgree t v = true) (hn : f.inst.memory[x]? = some n) :
    iprop(▷ Φ (.immV [v]) ∗ ↪[frame] f ∗ n ↦[wms][ k.unsigned + off ] (bits v)) ⊢
    WP ([.basic (.const k.value), .basic (.load t none ⟨x, a, off⟩)] : Expr) @ s ; E
      {{ w, (Φ w ∗ n ↦[wms][ k.unsigned + off ] (bits v)) ∗ ↪[frame] f }} := by
  have h := wp_load_deserialize Φ s E t (bits v) off a k n f (length_bits v t ht) hn
  rwa [deserialise_bits v t ht] at h

theorem wp_load_packed_deserialize (Φ : Val → IProp GF) (s : Stuckness) (E : CoPset)
    (t : ValueType) (bv : Bytes) (off : StaticOffset) (a : AlignmentExponent) (k : AddressOperand) (n : Nat)
    (f0 : Frame) (tp : PackedType) (sx : Sx) (hlen : bv.length = lengthTp tp)
    (htp : packedTypeOK tp t = true) (hn : f0.inst.memory[x]? = some n) :
    iprop(▷ Φ (.immV [wasmDeserialise (signExtend sx (lengthT t) bv) t]) ∗ ↪[frame] f0 ∗
      n ↦[wms][ k.unsigned + off ] bv) ⊢
    WP ([.basic (.const k.value), .basic (.load t (some (tp, sx)) ⟨x, a, off⟩)] : Expr) @ s ; E
      {{ w, (Φ w ∗ n ↦[wms][ k.unsigned + off ] bv) ∗ ↪[frame] f0 }} := by
  have hpos : bv.length > 0 := by rw [hlen]; cases tp <;> decide
  have key := wp_wasm_step (s := s) (E := E) (f := f0) (f' := f0)
    (Φ := fun w => iprop(Φ w ∗ n ↦[wms][ k.unsigned + off ] bv))
    (R := iprop(▷ Φ (.immV [wasmDeserialise (signExtend sx (lengthT t) bv) t]) ∗
      n ↦[wms][ k.unsigned + off ] bv))
    (es := [.basic (.const k.value), .basic (.load t (some (tp, sx)) ⟨x, a, off⟩)]) (by solve_toVal)
    fun ws => by
      unfold genHeapWasmStore
      iintro ⟨⟨HΦ, Hwms⟩, Hfn, Htb, Hm, Hgl, Hms, Hts, Hml, Htl⟩
      ihave %hm := wms_mems_some hpos $$ [$Hwms] [$Hm]
      obtain ⟨m, hm⟩ := hm
      ihave %hload := wms_is_load_packed n k.unsigned off bv m (lengthT t) ws sx hpos hm
        $$ [$Hwms] [$Hm]
      have hred : Reduce ws f0 [.basic (.const k.value), .basic (.load t (some (tp, sx)) ⟨x, a, off⟩)]
          ws f0 [.basic (.const (wasmDeserialise (signExtend sx (lengthT t) bv) t))] :=
        .loadPackedSuccess n m htp hn hm (by rw [← hlen]; exact hload)
      isplitr
      · ipureintro; exact ⟨_, _, _, hred⟩
      iintro !> %ws2 %f2 %es2 %Hred
      obtain ⟨rfl, rfl, rfl⟩ := reduce_det_of hred Hred
      imodintro
      iframe
      ipureintro
      exact ⟨rfl, by solve_toVal⟩
  iintro ⟨HΦ, Hf, Hwms⟩
  iapply key $$ [HΦ Hwms] Hf
  iframe

theorem wp_load_failure (Φ : Val → IProp GF) (s : Stuckness) (E : CoPset) (off : StaticOffset)
    (a : AlignmentExponent) (k : AddressOperand) (n : Nat) (f0 : Frame) (t : ValueType) (len : Nat)
    (hn : f0.inst.memory[x]? = some n) (hk : k.unsigned + off + lengthT t > len) :
    iprop(▷ Φ .trapV ∗ ↪[frame] f0 ∗ n ↦[wmlength] (aw, len)) ⊢
    WP ([.basic (.const k.value), .basic (.load t none ⟨x, a, off⟩)] : Expr) @ s ; E
      {{ w, (Φ w ∗ n ↦[wmlength] (aw, len)) ∗ ↪[frame] f0 }} := by
  have key := wp_wasm_step (s := s) (E := E) (f := f0) (f' := f0)
    (Φ := fun w => iprop(Φ w ∗ n ↦[wmlength] (aw, len)))
    (R := iprop(▷ Φ .trapV ∗ n ↦[wmlength] (aw, len)))
    (es := [.basic (.const k.value), .basic (.load t none ⟨x, a, off⟩)]) (by solve_toVal) fun ws => by
      unfold genHeapWasmStore
      iintro ⟨⟨HΦ, Hn⟩, Hfn, Htb, Hm, Hgl, Hms, Hts, Hml, Htl⟩
      ihave %hms := heap_lookup $$ [$Hms] [$Hn]
      rw [gmap_of_list_lookup, List.getElem?_map] at hms
      obtain ⟨m, hm, -⟩ := Option.map_eq_some_iff.1 hms
      ihave %hnone := wms_is_not_load n k.unsigned off len m ws (lengthT t) hk hm
        $$ [$Hn] [$Hms]
      have hred : Reduce ws f0 [.basic (.const k.value), .basic (.load t none ⟨x, a, off⟩)] ws f0
          [.trap] := .loadFailure n m hn hm hnone
      isplitr
      · ipureintro; exact ⟨_, _, _, hred⟩
      iintro !> %ws2 %f2 %es2 %Hred
      obtain ⟨rfl, rfl, rfl⟩ := reduce_det_of hred Hred
      imodintro
      iframe
      ipureintro
      exact ⟨rfl, by solve_toVal⟩
  iintro ⟨HΦ, Hf, Hn⟩
  iapply key $$ [HΦ Hn] Hf
  iframe

theorem wp_load_packed_failure (Φ : Val → IProp GF) (s : Stuckness) (E : CoPset)
    (off : StaticOffset) (a : AlignmentExponent) (k : AddressOperand) (n : Nat) (f0 : Frame) (t : ValueType)
    (len : Nat) (tp : PackedType) (sx : Sx) (hn : f0.inst.memory[x]? = some n)
    (htp : packedTypeOK tp t = true) (hk : k.unsigned + off + lengthTp tp > len) :
    iprop(▷ Φ .trapV ∗ ↪[frame] f0 ∗ n ↦[wmlength] (aw, len)) ⊢
    WP ([.basic (.const k.value), .basic (.load t (some (tp, sx)) ⟨x, a, off⟩)] : Expr) @ s ; E
      {{ w, (Φ w ∗ n ↦[wmlength] (aw, len)) ∗ ↪[frame] f0 }} := by
  have key := wp_wasm_step (s := s) (E := E) (f := f0) (f' := f0)
    (Φ := fun w => iprop(Φ w ∗ n ↦[wmlength] (aw, len)))
    (R := iprop(▷ Φ .trapV ∗ n ↦[wmlength] (aw, len)))
    (es := [.basic (.const k.value), .basic (.load t (some (tp, sx)) ⟨x, a, off⟩)]) (by solve_toVal)
    fun ws => by
      unfold genHeapWasmStore
      iintro ⟨⟨HΦ, Hn⟩, Hfn, Htb, Hm, Hgl, Hms, Hts, Hml, Htl⟩
      ihave %hms := heap_lookup $$ [$Hms] [$Hn]
      rw [gmap_of_list_lookup, List.getElem?_map] at hms
      obtain ⟨m, hm, -⟩ := Option.map_eq_some_iff.1 hms
      ihave %hnone := wms_is_not_load_packed n k.unsigned off len m ws (lengthTp tp)
        (lengthT t) sx hk hm $$ [$Hn] [$Hms]
      have hred : Reduce ws f0 [.basic (.const k.value), .basic (.load t (some (tp, sx)) ⟨x, a, off⟩)]
          ws f0 [.trap] := .loadPackedFailure n m htp hn hm hnone
      isplitr
      · ipureintro; exact ⟨_, _, _, hred⟩
      iintro !> %ws2 %f2 %es2 %Hred
      obtain ⟨rfl, rfl, rfl⟩ := reduce_det_of hred Hred
      imodintro
      iframe
      ipureintro
      exact ⟨rfl, by solve_toVal⟩
  iintro ⟨HΦ, Hf, Hn⟩
  iapply key $$ [HΦ Hn] Hf
  iframe

theorem wp_store (ϕ : Val → IProp GF) (s : Stuckness) (E : CoPset) (t : ValueType) (v : Value)
    (bs : Bytes) (off : StaticOffset) (a : AlignmentExponent) (k : AddressOperand) (n : Nat) (f : Frame)
    (ht : typesAgree t v = true) (hlen : bs.length = lengthT t)
    (hn : f.inst.memory[x]? = some n) :
    iprop(▷ ϕ (.immV []) ∗ ↪[frame] f ∗ n ↦[wms][ k.unsigned + off ] bs) ⊢
    WP ([.basic (.const k.value), .basic (.const v), .basic (.store t none ⟨x, a, off⟩)] : Expr)
      @ s ; E {{ w, (ϕ w ∗ n ↦[wms][ k.unsigned + off ] (bits v)) ∗ ↪[frame] f }} := by
  have hpos : bs.length > 0 := by rw [hlen]; cases t <;> decide
  have hbits := length_bits v t ht
  have key := wp_wasm_step (s := s) (E := E) (f := f) (f' := f)
    (Φ := fun w => iprop(ϕ w ∗ n ↦[wms][ k.unsigned + off ] (bits v)))
    (R := iprop(▷ ϕ (.immV []) ∗ n ↦[wms][ k.unsigned + off ] bs))
    (es := [.basic (.const k.value), .basic (.const v), .basic (.store t none ⟨x, a, off⟩)])
    (by solve_toVal) fun ws => by
      unfold genHeapWasmStore
      iintro ⟨⟨HΦ, Hwms⟩, Hfn, Htb, Hm, Hgl, Hms, Hts, Hml, Htl⟩
      ihave %hm := wms_mems_some hpos $$ [$Hwms] [$Hm]
      obtain ⟨m, hm⟩ := hm
      ihave %hload := wms_is_load n k.unsigned off bs m ws hpos hm $$ [$Hwms] [$Hm]
      have hbound := (load_some_iff.1 hload).1
      obtain ⟨m', hst⟩ := enough_space_to_store m k.unsigned off (bits v)
        (by rw [lengthMem_eq_data_length]; omega)
      have hred : Reduce ws f
          [.basic (.const k.value), .basic (.const v), .basic (.store t none ⟨x, a, off⟩)]
          (updSMem ws (updateListAt ws.mems n m')) f [] :=
        .storeSuccess m ht hn hm (by rw [← hbits]; exact hst)
      isplitr
      · ipureintro; exact ⟨_, _, _, hred⟩
      iintro !> %ws2 %f2 %es2 %Hred
      obtain ⟨rfl, rfl, rfl⟩ := reduce_det_of hred Hred
      imod gen_heap_update_big_wm bs (bits v) k.unsigned off n ws.mems _ m m' (by omega)
        hload hst rfl hm $$ Hm Hwms with ⟨Hm, Hwms⟩
      simp only [updSMem]
      rw [store_mem_meta_eq m _ off (bits v) m' n ws.mems hm hst,
        map_updateListAt (·.type.limits.max) hm
          (congrArg (fun mt : MemoryType => mt.limits.max) (store_mem_type _ _ _ _ _ _ hst)).symm]
      imodintro
      iframe
      ipureintro
      rfl
  iintro ⟨HΦ, Hf, Hwms⟩
  iapply key $$ [HΦ Hwms] Hf
  iframe

theorem wp_store_packed (ϕ : Val → IProp GF) (s : Stuckness) (E : CoPset) (t : ValueType)
    (v : Value) (bs : Bytes) (off : StaticOffset) (a : AlignmentExponent) (k : AddressOperand) (n : Nat)
    (f0 : Frame) (tp : PackedType) (ht : typesAgree t v = true) (hlen : bs.length = lengthTp tp)
    (htp : packedTypeOK tp t = true) (hn : f0.inst.memory[x]? = some n) :
    iprop(▷ ϕ (.immV []) ∗ ↪[frame] f0 ∗ n ↦[wms][ k.unsigned + off ] bs) ⊢
    WP ([.basic (.const k.value), .basic (.const v), .basic (.store t (some tp) ⟨x, a, off⟩)] : Expr)
      @ s ; E {{ w, (ϕ w ∗ n ↦[wms][ k.unsigned + off ]
        (bytesTakefill 0 (lengthTp tp) (bits v))) ∗ ↪[frame] f0 }} := by
  have hpos : bs.length > 0 := by rw [hlen]; cases tp <;> decide
  have hbs' := length_bytes_takefill 0 (lengthTp tp) (bits v)
  have key := wp_wasm_step (s := s) (E := E) (f := f0) (f' := f0)
    (Φ := fun w => iprop(ϕ w ∗ n ↦[wms][ k.unsigned + off ]
      (bytesTakefill 0 (lengthTp tp) (bits v))))
    (R := iprop(▷ ϕ (.immV []) ∗ n ↦[wms][ k.unsigned + off ] bs))
    (es := [.basic (.const k.value), .basic (.const v), .basic (.store t (some tp) ⟨x, a, off⟩)])
    (by solve_toVal) fun ws => by
      unfold genHeapWasmStore
      iintro ⟨⟨HΦ, Hwms⟩, Hfn, Htb, Hm, Hgl, Hms, Hts, Hml, Htl⟩
      ihave %hm := wms_mems_some hpos $$ [$Hwms] [$Hm]
      obtain ⟨m, hm⟩ := hm
      ihave %hload := wms_is_load n k.unsigned off bs m ws hpos hm $$ [$Hwms] [$Hm]
      have hbound := (load_some_iff.1 hload).1
      obtain ⟨m', hst⟩ : ∃ m', store m k.unsigned off (bits v) (lengthTp tp) = some m' :=
        ⟨_, store_some_iff.2 ⟨by omega, rfl⟩⟩
      have hst' : store m k.unsigned off (bytesTakefill 0 (lengthTp tp) (bits v))
          (bytesTakefill 0 (lengthTp tp) (bits v)).length = some m' := by
        rw [hbs', store_bytes_takefill_eq]; exact hst
      have hred : Reduce ws f0
          [.basic (.const k.value), .basic (.const v), .basic (.store t (some tp) ⟨x, a, off⟩)]
          (updSMem ws (updateListAt ws.mems n m')) f0 [] :=
        .storePackedSuccess m htp ht hn hm hst
      isplitr
      · ipureintro; exact ⟨_, _, _, hred⟩
      iintro !> %ws2 %f2 %es2 %Hred
      obtain ⟨rfl, rfl, rfl⟩ := reduce_det_of hred Hred
      imod gen_heap_update_big_wm bs _ k.unsigned off n ws.mems _ m m' (by omega)
        hload hst' rfl hm $$ Hm Hwms with ⟨Hm, Hwms⟩
      simp only [updSMem]
      rw [store_mem_meta_eq m _ off _ m' n ws.mems hm hst',
        map_updateListAt (·.type.limits.max) hm
          (congrArg (fun mt : MemoryType => mt.limits.max) (store_mem_type _ _ _ _ _ _ hst)).symm]
      imodintro
      iframe
      ipureintro
      rfl
  iintro ⟨HΦ, Hf, Hwms⟩
  iapply key $$ [HΦ Hwms] Hf
  iframe

theorem wp_store_failure (ϕ : Val → IProp GF) (s : Stuckness) (E : CoPset) (t : ValueType)
    (v : Value) (off : StaticOffset) (a : AlignmentExponent) (k : AddressOperand) (n : Nat) (f0 : Frame)
    (len : Nat) (ht : typesAgree t v = true) (hn : f0.inst.memory[x]? = some n)
    (hk : k.unsigned + off + lengthT t > len) :
    iprop(▷ ϕ .trapV ∗ ↪[frame] f0 ∗ n ↦[wmlength] (aw, len)) ⊢
    WP ([.basic (.const k.value), .basic (.const v), .basic (.store t none ⟨x, a, off⟩)] : Expr)
      @ s ; E {{ w, (ϕ w ∗ n ↦[wmlength] (aw, len)) ∗ ↪[frame] f0 }} := by
  have key := wp_wasm_step (s := s) (E := E) (f := f0) (f' := f0)
    (Φ := fun w => iprop(ϕ w ∗ n ↦[wmlength] (aw, len)))
    (R := iprop(▷ ϕ .trapV ∗ n ↦[wmlength] (aw, len)))
    (es := [.basic (.const k.value), .basic (.const v), .basic (.store t none ⟨x, a, off⟩)])
    (by solve_toVal) fun ws => by
      unfold genHeapWasmStore
      iintro ⟨⟨HΦ, Hn⟩, Hfn, Htb, Hm, Hgl, Hms, Hts, Hml, Htl⟩
      ihave %hms := heap_lookup $$ [$Hms] [$Hn]
      rw [gmap_of_list_lookup, List.getElem?_map] at hms
      obtain ⟨m, hm, -⟩ := Option.map_eq_some_iff.1 hms
      ihave %hnone := wms_is_not_store n k.unsigned off len m ws (lengthT t) (bits v) hk hm
        $$ [$Hn] [$Hms]
      have hred : Reduce ws f0
          [.basic (.const k.value), .basic (.const v), .basic (.store t none ⟨x, a, off⟩)] ws f0
          [.trap] := .storeFailure n m ht hn hm hnone
      isplitr
      · ipureintro; exact ⟨_, _, _, hred⟩
      iintro !> %ws2 %f2 %es2 %Hred
      obtain ⟨rfl, rfl, rfl⟩ := reduce_det_of hred Hred
      imodintro
      iframe
      ipureintro
      exact ⟨rfl, by solve_toVal⟩
  iintro ⟨HΦ, Hf, Hn⟩
  iapply key $$ [HΦ Hn] Hf
  iframe

theorem wp_store_packed_failure (ϕ : Val → IProp GF) (s : Stuckness) (E : CoPset) (t : ValueType)
    (v : Value) (off : StaticOffset) (a : AlignmentExponent) (k : AddressOperand) (n : Nat) (f0 : Frame)
    (len : Nat) (tp : PackedType) (ht : typesAgree t v = true) (hn : f0.inst.memory[x]? = some n)
    (htp : packedTypeOK tp t = true) (hk : k.unsigned + off + lengthTp tp > len) :
    iprop(▷ ϕ .trapV ∗ ↪[frame] f0 ∗ n ↦[wmlength] (aw, len)) ⊢
    WP ([.basic (.const k.value), .basic (.const v), .basic (.store t (some tp) ⟨x, a, off⟩)] : Expr)
      @ s ; E {{ w, (ϕ w ∗ n ↦[wmlength] (aw, len)) ∗ ↪[frame] f0 }} := by
  have key := wp_wasm_step (s := s) (E := E) (f := f0) (f' := f0)
    (Φ := fun w => iprop(ϕ w ∗ n ↦[wmlength] (aw, len)))
    (R := iprop(▷ ϕ .trapV ∗ n ↦[wmlength] (aw, len)))
    (es := [.basic (.const k.value), .basic (.const v), .basic (.store t (some tp) ⟨x, a, off⟩)])
    (by solve_toVal) fun ws => by
      unfold genHeapWasmStore
      iintro ⟨⟨HΦ, Hn⟩, Hfn, Htb, Hm, Hgl, Hms, Hts, Hml, Htl⟩
      ihave %hms := heap_lookup $$ [$Hms] [$Hn]
      rw [gmap_of_list_lookup, List.getElem?_map] at hms
      obtain ⟨m, hm, -⟩ := Option.map_eq_some_iff.1 hms
      ihave %hnone := wms_is_not_store_packed n k.unsigned off len m ws (lengthTp tp)
        (bits v) hk hm $$ [$Hn] [$Hms]
      have hred : Reduce ws f0
          [.basic (.const k.value), .basic (.const v), .basic (.store t (some tp) ⟨x, a, off⟩)] ws f0
          [.trap] := .storePackedFailure n m htp ht hn hm hnone
      isplitr
      · ipureintro; exact ⟨_, _, _, hred⟩
      iintro !> %ws2 %f2 %es2 %Hred
      obtain ⟨rfl, rfl, rfl⟩ := reduce_det_of hred Hred
      imodintro
      iframe
      ipureintro
      exact ⟨rfl, by solve_toVal⟩
  iintro ⟨HΦ, Hf, Hn⟩
  iapply key $$ [HΦ Hn] Hf
  iframe

theorem wp_current_memory (s : Stuckness) (E : CoPset) (k n : Nat) (f : Frame)
    (Φ : Val → IProp GF) (hk : f.inst.memory[x]? = some k) (hs : WellSized aw n) :
    iprop(▷ Φ (.immV [aw.natValue (n / pageSize)]) ∗
      ↪[frame] f ∗ k ↦[wmlength] (aw, n)) ⊢
    WP ([.basic (.currentMemory x)] : Expr) @ s ; E
      {{ w, (Φ w ∗ k ↦[wmlength] (aw, n)) ∗ ↪[frame] f }} := by
  have key := wp_wasm_step (s := s) (E := E) (f := f) (f' := f)
    (Φ := fun w => iprop(Φ w ∗ k ↦[wmlength] (aw, n)))
    (R := iprop(▷ Φ (.immV [aw.natValue (n / pageSize)]) ∗ k ↦[wmlength] (aw, n)))
    (es := [.basic (.currentMemory x)]) (by solve_toVal) fun ws => by
      unfold genHeapWasmStore
      iintro ⟨⟨HΦ, Hn⟩, Hfn, Htb, Hm, Hgl, Hms, Hts, Hml, Htl⟩
      ihave %hms := heap_lookup $$ [$Hms] [$Hn]
      rw [gmap_of_list_lookup, List.getElem?_map] at hms
      obtain ⟨m, hm, he⟩ := Option.map_eq_some_iff.1 hms
      have hw : m.type.address = aw := congrArg Prod.fst he
      have hlen : lengthMem m = n := congrArg (fun p => p.2.1) he
      have hred : Reduce ws f [.basic (.currentMemory x)] ws f
          [.basic (.const (aw.natValue (n / pageSize)))] := by
        rw [← hw]
        apply Reduce.currentMemory k m hk hm
        · rw [hlen]; exact hs.pages_mul
        · rw [hw]; exact hs.pages_fit
      isplitr
      · ipureintro; exact ⟨_, _, _, hred⟩
      iintro !> %ws2 %f2 %es2 %Hred
      obtain ⟨rfl, rfl, rfl⟩ := reduce_det_of hred Hred
      imodintro
      iframe
      ipureintro
      exact ⟨rfl, by solve_toVal⟩
  iintro ⟨HΦ, Hf, Hn⟩
  iapply key $$ [HΦ Hn] Hf
  iframe

private theorem gmapOfMemory_snoc {mems : List Memory} {k : Nat} {d : List Byte} {o : MemoryType}
    (hm : mems[k]? = some ⟨MemoryList.ofBytes d, o⟩) (b : Byte) :
    insert (gmapOfMemory mems) (k, d.length) b =
      gmapOfMemory (mems.set k ⟨MemoryList.ofBytes (d ++ [b]), o⟩) := by
  apply LawfulPartialMap.equiv_iff_eq.1
  rintro ⟨i, j⟩
  have hk := (List.getElem?_eq_some_iff.1 hm).1
  rw [LawfulPartialMap.get?_insert, gmapOfMemory, gmapOfMemory, gmap_of_list_2d_lookup, gmap_of_list_2d_lookup,
    List.map_set, List.getElem?_set, List.getElem?_map]
  by_cases hi : k = i
  · subst hi
    simp only [hm, Option.map_some, List.length_map, hk, ite_true, Prod.mk.injEq, true_and,
      memoryToList, MemoryList.data_ofBytes, List.getElem?_append, List.getElem?_singleton]
    grind
  · simp [hi]

/-- Allocate the bytes `bs` at the end of the memory `k` (data `d`). -/
private theorem heap_alloc_bytes (k : Nat) (o : MemoryType) (bs : Bytes) : ∀ (d : List Byte)
    (mems : List Memory), mems[k]? = some ⟨MemoryList.ofBytes d, o⟩ →
    ⊢ (genHeapInterp (G := WasmG.memHs) (gmapOfMemory mems) ==∗
      genHeapInterp (G := WasmG.memHs) (gmapOfMemory (mems.set k ⟨MemoryList.ofBytes (d ++ bs), o⟩)) ∗
        k ↦[wms][ d.length ] bs : IProp GF) := by
  induction bs with
  | nil =>
    intro d mems hm
    obtain ⟨hn, hm⟩ := List.getElem?_eq_some_iff.1 hm
    simp only [List.append_nil]
    rw [← hm, List.set_getElem_self hn]
    iintro Hσ
    imodintro
    isplitl [Hσ]
    · iexact Hσ
    unfold memBlockAtPos
    iapply BigSepL.bigSepL_nil.2
    iempintro
  | cons b bs ih =>
    intro d mems hm
    have hn := (List.getElem?_eq_some_iff.1 hm).1
    have key := ih (d ++ [b]) (mems.set k ⟨MemoryList.ofBytes (d ++ [b]), o⟩)
      (by rw [List.getElem?_set_self hn])
    rw [List.set_set, List.append_assoc, List.singleton_append, List.length_append,
      List.length_singleton] at key
    iintro Hσ
    imod @genHeap_alloc _ _ _ _ _ WasmG.memHs _ _ (k, d.length) b
      (by rw [get?_gmapOfMemory hm, MemoryList.data_ofBytes]; simp) $$ Hσ with ⟨Hσ, Hb, -⟩
    rw [gmapOfMemory_snoc hm b]
    imod key $$ Hσ with ⟨Hσ, Hbs⟩
    imodintro
    isplitl [Hσ]
    · iexact Hσ
    iapply (wandIff_equiv (wms_append (GF := GF) k d.length b bs)).2
    isplitl [Hb]
    · iexact Hb
    · iexact Hbs

@[rocq_alias iriswasm.gen_heap_alloc_grow]
theorem gen_heap_alloc_grow (m m' : Memory) (mems mems' : List Memory) (k n : Nat)
    (hm : mems[k]? = some m) (hg : memGrow m n = some m') (hu : updateListAt mems k m' = mems') :
    ⊢ (genHeapInterp (G := WasmG.memHs) (gmapOfMemory mems) ==∗
      genHeapInterp (G := WasmG.memHs) (gmapOfMemory mems') ∗
        k ↦[wms][ lengthMem m ] List.replicate (n * pageSize) (0 : Byte) : IProp GF) := by
  subst hu
  rw [← update_list_at_is_set_nth _ (List.getElem?_eq_some_iff.1 hm).1, lengthMem_eq_data_length]
  have he : gmapOfMemory (mems.set k m') = gmapOfMemory
      (mems.set k ⟨MemoryList.ofBytes (m.data.data ++ List.replicate (n * pageSize) 0), m.type⟩) := by
    simp only [gmapOfMemory, List.map_set, memoryToList, mem_grow_data m n m' hg,
      MemoryList.data_ofBytes]
  rw [he]
  exact heap_alloc_bytes k m.type _ m.data.data mems (by simpa only [MemoryList.ofBytes_data] using hm)

theorem wp_grow_memory (s : Stuckness) (E : CoPset) (k : Nat) (f : Frame) (n : Nat)
    (Φ Ψ : Val → IProp GF) (c : AddressOperand) (hk : f.inst.memory[x]? = some k) :
    iprop(↪[frame] f ∗ k ↦[wmlength] (aw, n) ∗
      ▷ Φ (.immV [c.result (n / pageSize)]) ∗
      ▷ Ψ (.immV [c.failure])) ⊢
    WP ([.basic (.const c.value), .basic (.growMemory x)] : Expr) @ s ; E
      {{ w, (((Φ w ∗ k ↦[wms][ n ] List.replicate (c.unsigned * pageSize) (0 : Byte) ∗
          k ↦[wmlength] (aw, n + c.unsigned * pageSize)) ∗
          ⌜MemInBound aw (n / pageSize + c.unsigned)⌝) ∨
        (Ψ w ∗ k ↦[wmlength] (aw, n))) ∗ ↪[frame] f }} := by
  have key := wp_wasm_step (s := s) (E := E) (f := f) (f' := f)
    (Φ := fun w => iprop(((Φ w ∗
        k ↦[wms][ n ] List.replicate (c.unsigned * pageSize) (0 : Byte) ∗
        k ↦[wmlength] (aw, n + c.unsigned * pageSize)) ∗
        ⌜MemInBound aw (n / pageSize + c.unsigned)⌝) ∨ (Ψ w ∗ k ↦[wmlength] (aw, n))))
    (R := iprop(k ↦[wmlength] (aw, n) ∗
      ▷ Φ (.immV [c.result (n / pageSize)]) ∗
      ▷ Ψ (.immV [c.failure])))
    (es := [.basic (.const c.value), .basic (.growMemory x)]) (by solve_toVal) fun ws => by
      unfold genHeapWasmStore
      iintro ⟨⟨Hn, HΦ, HΨ⟩, Hfn, Htb, Hm, Hgl, Hms, Hts, Hml, Htl⟩
      ihave %hms := heap_lookup $$ [$Hms] [$Hn]
      rw [gmap_of_list_lookup, List.getElem?_map] at hms
      obtain ⟨m, hm, he⟩ := Option.map_eq_some_iff.1 hms
      have hw : m.type.address = aw := congrArg Prod.fst he
      have hlen : lengthMem m = n := congrArg (fun p => p.2.1) he
      have hkl := (List.getElem?_eq_some_iff.1 hm).1
      isplitr
      · ipureintro; exact ⟨_, _, _, .growMemoryFailure (c := c)⟩
      iintro !> %ws2 %f2 %es2 %Hred
      obtain ⟨rfl, ⟨i, m', mem', hi, hm', -, hg, rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ :=
        grow_memory_inv (c := c) Hred
      · rw [hk, Option.some.injEq] at hi
        subst hi
        rw [hm, Option.some.injEq] at hm'
        subst hm'
        have hb : memSize m + c.unsigned ≤ aw.pageLimit := hw ▸ (memGrow_spec hg).2.2.1
        imod @genHeap_update _ _ _ _ _ WasmG.memsizeHs _ _ _ _
          (memLengthToken (aw, n + c.unsigned * pageSize)) $$ [$Hms $Hn] with ⟨Hms, Hn⟩
        imod gen_heap_alloc_grow m mem' ws.mems _ k c.unsigned hm hg rfl $$ Hm
          with ⟨Hm, Hwms⟩
        have e1 : (updateListAt ws.mems k mem').map memLengthMeta =
            (ws.mems.map memLengthMeta).set k (memLengthToken (aw, n + c.unsigned * pageSize)) := by
          rw [← update_list_at_is_set_nth _ hkl, List.map_set]
          simp only [memLengthMeta, memLengthToken, (memGrow_spec hg).2.1, hw,
            mem_grow_length _ _ _ hg, memSize, hlen, Nat.add_mul_div_right _ _ (by decide : 0 < pageSize)]
        simp only [updSMem]
        rw [← gmap_of_list_insert (ws.mems.map memLengthMeta) _ k (by simpa using hkl), ← e1,
          map_updateListAt (·.type.limits.max) hm (mem_grow_max _ _ _ hg).symm, hlen]
        imodintro
        isplitr
        · ipureintro; trivial
        isplitl [Hfn Htb Hm Hgl Hms Hts Hml Htl]
        · iframe
        iexists (Val.immV [c.result (n / pageSize)])
        isplitr
        · ipureintro; simp only [memSize, hlen]; solve_toVal
        ileft
        iframe
        ipureintro
        simp only [MemInBound]; rw [memSize, hlen] at hb; exact hb
      · imodintro
        isplitr
        · ipureintro; trivial
        isplitl [Hfn Htb Hm Hgl Hms Hts Hml Htl]
        · iframe
        iexists (Val.immV [c.failure])
        isplitr
        · ipureintro; solve_toVal
        iright
        iframe
  iintro ⟨Hf, Hn, HΦ, HΨ⟩
  iapply key $$ [Hn HΦ HΨ] Hf
  iframe

end iris

end IrisWasm
