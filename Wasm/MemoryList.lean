/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import Wasm.Bytes

/-! Port of `theories/memory_list.v`: Wasm linear memory as a list of bytes. -/

namespace Wasm

@[rocq_alias iriswasm.memory_list]
structure MemoryList where
  data : List Byte
  deriving DecidableEq, Repr, Inhabited

#rocq_ignore iriswasm.memory_list_eq_dec "deriving DecidableEq"
#rocq_ignore iriswasm.memory_list_eqb "deriving DecidableEq"
#rocq_ignore iriswasm.eqmemory_listP "deriving DecidableEq"

namespace MemoryList

@[rocq_alias iriswasm.mem_make]
def memMake (v : Byte) (len : Nat) : MemoryList := ⟨List.replicate len v⟩

@[rocq_alias iriswasm.memory_list.length_mem]
def lengthMem (ml : MemoryList) : Nat := ml.data.length

@[rocq_alias iriswasm.memory_list.mem_grow]
def memGrow (lenDelta : Nat) (ml : MemoryList) : MemoryList :=
  ⟨ml.data ++ List.replicate lenDelta 0⟩

@[rocq_alias iriswasm.mem_lookup]
def memLookup (i : Nat) (ml : MemoryList) : Option Byte := ml.data[i]?

@[rocq_alias iriswasm.mem_update]
def memUpdate (i : Nat) (v : Byte) (ml : MemoryList) : Option MemoryList :=
  if i < ml.data.length then some ⟨ml.data.take i ++ [v] ++ ml.data.drop (i + 1)⟩ else none

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
  simp [memLookup, lengthMem] at *; omega

@[rocq_alias iriswasm.memory_list_ax_lookup_make]
theorem memory_list_ax_lookup_make (i len : Nat) (b : Byte) (h : i < len) :
    (memMake b len).memLookup i = some b :=
  nth_repeat b i len h

@[rocq_alias iriswasm.memory_list_ax_lookup_update]
theorem memory_list_ax_lookup_update (mem mem' : MemoryList) (i : Nat) (b : Byte)
    (h : i < mem.lengthMem) (h' : some mem' = mem.memUpdate i b) : mem'.memLookup i = some b := by
  simp only [memUpdate, lengthMem] at *
  simp only [h, ↓reduceIte] at h'
  cases h'
  simpa [memLookup] using lookup_split mem.data i b h

@[rocq_alias iriswasm.memory_list_ax_lookup_skip]
theorem memory_list_ax_lookup_skip (mem mem' : MemoryList) (i i' : Nat) (b : Byte) (hne : i ≠ i')
    (h' : some mem' = mem.memUpdate i' b) : mem'.memLookup i = mem.memLookup i := by
  simp only [memUpdate] at h'
  split at h'
  · cases h'
    simpa [memLookup] using bar i i' mem.data b hne ‹_›
  · cases h'

@[rocq_alias iriswasm.memory_list_ax_length_constant_update]
theorem memory_list_ax_length_constant_update (i : Nat) (b : Byte) (mem mem' : MemoryList)
    (h' : some mem' = mem.memUpdate i b) : mem'.lengthMem = mem.lengthMem := by
  simp only [memUpdate] at h'
  split at h'
  · cases h'
    simpa [lengthMem] using split_preserves_length i b mem.data ‹_›
  · cases h'

end MemoryList

end Wasm
