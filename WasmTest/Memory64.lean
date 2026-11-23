import Wasm.Binary
import Wasm.ModuleValidation
import IrisWasm.Denotational.Run

namespace WasmTest.Memory64
open Wasm IrisWasm IrisWasm.Denotational

private def mt : MemoryType := ⟨.i64, ⟨65537, some 65538⟩⟩
private def m0 : Module :=
  { (default : Module) with
    types := [.tf [] [.i32]]
    funcs := [⟨.typeidx 0, [], [.const (.int64 0x100000000), .load .i32 (some (.i8,.u)) ⟨0,0,1⟩]⟩]
    mems := [mt]
    data := [⟨.memidx 0, [.const (.int64 0x100000001)], [0xab]⟩]
    exports := [⟨[0x66], .func (.funcidx 0)⟩] }

private def empty : StoreRecord := ⟨[], [], [], []⟩

theorem declared_memory64 : ModuleTyping m0 [] [.func (.tf [] [.i32])] :=
  (validateModule_iff m0 ⟨[], [.func (.tf [] [.i32])]⟩).mp rfl

#guard !(validateModule {m0 with data := [⟨.memidx 0, [.const (.int32 1)], [0xab]⟩]}).isOk
#guard !(validateModule {m0 with mems := [⟨.i32, ⟨1, none⟩⟩]}).isOk
#guard !(validateModule {m0 with mems := [⟨.i64, ⟨2^48+1, none⟩⟩]}).isOk

private def ctx : TContext := ⟨[], [], [], [], [mt], [], [], none⟩
#guard bETypeChecker ctx [.load .i32 none ⟨0,2,2^64-1⟩] (.tf [.i64] [.i32])
#guard !bETypeChecker ctx [.load .i32 none ⟨0,2,2^64⟩] (.tf [.i64] [.i32])
#guard !bETypeChecker ctx [.load .i32 none ⟨0,2,0⟩] (.tf [.i32] [.i32])
#guard bETypeChecker ctx [.growMemory 0] (.tf [.i64] [.i64])
#guard !bETypeChecker ctx [.growMemory 0] (.tf [.i32] [.i32])

private def highInitRead : Option Nat := do
  let (s, i, ex) := interpAllocModule empty m0 [] []
  guard (allocModule empty m0 [] [] (s, i, ex))
  let some d := m0.data[0]? | none
  let (_, .boundary (.immV [v])) := runUntil 2 (toEList d.offset, s, [], i) | none
  let off ← AddressOperand.ofValue? v
  guard (checkBoundsData i s m0 [off])
  let .ok s' := initMems s i [off.unsigned] m0.data | none
  let m ← s'.mems[0]?
  guard (m.type == mt && m.data.pages.size == 1 && m.data.memLookup 1 == some 0)
  let e ← ex[0]?
  let .func (.funcidx a) := e.desc | none
  let (_, .boundary (.immV [.int32 x])) := runUntil 7 ([.invoke a], s', [], emptyInstance) | none
  return x.toNat

theorem initialized_above_4GiB : highInitRead = some 0xab := by decide +kernel

private def allocated := interpAllocModule empty m0 [] []

/-- The high active segment also satisfies the relational instantiation premises. -/
theorem declarative_wide_instance :
    ∃ after, Instantiate empty m0 [] ((after, allocated.2.1, allocated.2.2), none) := by
  let offs := [AddressOperand.i64 0x100000001]
  have hb : checkBoundsData allocated.2.1 allocated.1 m0 offs = true := by decide +kernel
  obtain ⟨after, hinit⟩ := initMems_exists_of_bounds hb
  refine ⟨after, [], [.func (.tf [] [.i32])], allocated.1, [], [], offs,
    declared_memory64, .nil, ?_, .nil, .nil, ?_, rfl, hb, rfl, hinit⟩
  · decide +kernel
  · exact .cons .refl .nil

private def single (m : Memory) : State := (⟨[],[],[m],[]⟩, [], {emptyInstance with memory := [0]})
private def i64 (x : I64) := AdministrativeInstruction.basic (.const (.int64 x))
private def i32 (x : I32) := AdministrativeInstruction.basic (.const (.int32 x))

private def growCheck : Option Bool := do
  let st := single (memMk mt)
  let (es, s, _, _) ← runCut 3 ([.basic (.currentMemory 0), i64 1, .basic (.growMemory 0),
    .basic (.currentMemory 0)], st)
  let m ← s.mems[0]?
  return es == [i64 65537, i64 65537, i64 65538] && m.type == ⟨.i64, ⟨65538, some 65538⟩⟩ &&
    m.data.lengthMem == 65538 * pageSize && m.data.pages.size == 0

theorem grow_updates_descriptor : growCheck = some true := by decide +kernel
-- Even a zero delta cannot return the old count in an i32 if that count doesn't fit i32.
private def huge := single (memMk ⟨.i64, ⟨2^32, none⟩⟩)
#guard runCut 1 ([i32 0, .basic (.growMemory 0)], huge) == some ([i32 (-1)], huge)
#guard runCut 1 ([.basic (.currentMemory 0)], huge) == some ([i64 (2^32)], huge)

theorem size_stuck {s f s' f' out x i m} (hi : f.inst.memory[x]? = some i) (hm : s.mems[i]? = some m)
    (bad : ¬ (lengthMem m = memSize m * pageSize ∧ memSize m < 2^m.type.address.width)) :
    ¬ Reduce s f [.basic (.currentMemory x)] s' f' out := by
  intro step
  have hr := (round_next_iff (σ := stateOf s f) (σ' := stateOf s' f')).2 ⟨step, rfl, rfl⟩
  change Runs (layer _) (stateOf s f) (.next out) (stateOf s' f') at hr
  simp [layer, frag, basicLayer, handle, withMemory, stateOf, hi, hm, bad] at hr

-- Unaligned raw byte vectors are not rounded down to a page count.
private def broken := single ⟨MemoryList.ofBytes [1], ⟨.i64, ⟨0, none⟩⟩⟩
#guard runCut 1 ([.basic (.currentMemory 0)], broken) == none

private def failedSegmentStore : Option Bool := do
  let (s, _, i) := single (memMk mt)
  let d : ModuleData := ⟨.memidx 0, [], [0x55]⟩
  let .error after := initMems s i [2^32+1,65537*pageSize] [d,d] | none
  let m ← after.mems[0]?
  return m.data.memLookup (2^32+1) == some 0x55 && m.data.lengthMem == 65537*pageSize &&
    m.data.memLookup 1 == some 0 && m.data.pages.size == 1

theorem failed_segment_keeps_prior_write : failedSegmentStore = some true := by decide +kernel
#guard match initMem (single (memMk mt)).1 emptyInstance 0 ⟨.memidx 1, [], [7]⟩ with
  | .error s => s == (single (memMk mt)).1
  | _ => false

/-- The pinned `memory.fill-succ` writes `CONST at (i+1)` even on its last iteration. -/
theorem last_byte_fill_residual (aw : AddrType) :
    let m := memMk ⟨aw, ⟨aw.pageLimit, none⟩⟩
    let i := 2^aw.width - 1
    MemAgree m ∧ i+1 ≤ lengthMem m ∧ ¬ ∃ v : BitVec aw.width, v.toNat = i+1 := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · cases aw <;> constructor <;> decide +kernel
  · cases aw <;> decide +kernel
  · rintro ⟨v, h⟩
    have hb := v.isLt
    cases aw <;> simp [AddrType.width] at * <;> omega

/-- In the erratum, a forward source or destination can wrap only on the last byte.
    The unchanged zero-count continuation still passes that operand's bounds check. -/
theorem forward_residual_range {width length n : Nat} (i : BitVec width) (nonzero : 0 < n)
    (inBounds : i.toNat + n ≤ length) (sized : length ≤ 2^width) :
    let next := (BitVec.ofNat width (i.toNat + 1)).toNat
    next + (n - 1) ≤ length ∧
      (next = i.toNat + 1 ∨ (next = 0 ∧ n = 1 ∧ length = 2^width)) := by
  dsimp
  by_cases h : i.toNat + 1 < 2^width
  · simp [Nat.mod_eq_of_lt h]; omega
  · have atEnd : i.toNat + 1 = 2^width := by omega
    simp [atEnd]; omega

end WasmTest.Memory64
