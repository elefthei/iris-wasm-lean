import Wasm.Binary
import Wasm.ModuleValidation
import IrisWasm.Denotational.Run

namespace WasmTest.MultiMemory
open Wasm IrisWasm IrisWasm.Denotational

private def pageMem (b : Byte) (pages : Nat) : Memory :=
  ⟨(MemoryList.ofBytes [0, 0, 0, b]).memGrow (pages * pageSize - 4), ⟨.i32, ⟨pages, some 4⟩⟩⟩

-- Index 1 selects store address 0. Module indices 0 and 2 alias store address 1.
private def σ : State :=
  (⟨[], [], [pageMem 0x80 1, pageMem 0x7f 2], []⟩, [], {emptyInstance with memory := [1, 0, 1]})

private def parse (bs : Array UInt8) : Option Wasm.Expr :=
  (Binary.complete (Binary.structuredExpr Binary.numVecType fun tag =>
    if 0x28 ≤ tag && tag ≤ 0x40 || tag == 0xfd then Binary.memoryPayload tag
    else Binary.numericPayload tag) (ByteArray.mk bs).toByteSlice).toOption

private def atCut (steps : Nat) (bs : Array UInt8) : Option Cfg := do
  runCut steps (toEList (← parse bs), σ)

private def i32 (v : I32) := AdministrativeInstruction.basic (.const (.int32 v))

theorem decode_indexed_load : parse #[0x2c, 0x40, 1, 3, 0x0b] =
    some [.load .i32 (some (.i8, .s)) ⟨1, 0, 3⟩] := by decide +kernel

-- Same offset, different memory, including both extensions of the byte 0x80.
theorem indexed_signedness :
    atCut 3 #[0x41,0, 0x2c,0x40,1,3, 0x41,0, 0x2d,0x40,1,3, 0x41,0, 0x2c,0,3, 0x0b] =
      some ([i32 0xffffff80, i32 0x80, i32 0x7f], σ) := by decide +kernel

/-- Distinct indices alias one store memory; reading an f32 store as i32 retains the NaN payload. -/
theorem scalar_memory_bits :
    (atCut 3 #[0x41,3, 0x43,1,0,0x80,0x7f, 0x38,0x42,2,0,
      0x41,0, 0x28,2,3, 0x41,3, 0x2a,0x42,2,0, 0x0b]).map Prod.fst =
        some [i32 0x7f800001, .basic (.const (.float32 ⟨0x7f800001⟩))] := by decide +kernel

/-- Both reads and writes check the last byte of the range, including v128's sixteenth byte. -/
theorem full_width_oob :
    runCut 1 ([i32 (BitVec.ofNat 32 (pageSize-3)), .basic (.load .i32 none ⟨1,0,0⟩)], σ)
      = some ([.trap], σ) ∧
    runCut 1 ([i32 (BitVec.ofNat 32 (pageSize-3)), i32 9, .basic (.store .i32 none ⟨1,0,0⟩)], σ)
      = some ([.trap], σ) ∧
    runCut 1 ([i32 (BitVec.ofNat 32 (pageSize-15)), .basic (.load .v128 none ⟨1,0,0⟩)], σ)
      = some ([.trap], σ) ∧
    runCut 1 ([i32 (BitVec.ofNat 32 (pageSize-15)), .basic (.const (.vec128 9)),
      .basic (.store .v128 none ⟨1,0,0⟩)], σ) = some ([.trap], σ) := by
  repeat' apply And.intro
  all_goals decide +kernel

-- Store through index 2, read the same byte through index 0, and check the independent index 1.
#guard (atCut 3 #[0x41,0, 0x41,35, 0x3a,0x40,2,3, 0x41,0, 0x2d,0,3,
    0x41,0, 0x2d,0x40,1,3, 0x0b]).any (fun (es, _, _, _) => es == [i32 35, i32 0x80])

-- A successful grow through one alias changes size through the other alias only.
#guard (atCut 3 #[0x41,1, 0x40,2, 0x3f,0, 0x3f,1, 0x0b]).any
  (fun (es, _, _, _) => es == [i32 2, i32 3, i32 1])

theorem grow_can_fail : Reduce σ.1 ⟨σ.2.1, σ.2.2⟩ [i32 1, .basic (.growMemory 2)]
    σ.1 ⟨σ.2.1, σ.2.2⟩ [i32 int32MinusOne] := .growMemoryFailure (c := .i32 1)

#guard atCut 1 #[0x3f,3,0x0b] == none
#guard atCut 1 #[0x41,1,0x40,3,0x0b] == some ([i32 int32MinusOne], σ)
#guard atCut 1 #[0x41,0x7f,0x2d,0x40,1,1,0x0b] == some ([.trap], σ) -- no effective-address wrap

-- Exercise the raw operand rule on a sparse byte vector with 65537 pages.
private def wideBytes : Option Bool := do
  let large := MemoryList.memMake 0 (65537 * pageSize)
  let m : Memory := ⟨large, ⟨.i64, ⟨65537, none⟩⟩⟩
  let wide : State := (⟨[], [], [m], []⟩, [], {emptyInstance with memory := [0]})
  let hi := BasicInstruction.const (.int64 0x100000000)
  let lo := BasicInstruction.const (.int64 0)
  let read := BasicInstruction.load .i32 (some (.i8, .u)) ⟨0,0,1⟩
  let (es, s, _, _) ← runCut 3 (toEList [hi, .const (.int32 0xab), .store .i32 (some .i8) ⟨0,0,1⟩,
    hi, read, lo, read], wide)
  let after ← s.mems[0]?
  return es == [i32 0xab, i32 0] && after.data.pages.size == 1

theorem wide_address_preserved : wideBytes = some true := by decide +kernel
#guard atCut 1 #[0x42,0x7f,0x2d,0x40,1,1,0x0b] == some ([.trap], σ)
#guard atCut 1 #[0x43,0,0,0,0,0x2d,0,0,0x0b] == none
#guard atCut 1 #[0x42,0,0x40,3,0x0b] == some ([.basic (.const (.int64 (-1)))], σ)
#guard (atCut 1 #[0x42,1,0x40,1,0x0b]).any fun d => d.1 == [.basic (.const (.int64 1))]

theorem wide_grow_failure (s : StoreRecord) (f : Frame) (x : Nat) (d : I64) :
    Reduce s f [.basic (.const (.int64 d)), .basic (.growMemory x)] s f
      [.basic (.const (.int64 (-1)))] := .growMemoryFailure (c := .i64 d)

private def C : TContext :=
  ⟨[], [], [], [], [⟨.i32, ⟨1, some 4⟩⟩, ⟨.i32, ⟨2, some 4⟩⟩], [], [], none⟩
#guard bETypeChecker C [.load .i32 none ⟨1, 2, 0xffffffff⟩] (.tf [.i32] [.i32])
#guard !bETypeChecker C [.load .i32 none ⟨2, 2, 0⟩] (.tf [.i32] [.i32])
#guard !bETypeChecker C [.store .i32 none ⟨1, 2, 2^32⟩] (.tf [.i32, .i32] [])
#guard !bETypeChecker C [.growMemory 2] (.tf [.i32] [.i32])
-- An oversized memory32 offset is decoded without truncation and rejected in validation, not parsing.
theorem decode_large_offset : parse #[0x36,0x42,1,0x80,0x80,0x80,0x80,0x10,0x0b] =
    some [.store .i32 none ⟨1, 2, 2^32⟩] := by decide +kernel

/-- The contiguous scalar load/store range preserves the same decoded memory argument and suffix. -/
theorem memory_opcodes {s r : ByteSlice} {a : MemArg} (h : Binary.memArg s = .ok (a,r)) :
    [0x28,0x29,0x2a,0x2b,0x2c,0x2d,0x2e,0x2f,0x30,0x31,0x32,0x33,0x34,0x35,
     0x36,0x37,0x38,0x39,0x3a,0x3b,0x3c,0x3d,0x3e].map (fun tag => Binary.memoryPayload tag s) =
      ([.load .i32 none a, .load .i64 none a, .load .f32 none a, .load .f64 none a,
        .load .i32 (some (.i8,.s)) a, .load .i32 (some (.i8,.u)) a,
        .load .i32 (some (.i16,.s)) a, .load .i32 (some (.i16,.u)) a,
        .load .i64 (some (.i8,.s)) a, .load .i64 (some (.i8,.u)) a,
        .load .i64 (some (.i16,.s)) a, .load .i64 (some (.i16,.u)) a,
        .load .i64 (some (.i32,.s)) a, .load .i64 (some (.i32,.u)) a,
        .store .i32 none a, .store .i64 none a, .store .f32 none a, .store .f64 none a,
        .store .i32 (some .i8) a, .store .i32 (some .i16) a, .store .i64 (some .i8) a,
        .store .i64 (some .i16) a, .store .i64 (some .i32) a] : List BasicInstruction).map
          (fun op => .ok (op,r)) := by
  simp [Binary.memoryPayload, Functor.map, StateT.map, Except.map, h]

theorem size_grow_opcodes {s r : ByteSlice} {x : Nat} (h : Binary.u32 s = .ok (x,r)) :
    Binary.memoryPayload 0x3f s = .ok (.currentMemory x,r) ∧
      Binary.memoryPayload 0x40 s = .ok (.growMemory x,r) := by
  simp [Binary.memoryPayload, Functor.map, StateT.map, Except.map, h]

theorem vector_memory_opcodes {s p r : ByteSlice} {a : MemArg} (h : Binary.memArg p = .ok (a,r)) :
    (Binary.u32 s = .ok (0,p) → Binary.memoryPayload 0xfd s = .ok (.load .v128 none a,r)) ∧
    (Binary.u32 s = .ok (11,p) → Binary.memoryPayload 0xfd s = .ok (.store .v128 none a,r)) := by
  constructor <;> intro hu <;>
    simp [Binary.memoryPayload, Bind.bind, StateT.bind, MonadState.get, getThe, MonadStateOf.get,
      StateT.get, Pure.pure, StateT.pure, Except.bind, Except.pure, hu, h]

end WasmTest.MultiMemory
