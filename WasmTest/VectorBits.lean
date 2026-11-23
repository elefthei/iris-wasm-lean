import Wasm.Binary
import Wasm.ModuleValidation
import IrisWasm.Denotational.Run

namespace WasmTest.VectorBits
open Wasm IrisWasm IrisWasm.Denotational

private def decode (bs : Array UInt8) :=
  (Binary.complete Binary.vectorBitsInstr (ByteArray.mk bs).toByteSlice).toOption

private def state : State := (⟨[], [], [], []⟩, [], emptyInstance)
private def literal (x : BitVec 128) := AdministrativeInstruction.basic (.const (.vec128 x))

private def applyOpcode (bytes : Array UInt8) (args : List Value) : Option IrisWasm.Expr := do
  let op ← decode bytes
  return (← runCut 1 (vToEList args ++ [.basic op], state)).1

theorem decode_vector_bits :
    [77, 78, 79, 80, 81, 82, 83].map (fun n => decode #[0xfd, n]) =
      [some (.unop .v128 .vnot), some (.binop .v128 (.v .and)), some (.binop .v128 (.v .andNot)),
       some (.binop .v128 (.v .or)), some (.binop .v128 (.v .xor)), some .vbitselect,
       some (.testop .v128 .anyTrue)] := by decide +kernel

theorem decode_vector_const :
    decode #[0xfd, 0x8c, 0, 0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef,
      0x10, 0x32, 0x54, 0x76, 0x98, 0xba, 0xdc, 0xfe] =
      some (.const (.vec128 0xfedcba9876543210efcdab8967452301)) := by decide +kernel

#guard (decode (#[0xfd, 12] ++ Array.replicate 15 0)).isNone

theorem not_step (s : StoreRecord) (f : Frame) (x : BitVec 128) :
    Reduce s f [literal x, .basic (.unop .v128 .vnot)] s f [literal (~~~x)] :=
  .simple (.unop rfl rfl)

theorem binary_step (s : StoreRecord) (f : Frame) (op : VecBinop) (x y : BitVec 128) :
    Reduce s f [literal x, literal y, .basic (.binop .v128 (.v op))] s f
      [literal (appVecBinop op x y)] := .simple (.binopSuccess rfl rfl rfl rfl)

theorem bitselect_step (s : StoreRecord) (f : Frame) (x y m : BitVec 128) :
    Reduce s f [literal x, literal y, literal m, .basic .vbitselect] s f
      [literal ((x &&& m) ||| (y &&& (~~~m)))] := .simple .vbitselect

theorem any_true_step (s : StoreRecord) (f : Frame) (x : BitVec 128) :
    Reduce s f [literal x, .basic (.testop .v128 .anyTrue)] s f
      [.basic (.const (.int32 (wasmBool (x != 0))))] := .simple .testopV128

-- Pinned simd_bitwise.wast:31-33, lane zero occupies the low bits.
#guard applyOpcode #[0xfd, 78] [.vec128 0xffffffffffffffff0000000000000000,
  .vec128 0xffffffff00000000ffffffff00000000] == some [literal 0xffffffff000000000000000000000000]
#guard applyOpcode #[0xfd, 0xcf, 0] [.vec128 0xf0000000000000000000000000000007,
  .vec128 0x80000000000000000000000000000005] == some [literal 0x70000000000000000000000000000002]
#guard applyOpcode #[0xfd, 77] [.vec128 1] == some [literal 0xfffffffffffffffffffffffffffffffe]
#guard applyOpcode #[0xfd, 81] [.vec128 7, .int64 3] == none
#guard applyOpcode #[0xfd, 82] [.vec128 0xf0, .vec128 0x55, .vec128 0x3c] == some [literal 0x71]
#guard applyOpcode #[0xfd, 82] [.vec128 0xf0, .vec128 0x55, .int32 1] == none
#guard applyOpcode #[0xfd, 83] [.vec128 0x80000000000000000000000000000000] ==
  some [.basic (.const (.int32 1))]
#guard applyOpcode #[0xfd, 83] [.vec128 0] == some [.basic (.const (.int32 0))]
#guard runCut 1 ([literal 1, .basic (.testop .v128 .eqz)], state) == none
#guard runCut 1 ([.basic (.const (.int32 1)), .basic (.testop .i32 .anyTrue)], state) == none

private def memoryRoundTrip : Option Bool := do
  let s := { state.1 with mems := [⟨MemoryList.memMake 0 pageSize, ⟨.i32, ⟨1, none⟩⟩⟩] }
  let i := { emptyInstance with memory := [0] }
  let x := 0xfedcba98765432100123456789abcdef#128
  let (es, s', _, _) ← runCut 2 ([.basic (.const (.int32 1)), literal x,
    .basic (.store .v128 none ⟨0, 0, 6⟩), .basic (.const (.int32 7)), .basic (.load .v128 none ⟨0, 0, 0⟩)],
    s, [], i)
  let m ← s'.mems[0]?
  return es == [literal x] && m.data.memLookup 6 == some 0 && m.data.memLookup 7 == some 0xef &&
    m.data.memLookup 22 == some 0xfe && m.data.memLookup 23 == some 0

theorem full_vector_bytes : memoryRoundTrip = some true := by decide +kernel

private def vectorModule : Wasm.Module :=
  { (default : Wasm.Module) with
    types := [.tf [.v128, .v128] [.v128]]
    funcs := [⟨.typeidx 0, [], [.getLocal 0, .getLocal 1, .binop .v128 (.v .xor)]⟩] }

#guard (validateModule vectorModule).isOk
#guard bitzero .v128 == .vec128 0

end WasmTest.VectorBits
