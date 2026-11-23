/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import Wasm.Opsem

/-! Behaviour checks for `Wasm.Bytes`, `Wasm.Operations` and `Wasm.Opsem`. -/

namespace WasmTest.Operations

open Wasm

#guard decodeInt (encodeInt 4 0x01020304) = 0x01020304
#guard decodeInt (encodeInt 2 0x12345) = 0x2345
#guard wasmDeserialise (bits (.int64 7#64)) .i64 = .int64 7#64
#guard wasmDeserialise (bits (.int32 (BitVec.ofInt 32 (-5)))) .i32 = .int32 (BitVec.ofInt 32 (-5))
#guard appBinop (.i .add) (.int32 1#32) (.int32 2#32) = some (.int32 3#32)
#guard appBinop (.i (.div .s)) (.int32 1#32) (.int32 0#32) = none
#guard constList [.basic (.const (.int32 1#32)), .trap] = false

private def read80 (sx : Sx) : Option Value :=
  (loadPacked sx ⟨MemoryList.ofBytes [0x80], ⟨.i32, ⟨0, none⟩⟩⟩ 0 0 1 4).map (wasmDeserialise · .i32)

example : read80 .s = some (.int32 0xffffff80) := by decide
example : read80 .u = some (.int32 0x00000080) := by decide

-- Two distant addresses on consecutive logical pages, without a dense allocation.
private def highPage : Option Bool := do
  let hi := 2^32
  let m := MemoryList.memMake 0 (hi + pageSize)
  let m ← m.memUpdate (hi - 1) 0xab
  let m ← m.memUpdate hi 0xcd
  let bytes ← load ⟨m, ⟨.i64, ⟨65537, none⟩⟩⟩ (hi - 1) 0 2
  let cleared ← m.memUpdate (hi - 1) 0
  return bytes == [0xab, 0xcd] && m.memLookup 0 == some 0 && m.pages.size == 2 &&
    cleared.pages.size == 1 && cleared.memLookup hi == some 0xcd &&
    (m.memGrow pageSize).memLookup (hi + pageSize) == some 0 &&
    (m.memUpdate m.lengthMem 1).isNone

#guard highPage == some true

private def splitAndMerge : Option Bool := do
  let end_ := 2^32 + 1
  let t : RunTable Funcelem := RunTable.uniform end_ none
  let marked ← t.set? (end_ - 1) (some 17)
  let grown := marked.grow 1 (some 17)
  let reset ← grown.set? (end_ - 1) none
  return (t.set? end_ (some 17)).isNone && grown.get? (end_ - 2) == some none &&
    grown.get? end_ == some (some 17) && reset.get? (end_ - 1) == some none &&
    reset.get? end_ == some (some 17) && reset.runs.length == 2

#guard splitAndMerge == some true

example : cvt .i32 (some .s) (.float32 ⟨0xbf800000⟩) = some (.int32 0xffffffff) := by decide
example : cvt .i32 (some .u) (.float32 ⟨0xbf800000⟩) = none := by decide
example : cvt .i32 (some .s) (.float64 ⟨0x41e0000000000000⟩) = none := by decide
example : cvt .i32 (some .u) (.float64 ⟨0x41e0000000000000⟩) = some (.int32 0x80000000) := by decide

example : ReduceSimple [.basic (.const (.int32 1#32)), .basic (.const (.int32 2#32)),
    .basic (.binop .i32 (.i .add))] [.basic (.const (.int32 3#32))] :=
  .binopSuccess rfl rfl rfl rfl

end WasmTest.Operations
