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

example : ReduceSimple [.basic (.const (.int32 1#32)), .basic (.const (.int32 2#32)),
    .basic (.binop .i32 (.i .add))] [.basic (.const (.int32 3#32))] :=
  .binopSuccess (by rfl)

end WasmTest.Operations
