/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import Wasm.TypeCheckerReflectsTyping

/-! Behaviour checks for `Wasm.TypeChecker`. -/

namespace WasmTest.TypeChecker

open Wasm

def emptyC : TContext := ⟨[], [], [], [], [], [], [], none⟩

def add12 : List BasicInstruction :=
  [.const (.int32 1#32), .const (.int32 2#32), .binop .i32 (.i .add)]

#guard bETypeChecker emptyC add12 (.tf [] [.i32])
#guard !bETypeChecker emptyC add12 (.tf [] [.i64])
#guard !bETypeChecker emptyC [.binop .i32 (.i .add)] (.tf [.i64, .i64] [.i32])
#guard bETypeChecker emptyC [.block (.tf [] [.i32]) add12] (.tf [] [.i32])
-- `br 0` out of a block: the stack after `br` is polymorphic.
#guard bETypeChecker emptyC [.block (.tf [] [.i32]) [.const (.int32 7#32), .br 0, .drop]]
  (.tf [] [.i32])
-- `br 1` with only one enclosing label is ill-typed.
#guard !bETypeChecker emptyC [.block (.tf [] []) [.br 1]] (.tf [] [])
#guard bETypeChecker emptyC [.unreachable, .select] (.tf [] [.i64])
#guard !bETypeChecker emptyC [.currentMemory] (.tf [] [.i32])

-- The checker also reduces in the kernel.
example : bETypeChecker emptyC add12 (.tf [] [.i32]) = true := by decide

-- Typing derived through the reflection theorem (`Decidable (BeTyping ..)`).
example : BeTyping emptyC add12 (.tf [] [.i32]) := by decide

end WasmTest.TypeChecker
