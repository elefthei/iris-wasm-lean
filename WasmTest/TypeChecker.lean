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
#guard bETypeChecker emptyC [.block (.result (some .i32)) add12] (.tf [] [.i32])
-- `br 0` out of a block: the stack after `br` is polymorphic.
#guard bETypeChecker emptyC [.block (.result (some .i32)) [.const (.int32 7#32), .br 0, .drop]]
  (.tf [] [.i32])
-- `br 1` with only one enclosing label is ill-typed.
#guard !bETypeChecker emptyC [.block (.result none) [.br 1]] (.tf [] [])
#guard bETypeChecker emptyC [.unreachable, .select] (.tf [] [.i64])
#guard !bETypeChecker emptyC [.currentMemory 0] (.tf [] [.i32])
#guard !bETypeChecker emptyC [.const (.int32 0), .growMemory 0] (.tf [] [.i32])
#guard bETypeChecker emptyC [.unop .i64 (.extendS .i32)] (.tf [.i64] [.i64])
#guard !bETypeChecker emptyC [.unop .i32 (.extendS .i32)] (.tf [.i32] [.i32])
#guard !bETypeChecker emptyC [.unop .f32 (.extendS .i8)] (.tf [.f32] [.f32])
#guard bETypeChecker emptyC [.vbitselect] (.tf [.i64, .v128, .v128, .v128] [.i64, .v128])
#guard !bETypeChecker emptyC [.vbitselect] (.tf [.v128, .v128] [.v128])
#guard !bETypeChecker emptyC [.vbitselect] (.tf [.v128, .v128, .i32] [.v128])

#guard [ValueType.i32, .i64].all fun dst => [ValueType.f32, .f64].all fun src =>
  [Sx.s, .u].all fun sx =>
    bETypeChecker emptyC [.cvtop dst .truncSat src (some sx)] (.tf [src] [dst])
#guard !bETypeChecker emptyC [.cvtop .i32 .truncSat .f32 none] (.tf [.f32] [.i32])
#guard !bETypeChecker emptyC [.cvtop .i64 .truncSat .i32 (some .s)] (.tf [.i32] [.i64])
#guard !bETypeChecker emptyC [.cvtop .f64 .truncSat .f32 (some .s)] (.tf [.f32] [.f64])
#guard !bETypeChecker emptyC [.cvtop .i32 .truncSat .f64 (some .u)] (.tf [.f32] [.i32])

-- The checker also reduces in the kernel.
example : bETypeChecker emptyC add12 (.tf [] [.i32]) = true := by decide

-- Typing derived through the reflection theorem (`Decidable (BeTyping ..)`).
example : BeTyping emptyC add12 (.tf [] [.i32]) := by decide

end WasmTest.TypeChecker
