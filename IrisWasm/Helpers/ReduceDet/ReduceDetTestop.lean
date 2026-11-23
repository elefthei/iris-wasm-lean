/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Helpers.Prelude.IrisReduceDetPrelude

/-! Port of `theories/iris/helpers/reduce_det/reduce_det_testop.v`. -/

namespace IrisWasm

open Wasm Helpers.ReduceDetPrelude
open AdministrativeInstruction (basic trap)

theorem testop_i32_det {c : I32} {s : StoreRecord} {f : Frame} {s' : StoreRecord} {f' : Frame}
    {es : List AdministrativeInstruction} :
    Reduce s f [basic (.const (.int32 c)), basic (.testop .i32 .eqz)] s' f' es →
    reduceDetGoal s f [basic (.const (.int32 (wasmBool (Wasm.Int.ieqz c))))] s' f' es
      [basic (.const (.int32 c)), basic (.testop .i32 .eqz)] := by
  intro Hred
  only_one Hred

theorem testop_i64_det {c : I64} {s : StoreRecord} {f : Frame} {s' : StoreRecord} {f' : Frame}
    {es : List AdministrativeInstruction} :
    Reduce s f [basic (.const (.int64 c)), basic (.testop .i64 .eqz)] s' f' es →
    reduceDetGoal s f [basic (.const (.int32 (wasmBool (Wasm.Int.ieqz c))))] s' f' es
      [basic (.const (.int64 c)), basic (.testop .i64 .eqz)] := by
  intro Hred
  only_one Hred

theorem testop_v128_det {c : BitVec 128} {s s' : StoreRecord} {f f' : Frame}
    {es : List AdministrativeInstruction}
    (hr : Reduce s f [basic (.const (.vec128 c)), basic (.testop .v128 .anyTrue)] s' f' es) :
    reduceDetGoal s f [basic (.const (.int32 (wasmBool (c != 0))))] s' f' es
      [basic (.const (.vec128 c)), basic (.testop .v128 .anyTrue)] := by
  only_one hr

end IrisWasm
