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

@[rocq_alias iriswasm.testop_i32_det]
theorem testop_i32_det {c : I32} {s : StoreRecord} {f : Frame} {s' : StoreRecord} {f' : Frame}
    {es : List AdministrativeInstruction} {testop : Testop} :
    Reduce s f [basic (.const (.int32 c)), basic (.testop .i32 testop)] s' f' es →
    reduceDetGoal s f [basic (.const (.int32 (wasmBool (appTestopI testop c))))] s' f' es
      [basic (.const (.int32 c)), basic (.testop .i32 testop)] := by
  intro Hred
  only_one Hred

@[rocq_alias iriswasm.testop_i64_det]
theorem testop_i64_det {c : I64} {s : StoreRecord} {f : Frame} {s' : StoreRecord} {f' : Frame}
    {es : List AdministrativeInstruction} {testop : Testop} :
    Reduce s f [basic (.const (.int64 c)), basic (.testop .i64 testop)] s' f' es →
    reduceDetGoal s f [basic (.const (.int32 (wasmBool (appTestopI testop c))))] s' f' es
      [basic (.const (.int64 c)), basic (.testop .i64 testop)] := by
  intro Hred
  only_one Hred

end IrisWasm
