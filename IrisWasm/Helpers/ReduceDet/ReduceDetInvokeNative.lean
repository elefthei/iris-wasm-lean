/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Helpers.Prelude.IrisReduceDetPrelude

/-! Port of `theories/iris/helpers/reduce_det/reduce_det_invoke_native.v`. -/

namespace IrisWasm

open Wasm Helpers.ReduceDetPrelude

theorem invoke_native_det {ws2 : StoreRecord} {f2 : Frame} {es2 : List AdministrativeInstruction}
    {s : StoreRecord} {a : Nat} {f f' : Frame} {t1s t2s ts : List ValueType}
    {es : List BasicInstruction} {vcs : List Value} :
    s.funcs[a]? = some (.funcNative f'.inst (.tf t1s t2s) ts es) →
    t1s.length = vcs.length →
    f'.locs = vcs ++ nZeros ts →
    Reduce s f (vToEList vcs ++ [.invoke a]) ws2 f2 es2 →
    (s, f, [.local t2s.length f' [.label t2s.length [] (toEList es)]]) = (ws2, f2, es2) := by
  intro _ _ _ Hred
  only_one_reduction Hred
  obtain rfl := v_to_e_inj ‹vToEList _ = vToEList _›
  simp_all
  exact frame_ext (by simp_all) (by simp_all)

end IrisWasm
