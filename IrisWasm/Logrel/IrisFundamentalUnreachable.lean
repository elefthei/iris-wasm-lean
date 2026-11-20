/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Logrel.IrisFundamentalTrap

/-! Port of `theories/iris/logrel/iris_fundamental_unreachable.v`. -/

namespace IrisWasm

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm

variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF] [LogrelNaInvs GF]

@[rocq_alias iriswasm.typing_unreachable]
theorem typing_unreachable (C : TContext) (ts ts' : List ValueType) :
    ⊢ (semanticTyping C (toEList [.unreachable]) (.tf ts ts') : IProp GF) := by
  apply semantic_typing_immV
  intro i lh hl f ws
  iintro #Hi #Hctx Hf Hfv Hv
  iapply interp_expression_of_wp $$ [Hf] Hfv
  · ihave H := wp_wasm_empty_ctx (GF := GF) .NotStuck ⊤
      (fun w => iprop(⌜w = Val.trapV⌝ ∗ ↪[frame] f)) (ofVal (.immV ws) ++ toEList [.unreachable])
    icases H with ⟨-, H⟩
    iapply H
    rw [← List.append_nil (ofVal (.immV ws) ++ toEList [.unreachable])]
    iapply wp_base_push (s := .NotStuck) (E := ⊤) (es := toEList [.unreachable]) (l2 := []) (i := 0) (lh := .base [] []) (const_list_of_val ws)
    rw [← List.append_nil (toEList [.unreachable])]
    iapply wp_seq_trap_ctx
    iframe
    iintro Hf
    simp only [toEList, List.map_cons, List.map_nil]
    iapply wp_unreachable $$ Hf
    inext; ipureintro; rfl
  · unfold interpVal; ileft; ipureintro; rfl

end IrisWasm
