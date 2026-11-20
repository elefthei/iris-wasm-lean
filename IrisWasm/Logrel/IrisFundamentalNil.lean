/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Logrel.IrisFundamentalTrap

/-! Port of `theories/iris/logrel/iris_fundamental_nil.v`. -/

namespace IrisWasm

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm

variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF] [LogrelNaInvs GF]

@[rocq_alias iriswasm.typing_nil]
theorem typing_nil (C : TContext) :
    ⊢ (semanticTyping C (toEList []) (.tf [] []) : IProp GF) := by
  apply semantic_typing_immV
  intro i lh hl f ws
  iintro #Hi #Hctx Hf Hfv Hv
  ihave %Hlen := BI.BigSepL2.bigSepL2_length $$ Hv
  rcases ws with _ | ⟨_, _⟩ <;> simp at Hlen
  rw [show (ofVal (.immV []) ++ toEList [] : Expr) = ofVal (.immV []) from rfl]
  iapply interp_expression_of_wp $$ [Hf] Hfv
  · iapply wp_ofVal_frame (.immV []) $$ Hf
  · unfold interpVal interpValues; iright; iexists []
    isplitr
    · ipureintro; rfl
    · iexact Hv

end IrisWasm
