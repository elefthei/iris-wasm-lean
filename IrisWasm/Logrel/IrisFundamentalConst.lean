/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Logrel.IrisFundamentalTrap

/-! Port of `theories/iris/logrel/iris_fundamental_const.v`. -/

namespace IrisWasm

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm

variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF] [LogrelNaInvs GF]

@[rocq_alias iriswasm.typing_const]
theorem typing_const (C : TContext) (v : Value) :
    ⊢ (semanticTyping C (toEList [.const v]) (.tf [] [typeof v]) : IProp GF) := by
  apply semantic_typing_immV
  intro i lh hl f ws
  iintro #Hi #Hctx Hf Hfv Hv
  ihave %Hlen := BI.BigSepL2.bigSepL2_length $$ Hv
  rcases ws with _ | ⟨_, _⟩ <;> simp at Hlen
  rw [show (ofVal (.immV []) ++ toEList [.const v] : Expr) = ofVal (.immV [v]) from rfl]
  iapply interp_expression_of_wp $$ [Hf] Hfv
  · iapply wp_ofVal_frame (.immV [v]) $$ Hf
  · unfold interpVal interpValues; iright; iexists [v]
    isplitr
    · ipureintro; rfl
    · isplitl
      · iapply interp_value_type_of
      · iempintro

end IrisWasm
