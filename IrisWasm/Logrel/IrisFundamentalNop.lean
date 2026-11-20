/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Logrel.IrisFundamentalTrap

/-! Port of `theories/iris/logrel/iris_fundamental_nop.v`. -/

namespace IrisWasm

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm

variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF] [LogrelNaInvs GF]

@[rocq_alias iriswasm.typing_nop]
theorem typing_nop (C : TContext) :
    ⊢ (semanticTyping C (toEList [.nop]) (.tf [] []) : IProp GF) := by
  apply semantic_typing_immV
  intro i lh hl f ws
  iintro #Hi #Hctx Hf Hfv Hv
  ihave %Hlen := BI.BigSepL2.bigSepL2_length $$ Hv
  cases ws with
  | cons => simp at Hlen
  | nil =>
  simp only [ofVal, vToEList, toEList, List.map_nil, List.map_cons, List.nil_append]
  iapply interp_expression_of_wp $$ [Hf] Hfv
  · iapply wp_nop $$ Hf
    inext; ipureintro; rfl
  · unfold interpVal interpValues; iright; iexists []; isplitr
    · ipureintro; rfl
    · iexact Hv

end IrisWasm
