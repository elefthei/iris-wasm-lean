/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Logrel.IrisFundamentalTrap

/-! Port of `theories/iris/logrel/iris_fundamental_drop.v`. -/

namespace IrisWasm

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm

variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF] [LogrelNaInvs GF]

@[rocq_alias iriswasm.typing_drop]
theorem typing_drop (C : TContext) (t : ValueType) :
    ⊢ (semanticTyping C (toEList [.drop]) (.tf [t] []) : IProp GF) := by
  apply semantic_typing_immV
  intro i lh hl f ws
  iintro #Hi #Hctx Hf Hfv Hv
  ihave %Hlen := BI.BigSepL2.bigSepL2_length $$ Hv
  rcases ws with _ | ⟨w, _ | ⟨_, _⟩⟩ <;> simp at Hlen
  simp only [ofVal, vToEList, toEList, List.map_nil, List.map_cons, List.cons_append, List.nil_append]
  iapply interp_expression_of_wp $$ [Hf] Hfv
  · iapply wp_drop $$ Hf
    inext; ipureintro; rfl
  · unfold interpVal interpValues; iright; iexists []
    isplitr
    · ipureintro; rfl
    · iempintro

end IrisWasm
