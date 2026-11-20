/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Logrel.IrisFundamentalTrap

/-! Port of `theories/iris/logrel/iris_fundamental_select.v`. -/

namespace IrisWasm

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm

variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF] [LogrelNaInvs GF]

@[rocq_alias iriswasm.typing_select]
theorem typing_select (C : TContext) (t : ValueType) :
    ⊢ (semanticTyping C (toEList [.select]) (.tf [t, t, .i32] [t]) : IProp GF) := by
  apply semantic_typing_immV
  intro i lh hl f ws
  iintro #Hi #Hctx Hf Hfv Hv
  ihave %Hlen := BI.BigSepL2.bigSepL2_length $$ Hv
  rcases ws with _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨_, _⟩⟩⟩⟩ <;> simp at Hlen
  icases Hv with ⟨Hv1, Hv2, Hv3, -⟩
  ihave %Hz : ⌜∃ z, w3 = Value.int32 z⌝ $$ [Hv3]
  · simp only [interpValue, interpValueI32]; iexact Hv3
  obtain ⟨z, rfl⟩ := Hz

  simp only [ofVal, vToEList, toEList, List.map_nil, List.map_cons, List.cons_append, List.nil_append]
  by_cases hz : z = Int.zero
  · iapply interp_expression_of_wp $$ [Hf] Hfv
    · iapply wp_select_false hz $$ Hf
      inext; ipureintro; rfl
    · unfold interpVal interpValues; iright; iexists [w2]
      isplitr
      · ipureintro; rfl
      · isplitl
        · iexact Hv2
        · iempintro
  · iapply interp_expression_of_wp $$ [Hf] Hfv
    · iapply wp_select_true hz $$ Hf
      inext; ipureintro; rfl
    · unfold interpVal interpValues; iright; iexists [w1]
      isplitr
      · ipureintro; rfl
      · isplitl
        · iexact Hv1
        · iempintro

end IrisWasm
