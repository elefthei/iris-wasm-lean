/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Logrel.IrisFundamentalTrap

/-! Port of `theories/iris/logrel/iris_fundamental_get_local.v`. -/

namespace IrisWasm

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm

variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF] [LogrelNaInvs GF]

@[rocq_alias iriswasm.typing_get_local]
theorem typing_get_local (C : TContext) (i : Nat) (t : ValueType) :
    C.local_[i]? = some t →
    ⊢ (semanticTyping C (toEList [.getLocal i]) (.tf [] [t]) : IProp GF) := by
  intro hnth
  apply semantic_typing_immV
  intro j lh hl f ws
  iintro #Hi #Hctx Hf Hfv Hv
  ihave %Hlen := BI.BigSepL2.bigSepL2_length $$ Hv
  rcases ws with _ | ⟨_, _⟩ <;> simp at Hlen
  unfold interpFrame interpVal interpValues
  icases Hfv with ⟨%locs, %Heq, Hlocs, Hown⟩
  icases Hlocs with (%Hc | ⟨%wl, %Hw, Hlocs⟩)
  · cases Hc
  cases Hw
  ihave %Hlen' := BI.BigSepL2.bigSepL2_length $$ Hlocs
  obtain ⟨w, hw⟩ : ∃ w, locs[i]? = some w := by
    have := (List.getElem?_eq_some_iff.mp hnth).1
    exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
  icases BI.BigSepL2.bigSepL2_lookup_acc hw hnth $$ Hlocs with ⟨#Hw, Hcl⟩
  ihave Hlocs := Hcl $$ Hw
  subst Heq
  simp only [ofVal, vToEList, toEList, List.map_nil, List.map_cons, List.nil_append]
  iapply interp_expression_of_wp $$ [Hf] [Hlocs Hown]
  · iapply wp_get_local _ _ w i _ _ hw $$ [] Hf
    inext; ipureintro; rfl
  · simp only [interpFrame, interpVal, interpValues]; iexists locs; isplitr
    · ipureintro; rfl
    · iframe; iright; iexists locs; isplitr
      · ipureintro; rfl
      · iexact Hlocs
  · simp only [interpVal, interpValues]; iright; iexists [w]; isplitr
    · ipureintro; rfl
    · isplitl
      · iexact Hw
      · iempintro

end IrisWasm
