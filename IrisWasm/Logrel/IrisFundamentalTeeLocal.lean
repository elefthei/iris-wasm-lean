/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Logrel.IrisFundamentalTrap

/-! Port of `theories/iris/logrel/iris_fundamental_tee_local.v`. -/

namespace IrisWasm

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm

variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF] [LogrelNaInvs GF]

@[rocq_alias iriswasm.typing_tee_local]
theorem typing_tee_local (C : TContext) (i : Nat) (t : ValueType) :
    C.local_[i]? = some t →
    ⊢ (semanticTyping C (toEList [.teeLocal i]) (.tf [t] [t]) : IProp GF) := by
  intro hnth
  apply semantic_typing_immV
  intro j lh hl f ws
  iintro #Hi #Hctx Hf Hfv Hv
  ihave %Hlen := BI.BigSepL2.bigSepL2_length $$ Hv
  rcases ws with _ | ⟨w, _ | ⟨_, _⟩⟩ <;> simp at Hlen
  icases Hv with ⟨#Hw, -⟩
  unfold interpFrame interpVal interpValues
  icases Hfv with ⟨%locs, %Heq, Hlocs, Hown⟩
  icases Hlocs with (%Hc | ⟨%wl, %Hw', Hlocs⟩)
  · cases Hc
  cases Hw'
  ihave %Hlen' := BI.BigSepL2.bigSepL2_length $$ Hlocs
  have hi : i < locs.length := by
    have := (List.getElem?_eq_some_iff.mp hnth).1; omega
  obtain ⟨w0, hw0⟩ : ∃ w, locs[i]? = some w := ⟨_, List.getElem?_eq_getElem hi⟩
  icases BI.BigSepL2.bigSepL2_insert_acc hw0 hnth $$ Hlocs with ⟨-, Hcl⟩
  ihave Hlocs := Hcl $$ %w %t Hw
  have hs : C.local_.set i t = C.local_ := by
    apply List.ext_getElem?; intro n; rw [List.getElem?_set]; split <;> simp_all
  rw [hs]
  subst Heq
  simp only [ofVal, vToEList, toEList, List.map_nil, List.map_cons, List.cons_append,
    List.nil_append]
  iapply interp_expression_of_wp (f := ⟨locs.set i w, j⟩) $$ [Hf] [Hlocs Hown]
  · iapply wp_tee_local $$ Hf
    inext; iintro Hf
    rw [show ([.basic (.const w), .basic (.const w), .basic (.setLocal i)] : Expr) =
      vToEList [w] ++ [.basic (.const w), .basic (.setLocal i)] from rfl]
    iapply wp_val_app' _ _ (fun v => iprop(⌜v = .immV [w]⌝ ∗ ↪[frame] ⟨locs.set i w, j⟩)) [w]
    isplitr
    · imodintro; iintro ⟨%Hc, -⟩; cases Hc
    · iapply wp_set_local _ _ w i (fun v => iprop(⌜valCombine (.immV [w]) v = .immV [w]⌝))
        ⟨locs, j⟩ hi $$ [] Hf
      inext; ipureintro; rfl
  · simp only [interpFrame, interpVal, interpValues]; iexists (locs.set i w); isplitr
    · ipureintro; rfl
    · iframe; iright; iexists (locs.set i w); isplitr
      · ipureintro; rfl
      · iexact Hlocs
  · simp only [interpVal, interpValues]; iright; iexists [w]; isplitr
    · ipureintro; rfl
    · isplitl
      · iexact Hw
      · iempintro

end IrisWasm
