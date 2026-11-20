/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Logrel.IrisFundamentalBr

/-! Port of `theories/iris/logrel/iris_fundamental_br_if.v`. -/

namespace IrisWasm

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm

variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF] [LogrelNaInvs GF]

attribute [local instance] WasmG.invGS

@[rocq_alias iriswasm.typing_br_if]
theorem typing_br_if (C : TContext) (i : Nat) (ts : List ValueType)
    (hleq : i < C.label.length) (hlookup : plop2 C i ts = true) :
    ⊢ semanticTyping (GF := GF) C (toEList [.brIf i]) (.tf (ts ++ [.i32]) ts) := by
  unfold semanticTyping
  iintro %j %lh %hl #Hi #Hc %f %vs ⟨Hf, Hfv⟩ #Hv
  unfold interpVal interpValues
  icases Hv with (%Heq | ⟨%ws, %Heq, #Hv⟩)
  · subst Heq
    iapply interp_expression_trap $$ Hf Hfv
  subst Heq
  icases BigSepL2.bigSepL2_app_inv_right $$ Hv with ⟨%ws', %wl, %Heq, #Hv', #Hw⟩
  subst Heq
  icases BigSepL2.bigSepL2_cons_inv_right $$ Hw with ⟨%w, %wl', %Heq, #Hw, #Hrest⟩
  subst Heq
  ihave %Hl := BigSepL2.bigSepL2_length $$ Hrest
  obtain rfl : wl' = [] := List.eq_nil_of_length_eq_zero (by simpa using Hl)
  ihave %Hlen := BigSepL2.bigSepL2_length $$ Hv'
  iunfold interpValue at Hw
  iunfold interpValueI32 at Hw
  icases Hw with %⟨z, Heq⟩
  subst Heq
  unfold interpExpression
  rw [show ofVal (.immV (ws' ++ [.int32 z])) ++ toEList [.brIf i] =
      vToEList ws' ++ ([.basic (.const (.int32 z)), .basic (.brIf i)] ++ []) ++ [] by
    simp [ofVal, vToEList, toEList]]
  icases wp_wasm_empty_ctx (GF := GF) .NotStuck ⊤ _ _ with ⟨-, H⟩
  iapply H
  iapply wp_base_push (v_to_e_is_const_list ws')
  iapply wp_seq_ctx _ _ _
    (fun w => iprop(⌜w = .immV [] ∨ w = .brV (ValidHoled.base (n := i) [] [])⌝ ∗ ↪[frame] f))
  isplitr
  · iintro ⟨%Hc, -⟩
    rcases Hc with Hc | Hc <;> cases Hc
  isplitl [Hf]
  · by_cases hz : z = Wasm.Int.zero
    · ihave H := wp_br_if_false (s := .NotStuck) (E := ⊤) (i := i) (f := f)
        (Φ := fun w => iprop(⌜w = .immV [] ∨ w = .brV (ValidHoled.base (n := i) [] [])⌝)) hz $$ Hf
      iapply H
      inext; ipureintro; exact Or.inl rfl
    · iapply wp_br_if_true (s := .NotStuck) (E := ⊤) (i := i) (f := f) hz $$ Hf
      inext
      iintro Hf
      iapply IrisWp.wp_value (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
        (e := [.basic (.br i)]) (v := .brV (ValidHoled.base (n := i) [] [])) ⟨rfl⟩
      iframe
      ipureintro; exact Or.inr rfl
  iintro %w ⟨%Hw, Hf⟩
  unfold wpWasmCtx
  iintro %LI %hLI
  rw [lfilled_Ind_Equivalent] at hLI
  simp only [frameBase] at hLI
  cases hLI
  rcases Hw with rfl | rfl
  · iapply IrisWp.wp_value (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
      (v := .immV ws') ⟨by simp [ofVal, vToEList]; rfl⟩
    isplitr [Hf Hfv]
    · ileft; unfold interpVal interpValues; iright; iexists ws'; isplitr; · ipureintro; rfl
      iexact Hv'
    · iexists f; iframe
  · ihave Hbr := typing_br C i [] ts ts hleq hlookup
    unfold semanticTyping
    ihave Hbr := Hbr $$ %j %lh %hl Hi Hc %f %(.immV ws') [Hf Hfv]
    · iframe
    ihave Hbr := Hbr $$ []
    · rw [List.nil_append]; unfold interpVal interpValues; iright; iexists ws'; isplitr; · ipureintro; rfl
      iexact Hv'
    unfold interpExpression
    rw [show [] ++ vToEList ws' ++ (ofVal (.brV (ValidHoled.base (n := i) [] [])) ++ []) ++ ([] ++ [])
      = ofVal (.immV ws') ++ toEList [.br i] by simp [ofVal, vfill, vToEList, toEList]]
    iexact Hbr

end IrisWasm
