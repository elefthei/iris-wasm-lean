/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Logrel.IrisFundamentalBlock

/-! Port of `theories/iris/logrel/iris_fundamental_if.v`. -/

namespace IrisWasm

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm

variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF] [LogrelNaInvs GF]

attribute [local instance] WasmG.invGS

@[rocq_alias iriswasm.typing_if]
theorem typing_if (C : TContext) (tn tm : List ValueType) (es1 es2 : List BasicInstruction)
    (h1 : ⊢ semanticTyping (GF := GF) (updLabel C ([tm] ++ C.label)) (toEList es1) (.tf tn tm))
    (h2 : ⊢ semanticTyping (GF := GF) (updLabel C ([tm] ++ C.label)) (toEList es2) (.tf tn tm)) :
    ⊢ semanticTyping (GF := GF) C (toEList [.if_ (.tf tn tm) es1 es2]) (.tf (tn ++ [.i32]) tm) := by
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
  iunfold interpValue at Hw
  iunfold interpValueI32 at Hw
  icases Hw with %⟨z, Heq⟩
  subst Heq
  unfold interpExpression
  rw [show ofVal (.immV (ws' ++ [.int32 z])) ++ toEList [.if_ (.tf tn tm) es1 es2] =
      vToEList ws' ++ [.basic (.const (.int32 z)), .basic (.if_ (.tf tn tm) es1 es2)] ++ [] by
    simp [ofVal, vToEList, toEList]]
  icases wp_wasm_empty_ctx (GF := GF) .NotStuck ⊤ _ _ with ⟨-, H⟩
  iapply H
  iapply wp_base_push (v_to_e_is_const_list ws')
  simp only [frameBase, List.nil_append, List.append_nil]
  -- after the step, both branches are a `block` typed by `typing_block`
  have hcont : ∀ es, (⊢ semanticTyping (GF := GF) (updLabel C ([tm] ++ C.label)) (toEList es)
      (.tf tn tm)) → ⊢ iprop(□ interpInstance (GF := GF) C hl j -∗ □ interpCtx C.label C.return_ hl C.local_ j lh -∗
        □ ([∗list] w;τ ∈ ws';tn, interpValue τ w) -∗ interpFrame C.local_ j f -∗ ↪[frame] f -∗
        WP [AdministrativeInstruction.basic (.block (.tf tn tm) es)] CTX 0 ; (.base (vToEList ws') [])
          {{ vs, (interpVal tm vs ∨ interpBr C.local_ j C.return_ hl vs lh C.label ∨
            interpReturnOption C.return_ C.local_ j vs ∨
            interpCallHost C.local_ j C.return_ hl vs lh C.label tm) ∗
            ∃ f, ↪[frame] f ∗ interpFrame C.local_ j f }}) := by
    intro es h
    iintro #Hi #Hc #Hv' Hfv Hf
    unfold wpWasmCtx
    iintro %LI %hLI
    rw [lfilled_Ind_Equivalent] at hLI
    cases hLI
    ihave HH := typing_block C tn tm es h
    unfold semanticTyping
    ihave HH := HH $$ %j %lh %hl Hi Hc %f %(.immV ws') [Hf Hfv]
    · iframe
    ihave HH := HH $$ []
    · unfold interpVal interpValues; iright; iexists ws'; isplitr; · ipureintro; rfl
      iexact Hv'
    unfold interpExpression
    rw [show vToEList ws' ++ [.basic (.block (.tf tn tm) es)] ++ [] =
      ofVal (.immV ws') ++ toEList [.block (.tf tn tm) es] by simp [ofVal, toEList]]
    iexact HH
  by_cases hz : z = Wasm.Int.zero
  · iapply wp_if_false_ctx hz $$ Hf
    inext
    iintro Hf
    iapply hcont es2 h2 $$ Hi Hc Hv' Hfv Hf
  · iapply wp_if_true_ctx hz $$ Hf
    inext
    iintro Hf
    iapply hcont es1 h1 $$ Hi Hc Hv' Hfv Hf

end IrisWasm
