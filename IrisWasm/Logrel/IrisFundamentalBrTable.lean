/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Logrel.IrisFundamentalBr

/-! Port of `theories/iris/logrel/iris_fundamental_br_table.v`. -/

namespace IrisWasm

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm

variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF] [LogrelNaInvs GF]

attribute [local instance] WasmG.invGS

@[rocq_alias iriswasm.typing_br_table]
theorem typing_br_table (C : TContext) (i : Nat) (t1s ts t2s : List ValueType) (ins : List Nat)
    (hall : (ins ++ [i]).all (fun i => decide (i < C.label.length) && plop2 C i ts) = true) :
    ⊢ semanticTyping (GF := GF) C (toEList [.brTable ins i]) (.tf (t1s ++ ts ++ [.i32]) t2s) := by
  have hall' : ∀ k ∈ ins ++ [i], k < C.label.length ∧ plop2 C k ts = true := by
    simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hall
    exact hall
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
  rw [show ofVal (.immV (ws' ++ [.int32 z])) ++ toEList [.brTable ins i] =
      vToEList ws' ++ ([.basic (.const (.int32 z)), .basic (.brTable ins i)] ++ []) ++ [] by
    simp [ofVal, vToEList, toEList]]
  icases wp_wasm_empty_ctx (GF := GF) .NotStuck ⊤ _ _ with ⟨-, H⟩
  iapply H
  iapply wp_base_push (v_to_e_is_const_list ws')
  iapply wp_seq_ctx _ _ _
    (fun w => iprop(⌜∃ k, k ∈ ins ++ [i] ∧ w = .brV (ValidHoled.base (n := k) [] [])⌝ ∗
      ↪[frame] f))
  isplitr
  · iintro ⟨%⟨_, _, Hc⟩, -⟩
    cases Hc
  isplitl [Hf]
  · by_cases hz : ins.length ≤ Wasm.Int.natOfUint z
    · iapply wp_br_table_length (s := .NotStuck) (E := ⊤) (i := i) (f := f) hz $$ Hf
      inext
      iintro Hf
      iapply IrisWp.wp_value (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
        (e := [.basic (.br i)]) (v := .brV (ValidHoled.base (n := i) [] [])) ⟨rfl⟩
      iframe
      ipureintro; exact ⟨i, by simp, rfl⟩
    · have hj : ins[Wasm.Int.natOfUint z]? = some ins[Wasm.Int.natOfUint z] :=
        List.getElem?_eq_getElem (by omega)
      iapply wp_br_table (s := .NotStuck) (E := ⊤) (i := i) (f := f) hj $$ Hf
      inext
      iintro Hf
      iapply IrisWp.wp_value (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
        (e := [.basic (.br ins[Wasm.Int.natOfUint z])])
        (v := .brV (ValidHoled.base (n := ins[Wasm.Int.natOfUint z]) [] [])) ⟨rfl⟩
      iframe
      ipureintro; exact ⟨_, by simp, rfl⟩
  iintro %w ⟨%⟨k, Hk, Hw⟩, Hf⟩
  subst Hw
  obtain ⟨hleq, hlookup⟩ := hall' k Hk
  unfold wpWasmCtx
  iintro %LI %hLI
  rw [lfilled_Ind_Equivalent] at hLI
  simp only [frameBase] at hLI
  cases hLI
  ihave Hbr := typing_br C k t1s ts t2s hleq hlookup
  unfold semanticTyping
  ihave Hbr := Hbr $$ %j %lh %hl Hi Hc %f %(.immV ws') [Hf Hfv]
  · iframe
  ihave Hbr := Hbr $$ []
  · unfold interpVal interpValues; iright; iexists ws'; isplitr; · ipureintro; rfl
    iexact Hv'
  unfold interpExpression
  rw [show [] ++ vToEList ws' ++ (ofVal (.brV (ValidHoled.base (n := k) [] [])) ++ []) ++ ([] ++ [])
    = ofVal (.immV ws') ++ toEList [.br k] by simp [ofVal, vfill, vToEList, toEList]]
  iexact Hbr

end IrisWasm
