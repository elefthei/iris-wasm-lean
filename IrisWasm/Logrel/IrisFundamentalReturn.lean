/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Logrel.IrisFundamentalHelpers

/-! Port of `theories/iris/logrel/iris_fundamental_return.v`. -/

namespace IrisWasm

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm

variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF] [LogrelNaInvs GF]

attribute [local instance] WasmG.invGS

/-- The trap case shared by every typing rule (Coq repeats it inline). -/
private theorem interp_expression_trap (τc : List (List ValueType)) (τto : Option (List ValueType))
    (hl : List (Hostfuncidx × FunctionType)) (τs : List ValueType) (lh : Lholed)
    (τl : List ValueType) (i : Instance) (f : Frame) (es : Expr) :
    ⊢ iprop(↪[frame] f -∗ interpFrame (GF := GF) τl i f -∗
      interpExpression τc τto hl τs lh τl i (ofVal .trapV ++ es)) := by
  unfold interpExpression
  rw [show ofVal .trapV ++ es = [] ++ [.trap] ++ es from rfl]
  iintro Hf Hfv
  ihave Ht := wp_trap .NotStuck ⊤ (fun v => iprop(⌜v = Val.trapV⌝)) [] es f rfl $$ [] Hf
  · ipureintro; rfl
  iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ Ht
  iintro %v ⟨%rfl, Hf⟩
  isplitr [Hf Hfv]
  · ileft; unfold interpVal; ileft; ipureintro; rfl
  · iexists f; iframe

@[rocq_alias iriswasm.typing_return]
theorem typing_return (C : TContext) (ts t1s t2s : List ValueType) (h : C.return_ = some ts) :
    ⊢ semanticTyping (GF := GF) C (toEList [.return_]) (.tf (t1s ++ ts) t2s) := by
  unfold semanticTyping
  rw [h]
  iintro %i %lh %hl #Hi #Hc %f %vs ⟨Hf, Hfv⟩ #Hv
  unfold interpVal interpValues
  icases Hv with (%Heq | ⟨%ws, %Heq, #Hv⟩)
  · subst Heq
    iapply interp_expression_trap $$ Hf Hfv
  subst Heq
  unfold interpExpression
  rw [show ofVal (.immV ws) ++ toEList [.return_] = ofVal (.retV (.base ws [])) by
    simp [ofVal, sfill, toEList]]
  iapply IrisWp.wp_value' (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
  isplitr [Hf Hfv]
  · iright; iright; ileft
    unfold interpReturnOption
    iexists .base ws [], ws
    isplitr; · ipureintro; rfl
    isplitr; · ipureintro; rfl
    iexists t1s
    isplitr
    · unfold interpVal interpValues; iright; iexists ws; isplitr; · ipureintro; rfl
      iexact Hv
    iintro %f0 %f1 Hf
    ihave %Hlen := BigSepL2.bigSepL2_length $$ Hv
    obtain ⟨ws1, ws2, rfl, h1, h2⟩ := list_app_split ws t1s.length ts.length (by simpa using Hlen)
    ihave ⟨Hv1, Hv2⟩ := (BigSepL2.bigSepL2_append (Or.inl h1)).1 $$ Hv
    iapply wp_return (vs := vToEList ws2) (lh := .base (vToEList ws1) []) (i := 0)
      (to_of_val (.immV ws2)) (by simp [vToEList, h2])
      (by
        rw [lfilled_Ind_Equivalent]
        have := LfilledInd.lfilledBase (vToEList ws1) (vToEList ws2 ++ [.basic .return_]) []
          (v_to_e_is_const_list ws1)
        simpa [ofVal, sfill, vToEList] using this)
    inext
    iapply IrisWp.wp_value (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) (e := vToEList ws2) (v := .immV ws2) ⟨rfl⟩
    iframe
    unfold interpVal interpValues
    iright; iexists ws2; isplitr; · ipureintro; rfl
    iexact Hv2
  · iexists f; iframe

end IrisWasm
