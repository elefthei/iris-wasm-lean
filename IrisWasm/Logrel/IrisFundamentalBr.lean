/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Logrel.IrisFundamentalHelpers

/-! Port of `theories/iris/logrel/iris_fundamental_br.v`. -/

namespace IrisWasm

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm

variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF] [LogrelNaInvs GF]

attribute [local instance] WasmG.invGS

/-- The trap case shared by every typing rule (Coq repeats it inline). -/
theorem interp_expression_trap (τc : List (List ValueType)) (τto : Option (List ValueType))
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

@[rocq_alias iriswasm.typing_br]
theorem typing_br (C : TContext) (i : Nat) (t1s ts t2s : List ValueType)
    (hleq : i < C.label.length) (hlookup : plop2 C i ts = true) :
    ⊢ semanticTyping (GF := GF) C (toEList [.br i]) (.tf (t1s ++ ts) t2s) := by
  have Hlook : C.label[i]? = some ts := by simpa [plop2] using hlookup
  unfold semanticTyping interpCtx
  iintro %j %lh %hl #Hi ⟨%Hlh_base, %Hlh_len, %Hlh_valid, #Hc⟩ %f %vs ⟨Hf, Hfv⟩ #Hv
  have Hleneq := length_lholeds_length_depth _ _ Hlh_len
  unfold interpVal interpValues
  icases Hv with (%Heq | ⟨%ws, %Heq, #Hv⟩)
  · subst Heq
    iapply interp_expression_trap $$ Hf Hfv
  subst Heq
  ihave %Hlen := BigSepL2.bigSepL2_length $$ Hv
  obtain ⟨ws1, ws2, rfl, h1, h2⟩ := list_app_split ws t1s.length ts.length (by simpa using Hlen)
  unfold interpExpression
  rw [show ofVal (.immV (ws1 ++ ws2)) ++ toEList [.br i] =
      ofVal (.brV (ValidHoled.base (n := i) (ws1 ++ ws2) [])) by simp [ofVal, vfill, toEList]]
  iapply IrisWp.wp_value' (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
  isplitr [Hf Hfv]
  · iright; ileft
    rw [fixpoint_interp_br_eq]
    dsimp only [interpCallHostBrDef]
    unfold interpCtxContinuations
    ihave Hbr := BigSepL.bigSepL_lookup Hlook $$ Hc
    unfold interpCtxContinuation
    icases Hbr with ⟨%vs', %n, %es, %lh', %es', %lh'', %Hlayer, %Hdep, %Hmin, #Hbr⟩
    have Heq := get_layer_lh_depth lh i vs' n es lh' es' (by simp at Hleneq; omega) Hlayer
    have Hn := get_layer_lookup_lh_lengths C.label lh i ts vs' n es lh' es' Hlh_len Hlook Hlayer
    iexists i, ValidHoled.base (n := i) (ws1 ++ ws2) [], ws1 ++ ws2, 0
    isplitr; · ipureintro; rfl
    isplitr; · ipureintro; rfl
    isplitr; · ipureintro; rfl
    simp only [Nat.sub_zero]
    iexists ts, vs', n, es, lh', es', lh'', t1s
    isplitr; · ipureintro; exact Hlook
    isplitr; · ipureintro; exact Hlayer
    isplit; · ipureintro; exact Hdep
    isplitr; · ipureintro; exact Hmin
    isplitr
    · unfold interpVal interpValues; iright; iexists ws1 ++ ws2; isplitr; · ipureintro; rfl
      iexact Hv
    iintro %f0 ⟨Hf0, Hf0v⟩
    rw [show ofVal (.immV ((ws1 ++ ws2).drop t1s.length)) ++ [.basic (.br i)] =
        vToEList ws2 ++ [.basic (.br i)] by simp [ofVal, h1], Heq]
    iapply wp_br_ctx (v_to_e_is_const_list ws2) (by simp [vToEList, Hn, h2]) $$ Hf0
    inext
    iintro Hf0
    ihave ⟨Hv1, Hv2⟩ := (BigSepL2.bigSepL2_append (Or.inl h1)).1 $$ Hv
    ihave Hcont := Hbr $$ %(.immV ws2) %f0 [] [Hf0 Hf0v]
    · unfold interpVal interpValues; iright; iexists ws2; isplitr; · ipureintro; rfl
      iexact Hv2
    · iframe
    icases Hcont with ⟨%τs2, Hcont⟩
    unfold interpExpression
    rw [show vs' ++ vToEList ws2 ++ es ++ es' = vs' ++ (ofVal (.immV ws2) ++ es) ++ es' by
      simp [ofVal]]
    iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ Hcont
    iintro %v ⟨H, Hfr⟩
    iframe Hfr
    icases H with (H | H | H | H)
    · ileft; iexists τs2; iexact H
    · iright; ileft; inext; iunfold interpBr at H; iexact H
    · iright; iright; ileft; iexact H
    · iright; iright; iright; inext; iexists τs2; iunfold interpCallHost at H; iexact H
  · iexists f; iframe

end IrisWasm
