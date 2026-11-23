/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Logrel.IrisFundamentalBr

/-! Port of `theories/iris/logrel/iris_fundamental_block.v`. -/

namespace IrisWasm

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm

variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF] [LogrelNaInvs GF]

attribute [local instance] WasmG.invGS

@[rocq_alias iriswasm.interp_ctx_continuations_push_label_block]
theorem interp_ctx_continuations_push_label_block (lh : Lholed) (C : TContext)
    (hl : List (Hostfuncidx × FunctionType)) (i : Instance) (tm : List ValueType)
    (hbase : BaseIsEmpty lh) (_hlen : lengthLholeds C.label.reverse lh) :
    ⊢ iprop(interpCtxContinuations (GF := GF) C.label C.return_ hl C.local_ i lh -∗
      interpCtxContinuation (updLabel C ([tm] ++ C.label)).label C.return_ hl
        (pushBase lh tm.length [] [] []) 0 tm C.local_ i) := by
  iintro #Hc
  unfold interpCtxContinuation
  rw [lh_depth_push_base, show lhDepth lh + 1 - (0 + 1) = lhDepth lh by omega,
    get_layer_push_base_0 lh _ _ _ _ hbase]
  have hmin := lh_minus_push_base_Some lh tm.length [] [] [] hbase
  iexists [], tm.length, [], .base [] [], [], lh
  isplit; · ipureintro; rfl
  isplit; · ipureintro; omega
  isplit; · ipureintro; simp [hmin]
  imodintro
  iintro %v %f #Hw ⟨Hf, Hfv⟩
  simp only [List.nil_append, List.append_nil]
  unfold interpVal interpValues
  icases Hw with (%Heq | ⟨%ws, %Heq, #Hv⟩)
  · subst Heq
    iexists []
    ihave H := interp_expression_trap (GF := GF) ((updLabel C ([tm] ++ C.label)).label.drop (0 + 1))
      C.return_ hl [] lh C.local_ i f [] $$ Hf Hfv
    rw [List.append_nil]
    iexact H
  subst Heq
  iexists tm
  unfold interpExpression
  iapply IrisWp.wp_value (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
    (v := .immV ws) ⟨rfl⟩
  isplitr [Hf Hfv]
  · ileft; unfold interpVal interpValues; iright; iexists ws; isplitr; · ipureintro; rfl
    iexact Hv
  · iexists f; iframe

@[rocq_alias iriswasm.interp_ctx_push_label_block]
theorem interp_ctx_push_label_block (C : TContext) (hl : List (Hostfuncidx × FunctionType))
    (tm : List ValueType) (i : Instance) (lh : Lholed) :
    ⊢ iprop(interpCtx (GF := GF) C.label C.return_ hl C.local_ i lh -∗
      interpCtx (updLabel C ([tm] ++ C.label)).label C.return_ hl
        (updLabel C ([tm] ++ C.label)).local_ i (pushBase lh tm.length [] [] [])) := by
  unfold interpCtx
  iintro ⟨%Hlh_base, %Hlh_len, %Hlh_valid, #Hc⟩
  isplitr; · ipureintro; exact base_is_empty_push_base _ _ _
  isplitr
  · ipureintro
    simpa [updLabel] using length_lholeds_push_base lh _ tm [] Hlh_len
  isplitr; · ipureintro; exact lholed_valid_push_base _ _ _ Hlh_valid
  ihave Hc0 := interp_ctx_continuations_push_label_block lh C hl i tm Hlh_base Hlh_len $$ Hc
  unfold interpCtxContinuations
  simp only [updLabel, List.singleton_append]
  iapply BigSepL.bigSepL_cons.2
  isplitr
  · iexact Hc0
  iapply BigSepL.bigSepL_impl $$ Hc
  imodintro
  iintro %k %τs %_ Hcont
  unfold interpCtxContinuation
  icases Hcont with ⟨%vs, %j, %es0, %lh', %es', %lh'', %Hlayer, %Hdep, %Hmin, #Hcont⟩
  iexists vs, j, es0, pushBase lh' tm.length [] [] [], es', lh''
  rw [lh_depth_push_base, show lhDepth lh + 1 - (k + 1 + 1) = lhDepth lh - (k + 1) by omega]
  isplit; · ipureintro; exact get_layer_push_base _ _ _ _ _ _ _ _ _ _ _ Hlayer
  isplit; · ipureintro; exact Hdep
  isplit; · ipureintro; exact push_base_lh_minus_is_Some _ _ _ _ _ _ Hmin
  simp only [List.drop_succ_cons]
  iexact Hcont

theorem typing_block (C : TContext) {bt : Wasm.BlockType} (tn tm : List ValueType)
    (es : List BasicInstruction) (hsig : expandBlockType C.typesT bt = some (.tf tn tm))
    (h : ⊢ semanticTyping (GF := GF) (updLabel C ([tm] ++ C.label)) (toEList es) (.tf tn tm)) :
    ⊢ semanticTyping (GF := GF) C (toEList [.block bt es]) (.tf tn tm) := by
  unfold semanticTyping
  iintro %i %lh %hl #Hi #Hc %f %vs ⟨Hf, Hfv⟩ #Hv
  unfold interpVal interpValues
  icases Hv with (%Heq | ⟨%ws, %Heq, #Hv⟩)
  · subst Heq
    iapply interp_expression_trap $$ Hf Hfv
  subst Heq
  ihave %Hlen := BigSepL2.bigSepL2_length $$ Hv
  unfold interpExpression
  ihave ⟨%Htypes, Hfv⟩ := interp_frame_types $$ Hi Hfv
  rw [show toEList [.block bt es] = [.basic (.block bt es)] from rfl]
  iapply wp_block (bt := bt) (f := f) (vs := ofVal (.immV ws)) (es := es) (n := ws.length)
    (m := tm.length) (t1s := tn) (t2s := tm) (const_list_of_val ws) (of_val_length ws)
    Hlen.symm rfl (Htypes.symm ▸ hsig) $$ Hf
  inext
  iintro Hf
  icases wp_wasm_empty_ctx (GF := GF) .NotStuck ⊤ _ _ with ⟨-, H⟩
  iapply H
  iapply wp_label_push_nil
  rw [← List.append_nil (ofVal (.immV ws) ++ toEList es)]
  iapply wp_seq_can_trap_ctx _ _ _
    (fun w => iprop(interpValues tm w ∨
      interpBr C.local_ i C.return_ hl w (pushBase lh tm.length [] [] [])
        (updLabel C ([tm] ++ C.label)).label ∨
      interpReturnOption (updLabel C ([tm] ++ C.label)).return_
        (updLabel C ([tm] ++ C.label)).local_ i w ∨
      interpCallHost C.local_ i C.return_ hl w (pushBase lh tm.length [] [] [])
        (updLabel C ([tm] ++ C.label)).label tm))
    _ _ _ _ (interpFrame C.local_ i) f
  isplitr
  · iintro (H | H | H | H)
    · iunfold interpValues at H
      icases H with ⟨%_, %Hc, -⟩; cases Hc
    · rw [fixpoint_interp_br_eq]
      dsimp only [interpCallHostBrDef]
      icases H with ⟨%_, %_, %_, %_, %Hc, -⟩; cases Hc
    · unfold interpReturnOption
      icases H with ⟨%_, %_, %Hc, -⟩; cases Hc
    · rw [fixpoint_interp_call_host_eq]
      dsimp only [interpCallHostBrDef]
      icases H with ⟨%_, %_, %_, %_, %_, %_, %Hc, -⟩; cases Hc
  isplitr
  · iintro %f0 ⟨Hf0, Hfv0⟩
    isplitr [Hf0 Hfv0]
    · ileft; unfold interpVal; ileft; ipureintro; rfl
    · iexists f0; iframe
  isplitl [Hf]
  · iexact Hf
  isplitl [Hfv]
  · iintro Hf
    ihave HH := h
    ihave #Hc' := interp_ctx_push_label_block C hl tm i lh $$ Hc
    unfold semanticTyping
    rw [show (updLabel C ([tm] ++ C.label)).return_ = C.return_ from rfl,
      show (updLabel C ([tm] ++ C.label)).local_ = C.local_ from rfl]
    ihave HH := HH $$ %i %(pushBase lh tm.length [] [] []) %hl [] [] %f %(.immV ws) [Hf Hfv] []
    · iapply interp_instance_change_label $$ Hi
    · iexact Hc'
    · iframe
    · unfold interpVal interpValues; iright; iexists ws; isplitr; · ipureintro; rfl
      iexact Hv
    unfold interpExpression
    iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ HH
    iintro %v ⟨H, Hfr⟩
    iframe Hfr
    unfold interpVal
    icases H with ((H | H) | H | H | H)
    · ileft; iexact H
    · iright; ileft; iexact H
    · iright; iright; ileft; iexact H
    · iright; iright; iright; ileft; iexact H
    · iright; iright; iright; iright; iexact H
  iintro %w %f0 ⟨H, Hf0, Hfv0⟩
  simp only [List.append_nil, Nat.zero_add,
    show pushBase (.base [] []) tm.length [] [] [] = .rec_ [] tm.length [] (.base [] []) [] from rfl]
  icases H with (H | H | H | H)
  · iunfold interpValues at H
    icases H with ⟨%vs, %Heq, #Hvs⟩
    subst Heq
    iapply wp_val_return (vs' := []) (es'' := []) (const_list_of_val vs) $$ Hf0
    iintro Hf0
    iapply IrisWp.wp_value (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
      (e := [] ++ ofVal (.immV vs) ++ []) (v := .immV vs) ⟨by simp; rfl⟩
    isplitr [Hf0 Hfv0]
    · ileft; unfold interpVal interpValues; iright; iexists vs; isplitr; · ipureintro; rfl
      iexact Hvs
    · iexists f0; iframe
  · iapply interp_br_label C i w f0 tm lh hl $$ Hc H Hf0 Hfv0
  · iapply interp_return_label C tm i w f0 tm lh [] tm.length hl $$ H Hf0 Hfv0
  · iapply interp_call_host_label C i w f0 tm lh hl $$ Hc H Hf0 Hfv0

end IrisWasm
