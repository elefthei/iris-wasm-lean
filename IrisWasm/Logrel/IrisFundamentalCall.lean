/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Logrel.IrisFundamentalHelpers
import IrisWasm.Logrel.IrisFundamentalComposition
import IrisWasm.Logrel.IrisFundamentalTrap

/-! Port of `theories/iris/logrel/iris_fundamental_call.v`. -/

namespace IrisWasm

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm OFE

variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF] [LogrelNaInvs GF]

attribute [local instance] WasmG.invGS

open FundAux

/-- The Löb induction inside Coq's `typing_call`: a host call of a closure body is a host call of the
calling context. -/
theorem FundAux.call_host_cls_call_host (C : TContext) (j : Instance) (hl : List (Hostfuncidx × FunctionType))
    (lh : Lholed) (t2 : List ValueType) :
    ⊢ ∀ v, interpCallHostCls (GF := GF) hl t2 v -∗
      interpCallHost C.local_ j C.return_ hl v lh C.label t2 := by
  iloeb as IH
  iintro %v
  rw [fixpoint_interp_call_host_cls_eq]; dsimp only [interpCallHostClsDef]
  iintro Hw
  icases Hw with ⟨%vh, %v0, %tf, %h, %τs1, %τs2, %Heqv, %Heqt, %Hin, %Hb, #Hv0, #H⟩
  rw [fixpoint_interp_call_host_eq]; dsimp only [interpCallHostBrDef]; simp only [fold_br, fold_ch]
  iexists vh, v0, tf, h, τs1, τs2
  isplitr; · ipureintro; exact Heqv
  isplitr; · ipureintro; exact Heqt
  isplitr; · ipureintro; exact Hin
  isplitr; · ipureintro; exact Hb
  isplitr; · iexact Hv0
  imodintro
  iintro %v2 %f #Hv2 ⟨Hf, Hfv⟩
  unfold interpFrame
  icases Hfv with ⟨%locs, %Heq, #Hlocs, Hown⟩
  ihave H' := H $$ %v2 %f Hv2 Hf Hown
  iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ H'
  iintro %w ⟨Hw, Hf, Hown⟩
  isplitl [Hw]
  · icases Hw with (#Hw | Hw)
    · ileft; iexact Hw
    · iright; iright; iright; inext; iapply IH $$ %w Hw
  iexists f; iframe Hf; iexists locs; iframe
  isplitr; · ipureintro; exact Heq
  iexact Hlocs

/-- Invoking a function address whose closure is in the logical relation (the shared second half
of Coq's `typing_call` and `typing_call_indirect`). -/
theorem FundAux.invoke_closure (C : TContext) (j : Instance) (hl : List (Hostfuncidx × FunctionType))
    (lh : Lholed) (locs ws : List Value) (a : Nat) (cl : FunctionClosure) (tf1 tf2 : List ValueType) :
    ⊢ NonAtomicInvariant.inv (LogrelNaInvs.logrelNais GF) (wfN a) (a ↦[wf] cl : IProp GF) -∗
      interpClosure hl (.tf tf1 tf2) cl -∗
      ([∗list] w;τ ∈ ws;tf1, interpValue τ w) -∗
      interpVal C.local_ (.immV locs) -∗
      NonAtomicInvariant.own (LogrelNaInvs.logrelNais GF) ⊤ -∗
      ↪[frame] ⟨locs, j⟩ -∗
      WP (ofVal (.immV ws) ++ [.invoke a])
        {{ v, (interpVal tf2 v ∨ interpBr C.local_ j C.return_ hl v lh C.label ∨
            interpReturnOption C.return_ C.local_ j v ∨
            interpCallHost C.local_ j C.return_ hl v lh C.label tf2) ∗
          ∃ f, ↪[frame] f ∗ interpFrame C.local_ j f }} := by
  iintro #Hinv Hcl #Hv #Hlocs Hown Hf
  ihave %Hlen := BI.BigSepL2.bigSepL2_length $$ Hv
  iapply IrisWp.fupd_wp (ι := wasmIrisGS) (fun f => iprop(↪[frame] f))
  imod NonAtomicInvariant.inv_acc CoPset.subseteq_top CoPset.subseteq_top $$ Hinv Hown with
    ⟨>Hcl0, Hown, Hcls⟩
  imodintro
  have hval : toVal (ofVal (.immV ws)) = some (.immV ws) := to_of_val _
  rcases cl with ⟨i', ⟨t1, t2⟩, tlocs, e⟩ | ⟨⟨t1, t2⟩, h⟩
  · isimp only [interpClosure] at Hcl
    icases Hcl with ⟨%Htf, #Hcl⟩
    cases Htf
    iapply wp_invoke_native .NotStuck ⊤ _ _ ws tf1 tf2 tlocs a e i' tf2.length ⟨locs, j⟩ hval Hlen rfl
      $$ Hf Hcl0
    inext
    iintro ⟨Hf, Hcl0⟩
    iapply IrisWp.fupd_wp (ι := wasmIrisGS) (fun f => iprop(↪[frame] f))
    imod Hcls $$ [Hcl0 Hown] with Hown
    · iframe
    imodintro
    ihave H : wpWasmCtxFrame .NotStuck ⊤ [.basic (.block (.tf [] tf2) e)]
        (fun v => iprop((interpVal tf2 v ∨ interpCallHostCls hl tf2 v) ∗
          NonAtomicInvariant.own (LogrelNaInvs.logrelNais GF) ⊤ ∗ ↪[frame] ⟨locs, j⟩))
        tf2.length ⟨ws ++ nZeros tlocs, i'⟩ 0 (.base [] []) $$ [Hf Hown]
    · rw [← List.nil_append [AdministrativeInstruction.basic (.block (.tf [] tf2) e)]]
      iapply wp_block_local_ctx (vs := []) (t1s := []) rfl rfl rfl rfl $$ Hf
      inext
      iintro Hf
      iapply wp_label_push_nil_local
      simp only [List.nil_append, pushBase, Nat.zero_add]
      iunfold interpClosureNative at Hcl
      iapply Hcl $$ %ws %⟨locs, j⟩ [] Hown Hf
      iunfold interpVal; iright; iunfold interpValues
      iexists ws
      isplitr; · ipureintro; rfl
      iexact Hv
    unfold wpWasmCtxFrame
    ispecialize H $$ %_ %(lfilled_empty'.2 rfl)
    iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ H
    iintro %w ⟨Hw, Hown, Hf⟩
    isplitl [Hw]
    · icases Hw with (#Hw | Hw)
      · ileft; iexact Hw
      · iright; iright; iright; iapply call_host_cls_call_host $$ %w Hw
    iexists ⟨locs, j⟩; iframe Hf; iunfold interpFrame; iexists locs; iframe
    isplitr; · ipureintro; rfl
    iexact Hlocs
  · isimp only [interpClosure] at Hcl
    icases Hcl with ⟨%Htf, %Hin⟩
    cases Htf
    iapply wp_invoke_host .NotStuck ⊤ (ofVal (.immV ws)) ws ws.length tf1 tf2 a h ⟨locs, j⟩ _ rfl rfl Hlen.symm
      $$ Hcl0 Hf
    inext
    iintro Hcl0 Hf
    iapply IrisWp.fupd_wp (ι := wasmIrisGS) (fun f => iprop(↪[frame] f))
    imod Hcls $$ [Hcl0 Hown] with Hown
    · iframe
    imodintro
    rw [show ([.callHost (.tf tf1 tf2) h ws] : Expr) =
      ofVal (.callHostV (.tf tf1 tf2) h ws (.base [] [])) by simp [ofVal, llfill, vToEList]]
    iapply IrisWp.wp_value (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) ⟨rfl⟩
    isplitr [Hf Hown]
    rotate_left
    · iexists ⟨locs, j⟩; iframe Hf; iunfold interpFrame; iexists locs; iframe
      isplitr; · ipureintro; rfl
      iexact Hlocs
    iright; iright; iright
    rw [fixpoint_interp_call_host_eq]; dsimp only [interpCallHostBrDef]; simp only [fold_br, fold_ch]
    iexists .base [] [], ws, .tf tf1 tf2, h, tf1, tf2
    isplitr; · ipureintro; rfl
    isplitr; · ipureintro; rfl
    isplitr; · ipureintro; exact Hin
    isplitr; · ipureintro; exact trivial
    isplitr
    · iunfold interpVal; iright; iunfold interpValues
      iexists ws
      isplitr; · ipureintro; rfl
      iexact Hv
    imodintro
    iintro %v2 %f' #Hv2 ⟨Hf', Hfv'⟩
    rw [show llfill (.base [] []) (ofVal v2) = ofVal v2 by simp [llfill, vToEList]]
    iapply IrisWp.wp_value (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) ⟨rfl⟩
    isplitl []
    · ileft; iexact Hv2
    iexists f'; iframe


@[rocq_alias iriswasm.typing_call]
theorem typing_call (C : TContext) (i : Nat) (tf : FunctionType) (hleq : i + 1 ≤ C.funcT.length)
    (hlookup : C.funcT[i]? = some tf) :
    ⊢ semanticTyping (GF := GF) C (toEList [.call i]) tf := by
  obtain ⟨tf1, tf2⟩ := tf
  apply semantic_typing_immV
  intro j lh hl f ws
  iintro #Hi #Hctx Hf Hfv #Hv
  icases interp_instance_function_lookup C hl i (.tf tf1 tf2) j hleq hlookup $$ Hi with
    ⟨%a, %Ha, Hfunc⟩
  unfold interpFunction
  icases Hfunc with ⟨%cl, #Hinv, Hcl⟩
  unfold interpFrame
  icases Hfv with ⟨%locs, %Heq, #Hlocs, Hown⟩
  subst Heq
  unfold interpExpression
  iapply ctx_empty_elim
  rw [show ofVal (.immV ws) ++ toEList [.call i] = ofVal (.immV ws) ++ [.basic (.call i)] ++ [] by
    simp [toEList]]
  iapply wp_base_push (const_list_of_val ws)
  iapply wp_call_ctx .NotStuck ⊤ _ ⟨locs, j⟩ i a 0 _ Ha $$ Hf
  inext
  iintro Hf
  unfold wpWasmCtx
  iintro %LI %HLI
  have HLI' : LI = ofVal (.immV ws) ++ [.invoke a] := by
    simpa [frameBase, lfilled, lfill, const_list_of_val] using HLI.symm
  subst HLI'
  iapply invoke_closure $$ Hinv Hcl Hv Hlocs Hown Hf

end IrisWasm
