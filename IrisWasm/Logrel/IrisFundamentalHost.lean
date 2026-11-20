/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Logrel.IrisFundamentalHelpers

/-! Port of `theories/iris/logrel/iris_fundamental_host.v`. -/

namespace IrisWasm

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm OFE

variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF] [LogrelNaInvs GF]

attribute [local instance] WasmG.invGS

@[rocq_alias iriswasm.typing_local_host]
theorem typing_local_host [HostProgramLogic (hlc := hlc) GF] (C : TContext)
    (es : List BasicInstruction) (τ1 τ2 τs : List ValueType)
    (hctx : HostProgramLogic.hostCtx hlc GF) (hl : List (Hostfuncidx × FunctionType))
    (be_fundamental : ∀ C es τ, BeTyping C es τ → ⊢ semanticTyping (GF := GF) C (toEList es) τ)
    (hnil : C.label = [] ∧ C.return_ = none)
    (htyping : BeTyping (updLocalLabelReturn C (τ1 ++ τs) [τ2] (some τ2)) es (.tf [] τ2)) :
    ⊢ semanticTypingLocal (GF := GF) C hl es τs (.tf τ1 τ2) hctx := by
  unfold semanticTypingLocal interpHostReturn
  isplit
  · ipureintro; exact hnil
  iintro %i #Hi #Hhcalls #Hhreturn %f %vs Hf Hown #Hv
  have hnv : toVal ([.local τ2.length ⟨vs, i⟩ [.label τ2.length [] (toEList es)]] : Expr) = none := by
    rcases hv : toVal ([.local τ2.length ⟨vs, i⟩ [.label τ2.length [] (toEList es)]] : Expr) with
      _ | v
    · rfl
    obtain ⟨tf, h, w, vh, rfl⟩ := to_val_local_inv _ _ _ _ hv
    obtain ⟨LI, hLI, hLIv⟩ := to_val_call_host_rec_local _ [] _ _ _ [] _ _ _ hv
    simp [vToEList] at hLI
    subst hLI
    obtain ⟨vh', -, hvh'⟩ := to_val_call_host_label_inv _ _ _ _ _ _ _ hLIv
    exact (to_es_list_llfill_contr _ _ _ _ _ hvh').elim
  have Ht := be_fundamental _ _ _ htyping
  dsimp only [semanticTyping, updLocalLabelReturn] at Ht
  iunfold interpExpressionClosure
  ihave #Hctx : interpCtx (GF := GF) [τ2] (some τ2) hl (τ1 ++ τs) i
      (.rec_ [] τ2.length [] (.base [] []) []) $$ []
  · iunfold interpCtx
    isplitr; · ipureintro; exact ⟨rfl, rfl⟩
    isplitr; · ipureintro; exact ⟨rfl, trivial⟩
    isplitr; · ipureintro; exact ⟨rfl, rfl⟩
    iunfold interpCtxContinuations
    iapply BigSepL.bigSepL_singleton.2
    iunfold interpCtxContinuation
    iexists [], τ2.length, [], .base [] [], [], .base [] []
    isplitr; · ipureintro; rfl
    isplitr; · ipureintro; rfl
    isplitr; · ipureintro; rfl
    imodintro
    iintro %v %f' #Hv' ⟨Hf', Hfv'⟩
    iexists τ2
    iunfold interpExpression
    simp only [List.nil_append, List.append_nil]
    iapply IrisWp.wp_value (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) ⟨rfl⟩
    isplitl []
    · ileft; iexact Hv'
    iexists f'; iframe
  ihave #Hi' : interpInstance (GF := GF) { C with local_ := τ1 ++ τs, label := [τ2], return_ := some τ2 }
      hl i $$ []
  · rw [show interpInstance (GF := GF) { C with local_ := τ1 ++ τs, label := [τ2], return_ := some τ2 }
      hl i = interpInstance C hl i from rfl]
    iexact Hi
  ihave H : wpWasmFrame .NotStuck ⊤ [.label τ2.length [] (toEList es)]
      (fun w => iprop((interpVal τ2 w ∨ interpCallHostCls hl τ2 w) ∗ ↪[frame] f ∗
        NonAtomicInvariant.own (LogrelNaInvs.logrelNais GF) ⊤)) τ2.length ⟨vs, i⟩ $$ [Hf Hown]
  · iapply wp_frame_bind .NotStuck ⊤ _ τ2.length ⟨vs, i⟩ f _ hnv $$ Hf
    iintro Hf
    ihave Hb := Ht $$ %i %(.rec_ [] τ2.length [] (.base [] []) []) %hl Hi' Hctx %⟨vs, i⟩ %(.immV [])
      [Hf Hown] []
    · iframe Hf; iunfold interpFrame; iexists vs; iframe
      isplitr; · ipureintro; rfl
      iexact Hv
    · iunfold interpVal; iright; iunfold interpValues
      iexists []
      isplitr; · ipureintro; rfl
      iapply BigSepL2.bigSepL2_nil.2; iempintro
    rw [show ofVal (.immV []) ++ toEList es = toEList es by simp [ofVal, vToEList]]
    iunfold interpExpression at Hb
    icases wp_wasm_empty_ctx .NotStuck ⊤ _ [.label τ2.length [] (toEList es)] with ⟨-, Hemp⟩
    iapply Hemp
    iapply wp_label_push_nil
    simp only [pushBase, Nat.zero_add]
    iapply wp_label_bind
    iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ Hb
    iintro %v ⟨Hv', %f0, Hf0, Hf0v⟩
    icases Hv' with (Hv' | Hbr | Hret | Hch)
    · iunfold interpVal at Hv'
      icases Hv' with (%Htr | Hv')
      · subst Htr; rw [show ofVal Val.trapV = [AdministrativeInstruction.trap] from rfl]
        iapply local_host_trap $$ Hf0 Hf0v
      · iapply local_host_val $$ Hv' Hf0 Hf0v
    · iapply local_host_br $$ [Hbr] Hf0 Hf0v
      inext; iexact Hbr
    · iapply local_host_ret $$ Hret Hf0 Hf0v
    · iapply local_host_call $$ Hch Hf0 Hf0v
  iapply HostProgramLogic.wpHostBind
  unfold wpWasmFrame
  iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ H
  iintro %v ⟨Hres, Hf, Hown⟩
  icases Hres with (#Hres | #Hres)
  · iapply Hhreturn $$ Hres Hown Hf
  ihave #Hres' : ▷ interpCallHostCls hl τ2 v $$ []
  · inext; iexact Hres
  iclear Hres
  irevert Hres'
  iloeb as IH generalizing %v
  iintro #Hres
  rw [fixpoint_interp_call_host_cls_eq]; dsimp only [interpCallHostClsDef]
  iapply HostProgramLogic.fupdWpHost
  icases Hres with ⟨%vh, %w, %tf, %h, %τs1, %τs2, >%Heq, >%Htf, >%Hin, >%Hb, >#Hval, #Hres⟩
  imodintro
  subst Heq Htf
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 Hin
  iunfold interpHostCalls at Hhcalls
  ihave #Hh := BigSepL.bigSepL_lookup hk $$ Hhcalls
  dsimp only [interpClosureHost]
  rw [show ofVal (.callHostV (.tf τs1 τs2) h w vh) = llfill vh [.callHost (.tf τs1 τs2) h w] from rfl]
  iapply Hh $$ %w %f %vh Hval Hown Hf
  inext
  iintro %v2 #Hv2 Hown Hf
  iapply HostProgramLogic.wpHostBind
  ihave Hcont := Hres $$ %v2 %f Hv2 Hf Hown
  iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ Hcont
  iintro %v ⟨(Hw | #Hw), Hf, Hown⟩
  · iapply Hhreturn $$ Hw Hown Hf
  · iapply IH $$ %v Hf Hown
    imodintro; iexact Hw

end IrisWasm
