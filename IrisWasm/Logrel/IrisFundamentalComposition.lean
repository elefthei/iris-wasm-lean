/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Logrel.IrisFundamentalHelpers

/-! Port of `theories/iris/logrel/iris_fundamental_composition.v`.

`llholed_basic_sh_append` is also declared (with a different statement) in
`iris_robust_example_host.v`, so it lives in namespace `IrisWasm.IrisFundamentalComposition`. -/

namespace IrisWasm

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm OFE

variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF] [LogrelNaInvs GF]

attribute [local instance] WasmG.invGS

/-! Lean-only helpers shared by the fundamental-theorem case files (no Coq counterpart). -/
namespace FundAux

theorem lfilled_empty' {e LI : Expr} : lfilled 0 (.base [] []) e LI = true ↔ LI = e := by
  simp [lfilled, lfill, constList]

omit [LogrelNaInvs GF] in
theorem ctx_empty {e : Expr} {Φ : Val → IProp GF} :
    WP e {{ Φ }} ⊢ WP e CTX 0 ; (Lholed.base [] []) {{ Φ }} := by
  unfold wpWasmCtx; iintro H %LI %hLI; rw [lfilled_empty'.1 hLI]; iexact H

omit [LogrelNaInvs GF] in
theorem ctx_empty_elim {e : Expr} {Φ : Val → IProp GF} :
    WP e CTX 0 ; (Lholed.base [] []) {{ Φ }} ⊢ WP e {{ Φ }} := by
  unfold wpWasmCtx; iintro H; iapply H $$ %e %(lfilled_empty'.2 rfl)

section trapFalse
variable {τl : List ValueType} {i : Instance} {τto : Option (List ValueType)}
  {hl : List (Hostfuncidx × FunctionType)} {lh : Lholed} {τc : List (List ValueType)}
  {τs : List ValueType}

theorem br_trap_false : (interpBr τl i τto hl .trapV lh τc : IProp GF) ⊢ False := by
  rw [fixpoint_interp_br_eq]; dsimp only [interpCallHostBrDef]
  iintro ⟨%j, %vh, %vs, %p, %h, -⟩; cases h

theorem ch_trap_false :
    (interpCallHost τl i τto hl .trapV lh τc τs : IProp GF) ⊢ False := by
  rw [fixpoint_interp_call_host_eq]; dsimp only [interpCallHostBrDef]
  iintro ⟨%vh, %vs, %tf, %h, %τs1, %τs2, %hw, -⟩; cases hw

omit [LogrelNaInvs GF] in
theorem ret_trap_false :
    (interpReturnOption τto τl i .trapV : IProp GF) ⊢ False := by
  unfold interpReturnOption
  iintro ⟨%vh, %vs, %hw, -⟩; cases hw

omit [LogrelNaInvs GF] in
theorem values_trap_false : (interpValues τs .trapV : IProp GF) ⊢ False := by
  unfold interpValues
  iintro ⟨%ws, %hw, -⟩; cases hw

end trapFalse

omit [LogrelNaInvs GF] in
scoped instance isExcept0WpWasm {s : Stuckness} {E : CoPset} {e : Expr} {Φ : Val → IProp GF} :
    Iris.ProofMode.IsExcept0 (WP e @ s ; E {{ Φ }} : IProp GF) :=
  IrisWp.isExcept0Wp (P := fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)

theorem fold_br {τl i τto hl v lh τc} :
    (interpCallHostBr (GF := GF) τl i τto hl).2 v lh τc = interpBr τl i τto hl v lh τc := rfl

theorem fold_ch {τl i τto hl v lh τc t} :
    (interpCallHostBr (GF := GF) τl i τto hl).1 v lh τc t = interpCallHost τl i τto hl v lh τc t :=
  rfl

end FundAux

open FundAux


@[rocq_alias iriswasm.get_base_l_append]
theorem get_base_l_append {i : Nat} (lh : ValidHoled i) (e : List AdministrativeInstruction) :
    getBaseL (vhAppend lh e) = getBaseL lh := by
  cases lh <;> rfl

@[rocq_alias iriswasm.append_lh_depth]
theorem append_lh_depth {i : Nat} (lh : ValidHoled i) (e : List AdministrativeInstruction) :
    lhDepth (lhOfVh lh) = lhDepth (lhOfVh (vhAppend lh e)) := by
  cases lh <;> rfl

@[rocq_alias iriswasm.simple_get_base_l_append]
theorem simple_get_base_l_append (lh : SimpleValidHoled) (e : List AdministrativeInstruction) :
    simpleGetBaseL (shAppend lh e) = simpleGetBaseL lh := by
  cases lh <;> rfl

@[rocq_alias iriswasm.composition_br]
theorem composition_br (t1s t3s : List ValueType) (vs : Val) (C : TContext) (i : Instance)
    (hl : List (Hostfuncidx × FunctionType)) (w : Val) (lh : Lholed) (f' : Frame)
    (e : AdministrativeInstruction) :
    ⊢ interpVal (GF := GF) t1s vs -∗
      interpBr C.local_ i C.return_ hl w lh C.label -∗
      ↪[frame] f' -∗
      interpFrame C.local_ i f' -∗
      WP (ofVal w ++ [e]) CTX 0 ; (Lholed.base [] [])
        {{ v, (interpVal t3s v ∨
               interpBr C.local_ i C.return_ hl v lh C.label ∨
               interpReturnOption C.return_ C.local_ i v ∨
               interpCallHost C.local_ i C.return_ hl v lh C.label t3s) ∗
              ∃ f0, ↪[frame] f0 ∗ interpFrame C.local_ i f0 }} := by
  rw [fixpoint_interp_br_eq]; dsimp only [interpCallHostBrDef]
  iintro #Hv Hbr Hf Hfv
  iapply ctx_empty
  icases Hbr with ⟨%j, %vh, %vs', %p, %Heq, %Hbase, %Hdepth, Hbr⟩
  subst Heq
  rw [of_val_br_app_r]
  iapply IrisWp.wp_value (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) ⟨rfl⟩
  isplitr [Hf Hfv]
  · iright; ileft
    rw [fixpoint_interp_br_eq]; dsimp only [interpCallHostBrDef]
    iexists j, vhAppend vh [e], vs', p
    isplitr; · ipureintro; rfl
    isplitr; · ipureintro; rw [get_base_l_append]; exact Hbase
    isplitr; · ipureintro; rw [← append_lh_depth]; exact Hdepth
    iexact Hbr
  · iexists f'; iframe

@[rocq_alias iriswasm.composition_return]
theorem composition_return (t1s t3s : List ValueType) (vs : Val) (C : TContext) (i : Instance)
    (w : Val) (f' : Frame) (e : AdministrativeInstruction)
    (hl : List (Hostfuncidx × FunctionType)) (lh : Lholed) :
    ⊢ interpVal (GF := GF) t1s vs -∗
      interpReturnOption C.return_ C.local_ i w -∗
      ↪[frame] f' -∗
      interpFrame C.local_ i f' -∗
      WP (ofVal w ++ [e]) CTX 0 ; (Lholed.base [] [])
        {{ v, (interpVal t3s v ∨
               interpBr C.local_ i C.return_ hl v lh C.label ∨
               interpReturnOption C.return_ C.local_ i v ∨
               interpCallHost C.local_ i C.return_ hl v lh C.label t3s) ∗
              ∃ f0, ↪[frame] f0 ∗ interpFrame C.local_ i f0 }} := by
  iintro _ Hret Hf Hfv
  iunfold interpReturnOption at Hret
  icases Hret with ⟨%sh, %vs', %Hw, %Hbase, Hret⟩
  iapply ctx_empty
  subst Hw
  rcases hret : C.return_ with _ | τr
  · iexfalso; iexact Hret
  icases Hret with ⟨%τs'', #Hw, Hret⟩
  rw [of_val_ret_app_r]
  iapply IrisWp.wp_value (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) ⟨rfl⟩
  isplitr [Hf Hfv]
  rotate_left; · iexists f'; iframe
  iright; iright; ileft
  iunfold interpReturnOption
  iexists shAppend sh [e], vs'
  isplitr; · ipureintro; rfl
  isplitr; · ipureintro; rw [simple_get_base_l_append]; exact Hbase
  iexists τs''
  ihave Hw2 := Hw
  iunfold interpVal, interpValues at Hw2
  icases Hw2 with (%Hc | ⟨%ws, %Heq, Hws⟩)
  · cases Hc
  cases Heq
  ihave %Hlen := BigSepL2.bigSepL2_length $$ Hws
  isplitr
  · iexact Hw
  iintro %f0 %f1 Hf
  ispecialize Hret $$ %f0 %f1 Hf
  obtain ⟨lh', Hlh'⟩ := lfilled_simple_get_base_pull _ (shAppend sh [e]) [.basic .return_] _
    (vs'.take τs''.length) (vs'.drop τs''.length)
    (by rw [simple_get_base_l_append, List.take_append_drop]; exact Hbase) (sfill_to_lfilled _ _)
  obtain ⟨lh'', Hlh''⟩ := lfilled_simple_get_base_pull _ sh [.basic .return_] _
    (vs'.take τs''.length) (vs'.drop τs''.length)
    (by rw [List.take_append_drop]; exact Hbase) (sfill_to_lfilled _ _)
  isimp only [ofVal] at Hret
  isimp only [ofVal]
  iapply wp_ret_shift (const_list_of_val _) (by simp [of_val_length]; simp at Hlen; omega) Hlh'' Hlh'
  iexact Hret

@[rocq_alias iriswasm.llfill_sh_append]
theorem llfill_sh_append (vh : Llholed) (es es' : List AdministrativeInstruction) :
    llfill (llhAppend vh es) es' = llfill (.base [] es) (llfill vh es') := by
  cases vh <;> simp [llfill, llhAppend, vToEList]

@[rocq_alias iriswasm.is_basic_app]
theorem is_basic_app (l1 l2 : List AdministrativeInstruction) :
    isBasicExpr l1 → isBasicExpr l2 → isBasicExpr (l1 ++ l2) := by
  induction l1 with
  | nil => intro _ h; exact h
  | cons a l ih => intro ⟨ha, hl⟩ h2; exact ⟨ha, ih hl h2⟩

namespace IrisFundamentalComposition

@[rocq_alias iriswasm.iris_fundamental_composition.llholed_basic_sh_append]
theorem llholed_basic_sh_append (vh : Llholed) (e : AdministrativeInstruction) :
    isBasic e → llholedBasic vh → llholedBasic (llhAppend vh [e]) := by
  intro he hvh
  have h1 : isBasicExpr [e] := ⟨he, trivial⟩
  cases vh with
  | base => exact is_basic_app _ _ hvh h1
  | label => exact ⟨is_basic_app _ _ hvh.1 h1, hvh.2⟩
  | «local» => exact ⟨is_basic_app _ _ hvh.1 h1, hvh.2⟩

end IrisFundamentalComposition

private theorem ofVal_callHost_append (tf : FunctionType) (h : Hostfuncidx) (v : List Value)
    (vh : Llholed) (es : List AdministrativeInstruction) :
    ofVal (.callHostV tf h v vh) ++ es = ofVal (.callHostV tf h v (llhAppend vh es)) := by
  simp [ofVal, llfill_sh_append, llfill, vToEList]

private theorem llfill_append_r (vh : Llholed) (es es' : List AdministrativeInstruction) :
    llfill (llhAppend vh es) es' = llfill vh es' ++ es := by
  simp [llfill_sh_append, llfill, vToEList]

open IrisFundamentalComposition in
/-- The Löb induction of `composition_call_host`. -/
private theorem composition_call_host_loop (t2s t3s : List ValueType) (C : TContext)
    (i : Instance) (hl : List (Hostfuncidx × FunctionType)) (lh : Lholed)
    (e : AdministrativeInstruction) (he : isBasic e)
    (ht2 : ⊢ semanticTyping (GF := GF) C [e] (.tf t2s t3s)) :
    ⊢ interpInstance (GF := GF) C hl i -∗
      interpCtx C.label C.return_ hl C.local_ i lh -∗
      ∀ (vh : Llholed) (τs2 : List ValueType) (v2 : Val) (f : Frame), ⌜llholedBasic vh⌝ -∗
        interpVal τs2 v2 -∗
        □ (∀ v2 f, interpVal τs2 v2 -∗ ↪[frame] f ∗ interpFrame C.local_ i f -∗
          WP (llfill vh (ofVal v2))
          {{ vs, (interpVal t2s vs ∨
            ▷ interpBr C.local_ i C.return_ hl vs lh C.label ∨
            interpReturnOption C.return_ C.local_ i vs ∨
            ▷ interpCallHost C.local_ i C.return_ hl vs lh C.label t2s) ∗
            ∃ f, ↪[frame] f ∗ interpFrame C.local_ i f }}) -∗
        ↪[frame] f -∗ interpFrame C.local_ i f -∗
        WP (llfill vh (ofVal v2) ++ [e])
          {{ vs, (interpVal t3s vs ∨
            ▷ interpBr C.local_ i C.return_ hl vs lh C.label ∨
            interpReturnOption C.return_ C.local_ i vs ∨
            ▷ interpCallHost C.local_ i C.return_ hl vs lh C.label t3s) ∗
            ∃ f, ↪[frame] f ∗ interpFrame C.local_ i f }} := by
  simp only [semanticTyping] at ht2
  iintro #Hi #Hc
  iloeb as IH
  iintro %vh %τs2 %v2 %f %Hb #Hv2 #HK Hf Hfv
  iapply ctx_empty_elim
  iapply wp_seq_can_trap_ctx .NotStuck ⊤ _
    (fun w => iprop(interpValues t2s w ∨ ▷ interpBr C.local_ i C.return_ hl w lh C.label ∨
      interpReturnOption C.return_ C.local_ i w ∨
      ▷ interpCallHost C.local_ i C.return_ hl w lh C.label t2s))
    (llfill vh (ofVal v2)) [e] 0 (.base [] []) (interpFrame C.local_ i) f
  isplitr
  · iintro (H | H | H | H)
    · iexfalso; iapply values_trap_false $$ H
    · ihave H := later_mono br_trap_false $$ H
      icases H with >%H; exact H.elim
    · iexfalso; iapply ret_trap_false $$ H
    · ihave H := later_mono ch_trap_false $$ H
      icases H with >%H; exact H.elim
  isplitr
  · iintro %f0 ⟨Hf0, Hfv0⟩
    isplitr [Hf0 Hfv0]
    · ileft; iunfold interpVal; ileft; ipureintro; rfl
    · iexists f0; iframe
  isplitl [Hf]
  · iexact Hf
  isplitl [Hfv]
  · iintro Hf
    ihave H1 := HK $$ %v2 %f Hv2 [Hf Hfv]
    · iframe
    iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ H1
    iintro %v ⟨H, Hfr⟩
    iframe Hfr
    iunfold interpVal at H
    icases H with ((H | H) | H | H | H)
    · ileft; iexact H
    · iright; ileft; iexact H
    · iright; iright; ileft; iexact H
    · iright; iright; iright; ileft; iexact H
    · iright; iright; iright; iright; iexact H
  iintro %w %f0 ⟨Hw, Hf0, Hfv0⟩
  icases Hw with (Hw | Hbr | Hret | Hch)
  · iapply ctx_empty
    ihave H := ht2 $$ %i %lh %hl Hi Hc %f0 %w [Hf0 Hfv0] [Hw]
    · iframe
    · iunfold interpVal; iright; iexact Hw
    iunfold interpExpression at H
    iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ H
    iintro %v ⟨H, Hfr⟩
    iframe Hfr
    icases H with (H | H | H | H)
    · ileft; iexact H
    · iright; ileft; inext; iexact H
    · iright; iright; ileft; iexact H
    · iright; iright; iright; inext; iexact H
  · isimp only [fixpoint_interp_br_eq, interpCallHostBrDef] at Hbr
    iapply ctx_empty
    icases Hbr with ⟨%j, %vh', %vs', %p, >%Heq, >%Hbase, >%Hdepth, Hbr⟩
    subst Heq
    rw [of_val_br_app_r]
    iapply IrisWp.wp_value (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) ⟨rfl⟩
    isplitr [Hf0 Hfv0]
    rotate_left; · iexists f0; iframe
    iright; ileft; inext
    rw [fixpoint_interp_br_eq]; dsimp only [interpCallHostBrDef]
    iexists j, vhAppend vh' [e], vs', p
    isplitr; · ipureintro; rfl
    isplitr; · ipureintro; rw [get_base_l_append]; exact Hbase
    isplitr; · ipureintro; rw [← append_lh_depth]; exact Hdepth
    iexact Hbr
  · ihave H := composition_return τs2 t3s v2 C i w f0 e hl lh $$ Hv2 Hret Hf0 Hfv0
    iapply wp_wand_ctx .NotStuck ⊤ _ _ _ 0 (.base [] []) $$ H
    iintro %v ⟨H, Hfr⟩
    iframe Hfr
    icases H with (H | H | H | H)
    · ileft; iexact H
    · iright; ileft; inext; iexact H
    · iright; iright; ileft; iexact H
    · iright; iright; iright; inext; iexact H
  · isimp only [fixpoint_interp_call_host_eq, interpCallHostBrDef] at Hch
    iapply ctx_empty
    icases Hch with ⟨%vh0, %v0, %tf0, %h0, %τs1', %τs2', >%Heqch, >%Htf, >%Hin', >%Hb', #Hval, #H⟩
    subst Heqch
    rw [ofVal_callHost_append]
    iapply IrisWp.wp_value (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) ⟨rfl⟩
    isplitr [Hf0 Hfv0]
    rotate_left; · iexists f0; iframe
    iright; iright; iright; inext
    rw [fixpoint_interp_call_host_eq]; dsimp only [interpCallHostBrDef]; simp only [fold_br, fold_ch]
    iexists llhAppend vh0 [e], v0, tf0, h0, τs1', τs2'
    isplitr; · ipureintro; rfl
    isplitr; · ipureintro; exact Htf
    isplitr; · ipureintro; exact Hin'
    isplitr; · ipureintro; exact llholed_basic_sh_append _ _ he Hb'
    isplitr; · iexact Hval
    imodintro
    iintro %v1 %f1 #Hv1 ⟨Hf1, Hfv1⟩
    rw [llfill_append_r]
    iapply IH $$ %vh0 %τs2' %v1 %f1 %Hb' Hv1 H Hf1 Hfv1

open IrisFundamentalComposition in
@[rocq_alias iriswasm.composition_call_host]
theorem composition_call_host (t2s t3s : List ValueType) (C : TContext) (i : Instance)
    (hl : List (Hostfuncidx × FunctionType)) (w : Val) (lh : Lholed) (f' : Frame)
    (e : AdministrativeInstruction) (he : isBasic e)
    (ht2 : ⊢ semanticTyping (GF := GF) C [e] (.tf t2s t3s)) :
    ⊢ interpInstance (GF := GF) C hl i -∗
      interpCtx C.label C.return_ hl C.local_ i lh -∗
      interpCallHost C.local_ i C.return_ hl w lh C.label t2s -∗
      ↪[frame] f' -∗
      interpFrame C.local_ i f' -∗
      WP (ofVal w ++ [e]) CTX 0 ; (Lholed.base [] [])
        {{ v, (interpVal t3s v ∨
               interpBr C.local_ i C.return_ hl v lh C.label ∨
               interpReturnOption C.return_ C.local_ i v ∨
               interpCallHost C.local_ i C.return_ hl v lh C.label t3s) ∗
              ∃ f0, ↪[frame] f0 ∗ interpFrame C.local_ i f0 }} := by
  rw [fixpoint_interp_call_host_eq]; dsimp only [interpCallHostBrDef]
  simp only [fold_br, fold_ch]
  iintro #Hi #Hc Hch Hf Hfv
  icases Hch with ⟨%vh, %v, %tf, %h, %τs1, %τs2, %Heqv, %Heqt, %Hin, %Hb, #Hw, #HK⟩
  subst Heqv
  rw [ofVal_callHost_append]
  iapply ctx_empty
  iapply IrisWp.wp_value (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) ⟨rfl⟩
  isplitr [Hf Hfv]
  rotate_left; · iexists f'; iframe
  iright; iright; iright
  rw [fixpoint_interp_call_host_eq]; dsimp only [interpCallHostBrDef]; simp only [fold_br, fold_ch]
  iexists llhAppend vh [e], v, tf, h, τs1, τs2
  isplitr; · ipureintro; rfl
  isplitr; · ipureintro; exact Heqt
  isplitr; · ipureintro; exact Hin
  isplitr; · ipureintro; exact llholed_basic_sh_append _ _ he Hb
  isplitr; · iexact Hw
  imodintro
  iintro %v2 %f #Hv2 ⟨Hf, Hfv⟩
  rw [llfill_append_r]
  iapply composition_call_host_loop t2s t3s C i hl lh e he ht2 $$ Hi Hc %vh %τs2 %v2 %f %Hb Hv2 HK
    Hf Hfv

@[rocq_alias iriswasm.typing_composition]
theorem typing_composition (C : TContext) (es : Expr) (t1s t2s t3s : List ValueType)
    (e : AdministrativeInstruction) (hbasic : isBasic e)
    (ht1 : ⊢ semanticTyping (GF := GF) C es (.tf t1s t2s))
    (ht2 : ⊢ semanticTyping (GF := GF) C [e] (.tf t2s t3s)) :
    ⊢ semanticTyping (GF := GF) C (es ++ [e]) (.tf t1s t3s) := by
  simp only [semanticTyping] at ht1 ht2 ⊢
  iintro %i %lh %hl #Hi #Hc %f %vs ⟨Hf, Hfv⟩ #Hv
  unfold interpExpression
  rw [← List.append_assoc]
  iapply ctx_empty_elim
  iapply wp_seq_can_trap_ctx .NotStuck ⊤ _
    (fun w => iprop(interpValues t2s w ∨ interpBr C.local_ i C.return_ hl w lh C.label ∨
      interpReturnOption C.return_ C.local_ i w ∨
      interpCallHost C.local_ i C.return_ hl w lh C.label t2s))
    (ofVal vs ++ es) [e] 0 (.base [] []) (interpFrame C.local_ i) f
  isplitr
  · iintro (H | H | H | H)
    · iexfalso; iapply values_trap_false $$ H
    · iexfalso; iapply br_trap_false $$ H
    · iexfalso; iapply ret_trap_false $$ H
    · iexfalso; iapply ch_trap_false $$ H
  isplitr
  · iintro %f0 ⟨Hf0, Hfv0⟩
    isplitr [Hf0 Hfv0]
    · ileft; iunfold interpVal; ileft; ipureintro; rfl
    · iexists f0; iframe
  isplitl [Hf]
  · iexact Hf
  isplitl [Hfv]
  · iintro Hf
    ihave H1 := ht1 $$ %i %lh %hl Hi Hc %f %vs [Hf Hfv] Hv
    · iframe
    iunfold interpExpression at H1
    iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ H1
    iintro %v ⟨H, Hfr⟩
    iframe Hfr
    iunfold interpVal at H
    icases H with ((H | H) | H | H | H)
    · ileft; iexact H
    · iright; ileft; iexact H
    · iright; iright; ileft; iexact H
    · iright; iright; iright; ileft; iexact H
    · iright; iright; iright; iright; iexact H
  iintro %w %f0 ⟨Hw, Hf0, Hfv0⟩
  icases Hw with (Hw | Hbr | Hret | Hch)
  · iapply ctx_empty
    ihave H := ht2 $$ %i %lh %hl Hi Hc %f0 %w [Hf0 Hfv0] [Hw]
    · iframe
    · iunfold interpVal; iright; iexact Hw
    iunfold interpExpression at H
    iexact H
  · iapply composition_br t1s t3s vs C i hl w lh f0 e $$ Hv Hbr Hf0 Hfv0
  · iapply composition_return t1s t3s vs C i w f0 e hl lh $$ Hv Hret Hf0 Hfv0
  · iapply composition_call_host t2s t3s C i hl w lh f0 e hbasic ht2 $$ Hi Hc Hch Hf0 Hfv0

end IrisWasm
