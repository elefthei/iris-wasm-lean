/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Logrel.IrisFundamentalHelpers
import IrisWasm.Logrel.IrisFundamentalComposition

/-! Port of `theories/iris/logrel/iris_fundamental_weakening.v`. -/

namespace IrisWasm

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm OFE

variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF] [LogrelNaInvs GF]

attribute [local instance] WasmG.invGS

open FundAux

@[rocq_alias iriswasm.get_base_l_push_const]
theorem get_base_l_push_const {i : Nat} (lh : ValidHoled i) (w : List Value) :
    getBaseL (vhPushConst lh w) = w ++ getBaseL lh ∨ getBaseL (vhPushConst lh w) = getBaseL lh := by
  cases lh with
  | base => exact .inl rfl
  | rec_ => exact .inr rfl

@[rocq_alias iriswasm.push_const_lh_depth]
theorem push_const_lh_depth {i : Nat} (lh : ValidHoled i) (w : List Value) :
    lhDepth (lhOfVh lh) = lhDepth (lhOfVh (vhPushConst lh w)) := by
  cases lh <;> rfl

@[rocq_alias iriswasm.simple_get_base_l_push_const]
theorem simple_get_base_l_push_const (lh : SimpleValidHoled) (w : List Value) :
    simpleGetBaseL (shPushConst lh w) = w ++ simpleGetBaseL lh ∨
      simpleGetBaseL (shPushConst lh w) = simpleGetBaseL lh := by
  cases lh with
  | base => exact .inl rfl
  | rec_ => exact .inr rfl

@[rocq_alias iriswasm.sh_push_const_lh_depth]
theorem sh_push_const_lh_depth (lh : SimpleValidHoled) (w : List Value) :
    lhDepth (lhOfSh lh) = lhDepth (lhOfSh (shPushConst lh w)) := by
  cases lh <;> rfl

@[rocq_alias iriswasm.weakening_br]
theorem weakening_br (C : TContext) (i : Instance) (hl : List (Hostfuncidx × FunctionType))
    (v : Val) (lh : Lholed) (ws1 : List Value) (ts : List ValueType) :
    ⊢ ([∗list] y1;y2 ∈ ws1;ts, interpValue (GF := GF) y2 y1) -∗
      interpBr C.local_ i C.return_ hl v lh C.label -∗
      interpBr C.local_ i C.return_ hl (valCombine (.immV ws1) v) lh C.label := by
  simp only [fixpoint_interp_br_eq, interpCallHostBrDef]
  iintro #Hv1 ⟨%j, %lh', %w', %p, %Heq, %Hbase, %Hsize, %τs', %vs, %k, %es, %lh0, %es', %lh'', %τs'',
    %H, %H0, %H1, %H2, #H3, H4⟩
  subst Heq Hbase Hsize
  simp only [valCombine]
  iexists j, vhPushConst lh' ws1, getBaseL (vhPushConst lh' ws1), lhDepth (lhOfVh lh')
  isplitr; · ipureintro; rfl
  isplitr; · ipureintro; rfl
  isplitr; · ipureintro; rw [← push_const_lh_depth]
  rcases get_base_l_push_const lh' ws1 with Hb' | Hb'
  · ihave %Hlen1 := BigSepL2.bigSepL2_length $$ Hv1
    iexists τs', vs, k, es, lh0, es', lh'', ts ++ τs''
    isplitr; · ipureintro; exact H
    isplitr; · ipureintro; exact H0
    isplit; · ipureintro; exact H1
    isplitr; · ipureintro; exact H2
    rw [Hb']
    isplitr
    · iunfold interpVal, interpValues at H3
      iunfold interpVal, interpValues
      icases H3 with (%Hc | ⟨%w0, %Heq', Hw⟩)
      · cases Hc
      cases Heq'
      iright
      iexists ws1 ++ getBaseL lh'
      isplitr; · ipureintro; rfl
      rw [List.append_assoc]
      iapply BigSepL2.bigSepL2_app_wand $$ Hv1 Hw
    rw [show (ws1 ++ getBaseL lh').drop (ts ++ τs'').length = (getBaseL lh').drop τs''.length by
      rw [List.length_append, ← Hlen1, List.drop_append]; simp]
    iexact H4
  · iexists τs', vs, k, es, lh0, es', lh'', τs''
    isplitr; · ipureintro; exact H
    isplitr; · ipureintro; exact H0
    isplit; · ipureintro; exact H1
    isplitr; · ipureintro; exact H2
    rw [Hb']
    isplitr
    · iexact H3
    iexact H4

omit [LogrelNaInvs GF] in
@[rocq_alias iriswasm.weakening_return]
theorem weakening_return (ws1 : List Value) (ts : List ValueType) (C : TContext) (i : Instance)
    (v : Val) :
    ⊢ ([∗list] y1;y2 ∈ ws1;ts, interpValue (GF := GF) y2 y1) -∗
      interpReturnOption C.return_ C.local_ i v -∗
      interpReturnOption C.return_ C.local_ i (valCombine (.immV ws1) v) := by
  iintro #Hv1 Hret
  iunfold interpReturnOption at Hret
  iunfold interpReturnOption
  icases Hret with ⟨%sh, %ws', %Heq, %Hbase, Hret⟩
  subst Heq Hbase
  simp only [valCombine]
  iexists shPushConst sh ws1, simpleGetBaseL (shPushConst sh ws1)
  isplitr; · ipureintro; rfl
  isplitr; · ipureintro; rfl
  rcases hret : C.return_ with _ | τr
  · iexact Hret
  icases Hret with ⟨%τs'', #Hws', Hret⟩
  ihave Hw2 := Hws'
  iunfold interpVal, interpValues at Hw2
  icases Hw2 with (%Hc | ⟨%ws, %Heq, Hws⟩)
  · cases Hc
  cases Heq
  ihave %Hlen := BigSepL2.bigSepL2_length $$ Hws
  obtain ⟨lh'', Hlh''⟩ := lfilled_simple_get_base_pull _ sh [.basic .return_] _
    ((simpleGetBaseL sh).take τs''.length) ((simpleGetBaseL sh).drop τs''.length)
    (by rw [List.take_append_drop]) (sfill_to_lfilled _ _)
  rcases simple_get_base_l_push_const sh ws1 with Hb' | Hb'
  · ihave %Hlen1 := BigSepL2.bigSepL2_length $$ Hv1
    iexists ts ++ τs''
    isplitr
    · rw [Hb']
      iunfold interpVal, interpValues
      iright
      iexists ws1 ++ simpleGetBaseL sh
      isplitr; · ipureintro; rfl
      rw [List.append_assoc]
      iapply BigSepL2.bigSepL2_app_wand $$ Hv1 Hws
    obtain ⟨lh', Hlh'⟩ := lfilled_simple_get_base_pull _ (shPushConst sh ws1) [.basic .return_] _
      (ws1 ++ (simpleGetBaseL sh).take τs''.length) ((simpleGetBaseL sh).drop τs''.length)
      (by rw [Hb', List.append_assoc, List.take_append_drop]) (sfill_to_lfilled _ _)
    iintro %f0 %f1 Hf
    ispecialize Hret $$ %f0 %f1 Hf
    isimp only [ofVal] at Hret
    isimp only [ofVal]
    iapply wp_ret_shift (const_list_of_val _) (by simp [of_val_length]; simp at Hlen; omega)
      Hlh'' Hlh'
    iexact Hret
  · iexists τs''
    isplitr
    · rw [Hb']; iexact Hws'
    obtain ⟨lh', Hlh'⟩ := lfilled_simple_get_base_pull _ (shPushConst sh ws1) [.basic .return_] _
      ((simpleGetBaseL sh).take τs''.length) ((simpleGetBaseL sh).drop τs''.length)
      (by rw [Hb', List.take_append_drop]) (sfill_to_lfilled _ _)
    iintro %f0 %f1 Hf
    ispecialize Hret $$ %f0 %f1 Hf
    isimp only [ofVal] at Hret
    isimp only [ofVal]
    iapply wp_ret_shift (const_list_of_val _) (by simp [of_val_length]; simp at Hlen; omega)
      Hlh'' Hlh'
    iexact Hret

@[rocq_alias iriswasm.llfill_push_const]
theorem llfill_push_const (vh : Llholed) (ws1 : List Value) (e : List AdministrativeInstruction) :
    llfill (llhPushConst vh ws1) e = llfill (.base ws1 []) (llfill vh e) := by
  cases vh <;> simp [llfill, llhPushConst, ← v_to_e_cat]

@[rocq_alias iriswasm.llholed_basic_push_const]
theorem llholed_basic_push_const (vh : Llholed) (ws1 : List Value) :
    llholedBasic vh → llholedBasic (llhPushConst vh ws1) := by
  cases vh <;> exact id

@[rocq_alias iriswasm.weakening_call_host]
theorem weakening_call_host (ws1 : List Value) (ts : List ValueType) (C : TContext) (i : Instance)
    (v : Val) (hl : List (Hostfuncidx × FunctionType)) (lh : Lholed) (t2s : List ValueType) :
    ⊢ ([∗list] y1;y2 ∈ ws1;ts, interpValue (GF := GF) y2 y1) -∗
      interpCallHost C.local_ i C.return_ hl v lh C.label t2s -∗
      interpCallHost C.local_ i C.return_ hl (valCombine (.immV ws1) v) lh C.label (ts ++ t2s) := by
  iintro #Hv1
  iloeb as IH generalizing %v
  iintro Hch
  isimp only [fixpoint_interp_call_host_eq, interpCallHostBrDef] at Hch
  isimp only [fold_br, fold_ch] at Hch
  icases Hch with ⟨%vh, %v0, %tf, %h, %τs1, %τs2, %Heqv, %Heqt, %Hin, %Hb, #Hw, #HK⟩
  subst Heqv
  rw [show valCombine (.immV ws1) (.callHostV tf h v0 vh) = .callHostV tf h v0 (llhPushConst vh ws1)
    from rfl]
  rw [fixpoint_interp_call_host_eq]; dsimp only [interpCallHostBrDef]; simp only [fold_br, fold_ch]
  iexists llhPushConst vh ws1, v0, tf, h, τs1, τs2
  isplitr; · ipureintro; rfl
  isplitr; · ipureintro; exact Heqt
  isplitr; · ipureintro; exact Hin
  isplitr; · ipureintro; exact llholed_basic_push_const _ _ Hb
  isplitr; · iexact Hw
  imodintro
  iintro %v2 %f #Hv2 ⟨Hf, Hfv⟩
  rw [llfill_push_const]
  simp only [llfill, List.append_nil]
  ihave H : WP (vToEList ws1 ++ llfill vh (ofVal v2))
      {{ v, (⌜v = .trapV⌝ ∨ (interpValues (ts ++ t2s) v ∨
          ▷ interpBr C.local_ i C.return_ hl v lh C.label ∨
          interpReturnOption C.return_ C.local_ i v ∨
          ▷ interpCallHost C.local_ i C.return_ hl v lh C.label (ts ++ t2s))) ∗
        ∃ f, ↪[frame] f ∗ interpFrame C.local_ i f }} $$ [Hf Hfv]
  · iapply wp_val_can_trap_app .NotStuck ⊤ (fun v => iprop(interpValues (ts ++ t2s) v ∨
          ▷ interpBr C.local_ i C.return_ hl v lh C.label ∨
          interpReturnOption C.return_ C.local_ i v ∨
          ▷ interpCallHost C.local_ i C.return_ hl v lh C.label (ts ++ t2s)))
      (vToEList ws1) ws1 _ f (interpFrame C.local_ i) (to_of_val (.immV ws1))
    isplitr
    · imodintro
      iintro (H | H | H | H)
      · iexfalso; iapply values_trap_false $$ H
      · ihave H := later_mono br_trap_false $$ H
        icases H with >%H; exact H.elim
      · iexfalso; iapply ret_trap_false $$ H
      · ihave H := later_mono ch_trap_false $$ H
        icases H with >%H; exact H.elim
    isplitl [Hf]
    · iexact Hf
    iintro Hf
    ihave H := HK $$ %v2 %f Hv2 [Hf Hfv]
    · iframe
    iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ H
    iintro %v1 ⟨H, Hfr⟩
    iframe Hfr
    iunfold interpVal at H
    icases H with ((H | H) | H | H | H)
    · ileft; iexact H
    · iright; ileft
      iunfold interpValues at H
      iunfold interpValues
      icases H with ⟨%ws', %Heq', Hw'⟩
      subst Heq'
      iexists ws1 ++ ws'
      isplitr; · ipureintro; rfl
      iapply BigSepL2.bigSepL2_app_wand $$ Hv1 Hw'
    · iright; iright; ileft
      inext
      iapply weakening_br $$ Hv1 H
    · iright; iright; iright; ileft
      iapply weakening_return $$ Hv1 H
    · iright; iright; iright; iright
      inext
      iapply IH $$ H
  iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ H
  iintro %v1 ⟨H, Hfr⟩
  iframe Hfr
  icases H with (H | H | H | H | H)
  · ileft; iunfold interpVal; ileft; iexact H
  · ileft; iunfold interpVal; iright; iexact H
  · iright; ileft; iexact H
  · iright; iright; ileft; iexact H
  · iright; iright; iright; iexact H

@[rocq_alias iriswasm.typing_weakening]
theorem typing_weakening (C : TContext) (es : Expr) (t1s t2s ts : List ValueType)
    (hIH : ⊢ semanticTyping (GF := GF) C es (.tf t1s t2s)) :
    ⊢ semanticTyping (GF := GF) C es (.tf (ts ++ t1s) (ts ++ t2s)) := by
  simp only [semanticTyping] at hIH ⊢
  iintro %i %lh %hl #Hi #Hc %f %vs ⟨Hf, Hfv⟩ #Hv
  unfold interpExpression
  iunfold interpVal, interpValues at Hv
  icases Hv with (%Hv | ⟨%ws, %Heq, #Hv⟩)
  · subst Hv
    ihave H := wp_trap .NotStuck ⊤ (fun v => iprop(⌜v = .trapV⌝)) [] es f rfl $$ [] Hf
    · ipureintro; rfl
    rw [show ofVal .trapV ++ es = [] ++ [.trap] ++ es from rfl]
    iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ H
    iintro %v ⟨%Hv, Hf⟩
    subst Hv
    isplitl []
    · ileft; iunfold interpVal; ileft; ipureintro; rfl
    iexists f; iframe
  subst Heq
  ihave ⟨%ws1, %ws2, %Heq, #Hv1, #Hv2⟩ := BigSepL2.bigSepL2_app_inv_right $$ Hv
  subst Heq
  rw [show ofVal (.immV (ws1 ++ ws2)) ++ es = vToEList ws1 ++ (ofVal (.immV ws2) ++ es) by
    simp [ofVal, vToEList]]
  ihave H : WP (vToEList ws1 ++ (ofVal (.immV ws2) ++ es))
      {{ v, (⌜v = .trapV⌝ ∨ (interpValues (ts ++ t2s) v ∨
          interpBr C.local_ i C.return_ hl v lh C.label ∨
          interpReturnOption C.return_ C.local_ i v ∨
          interpCallHost C.local_ i C.return_ hl v lh C.label (ts ++ t2s))) ∗
        ∃ f, ↪[frame] f ∗ interpFrame C.local_ i f }} $$ [Hf Hfv]
  · iapply wp_val_can_trap_app .NotStuck ⊤ (fun v => iprop(interpValues (ts ++ t2s) v ∨
          interpBr C.local_ i C.return_ hl v lh C.label ∨
          interpReturnOption C.return_ C.local_ i v ∨
          interpCallHost C.local_ i C.return_ hl v lh C.label (ts ++ t2s)))
      (vToEList ws1) ws1 _ f (interpFrame C.local_ i) (to_of_val (.immV ws1))
    isplitr
    · imodintro
      iintro (H | H | H | H)
      · iexfalso; iapply values_trap_false $$ H
      · iexfalso; iapply br_trap_false $$ H
      · iexfalso; iapply ret_trap_false $$ H
      · iexfalso; iapply ch_trap_false $$ H
    isplitl [Hf]
    · iexact Hf
    iintro Hf
    ihave H := hIH $$ %i %lh %hl Hi Hc %f %(.immV ws2) [Hf Hfv] []
    · iframe
    · iunfold interpVal; iright; iunfold interpValues
      iexists ws2
      isplitr; · ipureintro; rfl
      iexact Hv2
    iunfold interpExpression at H
    iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ H
    iintro %v1 ⟨H, Hfr⟩
    iframe Hfr
    iunfold interpVal at H
    icases H with ((H | H) | H | H | H)
    · ileft; iexact H
    · iright; ileft
      iunfold interpValues at H
      iunfold interpValues
      icases H with ⟨%ws', %Heq', Hw'⟩
      subst Heq'
      iexists ws1 ++ ws'
      isplitr; · ipureintro; rfl
      iapply BigSepL2.bigSepL2_app_wand $$ Hv1 Hw'
    · iright; iright; ileft
      iapply weakening_br $$ Hv1 H
    · iright; iright; iright; ileft
      iapply weakening_return $$ Hv1 H
    · iright; iright; iright; iright
      iapply weakening_call_host $$ Hv1 H
  iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ H
  iintro %v1 ⟨H, Hfr⟩
  iframe Hfr
  icases H with (H | H | H | H | H)
  · ileft; iunfold interpVal; ileft; iexact H
  · ileft; iunfold interpVal; iright; iexact H
  · iright; ileft; iexact H
  · iright; iright; ileft; iexact H
  · iright; iright; iright; iexact H

end IrisWasm
