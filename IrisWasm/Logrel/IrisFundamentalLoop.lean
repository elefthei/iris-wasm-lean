/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Logrel.IrisFundamentalHelpers
import IrisWasm.Logrel.IrisFundamentalBr

/-! Port of `theories/iris/logrel/iris_fundamental_loop.v`.

`interp_br_step` and `interp_call_host_label` are also defined (without the loop hypothesis) in
`iris_fundamental_helpers.v`; the loop versions live in namespace `IrisWasm.IrisFundamentalLoop`. -/

namespace IrisWasm

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm

variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF] [LogrelNaInvs GF]
variable {bt : Wasm.BlockType}

attribute [local instance] WasmG.invGS

theorem interp_ctx_continuations_push_label_loop (lh : Lholed) (C : TContext) (i : Instance)
    (tm tn : List ValueType) (es : List BasicInstruction) (tr : Option (List ValueType))
    (hl : List (Hostfuncidx × FunctionType))
    (hbase : BaseIsEmpty lh) (_hlen : lengthLholeds C.label.reverse lh) :
    ⊢ iprop(□ (∀ (a : Frame) (a0 : List Value), ⌜a0.length = tn.length⌝ →
        ↪[frame] a -∗ interpFrame C.local_ i a -∗
        □ ([∗list] w;τ ∈ a0;tn, interpValue τ w) -∗
        WP (ofVal (.immV a0) ++ toEList [.loop bt es])
          {{ vs, (interpVal tm vs ∨ interpBr C.local_ i tr hl vs lh C.label ∨
                  interpReturnOption tr C.local_ i vs ∨
                  interpCallHost C.local_ i tr hl vs lh C.label tm) ∗
                 ∃ f0, ↪[frame] f0 ∗ interpFrame C.local_ i f0 }}) -∗
      interpCtxContinuations (GF := GF) C.label tr hl C.local_ i lh -∗
      interpCtxContinuation (updLabel C ([tn] ++ C.label)).label tr hl
        (pushBase lh tn.length [.basic (.loop bt es)] [] []) 0 tn C.local_ i) := by
  iintro #HIH #_
  unfold interpCtxContinuation
  rw [lh_depth_push_base, show lhDepth lh + 1 - (0 + 1) = lhDepth lh by omega,
    get_layer_push_base_0 lh _ _ _ _ hbase]
  have hmin := lh_minus_push_base_Some lh tn.length [.basic (.loop bt es)] [] [] hbase
  iexists [], tn.length, [.basic (.loop bt es)], .base [] [], [], lh
  isplit; · ipureintro; rfl
  isplit; · ipureintro; omega
  isplit; · ipureintro; simp [hmin]
  imodintro
  iintro %v %f #Hw ⟨Hf, Hfv⟩
  simp only [List.nil_append, List.append_nil, updLabel, List.singleton_append, Nat.zero_add,
    List.drop_succ_cons, List.drop_zero]
  iunfold interpVal at Hw
  icases Hw with (%Heq | Hw)
  · subst Heq
    iexists []
    iapply interp_expression_trap $$ Hf Hfv
  iunfold interpValues at Hw
  icases Hw with ⟨%ws, %Heq, #Hv⟩
  subst Heq
  iexists tm
  ihave %Hlen := BigSepL2.bigSepL2_length $$ Hv
  unfold interpExpression
  rw [show ([AdministrativeInstruction.basic (.loop bt es)] : List _) =
    toEList [.loop bt es] from rfl]
  iapply HIH $$ %f %ws %Hlen Hf Hfv Hv

theorem interp_ctx_push_label_loop (C : TContext) (tm : List ValueType) (i : Instance)
    (lh : Lholed) (tn : List ValueType) (es : List BasicInstruction)
    (tr : Option (List ValueType)) (hl : List (Hostfuncidx × FunctionType)) :
    ⊢ iprop(□ (∀ (a : Frame) (a0 : List Value), ⌜a0.length = tn.length⌝ →
        ↪[frame] a -∗ interpFrame C.local_ i a -∗
        □ ([∗list] w;τ ∈ a0;tn, interpValue τ w) -∗
        WP (ofVal (.immV a0) ++ toEList [.loop bt es])
          {{ vs, (interpVal tm vs ∨ interpBr C.local_ i tr hl vs lh C.label ∨
                  interpReturnOption tr C.local_ i vs ∨
                  interpCallHost C.local_ i tr hl vs lh C.label tm) ∗
                 ∃ f0, ↪[frame] f0 ∗ interpFrame C.local_ i f0 }}) -∗
      interpCtx (GF := GF) C.label tr hl C.local_ i lh -∗
      interpCtx (updLabel C ([tn] ++ C.label)).label tr hl (updLabel C ([tn] ++ C.label)).local_ i
        (pushBase lh tn.length [.basic (.loop bt es)] [] [])) := by
  unfold interpCtx
  iintro #HIH ⟨%Hlh_base, %Hlh_len, %Hlh_valid, #Hc⟩
  isplitr; · ipureintro; exact base_is_empty_push_base _ _ _
  isplitr
  · ipureintro
    simpa [updLabel] using length_lholeds_push_base lh _ tn _ Hlh_len
  isplitr; · ipureintro; exact lholed_valid_push_base _ _ _ Hlh_valid
  ihave Hc0 := interp_ctx_continuations_push_label_loop (bt := bt) lh C i tm tn es tr hl
    Hlh_base Hlh_len $$ HIH Hc
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
  iexists vs, j, es0, pushBase lh' tn.length [.basic (.loop bt es)] [] [], es', lh''
  rw [lh_depth_push_base, show lhDepth lh + 1 - (k + 1 + 1) = lhDepth lh - (k + 1) by omega]
  isplit; · ipureintro; exact get_layer_push_base _ _ _ _ _ _ _ _ _ _ _ Hlayer
  isplit; · ipureintro; exact Hdep
  isplit; · ipureintro; exact push_base_lh_minus_is_Some _ _ _ _ _ _ Hmin
  simp only [List.drop_succ_cons]
  iexact Hcont

private theorem loop_fold_br {τl i τto hl v lh τc} :
    (interpCallHostBr (GF := GF) τl i τto hl).2 v lh τc = interpBr τl i τto hl v lh τc := rfl

private theorem loop_fold_ch {τl i τto hl v lh τc t} :
    (interpCallHostBr (GF := GF) τl i τto hl).1 v lh τc t = interpCallHost τl i τto hl v lh τc t :=
  rfl

omit [LogrelNaInvs GF] in
private instance loopIsExcept0WpWasm {s : Stuckness} {E : CoPset} {e : Expr} {Φ : Val → IProp GF} :
    Iris.ProofMode.IsExcept0 (WP e @ s ; E {{ Φ }} : IProp GF) :=
  IrisWp.isExcept0Wp (P := fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)

namespace IrisFundamentalLoop

theorem interp_br_step (C : TContext) (j : Nat) (vh : ValidHoled j) (m : Nat) (vs : List Value)
    (tn : List ValueType) (p : Nat) (i : Instance) (es : List BasicInstruction)
    (tm : List ValueType) (lh : Lholed) (f' : Frame) (tr : Option (List ValueType))
    (hl : List (Hostfuncidx × FunctionType))
    (hlen : m = tn.length) (hbase : getBaseL vh = vs) (hsize : lhDepth (lhOfVh vh) = p)
    (e : j = p) :
    ⊢ iprop(□ (∀ (a : Frame) (a0 : List Value), ⌜a0.length = tn.length⌝ →
        ↪[frame] a -∗ interpFrame C.local_ i a -∗
        □ ([∗list] w;τ ∈ a0;tn, interpValue τ w) -∗
        WP (vToEList a0 ++ toEList [.loop bt es])
          {{ vs0, (interpVal tm vs0 ∨ interpBr C.local_ i tr hl vs0 lh C.label ∨
                   interpReturnOption tr C.local_ i vs0 ∨
                   interpCallHost C.local_ i tr hl vs0 lh C.label tm) ∗
                  ∃ f0, ↪[frame] f0 ∗ interpFrame C.local_ i f0 }}) -∗
      ▷ interpBrBody (GF := GF) (updLabel C ([tn] ++ C.label)).label
          (pushBase lh tn.length [.basic (.loop bt es)] [] []) j p vs C.local_ i tr hl -∗
      ↪[frame] f' -∗
      interpFrame C.local_ i f' -∗
      WP ([.label m [.basic (.loop bt es)] (vfill vh [.basic (.br j)])] : Expr)
        {{ v, (interpVal tm v ∨ interpBr C.local_ i tr hl v lh C.label ∨
               interpReturnOption tr C.local_ i v ∨
               interpCallHost C.local_ i tr hl v lh C.label tm) ∗
              ∃ f0, ↪[frame] f0 ∗ interpFrame C.local_ i f0 }}) := by
  subst e
  iintro #IH Hbr Hf Hfv
  rcases hpb : pullBaseLDropLen vh (vs.length - tn.length) with ⟨vh', l⟩
  rw [vfill_pull_base_l_take_len vh _ _ vh' l hpb]
  have hdepth := lh_depth_pull_base_l_take_len vh _ vh' l hpb
  have hfill := (vfill_to_lfilled vh' (l.map (fun x => AdministrativeInstruction.basic (.const x)) ++
    [.basic (.br (lhDepth (lhOfVh vh)))])).2
  rw [← hdepth, hsize] at hfill
  unfold interpBrBody
  rw [Nat.sub_self]
  icases Hbr with ⟨%τs', %vs0, %k, %es0, %lh', %es', %lh'', %τs'', >%Hlook, >%Hlayer, >%Hdep, >%Hmin, >#Hvalvs, Hbr⟩
  simp only [updLabel, List.singleton_append, List.getElem?_cons_zero, Option.some.injEq] at Hlook
  subst Hlook
  iunfold interpVal at Hvalvs
  icases Hvalvs with (%Hc | Hvalvs)
  · cases Hc
  iunfold interpValues at Hvalvs
  icases Hvalvs with ⟨%ws', %Heq', #Hvalvs⟩
  cases Heq'
  ihave %Hlen2 := BigSepL2.bigSepL2_length $$ Hvalvs
  simp only [List.length_append] at Hlen2
  have hlenl := length_pull_base_l_take_len vh _ vh' l vs hbase hpb
  have happ := take_drop_pull_base_l_take_len vh _ vh' l vs (by omega) hbase hpb
  iapply wp_br (vs := vToEList l) (es := [.basic (.loop bt es)]) (v_to_e_is_const_list l)
    (by simp [vToEList]; omega) hfill $$ Hf
  inext
  iintro Hf
  ihave #Hv2 : iprop(□ [∗list] w;τ ∈ vs.take (vs.length - tn.length) ++ l;τs'' ++ tn,
      interpValue τ w) $$ []
  · rw [← happ]; iexact Hvalvs
  ihave ⟨-, #Hv3⟩ := (BigSepL2.bigSepL2_append (Or.inr (by omega))).1 $$ Hv2
  rw [show ([AdministrativeInstruction.basic (.loop bt es)] : List _) =
    toEList [.loop bt es] from rfl]
  iapply IH $$ %f' %l %(by omega) Hf Hfv Hv3

theorem interp_call_host_label (C : TContext) (i : Instance) (w : Val) (f' : Frame)
    (tn tm : List ValueType) (es : List BasicInstruction) (lh : Lholed)
    (hl : List (Hostfuncidx × FunctionType)) :
    ⊢ iprop(□ (∀ (a : Frame) (a0 : List Value), ⌜a0.length = tn.length⌝ →
        ↪[frame] a -∗ interpFrame C.local_ i a -∗
        □ ([∗list] w;τ ∈ a0;tn, interpValue τ w) -∗
        WP (vToEList a0 ++ toEList [.loop bt es])
          {{ vs0, (interpVal tm vs0 ∨ interpBr C.local_ i C.return_ hl vs0 lh C.label ∨
                   interpReturnOption C.return_ C.local_ i vs0 ∨
                   interpCallHost C.local_ i C.return_ hl vs0 lh C.label tm) ∗
                  ∃ f0, ↪[frame] f0 ∗ interpFrame C.local_ i f0 }}) -∗
      interpCtx (GF := GF) C.label C.return_ hl C.local_ i lh -∗
      interpCallHost C.local_ i C.return_ hl w
        (pushBase lh tn.length [.basic (.loop bt es)] [] [])
        (updLabel C ([tn] ++ C.label)).label tm -∗
      ↪[frame] f' -∗
      interpFrame C.local_ i f' -∗
      WP (ofVal w) CTX 1 ; (Lholed.rec_ [] tn.length [.basic (.loop bt es)] (.base [] []) [])
        {{ v, (interpVal tm v ∨ interpBr C.local_ i C.return_ hl v lh C.label ∨
               interpReturnOption C.return_ C.local_ i v ∨
               interpCallHost C.local_ i C.return_ hl v lh C.label tm) ∗
              ∃ f0, ↪[frame] f0 ∗ interpFrame C.local_ i f0 }}) := by
  iintro #HIH #Hc Hch Hf Hfv
  rw [fixpoint_interp_call_host_eq]; dsimp only [interpCallHostBrDef]
  simp only [loop_fold_br, loop_fold_ch]
  icases Hch with ⟨%vh, %v, %tf, %h, %τs1, %τs2, %Heqw, %Htf, %Hin, %Hb, #Hv, #Hch⟩
  subst Heqw Htf
  rw [show Lholed.rec_ [] tn.length [.basic (.loop bt es)] (.base [] []) [] =
    pushBase (.base [] []) tn.length [.basic (.loop bt es)] [] [] from rfl]
  iapply wp_label_push_nil_inv
  icases wp_wasm_empty_ctx (GF := GF) .NotStuck ⊤ _ _ with ⟨HE, -⟩
  iapply HE
  iapply IrisWp.wp_value (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
    (e := [.label tn.length [.basic (.loop bt es)] (ofVal (.callHostV (.tf τs1 τs2) h v vh))])
    (v := .callHostV (.tf τs1 τs2) h v (.label [] tn.length [.basic (.loop bt es)] vh []))
    ⟨rfl⟩
  isplitr [Hf Hfv]
  rotate_left
  · iexists f'; iframe
  iright; iright; iright
  iclear HE
  irevert Hch Hv %Hb %Hin
  iloeb as IH generalizing %h %v %vh %τs1 %τs2
  iintro #Hch #Hv %Hb %Hin
  rw [fixpoint_interp_call_host_eq]; dsimp only [interpCallHostBrDef]
  simp only [loop_fold_br, loop_fold_ch]
  iexists .label [] tn.length [.basic (.loop bt es)] vh [], v, .tf τs1 τs2, h, τs1, τs2
  isplitr; · ipureintro; rfl
  isplitr; · ipureintro; rfl
  isplitr; · ipureintro; exact Hin
  isplitr; · ipureintro; exact ⟨trivial, Hb⟩
  isplitr; · iexact Hv
  imodintro
  iintro %v2 %f #Hw ⟨Hf, Hfv⟩
  rw [show llfill (.label [] tn.length [.basic (.loop bt es)] vh []) (ofVal v2) =
    [.label tn.length [.basic (.loop bt es)] (llfill vh (ofVal v2))] from rfl]
  icases wp_wasm_empty_ctx (GF := GF) .NotStuck ⊤ _ _ with ⟨-, HE⟩
  iapply HE
  iclear HE
  iapply wp_label_push_nil
  iapply wp_ctx_bind _ _ _ _ _ (pushBase (.base [] []) tn.length [.basic (.loop bt es)] [] [])
    (base_is_empty_push_base _ _ _)
  ihave Hch' := Hch $$ %v2 %f Hw [Hf Hfv]
  · iframe
  iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ Hch'
  iintro %v' ⟨Hv', %f0, Hf0, Hfv0⟩
  icases Hv' with (Hv' | Hv' | Hv' | Hv')
  · iapply wp_label_push_nil_inv
    icases wp_wasm_empty_ctx (GF := GF) .NotStuck ⊤ _ _ with ⟨HE, -⟩
    iapply HE
    iclear HE
    iunfold interpVal at Hv'
    icases Hv' with (%Heq | Hv')
    · subst Heq
      iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ [Hf0]
      · iapply wp_label_trap (Φ := fun v => iprop(⌜v = .trapV⌝)) (to_of_val _) $$ Hf0
        inext; ipureintro; rfl
      iintro %v0 ⟨%Heq, Hf0⟩
      subst Heq
      isplitr [Hf0 Hfv0]
      · ileft; iunfold interpVal; ileft; ipureintro; rfl
      · iexists f0; iframe
    · iunfold interpValues at Hv'
      icases Hv' with ⟨%ws, %Heq, #Hws⟩
      subst Heq
      iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ [Hf0]
      · iapply wp_label_value (Φ := fun v => iprop(⌜v = .immV ws⌝)) (to_of_val _) $$ Hf0
        inext; ipureintro; rfl
      iintro %v0 ⟨%Heq, Hf0⟩
      subst Heq
      isplitr [Hf0 Hfv0]
      · ileft; iunfold interpVal; iright; iunfold interpValues; iexists ws
        isplitr; · ipureintro; rfl
        iexact Hws
      · iexists f0; iframe
  · isimp only [fixpoint_interp_br_eq, interpCallHostBrDef] at Hv'
    iapply wp_label_push_nil_inv
    icases wp_wasm_empty_ctx (GF := GF) .NotStuck ⊤ _ _ with ⟨HE, -⟩
    iapply HE
    iclear HE
    icases Hv' with ⟨%j, %vh', %vs, %p, >%Heqbr, >%Hbase, >%Hsize, Hbr⟩
    subst Heqbr
    rw [show ofVal (.brV vh') = vfill vh' [.basic (.br j)] from rfl]
    by_cases hjp : j = p
    · iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ [Hbr Hf0 Hfv0]
      · iapply interp_br_step (bt := bt) C j vh' tn.length vs tn p i es tm lh f0 C.return_ hl
          rfl Hbase Hsize hjp
          $$ HIH [Hbr] Hf0 Hfv0
        unfold interpBrBody
        isimp only [loop_fold_br, loop_fold_ch] at Hbr
        iexact Hbr
      iintro %v0 ⟨H, Hfr⟩
      iframe Hfr
      icases H with (H | H | H | H)
      · ileft; iexact H
      · iright; ileft; inext; iexact H
      · iright; iright; ileft; iexact H
      · iright; iright; iright; inext; iexact H
    · ihave #Hcx := Hc
      iunfold interpCtx at Hcx
      icases Hcx with ⟨%Hlh_base, %Hlh_len, %Hlh_valid, -⟩
      iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ [Hbr Hf0 Hfv0]
      · iapply interp_br_stuck_push_later C j vh' tn.length vs p i tn tm lh f0
          [.basic (.loop bt es)] C.return_ hl rfl Hbase Hsize hjp Hlh_len Hlh_valid Hlh_base
          $$ [Hbr] Hf0 Hfv0
        unfold interpBrBody
        isimp only [loop_fold_br, loop_fold_ch] at Hbr
        iexact Hbr
      iintro %v0 ⟨H, Hfr⟩
      iframe Hfr
      icases H with (H | H | H | H)
      · ileft; iexact H
      · iright; ileft; iexact H
      · iright; iright; ileft; iexact H
      · iright; iright; iright; inext; iexact H
  · have hr := interp_return_label (GF := GF) C tn i v' f0 tm lh [.basic (.loop bt es)]
      tn.length hl
    rw [show (updLabel C ([tn] ++ C.label)).return_ = C.return_ from rfl,
      show (updLabel C ([tn] ++ C.label)).local_ = C.local_ from rfl] at hr
    ihave H := hr $$ Hv' Hf0 Hfv0
    rw [Nat.zero_add, show pushBase (.base [] []) tn.length [.basic (.loop bt es)] [] [] =
      .rec_ [] tn.length [.basic (.loop bt es)] (.base [] []) [] from rfl]
    iapply wp_wand_ctx $$ H
    iintro %v0 ⟨H, Hfr⟩
    iframe Hfr
    icases H with (H | H | H | H)
    · ileft; iexact H
    · iright; ileft; inext; iexact H
    · iright; iright; ileft; iexact H
    · iright; iright; iright; inext; iexact H
  · isimp only [fixpoint_interp_call_host_eq, interpCallHostBrDef] at Hv'
    iapply wp_label_push_nil_inv
    icases wp_wasm_empty_ctx (GF := GF) .NotStuck ⊤ _ _ with ⟨HE, -⟩
    iapply HE
    iclear HE
    icases Hv' with ⟨%vh0, %v0, %tf0, %h0, %τs1', %τs2', >%Heq, >%Htf0, >%Hin', >%Hb', #Hv0, #Hch0⟩
    subst Heq Htf0
    iapply IrisWp.wp_value (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
      (e := [.label tn.length [.basic (.loop bt es)]
        (ofVal (.callHostV (.tf τs1' τs2') h0 v0 vh0))])
      (v := .callHostV (.tf τs1' τs2') h0 v0 (.label [] tn.length [.basic (.loop bt es)] vh0 []))
      ⟨rfl⟩
    isplitr [Hf0 Hfv0]
    rotate_left
    · iexists f0; iframe
    iright; iright; iright
    inext
    isimp only [loop_fold_br, loop_fold_ch] at Hch0
    iapply IH $$ Hch0 Hv0 %Hb' %Hin'

end IrisFundamentalLoop

theorem typing_loop (C : TContext) (es : List BasicInstruction) (tn tm : List ValueType)
    (hsig : expandBlockType C.typesT bt = some (.tf tn tm))
    (h : ⊢ semanticTyping (GF := GF) (updLabel C ([tn] ++ C.label)) (toEList es) (.tf tn tm)) :
    ⊢ semanticTyping (GF := GF) C (toEList [.loop bt es]) (.tf tn tm) := by
  unfold semanticTyping
  iintro %i %lh %hl #Hi #Hc %f %vs ⟨Hf, Hfv⟩ #Hv
  unfold interpVal interpValues
  icases Hv with (%Heq | ⟨%ws, %Heq, #Hv⟩)
  · subst Heq
    iapply interp_expression_trap $$ Hf Hfv
  subst Heq
  ihave %Hlen := BigSepL2.bigSepL2_length $$ Hv
  unfold interpExpression
  irevert %Hlen Hf Hfv Hv
  iloeb as IH generalizing %f %ws
  iintro %Hlen Hf Hfv #Hv
  ihave ⟨%Htypes, Hfv⟩ := interp_frame_types $$ Hi Hfv
  rw [show toEList [.loop bt es] = [.basic (.loop bt es)] from rfl]
  iapply wp_loop (bt := bt) (f := f) (vs := ofVal (.immV ws)) (es := es) (n := tn.length)
    (m := tm.length) (t1s := tn) (t2s := tm) (const_list_of_val ws)
    ((of_val_length ws).trans Hlen) rfl rfl (Htypes.symm ▸ hsig) $$ Hf
  inext
  ihave #HIH : iprop(□ (∀ (a : Frame) (a0 : List Value), ⌜a0.length = tn.length⌝ →
        ↪[frame] a -∗ interpFrame C.local_ i a -∗
        □ ([∗list] w;τ ∈ a0;tn, interpValue τ w) -∗
        WP (ofVal (.immV a0) ++ toEList [.loop bt es])
          {{ vs, (interpVal tm vs ∨ interpBr C.local_ i C.return_ hl vs lh C.label ∨
                  interpReturnOption C.return_ C.local_ i vs ∨
                  interpCallHost C.local_ i C.return_ hl vs lh C.label tm) ∗
                 ∃ f0, ↪[frame] f0 ∗ interpFrame C.local_ i f0 }})) $$ []
  · imodintro
    iintro %a %a0 %Ha0 Ha Hfa #Hva
    rw [show toEList [.loop bt es] = [.basic (.loop bt es)] from rfl]
    iapply IH $$ %a %a0 %Ha0 Ha Hfa Hva
  ihave #HIH2 : iprop(□ (∀ (a : Frame) (a0 : List Value), ⌜a0.length = tn.length⌝ →
        ↪[frame] a -∗ interpFrame C.local_ i a -∗
        □ ([∗list] w;τ ∈ a0;tn, interpValue τ w) -∗
        WP (vToEList a0 ++ toEList [.loop bt es])
          {{ vs, (interpVal tm vs ∨ interpBr C.local_ i C.return_ hl vs lh C.label ∨
                  interpReturnOption C.return_ C.local_ i vs ∨
                  interpCallHost C.local_ i C.return_ hl vs lh C.label tm) ∗
                 ∃ f0, ↪[frame] f0 ∗ interpFrame C.local_ i f0 }})) $$ []
  · imodintro
    iintro %a %a0 %Ha0 Ha Hfa #Hva
    rw [show toEList [.loop bt es] = [.basic (.loop bt es)] from rfl,
      show vToEList a0 = ofVal (.immV a0) from rfl]
    iapply IH $$ %a %a0 %Ha0 Ha Hfa Hva
  iclear IH
  iintro Hf
  icases wp_wasm_empty_ctx (GF := GF) .NotStuck ⊤ _ _ with ⟨-, H⟩
  iapply H
  iclear H
  iapply wp_label_push_nil
  rw [← List.append_nil (ofVal (.immV ws) ++ toEList es)]
  iapply wp_seq_can_trap_ctx _ _ _
    (fun w => iprop(interpValues tm w ∨
      interpBr C.local_ i C.return_ hl w (pushBase lh tn.length [.basic (.loop bt es)] [] [])
        (updLabel C ([tn] ++ C.label)).label ∨
      interpReturnOption (updLabel C ([tn] ++ C.label)).return_
        (updLabel C ([tn] ++ C.label)).local_ i w ∨
      interpCallHost C.local_ i C.return_ hl w (pushBase lh tn.length [.basic (.loop bt es)] [] [])
        (updLabel C ([tn] ++ C.label)).label tm))
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
    ihave #Hc' := interp_ctx_push_label_loop (bt := bt) C tm i lh tn es C.return_ hl $$ HIH Hc
    unfold semanticTyping
    rw [show (updLabel C ([tn] ++ C.label)).return_ = C.return_ from rfl,
      show (updLabel C ([tn] ++ C.label)).local_ = C.local_ from rfl]
    ihave HH := HH $$ %i %(pushBase lh tn.length [.basic (.loop bt es)] [] []) %hl [] []
      %f %(.immV ws) [Hf Hfv] []
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
  simp only [List.append_nil, Nat.zero_add]
  icases H with (H | H | H | H)
  · iunfold interpValues at H
    icases H with ⟨%vs, %Heq, #Hvs⟩
    subst Heq
    rw [show pushBase (.base [] []) tn.length [.basic (.loop bt es)] [] [] =
      .rec_ [] tn.length [.basic (.loop bt es)] (.base [] []) [] from rfl]
    iapply wp_val_return (vs' := []) (es'' := []) (const_list_of_val vs) $$ Hf0
    iintro Hf0
    iapply IrisWp.wp_value (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
      (e := [] ++ ofVal (.immV vs) ++ []) (v := .immV vs) ⟨by simp; rfl⟩
    isplitr [Hf0 Hfv0]
    · ileft; unfold interpVal interpValues; iright; iexists vs; isplitr; · ipureintro; rfl
      iexact Hvs
    · iexists f0; iframe
  · rw [fixpoint_interp_br_eq]; dsimp only [interpCallHostBrDef]
    simp only [loop_fold_br, loop_fold_ch]
    iapply wp_label_push_nil_inv
    icases wp_wasm_empty_ctx (GF := GF) .NotStuck ⊤ _ _ with ⟨HE, -⟩
    iapply HE
    iclear HE
    icases H with ⟨%j, %vh', %vs, %p, %Heqbr, %Hbase, %Hsize, Hbr⟩
    subst Heqbr
    rw [show ofVal (.brV vh') = vfill vh' [.basic (.br j)] from rfl]
    by_cases hjp : j = p
    · iapply IrisFundamentalLoop.interp_br_step (bt := bt) C j vh' tn.length vs tn p i es tm lh f0
        C.return_ hl rfl Hbase Hsize hjp $$ HIH2 [Hbr] Hf0 Hfv0
      unfold interpBrBody
      iexact Hbr
    · ihave #Hcx := Hc
      iunfold interpCtx at Hcx
      icases Hcx with ⟨%Hlh_base, %Hlh_len, %Hlh_valid, -⟩
      iapply interp_br_stuck_push C j vh' tn.length vs p i tn tm lh f0
        [.basic (.loop bt es)] C.return_ hl rfl Hbase Hsize hjp Hlh_len Hlh_valid Hlh_base
        $$ [Hbr] Hf0 Hfv0
      unfold interpBrBody
      iexact Hbr
  · rw [show pushBase (.base [] []) tn.length [.basic (.loop bt es)] [] [] =
      .rec_ [] tn.length [.basic (.loop bt es)] (.base [] []) [] from rfl]
    iapply interp_return_label C tn i w f0 tm lh [.basic (.loop bt es)] tn.length hl
      $$ H Hf0 Hfv0
  · rw [show pushBase (.base [] []) tn.length [.basic (.loop bt es)] [] [] =
      .rec_ [] tn.length [.basic (.loop bt es)] (.base [] []) [] from rfl]
    iapply IrisFundamentalLoop.interp_call_host_label (bt := bt) C i w f0 tn tm es lh hl
      $$ HIH2 Hc H Hf0 Hfv0

end IrisWasm
