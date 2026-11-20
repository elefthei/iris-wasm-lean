/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Rules.IrisRulesControl
import IrisWasm.Rules.IrisRulesStructural
import IrisWasm.Helpers.Prelude.IrisWasmLangProperties
import IrisWasm.Helpers.Prelude.IrisReduceProperties

/-! Port of `theories/iris/rules/iris_rules_bind.v`. -/

namespace IrisWasm

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm

variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF]

private theorem wp_eq {s : Stuckness} {E : CoPset} {e : Expr} {Φ : Val → IProp GF} :
    (WP e @ s ; E {{ Φ }} : IProp GF) =
      IrisWp.wp (ι := wasmIrisGS) (fun f => iprop(↪[frame] f)) s E e Φ := rfl

private theorem lfilled_label1 {l1 l2 es e : Expr} {n : Nat} (hc : constList l1 = true) :
    lfilled 1 (.rec_ l1 n es (.base [] []) l2) e (l1 ++ [.label n es e] ++ l2) = true := by
  simpa using (lfilled_Ind_Equivalent _ _ _ _).2
    (.lfilledRec _ _ _ _ _ _ _ _ hc (.lfilledBase [] e [] rfl))

/-- Swap the frame owned by the state interpretation from `f` (which must be the current one)
to `f'`. -/
private theorem si_frame_swap {ws : StoreRecord} {locs : List Value} {inst : Instance}
    (f f' : Frame) :
    ⊢ (stateInterp (ws, locs, inst) -∗ ↪[frame] f ==∗
      ⌜f = ⟨locs, inst⟩⌝ ∗ stateInterp (ws, f'.locs, f'.inst) ∗ ↪[frame] f' : IProp GF) := by
  simp only [IrisWasm.stateInterp]
  unfold frameOwn
  iintro ⟨H1, H2, H3, H4, Ha, H5, H6, H7, H8⟩ Hf
  ihave %h : ⌜f = ⟨locs, inst⟩⌝ $$ [Ha Hf]
  · ihave %h := ghost_map_lookup $$ Ha Hf
    ipureintro
    rw [get?_insert_eq rfl] at h
    exact (Option.some.inj h).symm
  imod ghost_map_update f' $$ Ha Hf with ⟨Ha, Hf⟩
  have e : insert (insert (PartialMap.empty : UnitMapF Frame) () ⟨locs, inst⟩) () f' =
      insert (PartialMap.empty : UnitMapF Frame) () ⟨f'.locs, f'.inst⟩ := LawfulPartialMap.insert_insert_same
  rw [e]
  imodintro
  iframe
  ipureintro; exact h

private theorem wpctx_apply {s : Stuckness} {E : CoPset} {e : Expr} {Φ : Val → IProp GF}
    {i : Nat} {lh : Lholed} {LI : Expr} (h : lfilled i lh e LI = true) :
    (WP e @ s ; E CTX i ; lh {{ Φ }} : IProp GF) ⊢ WP LI @ s ; E {{ Φ }} := by
  unfold wpWasmCtx; iintro H; iapply H $$ %LI %h

private theorem wpctx_intro {s : Stuckness} {E : CoPset} {e : Expr} {Φ : Val → IProp GF}
    {i : Nat} {lh : Lholed} :
    iprop(∀ LI, ⌜lfilled i lh e LI = true⌝ -∗ WP LI @ s ; E {{ Φ }})
      ⊢ (WP e @ s ; E CTX i ; lh {{ Φ }} : IProp GF) := .rfl

private theorem lfilled_base_nonzero {i : Nat} {bef aft e LI : Expr} :
    lfilled (i + 1) (.base bef aft) e LI = false := by
  simp [lfilled, lfill]

private theorem lfilled_rec_zero {l1 l2 es e LI : Expr} {n : Nat} {lh : Lholed} :
    lfilled 0 (.rec_ l1 n es lh l2) e LI = false := by
  simp [lfilled, lfill]

@[rocq_alias iriswasm.wp_frame_bind]
theorem wp_frame_bind (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF) (n : Nat) (f f0 : Frame)
    (LI : Expr) :
    toVal [.local n f LI] = none →
    ⊢ (↪[frame] f0 -∗
      (↪[frame] f -∗ WP LI @ s ; E {{ w, ∃ f', (↪[frame] f0 -∗
        WP (ofVal w) @ s ; E FRAME n ; f' {{ w, Φ w }}) ∗ ↪[frame] f' }}) -∗
      WP LI @ s ; E FRAME n ; f {{ w, Φ w }} : IProp GF) := by
  intro hnv
  let := @WasmG.invGS hlc GF _
  unfold wpWasmFrame
  iloeb as IH generalizing %LI %f %f0 %hnv
  iintro Hf0 H
  iapply (IrisWp.wp_unfold (ι := wasmIrisGS) (fun f => iprop(↪[frame] f))).2
  have hnv' : Iris.ProgramLogic.toVal ([.local n f LI] : Expr) = none := hnv
  simp only [IrisWp.wp.pre, hnv']
  iintro %σ %ns %obs %obs' %nt Hσ
  rcases σ with ⟨ws, locs, inst⟩
  imod si_frame_swap f0 f $$ Hσ Hf0 with ⟨%rfl, Hσ, Hf⟩
  ihave H := H $$ Hf
  cases he : toVal LI with
  | some v =>
    ihave H := (IrisWp.wp_value_fupd (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
      ⟨of_to_val _ _ he⟩).1 $$ H
    imod H with ⟨%f', H, Hf⟩
    imod si_frame_swap f' ⟨locs, inst⟩ $$ Hσ Hf with ⟨%rfl, Hσ, Hf0⟩
    ihave H := H $$ Hf0
    rw [of_to_val _ _ he]
    ihave H := (IrisWp.wp_unfold (ι := wasmIrisGS) (fun f => iprop(↪[frame] f))).1 $$ H
    simp only [IrisWp.wp.pre, hnv']
    iapply H $$ %(ws, locs, inst) %ns %obs %obs' %nt Hσ
  | none =>
    ihave H := (IrisWp.wp_unfold (ι := wasmIrisGS) (fun f => iprop(↪[frame] f))).1 $$ H
    have he' : Iris.ProgramLogic.toVal LI = none := he
    simp only [IrisWp.wp.pre, he']
    icases H $$ %(ws, f.locs, f.inst) %ns %obs %obs' %nt Hσ with >⟨%Hred, H⟩
    imodintro
    isplitr
    · ipureintro
      cases s <;> simp only [Stuckness.MaybeReducible] at Hred ⊢
      obtain ⟨obs0, e₂, ⟨ws', locs', inst'⟩, eₜ, Hst, -, -⟩ := Hred
      exact ⟨[], [.local n ⟨locs', inst'⟩ e₂], (ws', locs, inst), [], .local Hst, rfl, rfl⟩
    iintro %e₂ %σ₂ %eₜ %Hstep Hc
    rcases σ₂ with ⟨ws', locs', inst'⟩
    obtain ⟨Hst, rfl, rfl⟩ := Hstep
    obtain ⟨es2', f1, rfl, hff, Hst'⟩ := reduce_det_local he Hst
    simp only [Frame.mk.injEq] at hff
    obtain ⟨rfl, rfl⟩ := hff
    dsimp only [step_fupdN]
    imod H $$ %es2' %(ws', f1.locs, f1.inst) %([] : List Expr)
      %(show primStep (LI, ws, f.locs, f.inst) [] (es2', (ws', f1.locs, f1.inst), []) from
        ⟨Hst', rfl, rfl⟩) Hc with H
    iintro !> !>
    imod H
    iintro !>
    iapply step_fupdN_wand $$ H
    iintro >⟨Hσ, %a, Ha, H, -⟩
    cases hv2 : toVal ([.local n f1 es2'] : Expr) with
    | none =>
      imod si_frame_swap a ⟨locs, inst⟩ $$ Hσ Ha with ⟨%ha, Hσ, Hf0⟩
      have ha : a = f1 := ha
      subst ha
      imodintro
      iframe Hσ
      iexists ⟨locs, inst⟩
      iframe Hf0
      isplitl
      · iintro Hf0
        iapply IH $$ %es2' %a %⟨locs, inst⟩ %hv2 Hf0 H
      · simp; iempintro
    | some v =>
      obtain ⟨tf, h, w, vh, rfl⟩ := to_val_local_inv _ _ _ _ hv2
      obtain ⟨LI', heq, hLI'⟩ := to_val_call_host_rec_local _ [] n f1 vh [] tf h w hv2
      simp only [vToEList, List.map_nil, List.nil_append, List.append_nil, List.cons.injEq,
        AdministrativeInstruction.local.injEq, and_true, true_and] at heq
      subst heq
      ihave H := H $$ Ha
      ihave H := (IrisWp.wp_value_fupd (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
        ⟨of_to_val _ _ hLI'⟩).1 $$ H
      imod H with ⟨%f', H, Hf'⟩
      imod si_frame_swap f' ⟨locs, inst⟩ $$ Hσ Hf' with ⟨%hf', Hσ, Hf0⟩
      have hf' : f' = f1 := hf'
      subst hf'
      imodintro
      iframe Hσ
      iexists ⟨locs, inst⟩
      iframe Hf0
      isplitl
      · iintro Hf0
        ihave H := H $$ Hf0
        rw [of_to_val _ _ hLI']
        iexact H
      · simp; iempintro

@[rocq_alias iriswasm.wp_label_bind]
theorem wp_label_bind (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF) (e : Expr) (n : Nat)
    (es l1 l2 : Expr) :
    ⊢ (WP e @ s ; E {{ w, WP (ofVal w) @ s ; E CTX 1 ; (.rec_ l1 n es (.base [] []) l2)
        {{ w, Φ w }} }} -∗
      WP e @ s ; E CTX 1 ; (.rec_ l1 n es (.base [] []) l2) {{ w, Φ w }} : IProp GF) := by
  let := @WasmG.invGS hlc GF _
  unfold wpWasmCtx
  iintro H %LI %HLI
  irevert H
  iloeb as IH generalizing %e %LI %HLI
  iintro H
  cases he : toVal e with
  | some v =>
    ihave H := (IrisWp.wp_value_fupd (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
      ⟨of_to_val _ _ he⟩).1 $$ H
    iapply IrisWp.fupd_wp (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
    imod H
    rw [of_to_val _ _ he]
    iapply H $$ %LI %HLI
  | none =>
    have hLI := to_val_None_lfilled _ _ _ _ he HLI
    have hc : constList l1 = true ∧ LI = l1 ++ [.label n es e] ++ l2 := by
      have := (lfilled_Ind_Equivalent _ _ _ _).1 HLI
      cases this with
      | lfilledRec _ _ _ _ _ _ _ _ hc h0 =>
        cases h0 with
        | lfilledBase _ _ _ _ => exact ⟨hc, by simp⟩
    obtain ⟨hc, rfl⟩ := hc
    rw [wp_eq, wp_eq, (IrisWp.wp_unfold (ι := wasmIrisGS) _).to_eq,
      (IrisWp.wp_unfold (ι := wasmIrisGS) _).to_eq]
    have he' : Iris.ProgramLogic.toVal e = none := he
    have hLI' : Iris.ProgramLogic.toVal (l1 ++ [.label n es e] ++ l2 : Expr) = none := hLI
    simp only [IrisWp.wp.pre, he', hLI']
    iintro %σ %ns %obs %obs' %nt Hσ
    icases H $$ %σ %ns %obs %obs' %nt Hσ with >⟨%Hred, H⟩
    imodintro
    isplitr
    · ipureintro
      cases s <;> simp only [Stuckness.MaybeReducible] at Hred ⊢
      exact lfilled_reducible HLI Hred
    iintro %e₂ %σ₂ %eₜ %Hstep Hc
    rcases σ with ⟨ws, locs, inst⟩
    rcases σ₂ with ⟨ws', locs', inst'⟩
    obtain ⟨Hst, rfl, rfl⟩ := Hstep
    obtain ⟨es2', rfl, Hst'⟩ := reduce_det_label Hst l1 l2 rfl hc he
    dsimp only [step_fupdN]
    imod H $$ %es2' %(ws', locs', inst') %([] : List Expr) %(show primStep (e, ws, locs, inst) [] (es2', (ws', locs', inst'), []) from ⟨Hst', rfl, rfl⟩) Hc with H
    iintro !> !>
    imod H
    iintro !>
    iapply step_fupdN_wand $$ H
    iintro >⟨Hσ, %a, Ha, H, -⟩
    imodintro
    iframe Hσ
    iexists a
    iframe Ha
    isplitl
    · iintro Ha
      ihave H := H $$ Ha
      have hf : lfilled 1 (.rec_ l1 n es (.base [] []) l2) es2' (l1 ++ [.label n es es2'] ++ l2) := by
        simpa using (lfilled_Ind_Equivalent _ _ _ _).2
          (.lfilledRec _ _ _ _ _ _ _ _ hc (.lfilledBase [] es2' [] rfl))
      iapply IH $$ %es2' %_ %hf H
    · simp; iempintro

@[rocq_alias iriswasm.wp_label_bind_inv]
theorem wp_label_bind_inv (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF) (e : Expr) (n : Nat)
    (es l1 l2 : Expr) :
    constList l1 = true →
    ⊢ (WP e @ s ; E CTX 1 ; (.rec_ l1 n es (.base [] []) l2) {{ w, Φ w }} -∗
      WP e @ s ; E {{ w, WP (ofVal w) @ s ; E CTX 1 ; (.rec_ l1 n es (.base [] []) l2)
        {{ w, Φ w }} }} : IProp GF) := by
  intro hc
  let := @WasmG.invGS hlc GF _
  unfold wpWasmCtx
  iloeb as IH generalizing %e
  iintro H
  ihave H := H $$ %(l1 ++ [.label n es e] ++ l2) %(lfilled_label1 hc)
  cases he : toVal e with
  | some v =>
    iapply (IrisWp.wp_value_fupd (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
      ⟨of_to_val _ _ he⟩).2
    imodintro
    iintro %LI %HLI
    rw [of_to_val _ _ he] at HLI
    rw [lfilled_inj HLI (lfilled_label1 hc)]
    iexact H
  | none =>
    have hLI := to_val_None_lfilled _ _ _ _ he (lfilled_label1 (n := n) (es := es) (l2 := l2) hc)
    rw [wp_eq, wp_eq, (IrisWp.wp_unfold (ι := wasmIrisGS) _).to_eq,
      (IrisWp.wp_unfold (ι := wasmIrisGS) _).to_eq]
    have he' : Iris.ProgramLogic.toVal e = none := he
    have hLI' : Iris.ProgramLogic.toVal (l1 ++ [.label n es e] ++ l2 : Expr) = none := hLI
    simp only [IrisWp.wp.pre, he', hLI']
    iintro %σ %ns %obs %obs' %nt Hσ
    icases H $$ %σ %ns %obs %obs' %nt Hσ with >⟨%Hred, H⟩
    imodintro
    rcases σ with ⟨ws, locs, inst⟩
    isplitr
    · ipureintro
      cases s <;> simp only [Stuckness.MaybeReducible] at Hred ⊢
      obtain ⟨obs0, e₂, ⟨ws', locs', inst'⟩, eₜ, Hst, -, -⟩ := Hred
      obtain ⟨es2', -, Hst'⟩ := reduce_det_label Hst l1 l2 rfl hc he
      exact ⟨[], es2', (ws', locs', inst'), [], Hst', rfl, rfl⟩
    iintro %e₂ %σ₂ %eₜ %Hstep Hc
    rcases σ₂ with ⟨ws', locs', inst'⟩
    obtain ⟨Hst, rfl, rfl⟩ := Hstep
    have Hst' : Reduce ws ⟨locs, inst⟩ (l1 ++ [.label n es e] ++ l2) ws' ⟨locs', inst'⟩
        (l1 ++ [.label n es e₂] ++ l2) :=
      .label _ _ _ _ Hst (lfilled_label1 hc) (lfilled_label1 hc)
    dsimp only [step_fupdN]
    imod H $$ %_ %(ws', locs', inst') %([] : List Expr)
      %(show primStep (_, ws, locs, inst) [] (_, (ws', locs', inst'), []) from ⟨Hst', rfl, rfl⟩)
      Hc with H
    iintro !> !>
    imod H
    iintro !>
    iapply step_fupdN_wand $$ H
    iintro >⟨Hσ, %a, Ha, H, -⟩
    imodintro
    iframe Hσ
    iexists a
    iframe Ha
    isplitl
    · iintro Ha
      ihave H := H $$ Ha
      iapply IH $$ %e₂
      iintro %LI %HLI
      rw [lfilled_inj HLI (lfilled_label1 hc)]
      iexact H
    · simp; iempintro

@[rocq_alias iriswasm.wp_label_bind_next]
theorem wp_label_bind_next (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF) (e : Expr) (n : Nat)
    (es l1 l2 : Expr) (i : Nat) (lh : Lholed) :
    BaseIsEmpty lh →
    ⊢ (WP e @ s ; E {{ w, WP (ofVal w) @ s ; E CTX (i + 1) ; (.rec_ l1 n es lh l2)
        {{ w, Φ w }} }} -∗
      WP e @ s ; E CTX (i + 1) ; (.rec_ l1 n es lh l2) {{ w, Φ w }} : IProp GF) := by
  induction lh generalizing i Φ e l1 l2 n es with
  | base bef aft =>
    rintro ⟨rfl, rfl⟩
    cases i with
    | zero => exact wp_label_bind s E Φ e n es l1 l2
    | succ i =>
      unfold wpWasmCtx
      iintro - %LI %HLI
      obtain ⟨LI', h1, -⟩ := lfilled_flatten _ _ _ _ _ _ _ _ HLI
      simp [lfilled_base_nonzero] at h1
  | rec_ l1' m es' lh l2' ih =>
    intro hb
    iintro He
    unfold wpWasmCtx
    iintro %LI %HLI
    obtain ⟨LI', hfill1, hfill2⟩ := lfilled_flatten _ _ _ _ _ _ _ _ HLI
    iapply wpctx_apply hfill2
    iapply wp_label_bind s E Φ LI' n es l1 l2
    cases i with
    | zero => simp [lfilled_rec_zero] at hfill1
    | succ i =>
      iapply wpctx_apply hfill1
      iapply ih (i := i) (Φ := fun w => iprop(WP (ofVal w) @ s ; E CTX 1 ;
        (.rec_ l1 n es (.base [] []) l2) {{ w, Φ w }})) (e := e) (l1 := l1') (l2 := l2') (n := m)
        (es := es') hb
      iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ He
      iintro %v He
      iapply wpctx_intro
      iintro %LI0 %HLI0
      have h0 := (lfilled_Ind_Equivalent _ _ _ _).1 HLI0
      cases h0 with
      | lfilledRec _ _ _ _ _ _ _ LI0' hc hLI0' =>
        have hc1 : constList l1 = true := by
          have := (lfilled_Ind_Equivalent _ _ _ _).1 HLI
          cases this; assumption
        iapply wp_label_bind_inv s E Φ _ n es l1 l2 hc1
        iapply wpctx_intro
        iintro %LI1 %HLI1
        have h1 := (lfilled_Ind_Equivalent _ _ _ _).1 HLI1
        cases h1 with
        | lfilledRec _ _ _ _ _ _ _ _ _ hb1 =>
          cases hb1 with
          | lfilledBase _ _ _ _ =>
            simp only [List.nil_append, List.append_nil]
            iapply He
            ipureintro
            exact (lfilled_Ind_Equivalent _ _ _ _).2 (.lfilledRec _ _ _ _ _ _ _ _ hc1
              (.lfilledRec _ _ _ _ _ _ _ _ hc hLI0'))

@[rocq_alias iriswasm.wp_ctx_bind]
theorem wp_ctx_bind (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF) (e : Expr) (i : Nat)
    (lh : Lholed) :
    BaseIsEmpty lh →
    ⊢ (WP e @ s ; E {{ w, WP (ofVal w) @ s ; E CTX i ; lh {{ w, Φ w }} }} -∗
      WP e @ s ; E CTX i ; lh {{ w, Φ w }} : IProp GF) := by
  cases lh with
  | base bef aft =>
    rintro ⟨rfl, rfl⟩
    unfold wpWasmCtx
    iintro He %LI %HLI
    cases i with
    | succ i => simp [lfilled_base_nonzero] at HLI
    | zero =>
      obtain ⟨-, rfl⟩ := lfilled_zero_base_inv HLI
      simp only [List.nil_append, List.append_nil]
      let := @WasmG.invGS hlc GF _
      iapply IrisWp.wp_fupd (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
      iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ He
      iintro %v Hv
      ihave Hv := Hv $$ %(ofVal v) %(by simp [lfilled, lfill, constList])
      iapply (IrisWp.wp_value_fupd (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) ⟨rfl⟩).1 $$ Hv
  | rec_ l1 n es lh l2 =>
    intro hb
    cases i with
    | zero =>
      unfold wpWasmCtx
      iintro - %LI %HLI
      simp [lfilled_rec_zero] at HLI
    | succ i => exact wp_label_bind_next s E Φ e n es l1 l2 i lh hb

end IrisWasm
