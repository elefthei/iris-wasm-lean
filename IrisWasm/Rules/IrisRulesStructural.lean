/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Language.IrisWpDef
import IrisWasm.Helpers.Prelude.IrisWasmLangProperties
import IrisWasm.Helpers.Prelude.IrisReduceProperties
import IrisWasm.Helpers.Prelude.IrisSplitReduce
import IrisWasm.Helpers.Prelude.FirstInstr
import IrisWasm.Helpers.IrisPrimStepSplit
import IrisWasm.Helpers.IrisWasmDeterm

/-! Port of `theories/iris/rules/iris_rules_structural.v`: empty lists, frame and context rules. -/

namespace IrisWasm

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm

variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF]

private abbrev frameP : Frame → IProp GF := fun f => iprop(↪[frame] f)

private theorem wp_unfold_w {s E} {e : Expr} {Φ : Val → IProp GF} :
    WP e @ s ; E {{ Φ }} ⊣⊢
      IrisWp.wp.pre (ι := wasmIrisGS) frameP s (IrisWp.wp (ι := wasmIrisGS) frameP s) E e Φ :=
  IrisWp.wp_unfold (ι := wasmIrisGS) frameP

private theorem trap_step {es : Expr} (h : toVal es = none) {lh : Lholed}
    (hl : lfilled 0 lh [.trap] es = true) (σ : State) : primStep (es, σ) [] ([.trap], σ, []) := by
  obtain ⟨s, l, i⟩ := σ
  refine ⟨.simple (.trap lh ?_ hl), rfl, rfl⟩
  rintro rfl; exact absurd h (by rw [show [AdministrativeInstruction.trap] = ofVal .trapV from rfl, to_of_val]; simp)

/-- A WP whose expression steps to `trap` while `¬ Ψ trapV` holds proves anything. -/
private theorem wp_trap_absurd {s s' : Stuckness} {E' : CoPset} {e : Expr} {Ψ Φ : Val → IProp GF} :
    iprop((¬ Ψ .trapV) ∗ WP [AdministrativeInstruction.trap] @ s ; E' {{ Ψ }}) ⊢ WP e @ s' ; E' {{ Φ }} := by
  let := @WasmG.invGS hlc GF _
  have e : (WP [AdministrativeInstruction.trap] @ s ; E' {{ Ψ }} : IProp GF) ⊣⊢ |={E'}=> Ψ .trapV :=
    IrisWp.wp_value_fupd' (ι := wasmIrisGS) frameP (v := .trapV)
  iintro ⟨Hn, H⟩
  iapply IrisWp.fupd_wp (ι := wasmIrisGS) frameP
  ihave H := e.1 $$ H
  imod H
  iexfalso
  iapply Hn $$ H


private theorem to_val_cons_val {v0 : Value} {es : Expr} {w : Val} (h : toVal es = some w)
    (hw : w ≠ .trapV) : toVal (.basic (.const v0) :: es) = some (valCombine (.immV [v0]) w) := by
  cases w with
  | immV l => rw [← of_to_val _ _ h]; exact to_val_cons_immV v0 l
  | trapV => exact absurd rfl hw
  | brV lh => exact to_val_cons_brV _ lh v0 es h
  | retV sh => exact to_val_cons_retV sh v0 es h
  | callHostV tf hf cvs lh => exact to_val_cons_callHostV tf hf cvs lh v0 es h

@[rocq_alias iriswasm.wp_val]
theorem wp_val (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF) (v0 : Value) (es : Expr) :
    iprop((¬ Φ .trapV) ∗ WP es @ Stuckness.NotStuck ; E {{ v, Φ (valCombine (.immV [v0]) v) }})
      ⊢ WP (.basic (.const v0) :: es) @ s ; E {{ v, Φ v }} := by
  let := @WasmG.invGS hlc GF _
  iintro ⟨Hn, H⟩
  iloeb as IH generalizing %es
  cases hes : toVal es with
  | some w =>
    by_cases hw : w = .trapV
    · subst hw
      obtain rfl := to_val_trap_is_singleton es hes
      iapply wp_trap_absurd (Ψ := fun v => Φ (valCombine (.immV [v0]) v)) $$ [Hn H]
      isplitl [Hn]
      · isimp only [valCombine]
        iexact Hn
      · iexact H
    · obtain rfl := of_to_val _ _ hes
      rw [show AdministrativeInstruction.basic (.const v0) :: ofVal w =
        ofVal (valCombine (.immV [v0]) w) from (of_to_val _ _ (to_val_cons_val hes hw)).symm]
      iapply (IrisWp.wp_value_fupd' (ι := wasmIrisGS) frameP).2
      iapply (IrisWp.wp_value_fupd' (ι := wasmIrisGS) frameP).1 $$ H
  | none =>
    have hn := to_val_cons_None es v0 hes
    iapply wp_unfold_w.2
    ihave H := wp_unfold_w.1 $$ H
    have hn' : Iris.ProgramLogic.toVal (AdministrativeInstruction.basic (.const v0) :: es) = none := hn
    have hes' : Iris.ProgramLogic.toVal es = none := hes
    simp only [IrisWp.wp.pre, hn', hes']
    iintro %σ %ns %obs %obs' %nt Hσ
    imod H $$ Hσ with ⟨%Hred, H⟩
    imodintro
    isplit
    · ipureintro
      cases s
      · exact prepend_reducible [.basic (.const v0)] es σ (Or.inl rfl) Hred
      · trivial
    · iintro %e₂ %σ₂ %eₜ %HStep Hcr
      have HStep : primStep ([.basic (.const v0)] ++ es, σ) obs (e₂, σ₂, eₜ) := HStep
      obtain ⟨rfl, rfl⟩ : obs = [] ∧ eₜ = [] := by
        have := prim_step_obs_efs_empty HStep; simp_all
      rcases reduce_ves v0 es e₂ σ σ₂ [] [] Hred HStep with ⟨he2, HStep2⟩ | ⟨lh, lh', -, hl2, rfl⟩
      · obtain ⟨e', rfl⟩ : ∃ e', e₂ = .basic (.const v0) :: e' := ⟨_, he2⟩
        dsimp only [step_fupdN]
        imod H $$ %e' %σ₂ %([] : List Expr) %HStep2 Hcr with H
        iintro !> !>
        imod H
        iintro !>
        iapply step_fupdN_wand $$ H
        iintro >⟨Hσ, %a, Ha, Hwp, -⟩
        imodintro
        iframe Hσ
        iexists a
        iframe Ha
        isplitl
        · iintro Ha
          iapply IH $$ %e' Hn (Hwp $$ Ha)
        · iapply BI.BigSepL.bigSepL_nil.2
          iempintro
      · dsimp only [step_fupdN]
        imod H $$ %([AdministrativeInstruction.trap] : Expr) %σ %([] : List Expr) %(trap_step hes hl2 σ) Hcr
          with H
        iintro !> !>
        imod H
        iintro !>
        iapply step_fupdN_wand $$ H
        iintro >⟨Hσ, %a, Ha, Hwp, -⟩
        imodintro
        iframe Hσ
        iexists a
        iframe Ha
        isplitl
        · iintro Ha
          iapply wp_trap_absurd (Ψ := fun v => Φ (valCombine (.immV [v0]) v)) $$ [Hn Hwp Ha]
          isplitl [Hn]
          · isimp only [valCombine]
            iexact Hn
          · iapply Hwp $$ Ha
        · iapply BI.BigSepL.bigSepL_nil.2
          iempintro
private theorem valCombine_nil (v : Val) : valCombine (.immV []) v = v := by
  cases v <;> simp [valCombine, vh_push_const_nil, sh_push_const_nil, llh_push_const_nil]

private theorem valCombine_cons (c : Value) (vs : List Value) (v : Val) :
    valCombine (.immV [c]) (valCombine (.immV vs) v) = valCombine (.immV (c :: vs)) v := by
  cases v <;> simp [valCombine, ← vh_push_const_app, ← sh_push_const_app, ← llh_push_const_app]

@[rocq_alias iriswasm.wp_val_app']
theorem wp_val_app' (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF) (vs : List Value)
    (es : Expr) :
    iprop((□ (¬ Φ .trapV)) ∗
      WP es @ Stuckness.NotStuck ; E {{ v, Φ (valCombine (.immV vs) v) }})
      ⊢ WP (vToEList vs ++ es) @ s ; E {{ v, Φ v }} := by
  let := @WasmG.invGS hlc GF _
  induction vs generalizing Φ s es with
  | nil =>
    rw [show vToEList [] ++ es = es from rfl]
    iintro ⟨#Hn, H⟩
    iapply IrisWp.wp_strong_mono (ι := wasmIrisGS) frameP Stuckness.NotStuck_le
      LawfulSet.subset_refl $$ H
    iintro %v Hv
    imodintro
    rw [valCombine_nil]
    iexact Hv
  | cons c vs ih =>
    rw [show vToEList (c :: vs) ++ es = .basic (.const c) :: (vToEList vs ++ es) from rfl]
    iintro ⟨#Hn, H⟩
    iapply wp_val
    isplitr
    · iexact Hn
    · iapply ih (Φ := fun v => Φ (valCombine (.immV [c]) v))
      isplitr
      · imodintro
        isimp only [valCombine]
        iexact Hn
      · iapply IrisWp.wp_mono (ι := wasmIrisGS) frameP (fun v => ?_) $$ H
        rw [valCombine_cons]

@[rocq_alias iriswasm.wp_val_app]
theorem wp_val_app (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF) (vs : Expr)
    (v' : List Value) (es : Expr) (h : toVal vs = some (.immV v')) :
    iprop((□ (¬ Φ .trapV)) ∗
      WP es @ Stuckness.NotStuck ; E {{ v, Φ (valCombine (.immV v') v) }})
      ⊢ WP (vs ++ es) @ s ; E {{ v, Φ v }} := by
  rw [← of_to_val _ _ h, ← of_val_imm]
  exact wp_val_app' s E Φ v' es

@[rocq_alias iriswasm.wp_seq]
theorem wp_seq (s : Stuckness) (E : CoPset) (Φ Ψ : Val → IProp GF) (es1 es2 : Expr) :
    iprop((¬ Ψ .trapV) ∗ WP es1 @ s ; E {{ w, Ψ w }} ∗
      ∀ w, Ψ w -∗ WP (ofVal w ++ es2) @ s ; E {{ v, Φ v }})
      ⊢ WP (es1 ++ es2) @ s ; E {{ v, Φ v }} := by
  let := @WasmG.invGS hlc GF _
  iintro ⟨Hn, H1, H2⟩
  iloeb as IH generalizing %es1
  cases hes : toVal es1 with
  | some w =>
    obtain rfl := of_to_val _ _ hes
    iapply IrisWp.fupd_wp (ι := wasmIrisGS) frameP
    ihave H1 := (IrisWp.wp_value_fupd' (ι := wasmIrisGS) frameP).1 $$ H1
    imod H1
    imodintro
    iapply H2 $$ H1
  | none =>
    have hn' : Iris.ProgramLogic.toVal (es1 ++ es2) = none := to_val_cat_None1 _ _ hes
    have hes' : Iris.ProgramLogic.toVal es1 = none := hes
    iapply wp_unfold_w.2
    ihave H1 := wp_unfold_w.1 $$ H1
    simp only [IrisWp.wp.pre, hn', hes']
    iintro %σ %ns %obs %obs' %nt Hσ
    imod H1 $$ Hσ with ⟨%Hred, H1⟩
    imodintro
    isplit
    · ipureintro
      cases s
      · exact append_reducible es1 es2 σ hes Hred
      · trivial
    · iintro %e₂ %σ₂ %eₜ %HStep Hcr
      have HStep : primStep (es1 ++ es2, σ) obs (e₂, σ₂, eₜ) := HStep
      obtain ⟨rfl, rfl⟩ : obs = [] ∧ eₜ = [] := by
        have := prim_step_obs_efs_empty HStep; simp_all
      rcases prim_step_split_reduce_r es1 es2 e₂ σ σ₂ [] [] hes HStep with
        ⟨es'', rfl, HStep2⟩ | ⟨n, m, lh, -, hl, hσ⟩
      · dsimp only [step_fupdN]
        imod H1 $$ %es'' %σ₂ %([] : List Expr) %HStep2 Hcr with H1
        iintro !> !>
        imod H1
        iintro !>
        iapply step_fupdN_wand $$ H1
        iintro >⟨Hσ, %a, Ha, Hwp, -⟩
        imodintro
        iframe Hσ
        iexists a
        iframe Ha
        isplitl
        · iintro Ha
          iapply IH $$ %es'' Hn (Hwp $$ Ha) H2
        · iapply BI.BigSepL.bigSepL_nil.2
          iempintro
      · subst σ₂
        dsimp only [step_fupdN]
        imod H1 $$ %([AdministrativeInstruction.trap] : Expr) %σ %([] : List Expr)
          %(trap_step hes hl σ) Hcr with H1
        iintro !> !>
        imod H1
        iintro !>
        iapply step_fupdN_wand $$ H1
        iintro >⟨Hσ, %a, Ha, Hwp, -⟩
        imodintro
        iframe Hσ
        iexists a
        iframe Ha
        isplitl
        · iintro Ha
          iapply wp_trap_absurd $$ [Hn Hwp Ha]
          isplitl [Hn]
          · iexact Hn
          · iapply Hwp $$ Ha
        · iapply BI.BigSepL.bigSepL_nil.2
          iempintro

@[rocq_alias iriswasm.wp_seq_ctx]
theorem wp_seq_ctx (s : Stuckness) (E : CoPset) (Φ Ψ : Val → IProp GF) (es1 es2 : Expr)
    (i : Nat) (lh : Lholed) :
    iprop((¬ Ψ .trapV) ∗ WP es1 @ Stuckness.NotStuck ; E {{ w, Ψ w }} ∗
      ∀ w, Ψ w -∗ WP (ofVal w ++ es2) @ s ; E CTX i ; lh {{ v, Φ v }})
      ⊢ WP (es1 ++ es2) @ s ; E CTX i ; lh {{ v, Φ v }} := by
  let := @WasmG.invGS hlc GF _
  unfold wpWasmCtx
  iintro ⟨Hn, H1, H2⟩
  iloeb as IH generalizing %es1
  iintro %LI %hfill
  cases hes : toVal es1 with
  | some w =>
    obtain rfl := of_to_val _ _ hes
    iapply IrisWp.fupd_wp (ι := wasmIrisGS) frameP
    ihave H1 := (IrisWp.wp_value_fupd' (ι := wasmIrisGS) frameP).1 $$ H1
    imod H1
    imodintro
    iapply H2 $$ H1 %LI %hfill
  | none =>
    have hn' : Iris.ProgramLogic.toVal LI = none :=
      to_val_None_lfilled LI i lh (es1 ++ es2) (to_val_cat_None1 _ _ hes) hfill
    have hes' : Iris.ProgramLogic.toVal es1 = none := hes
    iapply wp_unfold_w.2
    ihave H1 := wp_unfold_w.1 $$ H1
    simp only [IrisWp.wp.pre, hn', hes']
    iintro %σ %ns %obs %obs' %nt Hσ
    imod H1 $$ Hσ with ⟨%Hred, H1⟩
    imodintro
    isplit
    · ipureintro
      cases s
      · exact lfilled_reducible hfill (append_reducible es1 es2 σ hes Hred)
      · trivial
    · iintro %e₂ %σ₂ %eₜ %HStep Hcr
      have HStep : primStep (LI, σ) obs (e₂, σ₂, eₜ) := HStep
      obtain ⟨rfl, rfl⟩ : obs = [] ∧ eₜ = [] := by
        have := prim_step_obs_efs_empty HStep; simp_all
      rcases lfilled_prim_step_split_reduce_r i lh es1 es2 σ LI e₂ σ₂ [] [] hfill Hred HStep with
        ⟨e', HStep2, hfill2⟩ | ⟨⟨lh0, hl⟩, hσ⟩
      · dsimp only [step_fupdN]
        imod H1 $$ %e' %σ₂ %([] : List Expr) %HStep2 Hcr with H1
        iintro !> !>
        imod H1
        iintro !>
        iapply step_fupdN_wand $$ H1
        iintro >⟨Hσ, %a, Ha, Hwp, -⟩
        imodintro
        iframe Hσ
        iexists a
        iframe Ha
        isplitl
        · iintro Ha
          iapply IH $$ %e' Hn (Hwp $$ Ha) H2 %e₂ %hfill2
        · iapply BI.BigSepL.bigSepL_nil.2
          iempintro
      · subst σ₂
        dsimp only [step_fupdN]
        imod H1 $$ %([AdministrativeInstruction.trap] : Expr) %σ %([] : List Expr)
          %(trap_step hes hl σ) Hcr with H1
        iintro !> !>
        imod H1
        iintro !>
        iapply step_fupdN_wand $$ H1
        iintro >⟨Hσ, %a, Ha, Hwp, -⟩
        imodintro
        iframe Hσ
        iexists a
        iframe Ha
        isplitl
        · iintro Ha
          iapply wp_trap_absurd $$ [Hn Hwp Ha]
          isplitl [Hn]
          · iexact Hn
          · iapply Hwp $$ Ha
        · iapply BI.BigSepL.bigSepL_nil.2
          iempintro
/-! Contextual rules for Local computation -/

@[rocq_alias iriswasm.wp_frame_rewrite]
theorem wp_frame_rewrite (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF) (es : Expr) (n : Nat)
    (f : Frame) :
    WP es @ s ; E FRAME n ; f {{ v, Φ v }} ⊣⊢
      WP [AdministrativeInstruction.local n f es] @ s ; E {{ v, Φ v }} :=
  .rfl

@[rocq_alias iriswasm.wp_frame_value]
theorem wp_frame_value (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF) (es : Expr) (n : Nat)
    (f f0 : Frame) (vs : List Value) (hv : toVal es = some (.immV vs)) (hlen : es.length = n) :
    ⊢ ↪[frame] f0 -∗ ▷ Φ (.immV vs) -∗
      WP es @ s ; E FRAME n ; f {{ v, Φ v ∗ ↪[frame] f0 }} := by
  let := @WasmG.invGS hlc GF _
  have hconst := to_val_const_list es vs hv
  have hred : ∀ ws fr, Reduce ws fr [.local n f es] ws fr es :=
    fun _ _ => .simple (.localConst hconst hlen)
  have hnone : toVal [AdministrativeInstruction.local n f es] = none := by
    cases h : toVal [AdministrativeInstruction.local n f es] with
    | none => rfl
    | some w =>
      obtain ⟨tf, hf, w', vh, rfl⟩ := to_val_local_inv n f es w h
      obtain ⟨LI, heq, hLI⟩ := to_val_call_host_rec_local _ [] n f vh [] tf hf w' h
      simp [vToEList] at heq
      rw [← heq, hv] at hLI
      cases hLI
  unfold wpWasmFrame
  iintro Hf HΦ
  iapply IrisWp.wp_lift_atomic_step (ι := wasmIrisGS) frameP hnone f0
  iintro %σ %ns %obs %obs' %nt Hσ
  imodintro
  isplitr
  · ipureintro
    rcases σ with ⟨ws, locs, inst⟩
    cases s
    · exact ⟨[], _, (ws, locs, inst), [], hred ws ⟨locs, inst⟩, rfl, rfl⟩
    · trivial
  inext
  iintro %e₂ %σ₂ %eₜ %hstep -
  rcases σ with ⟨ws, locs, inst⟩
  rcases σ₂ with ⟨ws', locs', inst'⟩
  obtain ⟨hr, rfl, rfl⟩ := hstep
  rcases reduce_det (hred ws ⟨locs, inst⟩) hr with heq | ⟨i, hi⟩ | ⟨i1, _, _, hi, _⟩
  · simp only [Prod.mk.injEq, Frame.mk.injEq] at heq
    obtain ⟨rfl, ⟨rfl, rfl⟩, rfl⟩ := heq
    imodintro
    isplitl [Hσ]
    · iexact Hσ
    isplitl [HΦ]
    · iexists .immV vs
      isplit
      · ipureintro; exact hv
      · iexact HΦ
    isplitl [Hf]
    · iexact Hf
    · iapply BI.BigSepL.bigSepL_nil.2
      iempintro
  · rw [find_first_const es n f hconst] at hi; cases hi
  · rw [find_first_const es n f hconst] at hi; cases hi
/-- Owning the frame fragment pins down the current frame, and lets us replace it. -/
private theorem frame_update (ws : StoreRecord) (locs : List Value) (inst : Instance)
    (g f' : Frame) :
    ⊢ (stateInterp (ws, locs, inst) : IProp GF) -∗ ↪[frame] g -∗
      |==> (⌜g = ⟨locs, inst⟩⌝ ∗ stateInterp (ws, f'.locs, f'.inst) ∗ ↪[frame] f') := by
  obtain ⟨fl, fi⟩ := f'
  iintro Hσ Hg
  iunfold stateInterp at Hσ
  iunfold frameOwn at Hg
  icases Hσ with ⟨Hfu, Hta, Hme, Hgl, Hfr, Hr⟩
  ihave %hl := ghost_map_lookup $$ Hfr Hg
  ihave H := ghost_map_update ⟨fl, fi⟩ $$ Hfr Hg
  imod H with ⟨Hfr, Hg⟩
  isimp only [LawfulPartialMap.insert_insert_same] at Hfr
  simp only [LawfulPartialMap.get?_insert_eq rfl, Option.some.injEq] at hl
  imodintro
  isplitr
  · ipureintro; exact hl.symm
  isplitr [Hg]
  · isimp only [stateInterp]
    iframe
  · iunfold frameOwn
    iexact Hg

@[rocq_alias iriswasm.wp_seq_ctx_frame]
theorem wp_seq_ctx_frame (s : Stuckness) (E : CoPset) (Φ Ψ : Val → IProp GF) (es1 es2 : Expr)
    (i : Nat) (lh : Lholed) (n : Nat) (f f0 f1 : Frame)
    (hnone : ∀ LI, lfilled i lh (es1 ++ es2) LI = true → toVal [.local n f LI] = none) :
    iprop((¬ Ψ .trapV) ∗ ↪[frame] f0 ∗
      (↪[frame] f -∗ WP es1 @ Stuckness.NotStuck ; E {{ w, Ψ w ∗ ↪[frame] f1 }}) ∗
      ∀ w, Ψ w ∗ ↪[frame] f0 -∗ WP (ofVal w ++ es2) @ s ; E FRAME n ; f1 CTX i ; lh {{ v, Φ v }})
      ⊢ WP (es1 ++ es2) @ s ; E FRAME n ; f CTX i ; lh {{ v, Φ v }} := by
  let := @WasmG.invGS hlc GF _
  unfold wpWasmCtxFrame
  iintro ⟨Hn, Hf0, H1, H2⟩
  iloeb as IH generalizing %es1 %f %hnone
  iintro %LI %hfill
  have hLI : Iris.ProgramLogic.toVal [AdministrativeInstruction.local n f LI] = none :=
    hnone LI hfill
  iapply wp_unfold_w.2
  simp only [IrisWp.wp.pre, hLI]
  iintro %σ %ns %obs %obs' %nt Hσ
  rcases σ with ⟨ws, locs, inst⟩
  rcases f with ⟨fl, fi⟩
  imod frame_update ws locs inst f0 ⟨fl, fi⟩ $$ Hσ Hf0 with ⟨%hf0, Hσ, Hf⟩
  subst hf0
  ihave H1 := H1 $$ Hf
  cases hes : toVal es1 with
  | some w =>
    obtain rfl := of_to_val _ _ hes
    ihave H1 := (IrisWp.wp_value_fupd' (ι := wasmIrisGS) frameP).1 $$ H1
    imod H1 with ⟨HΨ, Hf1⟩
    imod frame_update ws fl fi f1 ⟨locs, inst⟩ $$ Hσ Hf1 with ⟨%hf1, Hσ, Hf0⟩
    subst hf1
    ihave H2 := H2 $$ [HΨ Hf0] %LI %hfill
    · isplitl [HΨ]
      · iexact HΨ
      · iexact Hf0
    ihave H2 := wp_unfold_w.1 $$ H2
    isimp only [IrisWp.wp.pre, hLI] at H2
    iapply H2 $$ %(ws, locs, inst) %ns %obs %obs' %nt Hσ
  | none =>
    have hes' : Iris.ProgramLogic.toVal es1 = none := hes
    ihave H1 := wp_unfold_w.1 $$ H1
    isimp only [IrisWp.wp.pre, hes'] at H1
    imod H1 $$ %(ws, fl, fi) %ns %obs %obs' %nt Hσ with ⟨%Hred, H1⟩
    imodintro
    isplit
    · ipureintro
      cases s
      · exact local_frame_lfilled_reducible n locs inst hfill (append_reducible es1 es2 _ hes Hred)
      · trivial
    · iintro %e₂ %σ₂ %eₜ %HStep Hcr
      rcases σ₂ with ⟨ws', locs', inst'⟩
      have HStep : primStep ([.local n ⟨fl, fi⟩ LI], (ws, locs, inst)) obs
          (e₂, (ws', locs', inst'), eₜ) := HStep
      obtain ⟨rfl, rfl⟩ : obs = [] ∧ eₜ = [] := by
        have := prim_step_obs_efs_empty HStep; simp_all
      rcases local_frame_lfilled_prim_step_split_reduce_r es1 es2 ws fl fi n locs inst e₂ ws' locs'
          inst' [] [] i lh LI hfill Hred HStep with
        ⟨e', v'', i'', LI', HStep2, rfl, rfl, rfl, hfill2⟩ | ⟨lh0, hl, heq⟩
      · dsimp only [step_fupdN]
        imod H1 $$ %e' %(ws', v'', i'') %([] : List Expr) %HStep2 Hcr with H1
        iintro !> !>
        imod H1
        iintro !>
        iapply step_fupdN_wand $$ H1
        iintro >⟨Hσ, %a, Ha, Hwp, -⟩
        cases he' : toVal e' with
        | some w =>
          obtain rfl := of_to_val _ _ he'
          ihave H := Hwp $$ Ha
          ihave H := (IrisWp.wp_value_fupd' (ι := wasmIrisGS) frameP).1 $$ H
          imod H with ⟨HΨ, Hf1⟩
          imod frame_update ws' v'' i'' f1 ⟨locs, inst⟩ $$ Hσ Hf1 with ⟨%hf1, Hσ, Hfo⟩
          subst hf1
          imodintro
          isplitl [Hσ]
          · iexact Hσ
          iexists ⟨locs, inst⟩
          isplitl [Hfo]
          · iexact Hfo
          isplitl
          · iintro Hfo
            iapply H2 $$ [HΨ Hfo] %LI' %hfill2
            isplitl [HΨ]
            · iexact HΨ
            · iexact Hfo
          · iapply BI.BigSepL.bigSepL_nil.2
            iempintro
        | none =>
          imod frame_update ws' v'' i'' a ⟨locs, inst⟩ $$ Hσ Ha with ⟨%ha, Hσ, Hfo⟩
          subst ha
          have hnone' : ∀ LI, lfilled i lh (e' ++ es2) LI = true →
              toVal [AdministrativeInstruction.local n ⟨v'', i''⟩ LI] = none := by
            intro LI0 h0
            obtain rfl := lfilled_inj h0 hfill2
            obtain ⟨sh, rfl⟩ := lfilled_to_sfill i lh _ _ h0
            obtain ⟨vh, hvh⟩ := sfill_nested sh (.base [] es2) e'
            have h3 := to_val_local_none_inv n ⟨v'', i''⟩ e' (llOfSh vh) he'
              (to_val_local_none_none n _ e' he')
            rw [← sfill_to_llfill, ← hvh] at h3
            simpa [sfill, vToEList] using h3
          imodintro
          isplitl [Hσ]
          · iexact Hσ
          iexists ⟨locs, inst⟩
          isplitl [Hfo]
          · iexact Hfo
          isplitl
          · iintro Hfo
            iapply IH $$ %e' %⟨v'', i''⟩ %hnone' Hn Hfo Hwp H2 %LI' %hfill2
          · iapply BI.BigSepL.bigSepL_nil.2
            iempintro
      · simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        dsimp only [step_fupdN]
        imod H1 $$ %([AdministrativeInstruction.trap] : Expr) %(ws, fl, fi) %([] : List Expr)
          %(trap_step hes hl _) Hcr with H1
        iintro !> !>
        imod H1
        iintro !>
        iapply step_fupdN_wand $$ H1
        iintro >⟨Hσ, %a, Ha, Hwp, -⟩
        ihave H := Hwp $$ Ha
        have e : (WP [AdministrativeInstruction.trap] @ Stuckness.NotStuck ; E {{ w, Ψ w ∗ ↪[frame] f1 }} :
            IProp GF) ⊣⊢ |={E}=> (Ψ .trapV ∗ ↪[frame] f1) :=
          IrisWp.wp_value_fupd' (ι := wasmIrisGS) frameP (v := .trapV)
        ihave H := e.1 $$ H
        imod H with ⟨HΨ, -⟩
        iexfalso
        iapply Hn $$ HΨ

private theorem lfilled_empty {e LI : Expr} : lfilled 0 (.base [] []) e LI = true ↔ LI = e := by
  simp [lfilled, lfill, constList]

@[rocq_alias iriswasm.wp_wasm_empty_ctx]
theorem wp_wasm_empty_ctx (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF) (e : Expr) :
    ⊢ WP e @ s ; E {{ Φ }} ∗-∗ WP e @ s ; E CTX_EMPTY {{ Φ }} := by
  unfold wpWasmCtx
  isplit
  · iintro H %LI %hLI
    rw [lfilled_empty.1 hLI]
    iexact H
  · iintro H
    iapply H $$ %e %(lfilled_empty.2 rfl)

@[rocq_alias iriswasm.wp_wasm_empty_ctx_frame]
theorem wp_wasm_empty_ctx_frame (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF) (e : Expr)
    (n : Nat) (f : Frame) :
    ⊢ WP e @ s ; E FRAME n ; f {{ Φ }} ∗-∗ WP e @ s ; E FRAME n ; f CTX_EMPTY {{ v, Φ v }} := by
  unfold wpWasmCtxFrame wpWasmFrame
  isplit
  · iintro H %LI %hLI
    rw [lfilled_empty.1 hLI]
    iexact H
  · iintro H
    iapply H $$ %e %(lfilled_empty.2 rfl)

@[rocq_alias iriswasm.wp_nil]
theorem wp_nil (s : Stuckness) (E : CoPset) (Φ : IProp GF) (f : Frame) :
    iprop(↪[frame] f ∗ Φ) ⊢ WP [] @ s ; E CTX_EMPTY {{ fun _ => Φ }} := by
  let := @WasmG.invGS hlc GF _
  have e : (WP ([] : Expr) @ s ; E {{ fun _ => Φ }} : IProp GF) ⊣⊢ |={E}=> Φ :=
    IrisWp.wp_value_fupd' (ι := wasmIrisGS) frameP (v := .immV [])
  iintro ⟨-, H⟩
  ihave W := wp_wasm_empty_ctx s E (fun _ => Φ) []
  icases W with ⟨W, -⟩
  iapply W
  iapply e.2
  imodintro
  iexact H

@[rocq_alias iriswasm.wp_wand_ctx]
theorem wp_wand_ctx (s : Stuckness) (E : CoPset) (e : Expr) (Φ Ψ : Val → IProp GF) (i : Nat)
    (lh : Lholed) :
    ⊢ WP e @ s ; E CTX i ; lh {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s ; E CTX i ; lh {{ Ψ }} := by
  unfold wpWasmCtx
  iintro Hwp H %LI %hLI
  iapply IrisWp.wp_wand (ι := wasmIrisGS) frameP $$ [Hwp] H
  iapply Hwp $$ %LI %hLI

@[rocq_alias iriswasm.wp_frame_seq]
theorem wp_frame_seq (es1 es2 : Expr) (n : Nat) (f0 f f' : Frame) (E : CoPset) (s : Stuckness)
    (Ψ Φ : Val → IProp GF) (hnone : toVal [.local n f (es1 ++ es2)] = none) :
    ⊢ (¬ Ψ .trapV) -∗ ↪[frame] f0 -∗
      (↪[frame] f -∗ WP es1 @ Stuckness.NotStuck ; E {{ v, Ψ v ∗ ↪[frame] f' }}) -∗
      (∀ w, ↪[frame] f0 -∗ Ψ w -∗
        WP (ofVal w ++ es2) @ s ; E FRAME n ; f' {{ v, Φ v ∗ ↪[frame] f0 }}) -∗
      WP (es1 ++ es2) @ s ; E FRAME n ; f {{ v, Φ v ∗ ↪[frame] f0 }} := by
  have hseq := wp_seq_ctx_frame s E (fun v => iprop(Φ v ∗ ↪[frame] f0)) Ψ es1 es2 0
    (.base [] []) n f f0 f' (fun LI h => by rw [lfilled_empty.1 h]; exact hnone)
  iintro Hn Hf0 H1 H2
  ihave W := wp_wasm_empty_ctx_frame s E (fun v => iprop(Φ v ∗ ↪[frame] f0)) (es1 ++ es2) n f
  icases W with ⟨-, W⟩
  iapply W
  iapply hseq
  isplitl [Hn]
  · iexact Hn
  isplitl [Hf0]
  · iexact Hf0
  isplitl [H1]
  · iexact H1
  iintro %w ⟨HΨ, Hf0⟩
  ihave W := wp_wasm_empty_ctx_frame s E (fun v => iprop(Φ v ∗ ↪[frame] f0)) (ofVal w ++ es2) n f'
  icases W with ⟨W, -⟩
  iapply W
  iapply H2 $$ Hf0 HΨ

end IrisWasm
