/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Rules.IrisRulesControl
import IrisWasm.Rules.IrisRulesBind
import IrisWasm.Rules.IrisRulesStructural
import IrisWasm.Helpers.Prelude.IrisWasmLangProperties
import IrisWasm.Helpers.Prelude.IrisSplitReduce
import IrisWasm.Helpers.IrisPrimStepSplit
import IrisWasm.Helpers.IrisWasmDeterm
import IrisWasm.Helpers.Prelude.IrisReduceProperties
import IrisWasm.Helpers.Prelude.IrisReduceDetPrelude

/-! Port of `theories/iris/rules/iris_rules_trap.v`. -/

namespace IrisWasm

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm

variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF]

-- statements below use fancy updates, which need the (non-instance) `WasmG.invGS`
set_option warn.classDefReducibility false
attribute [local instance] WasmG.invGS

private theorem wp_trap_value {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF} :
    Φ .trapV ⊢ WP ([.trap] : Expr) @ s ; E {{ Φ }} :=
  IrisWp.wp_value (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) ⟨rfl⟩

private theorem si_frame_agree {ws : StoreRecord} {locs : List Value} {inst : Instance}
    {f : Frame} :
    ⊢ (stateInterp (ws, locs, inst) -∗ ↪[frame] f -∗ ⌜f = ⟨locs, inst⟩⌝ : IProp GF) := by
  simp only [IrisWasm.stateInterp]
  unfold frameOwn
  iintro ⟨-, -, -, -, Ha, -⟩ Hf
  ihave %h := ghost_map_lookup $$ Ha Hf
  ipureintro
  rw [get?_insert_eq rfl] at h
  exact (Option.some.inj h).symm

local notation "wpU" => IrisWp.wp_unfold (ι := wasmIrisGS) (fun f => iprop(↪[frame] f))

@[rocq_alias iriswasm.wp_trap]
theorem wp_trap (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF) (vs1 es2 : Expr) (f : Frame) :
    constList vs1 = true →
    ⊢ (Φ .trapV -∗ ↪[frame] f -∗
      WP (vs1 ++ [.trap] ++ es2) @ s ; E {{ v, Φ v ∗ ↪[frame] f }} : IProp GF) := by
  intro hc
  let := @WasmG.invGS hlc GF _
  iloeb as IH generalizing %vs1 %es2 %hc
  iintro HΦ Hf
  by_cases hne : vs1 ≠ [] ∨ es2 ≠ []
  · have hv := to_val_not_trap_interweave _ _ hc hne
    have hfill : lfilled 0 (.base vs1 es2) [.trap] (vs1 ++ [.trap] ++ es2) = true :=
      (lfilled_Ind_Equivalent _ _ _ _).2 (.lfilledBase _ _ _ hc)
    have hneq : vs1 ++ [.trap] ++ es2 ≠ [.trap] := by
      intro h; rw [h] at hv; simp [toVal, mergeValuesList, toValInstr, mergeValues] at hv
    iapply IrisWp.wp_lift_step (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) hv
    iintro %σ %ns %obs %obs' %nt Hσ
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hcls
    rcases σ with ⟨ws, locs, inst⟩
    isplitr
    · ipureintro
      cases s <;> simp only [Stuckness.MaybeReducible]
      exact ⟨[], [.trap], (ws, locs, inst), [], .simple (.trap _ hneq hfill), rfl, rfl⟩
    inext
    iintro %e₂ %σ₂ %eₜ %Hstep -
    rcases σ₂ with ⟨ws', locs', inst'⟩
    obtain ⟨H, rfl, rfl⟩ := Hstep
    obtain ⟨lh', hfill', heq⟩ := trap_reduce hfill H
    simp only [Prod.mk.injEq, Frame.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    obtain ⟨bef, aft, -, hc', rfl⟩ := IrisWasm.Helpers.ReduceDetPrelude.lfilled0 hfill'
    imod Hcls
    imodintro
    iframe Hσ
    iexists f
    iframe Hf
    isplitl
    · iintro Hf
      iapply IH $$ %bef %aft %hc' HΦ Hf
    · simp; iempintro
  · simp only [not_or, Decidable.not_not] at hne
    obtain ⟨rfl, rfl⟩ := hne
    simp only [List.nil_append, List.append_nil]
    iapply wp_trap_value
    iframe

@[rocq_alias iriswasm.wp_seq_trap]
theorem wp_seq_trap (s : Stuckness) (E : CoPset) (es1 es2 : Expr) (f f' : Frame) :
    (iprop(↪[frame] f ∗
      (↪[frame] f -∗ WP es1 @ s ; E {{ w, ⌜w = .trapV⌝ ∗ ↪[frame] f' }})) : IProp GF)
    ⊢ WP (es1 ++ es2) @ s ; E {{ w, ⌜w = .trapV⌝ ∗ ↪[frame] f' }} := by
  let := @WasmG.invGS hlc GF _
  iintro ⟨Hf, H⟩
  irevert Hf H
  iloeb as IH generalizing %es1 %es2 %f
  iintro Hf H
  ihave H := H $$ Hf
  cases he : toVal es1 with
  | some v =>
    ihave H := (IrisWp.wp_value_fupd (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
      ⟨of_to_val _ _ he⟩).1 $$ H
    iapply IrisWp.fupd_wp (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
    imod H with ⟨%hv, Hf⟩
    subst hv
    rw [to_val_trap_is_singleton _ he]
    imodintro
    have := wp_trap (GF := GF) s E (fun w => iprop(⌜w = .trapV⌝)) [] es2 f' rfl
    simp only [List.nil_append] at this
    iapply this $$ [] Hf
    ipureintro; trivial
  | none =>
    have hnv : Iris.ProgramLogic.toVal (es1 ++ es2 : Expr) = none := to_val_cat_None1 _ _ he
    have he' : Iris.ProgramLogic.toVal es1 = none := he
    iapply wpU.2
    ihave H := wpU.1 $$ H
    simp only [IrisWp.wp.pre, hnv, he']
    iintro %σ %ns %obs %obs' %nt Hσ
    rcases σ with ⟨ws, locs, inst⟩
    icases H $$ %(ws, locs, inst) %ns %obs %obs' %nt Hσ with >⟨%Hred, H⟩
    imodintro
    isplitr
    · ipureintro
      cases s <;> simp only [Stuckness.MaybeReducible] at Hred ⊢
      exact append_reducible _ _ _ he Hred
    iintro %e₂ %σ₂ %eₜ %Hstep Hc
    rcases σ₂ with ⟨ws', locs', inst'⟩
    obtain ⟨Hst, rfl, rfl⟩ := Hstep
    rcases prim_step_split_reduce_r es1 es2 e₂ (ws, locs, inst) (ws', locs', inst') [] []
      he ⟨Hst, rfl, rfl⟩ with ⟨es'', rfl, Hst'⟩ | ⟨n, m, lh, hfill, hfill1, hσ⟩
    · dsimp only [step_fupdN]
      imod H $$ %es'' %(ws', locs', inst') %([] : List Expr) %Hst' Hc with H
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
        iapply IH $$ %es'' %es2 %a Ha H
      · simp; iempintro
    · simp only [Prod.mk.injEq] at hσ
      obtain ⟨h1, h2, h3⟩ := hσ
      subst ws' locs' inst'
      obtain ⟨bef, aft, -, hc, rfl⟩ := IrisWasm.Helpers.ReduceDetPrelude.lfilled0 hfill1
      have hneq : bef ++ [.trap] ++ aft ≠ [.trap] := by
        intro h; rw [h] at he; simp [toVal, mergeValuesList, toValInstr, mergeValues] at he
      have Hst' : primStep (bef ++ [.trap] ++ aft, ws, locs, inst) [] ([.trap], (ws, locs, inst), []) :=
        ⟨.simple (.trap _ hneq ((lfilled_Ind_Equivalent _ _ _ _).2 (.lfilledBase _ _ _ hc))), rfl, rfl⟩
      obtain ⟨bef', aft', -, hc', rfl⟩ := IrisWasm.Helpers.ReduceDetPrelude.lfilled0 hfill
      dsimp only [step_fupdN]
      imod H $$ %([.trap] : Expr) %(ws, locs, inst) %([] : List Expr) %Hst' Hc with H
      iintro !> !>
      imod H
      iintro !>
      iapply step_fupdN_wand $$ H
      iintro >⟨Hσ, %a, Ha, H, -⟩
      ihave %ha : ⌜a = ⟨locs, inst⟩⌝ $$ [Hσ Ha]
      · iapply si_frame_agree $$ Hσ Ha
      ihave H := H $$ Ha
      ihave H := (IrisWp.wp_value_fupd (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
        (e := [.trap]) (v := .trapV) ⟨rfl⟩).1 $$ H
      imod H with ⟨-, Hf⟩
      ihave %hf : ⌜f' = ⟨locs, inst⟩⌝ $$ [Hσ Hf]
      · iapply si_frame_agree $$ Hσ Hf
      subst ha hf
      imodintro
      iframe Hσ
      iexists ⟨locs, inst⟩
      iframe Hf
      isplitl
      · iintro Hf
        iapply wp_trap s E (fun w => iprop(⌜w = .trapV⌝)) bef' aft' _ hc' $$ [] Hf
        ipureintro; rfl
      · simp; iempintro

@[rocq_alias iriswasm.wp_val_trap]
theorem wp_val_trap (s : Stuckness) (E : CoPset) (v0 : Value) (es1 : Expr) (f f' : Frame) :
    (iprop(↪[frame] f ∗
      (↪[frame] f -∗ WP es1 @ Stuckness.NotStuck ; E {{ w, ⌜w = .trapV⌝ ∗ ↪[frame] f' }}))
      : IProp GF)
    ⊢ WP (.basic (.const v0) :: es1) @ s ; E {{ w, ⌜w = .trapV⌝ ∗ ↪[frame] f' }} := by
  iintro ⟨Hf, H⟩
  irevert Hf H
  iloeb as IH generalizing %v0 %es1 %f
  iintro Hf H
  ihave H := H $$ Hf
  cases he : toVal es1 with
  | some v =>
    ihave H := (IrisWp.wp_value_fupd (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
      ⟨of_to_val _ _ he⟩).1 $$ H
    iapply IrisWp.fupd_wp (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
    imod H with ⟨%hv, Hf⟩
    subst hv
    rw [to_val_trap_is_singleton _ he]
    imodintro
    have := wp_trap (GF := GF) s E (fun w => iprop(⌜w = .trapV⌝)) [.basic (.const v0)] [] f' rfl
    simp only [List.append_nil, List.cons_append, List.nil_append] at this
    iapply this $$ [] Hf
    ipureintro; trivial
  | none =>
    have hnv : Iris.ProgramLogic.toVal (.basic (.const v0) :: es1 : Expr) = none :=
      to_val_cons_None _ _ he
    have he' : Iris.ProgramLogic.toVal es1 = none := he
    iapply wpU.2
    ihave H := wpU.1 $$ H
    simp only [IrisWp.wp.pre, hnv, he']
    iintro %σ %ns %obs %obs' %nt Hσ
    rcases σ with ⟨ws, locs, inst⟩
    icases H $$ %(ws, locs, inst) %ns %obs %obs' %nt Hσ with >⟨%Hred, H⟩
    imodintro
    isplitr
    · ipureintro
      simp only [Stuckness.MaybeReducible] at Hred
      cases s <;> simp only [Stuckness.MaybeReducible]
      exact prepend_reducible [.basic (.const v0)] es1 _ (.inl rfl) Hred
    iintro %e₂ %σ₂ %eₜ %Hstep Hc
    rcases σ₂ with ⟨ws', locs', inst'⟩
    obtain ⟨Hst, rfl, rfl⟩ := Hstep
    simp only [Stuckness.MaybeReducible] at Hred
    rcases reduce_ves v0 es1 e₂ (ws, locs, inst) (ws', locs', inst') [] [] Hred
      ⟨Hst, rfl, rfl⟩ with ⟨he₂, Hst'⟩ | ⟨lh, lh', hfill, hfill1, hσ⟩
    · generalize e₂.drop 1 = e' at he₂ Hst'
      subst he₂
      dsimp only [step_fupdN]
      imod H $$ %e' %(ws', locs', inst') %([] : List Expr) %Hst' Hc with H
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
        simp only [List.cons_append, List.nil_append]
        iapply IH $$ %v0 %e' %a Ha H
      · simp; iempintro
    · simp only [Prod.mk.injEq] at hσ
      obtain ⟨h1, h2, h3⟩ := hσ
      subst ws' locs' inst'
      obtain ⟨bef, aft, -, hc, rfl⟩ := IrisWasm.Helpers.ReduceDetPrelude.lfilled0 hfill1
      have hneq : bef ++ [.trap] ++ aft ≠ [.trap] := by
        intro h; rw [h] at he; simp [toVal, mergeValuesList, toValInstr, mergeValues] at he
      have Hst' : primStep (bef ++ [.trap] ++ aft, ws, locs, inst) [] ([.trap], (ws, locs, inst), []) :=
        ⟨.simple (.trap _ hneq ((lfilled_Ind_Equivalent _ _ _ _).2 (.lfilledBase _ _ _ hc))), rfl, rfl⟩
      obtain ⟨bef', aft', -, hc', rfl⟩ := IrisWasm.Helpers.ReduceDetPrelude.lfilled0 hfill
      dsimp only [step_fupdN]
      imod H $$ %([.trap] : Expr) %(ws, locs, inst) %([] : List Expr) %Hst' Hc with H
      iintro !> !>
      imod H
      iintro !>
      iapply step_fupdN_wand $$ H
      iintro >⟨Hσ, %a, Ha, H, -⟩
      ihave H := H $$ Ha
      ihave H := (IrisWp.wp_value_fupd (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
        (e := [.trap]) (v := .trapV) ⟨rfl⟩).1 $$ H
      imod H with ⟨-, Hf⟩
      imodintro
      iframe Hσ
      iexists f'
      iframe Hf
      isplitl
      · iintro Hf
        iapply wp_trap s E (fun w => iprop(⌜w = .trapV⌝)) bef' aft' _ hc' $$ [] Hf
        ipureintro; rfl
      · simp; iempintro



@[rocq_alias iriswasm.wp_val_app_trap']
theorem wp_val_app_trap' (s : Stuckness) (E : CoPset) (vs : List Value) (es : Expr)
    (f f' : Frame) :
    (iprop(↪[frame] f ∗
      (↪[frame] f -∗ WP es @ Stuckness.NotStuck ; E {{ w, ⌜w = .trapV⌝ ∗ ↪[frame] f' }}))
      : IProp GF)
    ⊢ WP (vToEList vs ++ es) @ s ; E {{ w, ⌜w = .trapV⌝ ∗ ↪[frame] f' }} := by
  induction vs generalizing s with
  | nil =>
    simp only [vToEList, List.map_nil, List.nil_append]
    iintro ⟨Hf, H⟩
    ihave H := H $$ Hf
    cases s
    · iexact H
    · iapply IrisWp.wp_stuck_weaken (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ H
  | cons c vs ih =>
    rw [show vToEList (c :: vs) = .basic (.const c) :: vToEList vs from rfl, List.cons_append]
    iintro ⟨Hf, H⟩
    iapply wp_val_trap
    isplitl [Hf]
    · iexact Hf
    iintro Hf
    iapply ih .NotStuck
    isplitl [Hf]
    · iexact Hf
    iexact H

@[rocq_alias iriswasm.wp_val_app_trap]
theorem wp_val_app_trap (s : Stuckness) (E : CoPset) (vs : Expr) (v' : List Value) (es : Expr)
    (f f' : Frame) :
    toVal vs = some (.immV v') →
    (iprop(↪[frame] f ∗
      (↪[frame] f -∗ WP es @ Stuckness.NotStuck ; E {{ w, ⌜w = .trapV⌝ ∗ ↪[frame] f' }}))
      : IProp GF)
    ⊢ WP (vs ++ es) @ s ; E {{ w, ⌜w = .trapV⌝ ∗ ↪[frame] f' }} := by
  intro h
  rw [← of_to_val _ _ h]
  exact wp_val_app_trap' s E v' es f f'


namespace IrisRulesTrap

/-- Same Coq name as `IrisWasm.wp_label_trap` (`iris_rules_control.v`). -/
@[rocq_alias iriswasm.iris_rules_trap.wp_label_trap]
theorem wp_label_trap (s : Stuckness) (E : CoPset) (LI vs : Expr) (n : Nat) (es' es'' : Expr)
    (f f' : Frame) :
    constList vs = true →
    ⊢ (↪[frame] f -∗
      (↪[frame] f -∗ WP LI @ E {{ w, ⌜w = .trapV⌝ ∗ ↪[frame] f' }}) -∗
      WP (vs ++ [.label n es' LI] ++ es'') @ s ; E {{ w, ⌜w = .trapV⌝ ∗ ↪[frame] f' }}
      : IProp GF) := by
  intro hc
  let := @WasmG.invGS hlc GF _
  iloeb as IH generalizing %vs %LI %n %es' %f %es'' %s %hc
  iintro Hf Hcont
  obtain ⟨v, hv⟩ := const_list_to_val vs hc
  rw [List.append_assoc]
  iapply wp_val_app_trap s E vs v ([AdministrativeInstruction.label n es' LI] ++ es'') f f' hv
  isplitl [Hf]
  · iexact Hf
  iintro Hf
  iapply wp_seq_trap .NotStuck E [AdministrativeInstruction.label n es' LI] es'' f f'
  isplitl [Hf]
  · iexact Hf
  iintro Hf
  ihave H := Hcont $$ Hf
  cases he : toVal LI with
  | some v =>
    ihave H := (IrisWp.wp_value_fupd (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
      ⟨of_to_val _ _ he⟩).1 $$ H
    iapply IrisWp.fupd_wp (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
    imod H with ⟨%hv, Hf⟩
    subst hv
    imodintro
    iapply IrisWasm.wp_label_trap (Φ := fun w => iprop(⌜w = .trapV⌝)) he $$ Hf
    inext; ipureintro; trivial
  | none =>
    have hnv : Iris.ProgramLogic.toVal ([.label n es' LI] : Expr) = none :=
      to_val_None_label _ _ _ he
    have he' : Iris.ProgramLogic.toVal LI = none := he
    have hfill : ∀ e, lfilled 1 (.rec_ [] n es' (.base [] []) []) (e ++ []) [.label n es' e] = true :=
      fun e => by
        rw [List.append_nil]
        exact IrisWasm.Helpers.ReduceDetPrelude.lfilled_label n es'
          (IrisWasm.Helpers.ReduceDetPrelude.lfilled_base.2 rfl)
    iapply wpU.2
    ihave H := wpU.1 $$ H
    simp only [IrisWp.wp.pre, hnv, he']
    iintro %σ %ns %obs %obs' %nt Hσ
    rcases σ with ⟨ws, locs, inst⟩
    icases H $$ %(ws, locs, inst) %ns %obs %obs' %nt Hσ with >⟨%Hred, H⟩
    imodintro
    simp only [Stuckness.MaybeReducible] at Hred ⊢
    isplitr
    · ipureintro
      exact lfilled_reducible (hfill LI) (by simpa using Hred)
    iintro %e₂ %σ₂ %eₜ %Hstep Hc
    rcases σ₂ with ⟨ws', locs', inst'⟩
    obtain ⟨Hst, rfl, rfl⟩ := Hstep
    rcases lfilled_prim_step_split_reduce_r 1 _ LI [] (ws, locs, inst) _ e₂ (ws', locs', inst') [] []
      (hfill LI) (by simpa using Hred) ⟨Hst, rfl, rfl⟩ with ⟨e', Hst', hfill'⟩ | ⟨⟨lh, hlh⟩, hσ⟩
    · have := lfilled_inj hfill' (hfill e')
      subst this
      dsimp only [step_fupdN]
      imod H $$ %e' %(ws', locs', inst') %([] : List Expr) %Hst' Hc with H
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
        rw [← List.nil_append [AdministrativeInstruction.label n es' e'],
          ← List.append_nil ([] ++ [AdministrativeInstruction.label n es' e'])]
        iapply IH $$ %([] : Expr) %e' %n %es' %a %([] : Expr) %Stuckness.NotStuck %rfl Ha H
      · simp; iempintro
    · simp only [Prod.mk.injEq] at hσ
      obtain ⟨h1, h2, h3⟩ := hσ
      subst ws' locs' inst'
      obtain ⟨lh'', hlh''⟩ := lfilled_trans hlh (by simpa only [List.append_nil] using hfill LI)
      obtain ⟨⟨lh', j, hj, hle⟩, -⟩ := trap_reduce_nested hlh'' Hst
      obtain ⟨bef, aft, -, hcb, rfl⟩ := IrisWasm.Helpers.ReduceDetPrelude.lfilled0 hlh
      have hneq : bef ++ [.trap] ++ aft ≠ [.trap] := by
        intro h; rw [h] at he; simp [toVal, mergeValuesList, toValInstr, mergeValues] at he
      have Hst' : primStep (bef ++ [.trap] ++ aft, ws, locs, inst) [] ([.trap], (ws, locs, inst), []) :=
        ⟨.simple (.trap _ hneq ((lfilled_Ind_Equivalent _ _ _ _).2 (.lfilledBase _ _ _ hcb))), rfl, rfl⟩
      dsimp only [step_fupdN]
      imod H $$ %([.trap] : Expr) %(ws, locs, inst) %([] : List Expr) %Hst' Hc with H
      iintro !> !>
      imod H
      iintro !>
      iapply step_fupdN_wand $$ H
      iintro >⟨Hσ, %a, Ha, H, -⟩
      ihave H := H $$ Ha
      ihave H := (IrisWp.wp_value_fupd (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
        (e := [.trap]) (v := .trapV) ⟨rfl⟩).1 $$ H
      imod H with ⟨-, Hf⟩
      imodintro
      iframe Hσ
      iexists f'
      iframe Hf
      isplitl
      · iintro Hf
        match j, hj, hle with
        | 0, hj, _ =>
          obtain ⟨bef', aft', -, hc', rfl⟩ := IrisWasm.Helpers.ReduceDetPrelude.lfilled0 hj
          iapply wp_trap .NotStuck E (fun w => iprop(⌜w = .trapV⌝)) bef' aft' _ hc' $$ [] Hf
          ipureintro; rfl
        | 1, hj, _ =>
          obtain ⟨bef', n', es0, lh0, aft', LI0, -, hc', hf0, rfl⟩ :=
            IrisWasm.Helpers.ReduceDetPrelude.lfilledS hj
          obtain ⟨b2, a2, -, hc2, rfl⟩ := IrisWasm.Helpers.ReduceDetPrelude.lfilled0 hf0
          rw [show bef' ++ AdministrativeInstruction.label n' es0 (b2 ++ [.trap] ++ a2) :: aft' =
            bef' ++ [.label n' es0 (b2 ++ [.trap] ++ a2)] ++ aft' by simp]
          iapply IH $$ %bef' %(b2 ++ [.trap] ++ a2) %n' %es0 %f' %aft' %Stuckness.NotStuck %hc' Hf
          iintro Hf
          iapply wp_trap .NotStuck E (fun w => iprop(⌜w = .trapV⌝)) b2 a2 _ hc2 $$ [] Hf
          ipureintro; rfl
        | j + 2, _, hle => omega
      · simp; iempintro


end IrisRulesTrap

@[rocq_alias iriswasm.reduce_det_local_trap]
theorem reduce_det_local_trap (ws : StoreRecord) (f : Frame) (ws' : StoreRecord) (f' : Frame)
    (es2 : Expr) (n : Nat) (f0 : Frame) :
    Reduce ws f [.local n f0 [.trap]] ws' f' es2 → es2 = [.trap] ∧ ws = ws' ∧ f = f' := by
  intro h
  rcases IrisWasm.Helpers.ReduceDetPrelude.inv_local h with
    ⟨rfl, rfl, ⟨hc, -⟩ | ⟨-, rfl⟩ | ⟨i, lh, vs, -, -, hfill, -⟩⟩ | ⟨_, _, h', -⟩
  · simp [constList, isConst] at hc
  · exact ⟨rfl, rfl, rfl⟩
  · cases i with
    | zero =>
      obtain ⟨bef, aft, -, -, he⟩ := IrisWasm.Helpers.ReduceDetPrelude.lfilled0 hfill
      have := congrArg (AdministrativeInstruction.basic .return_ ∈ ·) he; simp at this
    | succ i =>
      obtain ⟨bef, n', es0, lh', aft, LI0, -, -, -, he⟩ := IrisWasm.Helpers.ReduceDetPrelude.lfilledS hfill
      have := congrArg (AdministrativeInstruction.label n' es0 LI0 ∈ ·) he; simp at this
  · exact (IrisWasm.test_no_reduce_trap h').elim

@[rocq_alias iriswasm.wp_frame_trap]
theorem wp_frame_trap (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF) (n : Nat) (f f0 : Frame) :
    ⊢ (↪[frame] f0 -∗ ▷ Φ .trapV -∗
      WP ([.trap] : Expr) @ s ; E FRAME n ; f {{ v, Φ v ∗ ↪[frame] f0 }} : IProp GF) := by
  let := @WasmG.invGS hlc GF _
  unfold wpWasmFrame
  iintro Hf HΦ
  iapply IrisWp.wp_lift_atomic_step (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
    (show IrisWasm.toVal [.local n f [.trap]] = none by
      rw [toVal_singleton, toValInstr_local, show toVal [.trap] = some .trapV from to_of_val .trapV]
      rfl) f0
  iintro %σ %ns %obs %obs' %nt Hσ !>
  rcases σ with ⟨ws, locs, inst⟩
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact ⟨[], [.trap], (ws, locs, inst), [], .simple .localTrap, rfl, rfl⟩
  iintro !> %e₂ %σ₂ %eₜ %Hstep Hcr
  rcases σ₂ with ⟨ws', locs', inst'⟩
  obtain ⟨H, rfl, rfl⟩ := Hstep
  obtain ⟨rfl, rfl, h⟩ := reduce_det_local_trap _ _ _ _ _ _ _ H
  injection h with h1 h2
  subst h1 h2
  imodintro
  iframe
  isplitl
  · ipureintro; exact to_of_val .trapV
  · simp; exact .rfl

@[rocq_alias iriswasm.wp_frame_trap_nested]
theorem wp_frame_trap_nested (s : Stuckness) (E : CoPset) (n : Nat) (f f0 : Frame) (LI : Expr)
    (f' : Frame) :
    toVal [.local n f LI] = none →
    ⊢ (↪[frame] f0 -∗
      (↪[frame] f -∗ WP LI @ s ; E {{ w, ⌜w = .trapV⌝ ∗ ↪[frame] f' }}) -∗
      WP LI @ s ; E FRAME n ; f {{ w, ⌜w = .trapV⌝ ∗ ↪[frame] f0 }} : IProp GF) := by
  intro hnone
  iintro Hf0 H
  iapply wp_frame_bind s E (fun w => iprop(⌜w = .trapV⌝ ∗ ↪[frame] f0)) n f f0 LI hnone $$ Hf0
  iintro Hf
  ihave H := H $$ Hf
  iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ H
  iintro %w ⟨%hw, Hf'⟩
  subst hw
  iexists f'
  iframe Hf'
  iintro Hf0
  rw [show ofVal Val.trapV = [AdministrativeInstruction.trap] from rfl]
  iapply wp_frame_trap s E (fun w => iprop(⌜w = .trapV⌝)) n f' f0 $$ Hf0
  inext; ipureintro; trivial


@[rocq_alias iriswasm.wp_seq_trap_ctx]
theorem wp_seq_trap_ctx (s : Stuckness) (E : CoPset) (es1 es2 : Expr) (f f' : Frame) (i : Nat)
    (lh : Lholed) :
    (iprop(↪[frame] f ∗
      (↪[frame] f -∗ WP es1 @ Stuckness.NotStuck ; E {{ w, ⌜w = .trapV⌝ ∗ ↪[frame] f' }}))
      : IProp GF)
    ⊢ WP (es1 ++ es2) @ s ; E CTX i ; lh {{ w, ⌜w = .trapV⌝ ∗ ↪[frame] f' }} := by
  induction i generalizing s lh with
  | zero =>
    unfold wpWasmCtx
    iintro ⟨Hf, Hes1⟩ %LI %hfill
    obtain ⟨bef, aft, rfl, hc, rfl⟩ := IrisWasm.Helpers.ReduceDetPrelude.lfilled0 hfill
    obtain ⟨v, hv⟩ := const_list_to_val bef hc
    iapply wp_seq_trap s E (bef ++ (es1 ++ es2)) aft f f'
    isplitl [Hf]
    · iexact Hf
    iintro Hf
    iapply wp_val_app_trap s E bef v (es1 ++ es2) f f' hv
    isplitl [Hf]
    · iexact Hf
    iintro Hf
    iapply wp_seq_trap .NotStuck E es1 es2 f f'
    isplitl [Hf]
    · iexact Hf
    iexact Hes1
  | succ i ih =>
    unfold wpWasmCtx
    iintro ⟨Hf, Hes1⟩ %LI %hfill
    obtain ⟨bef, n, es0, lh', aft, LI0, rfl, hc, hf0, rfl⟩ :=
      IrisWasm.Helpers.ReduceDetPrelude.lfilledS hfill
    rw [show bef ++ AdministrativeInstruction.label n es0 LI0 :: aft =
      bef ++ [.label n es0 LI0] ++ aft by simp]
    iapply IrisRulesTrap.wp_label_trap s E LI0 bef n es0 aft f f' hc $$ Hf
    iintro Hf
    have H := ih .NotStuck lh'
    unfold wpWasmCtx at H
    ihave H := H $$ [Hf Hes1]
    · isplitl [Hf]
      · iexact Hf
      iexact Hes1
    iapply H $$ %LI0 %hf0

@[rocq_alias iriswasm.wp_trap_ctx]
theorem wp_trap_ctx (s : Stuckness) (E : CoPset) (f : Frame) (i : Nat) (lh : Lholed)
    (vs es : Expr) :
    constList vs = true →
    ⊢ (↪[frame] f -∗
      WP (vs ++ [.trap] ++ es) @ s ; E CTX i ; lh {{ v, ⌜v = .trapV⌝ ∗ ↪[frame] f }}
      : IProp GF) := by
  intro hc
  iintro Hf
  iapply wp_seq_trap_ctx s E (vs ++ [AdministrativeInstruction.trap]) es f f i lh
  isplitl [Hf]
  · iexact Hf
  iintro Hf
  have H := wp_trap (GF := GF) .NotStuck E (fun w => iprop(⌜w = .trapV⌝)) vs [] f hc
  rw [List.append_nil] at H
  iapply H $$ [] Hf
  ipureintro; trivial


/-- Sequencing rule which is always allowed to trap; useful for semantic type soundness. -/
@[rocq_alias iriswasm.wp_seq_can_trap_ctx]
theorem wp_seq_can_trap_ctx (s : Stuckness) (E : CoPset) (Φ Ψ : Val → IProp GF) (es1 es2 : Expr)
    (i : Nat) (lh : Lholed) (Φf : Frame → IProp GF) (f : Frame) :
    (iprop((Ψ .trapV ={E}=∗ ⌜False⌝) ∗ (∀ f, ↪[frame] f ∗ Φf f -∗ Φ .trapV) ∗ ↪[frame] f ∗
      (↪[frame] f -∗ WP es1 @ Stuckness.NotStuck ; E
        {{ w, (⌜w = .trapV⌝ ∨ Ψ w) ∗ ∃ f0, ↪[frame] f0 ∗ Φf f0 }}) ∗
      ∀ w f0, Ψ w ∗ ↪[frame] f0 ∗ Φf f0 -∗
        WP (ofVal w ++ es2) @ s ; E CTX i ; lh {{ v, Φ v }}) : IProp GF)
    ⊢ WP (es1 ++ es2) @ s ; E CTX i ; lh {{ v, Φ v }} := by
  unfold wpWasmCtx
  iintro ⟨Hntrap, Ht, Hf, Hes1, Hes2⟩
  irevert Hntrap Ht Hf Hes1 Hes2
  iloeb as IH generalizing %es1 %f
  iintro Hntrap Ht Hf Hes1 Hes2 %LI %hfill
  ihave H := Hes1 $$ Hf
  cases he : toVal es1 with
  | some v =>
    ihave H := (IrisWp.wp_value_fupd (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
      ⟨of_to_val _ _ he⟩).1 $$ H
    iapply IrisWp.fupd_wp (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
    imod H with ⟨Hor, %f0, Hf0, HΦf⟩
    icases Hor with (%hv | HΨ)
    · subst hv
      have h1 := to_val_trap_is_singleton _ he
      subst h1
      imodintro
      have H := wp_trap_ctx (GF := GF) s E f0 i lh [] es2 rfl
      unfold wpWasmCtx at H
      ihave H := H $$ Hf0 %LI %(by simpa using hfill)
      iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ H
      iintro %w ⟨%hw, Hf0⟩
      subst hw
      iapply Ht
      isplitl [Hf0]
      · iexact Hf0
      iexact HΦf
    · imodintro
      have h1 := of_to_val _ _ he
      subst h1
      iapply Hes2 $$ %v %f0 [HΨ Hf0 HΦf] %LI %hfill
      isplitl [HΨ]
      · iexact HΨ
      isplitl [Hf0]
      · iexact Hf0
      iexact HΦf
  | none =>
    let := @WasmG.invGS hlc GF _
    have hLI : toVal LI = none := to_val_None_lfilled LI i lh _ (to_val_cat_None1 _ _ he) hfill
    have hnv : Iris.ProgramLogic.toVal LI = none := hLI
    have he' : Iris.ProgramLogic.toVal es1 = none := he
    iapply wpU.2
    ihave H := wpU.1 $$ H
    simp only [IrisWp.wp.pre, hnv, he']
    iintro %σ %ns %obs %obs' %nt Hσ
    rcases σ with ⟨ws, locs, inst⟩
    icases H $$ %(ws, locs, inst) %ns %obs %obs' %nt Hσ with >⟨%Hred, H⟩
    imodintro
    simp only [Stuckness.MaybeReducible] at Hred
    isplitr
    · ipureintro
      cases s <;> simp only [Stuckness.MaybeReducible]
      exact lfilled_reducible hfill (append_reducible _ _ _ he Hred)
    iintro %e₂ %σ₂ %eₜ %Hstep Hc
    rcases σ₂ with ⟨ws', locs', inst'⟩
    obtain ⟨Hst, rfl, rfl⟩ := Hstep
    rcases lfilled_prim_step_split_reduce_r i lh es1 es2 (ws, locs, inst) LI e₂ (ws', locs', inst') [] []
      hfill Hred ⟨Hst, rfl, rfl⟩ with ⟨e', Hst', hfill'⟩ | ⟨⟨lh1, hlh⟩, hσ⟩
    · dsimp only [step_fupdN]
      imod H $$ %e' %(ws', locs', inst') %([] : List Expr) %Hst' Hc with H
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
        iapply IH $$ %e' %a Hntrap Ht Ha H Hes2 %e₂ %hfill'
      · simp; iempintro
    · simp only [Prod.mk.injEq] at hσ
      obtain ⟨h1, h2, h3⟩ := hσ
      subst ws' locs' inst'
      obtain ⟨bef, aft, -, hcb, rfl⟩ := IrisWasm.Helpers.ReduceDetPrelude.lfilled0 hlh
      have hneq : bef ++ [.trap] ++ aft ≠ [.trap] := by
        intro h; rw [h] at he; simp [toVal, mergeValuesList, toValInstr, mergeValues] at he
      have Hst' : primStep (bef ++ [.trap] ++ aft, ws, locs, inst) [] ([.trap], (ws, locs, inst), []) :=
        ⟨.simple (.trap _ hneq ((lfilled_Ind_Equivalent _ _ _ _).2 (.lfilledBase _ _ _ hcb))), rfl, rfl⟩
      have hl0 : lfilled 0 (.base bef (aft ++ es2)) [.trap] (bef ++ [.trap] ++ aft ++ es2) = true := by
        rw [lfilled_Ind_Equivalent]
        simpa using LfilledInd.lfilledBase bef [.trap] (aft ++ es2) hcb
      obtain ⟨lh'', hlh''⟩ := lfilled_trans hl0 hfill
      obtain ⟨lh2, j, hj, -⟩ := trap_reduce_lfilled Hst hlh''
      dsimp only [step_fupdN]
      imod H $$ %([.trap] : Expr) %(ws, locs, inst) %([] : List Expr) %Hst' Hc with H
      iintro !> !>
      imod H
      iintro !>
      iapply step_fupdN_wand $$ H
      iintro >⟨Hσ, %a, Ha, H, -⟩
      ihave H := H $$ Ha
      ihave H := (IrisWp.wp_value_fupd (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
        (e := [.trap]) (v := .trapV) ⟨rfl⟩).1 $$ H
      imod H with ⟨Hor, %f0, Hf0, HΦf⟩
      icases Hor with (- | HΨ)
      · imodintro
        iframe Hσ
        iexists f0
        iframe Hf0
        isplitl
        · iintro Hf0
          have H := wp_trap_ctx (GF := GF) s E f0 j lh2 [] [] rfl
          unfold wpWasmCtx at H
          ihave H := H $$ Hf0 %e₂ %(by simpa using hj)
          iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ H
          iintro %w ⟨%hw, Hf0⟩
          subst hw
          iapply Ht
          isplitl [Hf0]
          · iexact Hf0
          iexact HΦf
        · simp; iempintro
      · imod Hntrap $$ HΨ with %hF
        exact hF.elim


private theorem to_val_cons_val' {v0 : Value} {es : Expr} {w : Val} (h : toVal es = some w)
    (hw : w ≠ .trapV) : toVal (.basic (.const v0) :: es) = some (valCombine (.immV [v0]) w) := by
  cases w with
  | immV l => rw [← of_to_val _ _ h]; exact to_val_cons_immV v0 l
  | trapV => exact absurd rfl hw
  | brV lh => exact to_val_cons_brV _ lh v0 es h
  | retV sh => exact to_val_cons_retV sh v0 es h
  | callHostV tf hf cvs lh => exact to_val_cons_callHostV tf hf cvs lh v0 es h

/-- A trapping expression satisfies the "can trap" postcondition. -/
private theorem wp_trap_can_trap {s : Stuckness} {E : CoPset} {vs es : Expr} (hc : constList vs = true)
    {f0 : Frame} {Φ : Val → IProp GF} {Φf : Frame → IProp GF} :
    ⊢ (↪[frame] f0 -∗ Φf f0 -∗ WP (vs ++ [.trap] ++ es) @ s ; E
      {{ v, (⌜v = .trapV⌝ ∨ Φ v) ∗ ∃ f, ↪[frame] f ∗ Φf f }} : IProp GF) := by
  iintro Hf0 HΦf
  ihave H := wp_trap s E (fun w => iprop(⌜w = .trapV⌝ ∗ Φf f0)) vs es f0 hc $$ [HΦf] Hf0
  · isplitr
    · ipureintro; rfl
    iexact HΦf
  iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ H
  iintro %w ⟨⟨%hw, HΦf⟩, Hf0⟩
  isplitr [Hf0 HΦf]
  · ileft; ipureintro; exact hw
  iexists f0
  isplitl [Hf0]
  · iexact Hf0
  iexact HΦf

@[rocq_alias iriswasm.wp_val_can_trap]
theorem wp_val_can_trap (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF) (v0 : Value)
    (es : Expr) (f : Frame) (Φf : Frame → IProp GF) :
    (iprop((Φ .trapV ={E}=∗ ⌜False⌝) ∗ ↪[frame] f ∗
      (↪[frame] f -∗ WP es @ Stuckness.NotStuck ; E
        {{ v, (⌜v = .trapV⌝ ∨ Φ (valCombine (.immV [v0]) v)) ∗ ∃ f, ↪[frame] f ∗ Φf f }}))
      : IProp GF)
    ⊢ WP (.basic (.const v0) :: es) @ s ; E
        {{ v, (⌜v = .trapV⌝ ∨ Φ v) ∗ ∃ f, ↪[frame] f ∗ Φf f }} := by
  iintro ⟨Hntrap, Hf, H⟩
  irevert Hntrap Hf H
  iloeb as IH generalizing %es %f
  iintro Hntrap Hf H
  ihave H := H $$ Hf
  cases he : toVal es with
  | some v =>
    ihave H := (IrisWp.wp_value_fupd (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
      ⟨of_to_val _ _ he⟩).1 $$ H
    by_cases hv : v = .trapV
    · subst hv
      have h1 := to_val_trap_is_singleton _ he
      subst h1
      iapply IrisWp.fupd_wp (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
      imod H with ⟨Hor, %f0, Hf0, HΦf⟩
      icases Hor with (- | HΦ)
      · imodintro
        have H := wp_trap_can_trap (GF := GF) (s := s) (E := E) (Φ := Φ) (Φf := Φf)
          (vs := [.basic (.const v0)]) (es := []) (f0 := f0) rfl
        simp only [List.append_nil, List.cons_append, List.nil_append] at H
        iapply H $$ Hf0 HΦf
      · rw [show valCombine (.immV [v0]) .trapV = .trapV from rfl]
        imod Hntrap $$ HΦ with %hF
        exact hF.elim
    · iapply (IrisWp.wp_value_fupd (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
        ⟨of_to_val _ _ (to_val_cons_val' (v0 := v0) he hv)⟩).2
      imod H with ⟨Hor, Hfr⟩
      icases Hor with (%hv' | HΦ)
      · exact absurd hv' hv
      · imodintro
        isplitl [HΦ]
        · iright; iexact HΦ
        iexact Hfr
  | none =>
    let := @WasmG.invGS hlc GF _
    have hnv : Iris.ProgramLogic.toVal (.basic (.const v0) :: es : Expr) = none :=
      to_val_cons_None _ _ he
    have he' : Iris.ProgramLogic.toVal es = none := he
    iapply wpU.2
    ihave H := wpU.1 $$ H
    simp only [IrisWp.wp.pre, hnv, he']
    iintro %σ %ns %obs %obs' %nt Hσ
    rcases σ with ⟨ws, locs, inst⟩
    icases H $$ %(ws, locs, inst) %ns %obs %obs' %nt Hσ with >⟨%Hred, H⟩
    imodintro
    simp only [Stuckness.MaybeReducible] at Hred
    isplitr
    · ipureintro
      cases s <;> simp only [Stuckness.MaybeReducible]
      exact prepend_reducible [.basic (.const v0)] es _ (.inl rfl) Hred
    iintro %e₂ %σ₂ %eₜ %Hstep Hc
    rcases σ₂ with ⟨ws', locs', inst'⟩
    obtain ⟨Hst, rfl, rfl⟩ := Hstep
    rcases reduce_ves v0 es e₂ (ws, locs, inst) (ws', locs', inst') [] [] Hred
      ⟨Hst, rfl, rfl⟩ with ⟨he₂, Hst'⟩ | ⟨lh, lh', hfill, hfill1, hσ⟩
    · generalize e₂.drop 1 = e' at he₂ Hst'
      subst he₂
      dsimp only [step_fupdN]
      imod H $$ %e' %(ws', locs', inst') %([] : List Expr) %Hst' Hc with H
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
        simp only [List.cons_append, List.nil_append]
        iapply IH $$ %e' %a Hntrap Ha H
      · simp; iempintro
    · simp only [Prod.mk.injEq] at hσ
      obtain ⟨h1, h2, h3⟩ := hσ
      subst ws' locs' inst'
      obtain ⟨bef, aft, -, hc, rfl⟩ := IrisWasm.Helpers.ReduceDetPrelude.lfilled0 hfill1
      have hneq : bef ++ [.trap] ++ aft ≠ [.trap] := by
        intro h; rw [h] at he; simp [toVal, mergeValuesList, toValInstr, mergeValues] at he
      have Hst' : primStep (bef ++ [.trap] ++ aft, ws, locs, inst) [] ([.trap], (ws, locs, inst), []) :=
        ⟨.simple (.trap _ hneq ((lfilled_Ind_Equivalent _ _ _ _).2 (.lfilledBase _ _ _ hc))), rfl, rfl⟩
      obtain ⟨bef', aft', -, hc', rfl⟩ := IrisWasm.Helpers.ReduceDetPrelude.lfilled0 hfill
      dsimp only [step_fupdN]
      imod H $$ %([.trap] : Expr) %(ws, locs, inst) %([] : List Expr) %Hst' Hc with H
      iintro !> !>
      imod H
      iintro !>
      iapply step_fupdN_wand $$ H
      iintro >⟨Hσ, %a, Ha, H, -⟩
      ihave H := H $$ Ha
      ihave H := (IrisWp.wp_value_fupd (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
        (e := [.trap]) (v := .trapV) ⟨rfl⟩).1 $$ H
      imod H with ⟨Hor, %f0, Hf0, HΦf⟩
      icases Hor with (- | HΦ)
      · imodintro
        iframe Hσ
        iexists f0
        iframe Hf0
        isplitl
        · iintro Hf0
          iapply wp_trap_can_trap hc' $$ Hf0 HΦf
        · simp; iempintro
      · rw [show valCombine (.immV [v0]) .trapV = .trapV from rfl]
        imod Hntrap $$ HΦ with %hF
        exact hF.elim


/-! Some alternative formulations, useful for the soundness proof. -/

private theorem valCombine_nil' (v : Val) : valCombine (.immV []) v = v := by
  cases v <;> simp [valCombine, vh_push_const_nil, sh_push_const_nil, llh_push_const_nil]

private theorem valCombine_cons' (c : Value) (vs : List Value) (v : Val) :
    valCombine (.immV [c]) (valCombine (.immV vs) v) = valCombine (.immV (c :: vs)) v := by
  cases v <;> simp [valCombine, ← vh_push_const_app, ← sh_push_const_app, ← llh_push_const_app]

@[rocq_alias iriswasm.wp_val_can_trap_app']
theorem wp_val_can_trap_app' (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF) (vs : List Value)
    (es : Expr) (f : Frame) (Φf : Frame → IProp GF) :
    (iprop(□ (Φ .trapV ={E}=∗ ⌜False⌝) ∗ ↪[frame] f ∗
      (↪[frame] f -∗ WP es @ Stuckness.NotStuck ; E
        {{ v, (⌜v = .trapV⌝ ∨ Φ (valCombine (.immV vs) v)) ∗ ∃ f, ↪[frame] f ∗ Φf f }}))
      : IProp GF)
    ⊢ WP (vToEList vs ++ es) @ s ; E
        {{ v, (⌜v = .trapV⌝ ∨ Φ v) ∗ ∃ f, ↪[frame] f ∗ Φf f }} := by
  induction vs generalizing Φ s es with
  | nil =>
    rw [show vToEList [] ++ es = es from rfl]
    simp only [valCombine_nil']
    iintro ⟨-, Hf, H⟩
    ihave H := H $$ Hf
    cases s
    · iexact H
    · iapply IrisWp.wp_stuck_weaken (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ H
  | cons c vs ih =>
    rw [show vToEList (c :: vs) ++ es = .basic (.const c) :: (vToEList vs ++ es) from rfl]
    iintro ⟨#Hn, Hf, H⟩
    iapply wp_val_can_trap
    isplitr [Hf H]
    · iexact Hn
    isplitl [Hf]
    · iexact Hf
    iintro Hf
    iapply ih (Φ := fun v => Φ (valCombine (.immV [c]) v))
    isplitr [Hf H]
    · imodintro
      rw [show valCombine (.immV [c]) .trapV = .trapV from rfl]
      iexact Hn
    isplitl [Hf]
    · iexact Hf
    iintro Hf
    ihave H := H $$ Hf
    iapply IrisWp.wp_mono (ι := wasmIrisGS) (fun f => iprop(↪[frame] f)) (fun v => ?_) $$ H
    rw [valCombine_cons']

@[rocq_alias iriswasm.wp_val_return']
theorem wp_val_return' (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF) (vs vs' es' es'' : Expr)
    (n : Nat) (f0 : Frame) (Φf : Frame → IProp GF) :
    constList vs = true →
    ⊢ (↪[frame] f0 -∗
      (↪[frame] f0 -∗ WP (vs' ++ vs ++ es'') @ s ; E {{ v, Φ v ∗ ∃ f, ↪[frame] f ∗ Φf f }}) -∗
      WP vs @ s ; E CTX 1 ; (.rec_ vs' n es' (.base [] []) es'')
        {{ v, Φ v ∗ ∃ f, ↪[frame] f ∗ Φf f }} : IProp GF) := by
  intro hc
  unfold wpWasmCtx
  iintro Hf0 HWP %LI %hfill
  obtain ⟨bef, n0, es0, lh', aft, LI0, hlh, hcb, hf0, rfl⟩ :=
    IrisWasm.Helpers.ReduceDetPrelude.lfilledS hfill
  cases hlh
  have h := IrisWasm.Helpers.ReduceDetPrelude.lfilled_base.1 hf0
  subst LI0
  obtain ⟨v1, hv1⟩ := const_list_to_val vs hc
  obtain ⟨v2, hv2⟩ := const_list_to_val vs' hcb
  rw [show vs' ++ AdministrativeInstruction.label n es' vs :: es'' =
    vs' ++ [.label n es' vs] ++ es'' by simp]
  iapply wp_seq s E _ (fun v => iprop(⌜v = .immV (v2 ++ v1)⌝ ∗ ↪[frame] f0))
  isplitr [Hf0 HWP]
  · iintro ⟨%h, -⟩
    cases h
  isplitl [Hf0]
  · iapply wp_val_app s E _ vs' v2 _ hv2
    isplitr
    · imodintro
      iintro ⟨%h, -⟩
      cases h
    iapply wp_label_value (Φ := fun v => iprop(⌜valCombine (.immV v2) v = .immV (v2 ++ v1)⌝)) hv1 $$ Hf0
    inext; ipureintro; rfl
  iintro %w ⟨%hw, Hf0⟩
  subst hw
  rw [← of_to_val _ _ hv1, ← of_to_val _ _ hv2,
    show ofVal (.immV (v2 ++ v1)) = ofVal (.immV v2) ++ ofVal (.immV v1) by
      simp [ofVal, vToEList]]
  iapply HWP $$ Hf0

@[rocq_alias iriswasm.wp_val_can_trap_app]
theorem wp_val_can_trap_app (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF) (vs : Expr)
    (v' : List Value) (es : Expr) (f : Frame) (Φf : Frame → IProp GF) :
    toVal vs = some (.immV v') →
    (iprop(□ (Φ .trapV ={E}=∗ ⌜False⌝) ∗ ↪[frame] f ∗
      (↪[frame] f -∗ WP es @ Stuckness.NotStuck ; E
        {{ v, (⌜v = .trapV⌝ ∨ Φ (valCombine (.immV v') v)) ∗ ∃ f, ↪[frame] f ∗ Φf f }}))
      : IProp GF)
    ⊢ WP (vs ++ es) @ s ; E {{ v, (⌜v = .trapV⌝ ∨ Φ v) ∗ ∃ f, ↪[frame] f ∗ Φf f }} := by
  intro h
  rw [← of_to_val _ _ h, ← of_val_imm]
  exact wp_val_can_trap_app' s E Φ v' es f Φf

@[rocq_alias iriswasm.wp_seq_can_trap_same_ctx]
theorem wp_seq_can_trap_same_ctx (Φ Ψ : Val → IProp GF) (s : Stuckness) (E : CoPset)
    (es1 es2 : Expr) (f : Frame) (i : Nat) (lh : Lholed) :
    (iprop((Ψ .trapV ={E}=∗ False) ∗ Φ .trapV ∗ ↪[frame] f ∗
      (↪[frame] f -∗ WP es1 @ Stuckness.NotStuck ; E
        {{ w, (⌜w = .trapV⌝ ∨ Ψ w) ∗ ↪[frame] f }}) ∗
      (∀ w, Ψ w ∗ ↪[frame] f -∗
        WP (ofVal w ++ es2) @ s ; E CTX i ; lh {{ v, Φ v ∗ ↪[frame] f }})) : IProp GF)
    ⊢ WP (es1 ++ es2) @ s ; E CTX i ; lh {{ v, Φ v ∗ ↪[frame] f }} := by
  iintro ⟨HPsi, HΦ, Hf, Hes1, Hes2⟩
  iapply wp_wand_ctx s E _ (fun v => iprop(Φ v ∗ ∃ f0, ↪[frame] f0 ∗ ⌜f0 = f⌝)) _ i lh $$ [-]
  · iapply wp_seq_can_trap_ctx s E _ Ψ es1 es2 i lh (fun f0 => iprop(⌜f0 = f⌝)) f
    isplitl [HPsi]
    · iintro HΨ
      imod HPsi $$ HΨ with H
      iexfalso
      iexact H
    isplitl [HΦ]
    · iintro %f' ⟨Hf, %heq⟩
      isplitl [HΦ]
      · iexact HΦ
      iexists f'
      isplitl [Hf]
      · iexact Hf
      ipureintro; exact heq
    isplitl [Hf]
    · iexact Hf
    isplitl [Hes1]
    · iintro Hf
      ihave H := Hes1 $$ Hf
      iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ H
      iintro %v ⟨Hv, Hf⟩
      isplitl [Hv]
      · iexact Hv
      iexists f
      isplitl [Hf]
      · iexact Hf
      ipureintro; rfl
    iintro %w %f' ⟨HΨ, Hf, %heq⟩
    subst heq
    ihave H := Hes2 $$ %w [HΨ Hf]
    · isplitl [HΨ]
      · iexact HΨ
      iexact Hf
    iapply wp_wand_ctx $$ H
    iintro %v ⟨Hv, Hf⟩
    isplitl [Hv]
    · iexact Hv
    iexists f'
    isplitl [Hf]
    · iexact Hf
    ipureintro; rfl
  · iintro %v ⟨Hv, %f0, Hf0, %heq⟩
    subst heq
    isplitl [Hv]
    · iexact Hv
    iexact Hf0

@[rocq_alias iriswasm.wp_seq_can_trap_same_empty_ctx]
theorem wp_seq_can_trap_same_empty_ctx (Φ Ψ : Val → IProp GF) (s : Stuckness) (E : CoPset)
    (es1 es2 : Expr) (f : Frame) :
    (iprop((Ψ .trapV ={E}=∗ False) ∗ Φ .trapV ∗ ↪[frame] f ∗
      (↪[frame] f -∗ WP es1 @ Stuckness.NotStuck ; E
        {{ w, (⌜w = .trapV⌝ ∨ Ψ w) ∗ ↪[frame] f }}) ∗
      (∀ w, Ψ w ∗ ↪[frame] f -∗ WP (ofVal w ++ es2) @ s ; E {{ v, Φ v ∗ ↪[frame] f }}))
      : IProp GF)
    ⊢ WP (es1 ++ es2) @ s ; E {{ v, Φ v ∗ ↪[frame] f }} := by
  iintro H
  ihave W := wp_wasm_empty_ctx s E (fun v => iprop(Φ v ∗ ↪[frame] f)) (es1 ++ es2)
  icases W with ⟨-, W⟩
  iapply W
  iapply wp_seq_can_trap_same_ctx Φ Ψ s E es1 es2 f 0 (.base [] [])
  icases H with ⟨HPsi, HΦ, Hf, Hes1, Hes2⟩
  isplitl [HPsi]
  · iexact HPsi
  isplitl [HΦ]
  · iexact HΦ
  isplitl [Hf]
  · iexact Hf
  isplitl [Hes1]
  · iexact Hes1
  iintro %w Hw
  ihave W := wp_wasm_empty_ctx s E (fun v => iprop(Φ v ∗ ↪[frame] f)) (ofVal w ++ es2)
  icases W with ⟨W, -⟩
  iapply W
  iapply Hes2 $$ Hw


end IrisWasm
