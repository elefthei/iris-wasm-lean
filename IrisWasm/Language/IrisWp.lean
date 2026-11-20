/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import Iris.ProgramLogic.WeakestPre
import Iris.ProgramLogic.Lifting

/-! Port of `theories/iris/language/iris_wp.v`.

Iris-Wasm's weakest precondition differs from the standard Iris one in a single place: after each
step the continuation `wp E e₂ Φ` is guarded by a frame resource `P a`, i.e. it becomes
`∃ a, P a ∗ (P a -∗ wp E e₂ Φ)`. For Wasm, `P` is the ownership of the current frame. The
definitions here are generic in the language; `IrisWasm.wpWasm` instantiates them. -/

namespace IrisWasm.IrisWp

open Iris Iris.BI Iris.ProgramLogic Iris.Std Language.Notation

variable {hlc : HasLC} {Expr State Obs Val : Type _}
variable [Λ : Language Expr State Obs Val]
variable {GF : BundledGFunctors} [ι : IrisGS_gen hlc Expr GF]
variable {A : Type _}

@[rocq_alias iriswasm.wp_pre]
def wp.pre (P : A → IProp GF) (s : Stuckness)
    (wp : CoPset → Expr → (Val → IProp GF) → IProp GF) (E : CoPset) (e₁ : Expr)
    (Φ : Val → IProp GF) : IProp GF :=
  match toVal e₁ with
  | some v => iprop(|={E}=> Φ v)
  | none => iprop(∀ (σ₁ : State) (ns : Nat) (obs obs' : List Obs) (nt : Nat),
    stateInterp σ₁ ns (obs ++ obs') nt ={E,∅}=∗
    ⌜s.MaybeReducible (e₁, σ₁)⌝ ∗
    ∀ e₂ σ₂ eₜ, ⌜(e₁, σ₁) -<obs>-> (e₂, σ₂, eₜ)⌝ -∗
      £ (ι.numLatersPerStep ns + 1) ={∅}▷=∗^[ι.numLatersPerStep ns + 1] |={∅,E}=>
      stateInterp σ₂ (ns + 1) obs' (nt + eₜ.length) ∗
      ∃ a, P a ∗ (P a -∗ wp E e₂ Φ) ∗ [∗list] e' ∈ eₜ, wp ⊤ e' ι.forkPost)

@[rocq_alias iriswasm.wp_pre_contractive]
instance wp.pre.contractive (P : A → IProp GF) (s : Stuckness) :
    OFE.Contractive (wp.pre P s (ι := ι)) where
  distLater_dist := by
    intros n wp wp' Hwp E e₁ Φ
    unfold pre
    cases toVal e₁
    case some _ =>
      exact .rfl
    case none =>
      refine BI.forall_ne (fun σ₁ => ?_)
      refine BI.forall_ne (fun ns => ?_)
      refine BI.forall_ne (fun obs => ?_)
      refine BI.forall_ne (fun obs' => ?_)
      refine BI.forall_ne (fun nt => ?_)
      refine BI.wand_ne.ne .rfl ?_
      refine BIFUpdate.ne.ne ?_
      refine BI.sep_ne.ne .rfl ?_
      refine BI.forall_ne (fun e₂ => ?_)
      refine BI.forall_ne (fun σ₂ => ?_)
      refine BI.forall_ne (fun eₜ => ?_)
      refine BI.wand_ne.ne .rfl ?_
      refine BI.wand_ne.ne .rfl ?_
      refine BIFUpdate.ne.ne ?_
      refine OFE.Contractive.distLater_dist fun m m_n => ?_
      refine BIFUpdate.ne.ne ?_
      refine step_fupdN_ne.ne ?_
      refine BIFUpdate.ne.ne ?_
      refine BI.sep_ne.ne .rfl ?_
      refine BI.exists_ne (fun a => ?_)
      refine BI.sep_ne.ne .rfl ?_
      refine BI.sep_ne.ne ?_ ?_
      · exact BI.wand_ne.ne .rfl (Hwp m m_n _ _ _)
      · exact BI.BigSepL.bigSepL_dist <| fun _ => Hwp m m_n _ _ _

/-- The Iris-Wasm weakest precondition, generic in the language and the frame predicate `P`. -/
@[rocq_alias iriswasm.wp_def]
def wp (P : A → IProp GF) (s : Stuckness) : CoPset → Expr → (Val → IProp GF) → IProp GF :=
  fixpoint (wp.pre P s (ι := ι))

#rocq_ignore iriswasm.wp_aux "no sealing in Lean"
#rocq_ignore iriswasm.wp' "no sealing in Lean"
#rocq_ignore iriswasm.wp_eq "no sealing in Lean"
#rocq_ignore iriswasm.wp_instance "the generic wp is a plain function; IrisWasm.wpWasm is the Wp instance"

variable (P : A → IProp GF)

@[rocq_alias iriswasm.wp_unfold]
theorem wp_unfold {s E} {e : Expr} {Φ : Val → IProp GF} :
    wp P s E e Φ ⊣⊢ wp.pre P s (wp P s) E e Φ :=
  BI.equiv_iff.1 <| OFE.eq_dist_2 <|
    fun _n => (fixpoint_unfold (f := (wp.pre P s (ι := ι)).toContractiveHom)).dist E e Φ


@[rocq_alias iriswasm.wp_ne]
instance wp_ne {s : Stuckness} {E} {e : Expr} :
    OFE.NonExpansive (wp P s E e) where
  ne {n Φ₁ Φ₂} HΦ := by
    induction n using Nat.strongRecOn generalizing e E Φ₁ Φ₂ with | ind n IH =>
    simp only [(wp_unfold P).to_eq]
    dsimp only [wp.pre]
    cases toVal e
    case some v =>
      exact BIFUpdate.ne.ne <| HΦ v
    case none =>
      refine BI.forall_ne fun σ₁ => ?_
      refine BI.forall_ne fun ns => ?_
      refine BI.forall_ne fun obs => ?_
      refine BI.forall_ne fun obs' => ?_
      refine BI.forall_ne fun nt => ?_
      refine BI.wand_ne.ne .rfl ?_
      refine BIFUpdate.ne.ne ?_
      refine BI.sep_ne.ne .rfl ?_
      refine BI.forall_ne fun e₂  => ?_
      refine BI.forall_ne fun σ₂ => ?_
      refine BI.forall_ne fun eₜ => ?_
      refine BI.wand_ne.ne .rfl ?_
      refine BI.wand_ne.ne .rfl ?_
      refine step_fupdN_contractive.distLater_dist fun m n_m => ?_
      refine BIFUpdate.ne.ne ?_
      refine BI.sep_ne.ne .rfl ?_
      refine BI.exists_ne (fun a => ?_)
      refine BI.sep_ne.ne .rfl ?_
      refine BI.sep_ne.ne ?_ .rfl
      exact BI.wand_ne.ne .rfl <| IH m n_m <| OFE.dist_lt HΦ n_m

#rocq_ignore iriswasm.wp_proper "Derivable using NonExpansive.eqv"

@[rocq_alias iriswasm.wp_contractive]
theorem wp_contractive (s : Stuckness) E (e : Expr) (h : toVal e = none) :
    OFE.Contractive (wp P s E e) where
  distLater_dist {n Φ₁ Φ₂} HΦ := by
    simp only [(wp_unfold P).to_eq]
    simp only [wp.pre, h]
    refine BI.forall_ne fun σ₁ => ?_
    refine BI.forall_ne fun ns => ?_
    refine BI.forall_ne fun obs => ?_
    refine BI.forall_ne fun obs' => ?_
    refine BI.forall_ne fun nt => ?_
    refine BI.wand_ne.ne .rfl ?_
    refine BIFUpdate.ne.ne ?_
    refine BI.sep_ne.ne .rfl ?_
    refine BI.forall_ne fun e₂  => ?_
    refine BI.forall_ne fun σ₂ => ?_
    refine BI.forall_ne fun eₜ => ?_
    refine BI.wand_ne.ne .rfl ?_
    refine BI.wand_ne.ne .rfl ?_
    refine step_fupdN_contractive.distLater_dist fun m n_m => ?_
    refine BIFUpdate.ne.ne ?_
    refine BI.sep_ne.ne .rfl ?_
    refine BI.exists_ne (fun a => ?_)
    refine BI.sep_ne.ne .rfl ?_
    refine BI.sep_ne.ne ?_ .rfl
    exact BI.wand_ne.ne .rfl <| (wp_ne P).ne (HΦ m n_m)

@[rocq_alias iriswasm.wp_value_fupd']
theorem wp_value_fupd' {s : Stuckness} {E} {Φ : Val → IProp GF} {v : Val} :
    wp P s E (v : Expr) Φ ⊣⊢ |={E}=> Φ v := by
  simp [(wp_unfold P).to_eq, toVal_coe, wp.pre]

@[rocq_alias iriswasm.wp_strong_mono]
theorem wp_strong_mono {s₁ s₂ : Stuckness} {E₁ E₂} {e : Expr} {Φ Ψ : Val → IProp GF}
    (hs : s₁ ≤ s₂) (hE : E₁ ⊆ E₂) :
    ⊢ wp P s₁ E₁ e Φ -∗ (∀ v, Φ v ={E₂}=∗ Ψ v) -∗ wp P s₂ E₂ e Ψ := by
  iloeb as IH generalizing %e %Φ %Ψ %E₁ %E₂ %hE
  rw [(wp_unfold P).to_eq, (wp_unfold P).to_eq]
  iintro H HΦ
  dsimp only [wp.pre]
  match toVal e with
  | none =>
    dsimp only
    iintro %σ₁ %ns %obs %obs' %nt Hσ
    imod fupd_mask_subseteq hE with Hclose
    icases H $$ Hσ with >⟨%h, H⟩
    imodintro
    isplit
    · simp only [LE.le] at hs
      ipureintro
      grind [cases Stuckness]
    · iintro %e₂ %σ₂ %eₜ #hstep hc
      dsimp only [step_fupdN]
      imod H $$ hstep hc with H
      iintro !> !>; imod H; iintro !>
      iapply step_fupdN_wand $$ H
      iintro >⟨aux, %a, Ha, H, Hefs⟩
      imod Hclose
      imodintro
      iframe aux
      iexists a
      iframe Ha
      isplitr [Hefs]
      · iintro Ha
        iapply IH $$ %e₂ %Φ %Ψ %E₁ %E₂ %hE [H Ha] HΦ
        iapply H $$ Ha
      · iapply BI.BigSepL.bigSepL_impl $$ Hefs
        iintro !> %k %e' %_ H
        iapply IH $$ %e' %_ %_ %⊤ %_ %LawfulSet.subset_refl H
        iintro %v H
        imodintro
        iassumption
  | some v =>
    dsimp only
    imod fupd_mask_mono hE $$ H with h
    iapply HΦ $$ h

@[rocq_alias iriswasm.fupd_wp]
theorem fupd_wp {s : Stuckness} {E} {e : Expr} {Φ : Val → IProp GF} :
    (|={E}=> wp P s E e Φ) ⊢ wp P s E e Φ := by
  simp only [(wp_unfold P).to_eq]
  iintro H
  match h: toVal e with
  | some v =>
    simp only [wp.pre, h]
    imod H
    iassumption
  | none =>
    simp only [wp.pre, h]
    iintro %σ₁ %ns %obs %obs' %nt
    imod H with H
    iassumption

@[rocq_alias iriswasm.wp_fupd]
theorem wp_fupd {s : Stuckness} {E} {e : Expr} {Φ : Val → IProp GF} :
    wp P s E e (fun v => iprop(|={E}=> Φ v)) ⊢ wp P s E e Φ := by
  iintro h
  iapply wp_strong_mono P (Std.IsPreorder.le_refl _) LawfulSet.subset_refl $$ h
  iintro %v h
  iassumption


@[rocq_alias iriswasm.wp_atomic]
theorem wp_atomic {s : Stuckness} {E1 E2 : CoPset} {e : Expr} {Φ : Val → IProp GF} (a : A)
    [ι' : Language.Atomic ↑s e] :
    (|={E1,E2}=> wp P s E2 e (fun v => iprop(|={E2,E1}=> Φ v ∗ P a))) ⊢
      wp P s E1 e (fun v => iprop(Φ v ∗ P a)) := by
  simp only [(wp_unfold P).to_eq]
  iintro H
  match He : toVal e with
  | some v =>
    simp only [wp.pre, He]
    iapply BIFUpdate.trans (E2 := E2)
    imod H
    iassumption
  | none =>
    simp only [wp.pre, He]
    iintro %σ₁ %ns %obs %obs' %nt Hσ
    imod H
    imod H $$ Hσ with ⟨$, H⟩
    imodintro
    iintro %e2 %σ2 %efs %Hstep Hcred
    ihave aux := H $$ %e2 %σ2 %efs %Hstep Hcred
    iapply step_fupdN_wand $$ aux
    iintro >(⟨Hσ, %a', Ha', H, Hefs⟩)
    ispecialize H $$ Ha'
    irevert %ι'
    match s with
    | .NotStuck =>
      simp only [(wp_unfold P).to_eq]
      dsimp only [wp.pre]
      match h₂ : toVal e2 with
      | some v2 =>
        iintro %ι'
        icases H with > > ⟨HΦ, Ha⟩
        iframe
        imodintro
        iintro Ha !>
        iexact Ha
      | none =>
        iintro %ι'
        icases H $$ %σ2 %(ns +1) %([]) %_ %(nt + efs.length) [Hσ] with >⟨%h, _⟩
        · exact .rfl
        exact ((Language.not_reducible_iff_irreducible.mpr (ι'.atomic Hstep)) h).elim
    | .MaybeStuck =>
      iintro %ι'
      have ⟨v, h⟩ := Option.isSome_iff_exists.mp (ι'.atomic Hstep)
      obtain ⟨rfl⟩ := (ToVal.coe_of_toVal_eq_some h)
      simp only [(wp_value_fupd' P).to_eq]
      imod H with > ⟨HΦ, Ha⟩
      iframe
      imodintro
      iintro Ha !>
      iexact Ha


@[rocq_alias iriswasm.wp_step_fupdN_strong]
theorem wp_step_fupdN_strong {s : Stuckness} {E1 E2 : CoPset} {e : Expr} {R : IProp GF} {Φ} {n}
    (toVal_e : toVal e = none) (E2_E1 : E2 ⊆ E1) :
    (∀ (σ : State) ns obs nt, stateInterp σ ns obs nt ={E1, ∅}=∗ ⌜n ≤ ι.numLatersPerStep ns + 1⌝)
    ∧ ((|={E1,E2}=> |={∅}▷=>^[n] |={E2,E1}=> R)
    ∗ wp P s E2 e (fun v => iprop(R ={E1}=∗ Φ v))) ⊢
    wp P s E1 e Φ := by
  match n with
  | 0 =>
    iintro ⟨-, ⟨Hp, Hwp⟩⟩
    iapply wp_strong_mono P (Std.IsPreorder.le_refl s) E2_E1 $$ Hwp
    iintro %v H
    dsimp only [step_fupdN]
    imod Hp
    imod Hp
    iapply H $$ Hp
  | n+1 =>
    simp only [(wp_unfold P).to_eq]
    simp only [wp.pre, toVal_e]
    iintro H %σ₁ %ns %obs %obs' %nt Hσ₁
    by_cases Hn : n ≤ ι.numLatersPerStep ns
    · icases H with ⟨-, ⟨Hp, Hwp⟩⟩
      imod Hp
      dsimp only [step_fupdN]
      imod Hwp $$ Hσ₁ with ⟨$, H⟩
      iintro !> %e₂ %σ₂ %efs %Hstep Hcred
      icases H $$ %_ %_ %_ %Hstep Hcred with H
      imod H; imod Hp
      iintro !> !>
      imod H; imod Hp
      imodintro
      generalize ι.numLatersPerStep ns = n0 at *
      induction n generalizing n0 with
      | zero =>
        iapply step_fupdN_wand $$ H
        iintro >⟨$, %a, Ha, Hwp, $⟩
        dsimp only [step_fupdN]
        imod Hp
        imodintro
        iexists a
        iframe Ha
        iintro Ha
        iapply wp_strong_mono P (Std.IsPreorder.le_refl s) E2_E1 $$ [Hwp Ha]
        · iapply Hwp $$ Ha
        iintro %v HΦ
        iapply HΦ $$ Hp
      | succ n IH =>
        obtain ⟨n0, rfl⟩ : ∃ n0', n0 = n0' + 1 := by cases n0 <;> grind
        dsimp only [step_fupdN]
        imod Hp; imod H; imodintro; imodintro; imod Hp; imod H; imodintro
        unfold ProofMode.Entails' at IH
        iapply IH n0 (Nat.le_of_succ_le_succ Hn) $$ [$]
    · icases H with ⟨interp, -⟩
      imod interp $$ Hσ₁ with %h
      grind only

/-! ## Derived rules -/

@[rocq_alias iriswasm.wp_mono]
theorem wp_mono {s : Stuckness} {E : CoPset} {e : Expr} {Φ Ψ : Val → IProp GF} :
    (∀ v, Φ v ⊢ Ψ v) → wp P s E e Φ ⊢ wp P s E e Ψ := by
  iintro %HΦ H
  iapply wp_strong_mono P (Std.IsPreorder.le_refl s) (LawfulSet.subset_refl) $$ H
  iintro %v HΨ !>
  iapply HΦ $$ HΨ

@[rocq_alias iriswasm.wp_stuck_mono]
theorem wp_stuck_mono {s₁ s₂ : Stuckness} {E : CoPset} {e : Expr} {Φ : Val → IProp GF} :
    s₁ ≤ s₂ → wp P s₁ E e Φ ⊢ wp P s₂ E e Φ := by
  iintro %s₁s₂ Hwp
  iapply wp_strong_mono P s₁s₂ (LawfulSet.subset_refl) $$ Hwp
  iintro %v HΦ
  iframe HΦ

@[rocq_alias iriswasm.wp_stuck_weaken]
theorem wp_stuck_weaken {s : Stuckness} {E : CoPset} {e : Expr} {Φ : Val → IProp GF} :
    wp P s E e Φ ⊢ wp P .MaybeStuck E e Φ :=
  wp_stuck_mono P Stuckness.le_MaybeStuck

@[rocq_alias iriswasm.wp_mask_mono]
theorem wp_mask_mono {s : Stuckness} {E₁ E₂ : CoPset} {e : Expr} {Φ : Val → IProp GF}
    (E₁_E₂ : E₁ ⊆ E₂) : wp P s E₁ e Φ ⊢ wp P s E₂ e Φ := by
  iintro Hwp
  iapply wp_strong_mono P (Std.IsPreorder.le_refl s) E₁_E₂ $$ Hwp
  iintro %v HΦ
  iframe HΦ

#rocq_ignore iriswasm.wp_mono' "No `Proper` typeclass in Lean"
#rocq_ignore iriswasm.wp_flip_mono' "No `Proper` typeclass in Lean"

@[rocq_alias iriswasm.wp_value_fupd]
theorem wp_value_fupd {s : Stuckness} {E : CoPset} {e : Expr} {v : Val} {Φ : Val → IProp GF} :
    Language.IntoVal e v → wp P s E e Φ ⊣⊢ |={E}=> Φ v
  | ⟨h⟩ => h ▸ wp_value_fupd' P

@[rocq_alias iriswasm.wp_value']
theorem wp_value' {s : Stuckness} {E : CoPset} {v : Val} {Φ : Val → IProp GF} :
    Φ v ⊢ wp P s E (v : Expr) Φ :=
  fupd_intro.trans (wp_value_fupd' P).2

@[rocq_alias iriswasm.wp_value]
theorem wp_value {s : Stuckness} {E : CoPset} {e : Expr} {v : Val} {Φ : Val → IProp GF} :
    Language.IntoVal e v → Φ v ⊢ wp P s E e Φ
  | ⟨h⟩ => h ▸ wp_value' P

@[rocq_alias iriswasm.wp_frame_l]
theorem wp_frame_l {s : Stuckness} {E : CoPset} {e : Expr} {Φ : Val → IProp GF} {R : IProp GF} :
    R ∗ wp P s E e Φ ⊢ wp P s E e (fun v => iprop(R ∗ Φ v)) := by
  iintro ⟨_, H⟩
  iapply wp_strong_mono P (Std.IsPreorder.le_refl s) (LawfulSet.subset_refl) $$ H
  iframe
  iintro %x
  iapply fupd_intro

@[rocq_alias iriswasm.wp_frame_r]
theorem wp_frame_r {s : Stuckness} {E : CoPset} {e : Expr} {Φ : Val → IProp GF} {R : IProp GF} :
    wp P s E e Φ ∗ R ⊢ wp P s E e (fun v => iprop(Φ v ∗ R)) :=
  BI.sep_comm.1.trans <| (wp_frame_l P).trans <| wp_mono P fun _ => BI.sep_comm.1

@[rocq_alias iriswasm.wp_step_fupdN]
theorem wp_step_fupdN {s : Stuckness} {E₁ E₂ : CoPset} {e : Expr} {R : IProp GF}
    {Φ : Val → IProp GF} {n : Nat} (toVal_e : toVal e = none) (E₂E₁ : E₂ ⊆ E₁) :
    (∀ (σ : State) ns obs nt, stateInterp σ ns obs nt ={E₁,∅}=∗ ⌜n ≤ (ι.numLatersPerStep ns)+1⌝) ∧
    (((|={E₁\E₂,∅}=> |={∅}▷=>^[n] |={∅,E₁\E₂}=> R) ∗
    wp P s E₂ e (fun v => iprop(R ={E₁}=∗ Φ v)))) -∗
    wp P s E₁ e Φ := by
  iintro H
  iapply wp_step_fupdN_strong P (s := s) (R := R) (n := n) toVal_e E₂E₁ $$ [H]
  iapply BI.and_mono_right $$ H
  iintro ⟨HP, $⟩
  imod fupd_mask_subseteq_emptyset_difference (show E₁\ E₂ ⊆ E₁ from LawfulSet.diff_subset_left)
    with G
  imod HP
  imod G with -
  rw [show E₁ \ (E₁ \ E₂) = E₂ from LawfulSet.diff_self_diff_of_subset E₂E₁]
  imodintro
  iapply step_fupdN_wand $$ HP; iintro H
  iapply fupd_mask_frame LawfulSet.empty_subset
  imod H
  imodintro
  simp [LawfulSet.diff_empty, ←LawfulSet.diff_subset_decomp E₂E₁]
  itrivial

@[rocq_alias iriswasm.wp_step_fupd]
theorem wp_step_fupd {s : Stuckness} {E₁ E₂ : CoPset} {e : Expr} {R : IProp GF}
    {Φ : Val → IProp GF} (toVal_e : toVal e = none) (E₂E₁ : E₂ ⊆ E₁) :
    (|={E₁}[E₂]▷=> R) -∗ wp P s E₂ e (fun v => iprop(R ={E₁}=∗ Φ v)) -∗ wp P s E₁ e Φ := by
  iintro HR H
  iapply wp_step_fupdN_strong P (n := 1) (R := R) toVal_e E₂E₁ $$ [-]
  iframe H
  isplit
  · iintro %σ %ns %obj %nt interp
    iapply fupd_mask_intro_discard LawfulSet.empty_subset $$ [HR]
    itrivial
  · imod HR
    dsimp only [step_fupdN]
    iframe

@[rocq_alias iriswasm.wp_frame_step_l]
theorem wp_frame_step_l {s : Stuckness} {E₁ E₂ : CoPset} {e : Expr} {Φ : Val → IProp GF}
    {R : IProp GF} (toVal_e : toVal e = none) (E₂E₁ : E₂ ⊆ E₁) :
    (|={E₁}[E₂]▷=> R) ∗ wp P s E₂ e Φ ⊢ wp P s E₁ e (fun v => iprop(R ∗ Φ v)) := by
  iintro ⟨Hu, Hwp⟩
  iapply wp_step_fupd P toVal_e E₂E₁ $$ Hu
  iapply wp_mono P $$ Hwp
  iintro %x $ $

@[rocq_alias iriswasm.wp_frame_step_r]
theorem wp_frame_step_r {s : Stuckness} {E₁ E₂ : CoPset} {e : Expr} {Φ : Val → IProp GF}
    {R : IProp GF} (h1 : toVal e = none) (h2 : E₂ ⊆ E₁) :
    wp P s E₂ e Φ ∗ (|={E₁}[E₂]▷=> R) ⊢ wp P s E₁ e (fun v => iprop(Φ v ∗ R)) :=
  (BI.sep_comm.1.trans <| wp_frame_step_l P h1 h2 |>.trans <| wp_mono P (fun _ => BI.sep_comm.1))

@[rocq_alias iriswasm.wp_frame_step_l']
theorem wp_frame_step_l' {s : Stuckness} {E : CoPset} {e : Expr} {Φ : Val → IProp GF}
    {R : IProp GF} (toVal_e : toVal e = none) :
    (▷ R) ∗ wp P s E e Φ ⊢ wp P s E e (fun v => iprop(R ∗ Φ v)) := by
  iintro ⟨Hu, Hwp⟩
  iapply wp_frame_step_l P toVal_e LawfulSet.subset_refl
  iframe

@[rocq_alias iriswasm.wp_frame_step_r']
theorem wp_frame_step_r' {s : Stuckness} {E : CoPset} {e : Expr} {Φ : Val → IProp GF}
    {R : IProp GF} (h1 : toVal e = none) :
    wp P s E e Φ ∗ (▷ R) ⊢ wp P s E e (fun v => iprop(Φ v ∗ R)) :=
  (BI.sep_comm.1.trans <| wp_frame_step_l' P h1 |>.trans <| wp_mono P (fun _ => BI.sep_comm.1))

@[rocq_alias iriswasm.wp_wand]
theorem wp_wand {s : Stuckness} {E : CoPset} {e : Expr} {Φ Ψ : Val → IProp GF} :
    wp P s E e Φ ⊢ (∀ v, Φ v -∗ Ψ v) -∗ wp P s E e Ψ := by
  iintro Hwp H
  iapply wp_strong_mono P (Std.IsPreorder.le_refl s) LawfulSet.subset_refl $$ Hwp
  iintro %v HΦ
  icases H $$ HΦ with H
  imodintro; iframe

@[rocq_alias iriswasm.wp_wand_l]
theorem wp_wand_l {s : Stuckness} {E : CoPset} {e : Expr} {Φ Ψ : Val → IProp GF} :
    (∀ v, Φ v -∗ Ψ v) ∗ wp P s E e Φ ⊢ wp P s E e Ψ :=
  BI.wand_elim_swap (wp_wand P)

@[rocq_alias iriswasm.wp_wand_r]
theorem wp_wand_r {s : Stuckness} {E : CoPset} {e : Expr} {Φ Ψ : Val → IProp GF} :
    wp P s E e Φ ∗ (∀ v, Φ v -∗ Ψ v) ⊢ wp P s E e Ψ :=
  BI.wand_elim (wp_wand P)

@[rocq_alias iriswasm.wp_frame_wand]
theorem wp_frame_wand {s : Stuckness} {E : CoPset} {e : Expr} {Φ : Val → IProp GF}
    {R : IProp GF} : R ⊢ wp P s E e (fun v => iprop(R -∗ Φ v)) -∗ wp P s E e Φ := by
  iintro R Hwp
  iapply wp_wand P $$ Hwp
  iintro %v H
  iapply H $$ R

/-! ## Lifting lemmas -/

section Lifting

open Language

variable {s : Stuckness} {E E₁ : CoPset} {e e₁ e₂ : Expr} {Φ : Val → IProp GF}

@[rocq_alias iriswasm.wp_lift_step_fupdN]
theorem wp_lift_step_fupdN (h : toVal e₁ = none) :
    (∀ σ₁ ns (obs obs' : List Obs) nt,
      stateInterp σ₁ ns (obs ++ obs') nt ={E,∅}=∗
      ⌜s.MaybeReducible (e₁, σ₁)⌝ ∗
      ∀ e₂ σ₂ eₜ, ⌜(e₁, σ₁) -<obs>-> (e₂, σ₂, eₜ)⌝ -∗
        £ (ι.numLatersPerStep ns + 1) ={∅}▷=∗^[ι.numLatersPerStep ns + 1] |={∅,E}=>
        stateInterp σ₂ (ns + 1) obs' (nt + eₜ.length) ∗
        ∃ a, P a ∗ (P a -∗ wp P s E e₂ Φ) ∗
        [∗list] ef ∈ eₜ, wp P s ⊤ ef ι.forkPost)
    ⊢ wp P s E e₁ Φ := by simp [(wp_unfold P (e := e₁)).to_eq, wp.pre, h]

@[rocq_alias iriswasm.wp_lift_step_fupd]
theorem wp_lift_step_fupd (h : toVal e₁ = none) :
    (∀ σ₁ ns (obs obs' : List Obs) nt,
      stateInterp σ₁ ns (obs ++ obs') nt ={E,∅}=∗
      ⌜s.MaybeReducible (e₁, σ₁)⌝ ∗
      ∀ e₂ σ₂ eₜ, ⌜(e₁, σ₁) -<obs>-> (e₂, σ₂, eₜ)⌝ -∗
        £ 1 ={∅}=∗ ▷ |={∅,E}=>
        stateInterp σ₂ (ns + 1) obs' (nt + eₜ.length) ∗
        ∃ a, P a ∗ (P a -∗ wp P s E e₂ Φ) ∗
        [∗list] ef ∈ eₜ, wp P s ⊤ ef ι.forkPost)
    ⊢ wp P s E e₁ Φ := by
  refine .trans ?_ <| wp_lift_step_fupdN P h
  iintro Hwp %σ₁ %ns %obs %obs' %nt Hσ
  imod Hwp $$ Hσ with ⟨$, Hwp⟩
  iintro !> %e₂ %σ₂ %eₜ %Hstep Hcred
  ihave Hcred := lc_weaken 1 (Nat.le_add_left 1 (ι.numLatersPerStep ns)) $$ Hcred
  refine .trans ?_ <| step_fupd_mono <|
    (laterN_intro _).trans <| step_fupdN_intro Std.LawfulSet.empty_subset
  iintro ⟨Hwp, Hcred⟩
  imod Hwp $$ %_ %_ %_ %Hstep Hcred with Hwp
  iapply step_fupd_intro Std.LawfulSet.empty_subset
  iassumption

@[rocq_alias iriswasm.wp_lift_stuck]
theorem wp_lift_stuck (h : toVal e = none) :
    (∀ σ ns obs nt, stateInterp σ ns obs nt ={E,∅}=∗ ⌜PrimStep.Stuck (e,σ)⌝)
    ⊢ wp P .MaybeStuck E e Φ := by
  iintro H
  rw [(wp_unfold P).to_eq]
  simp only [wp.pre, h]
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  imod H $$ Hσ with %Hirr
  replace ⟨_, Hirr⟩ := Hirr
  imodintro
  isplit
  · ipureintro; simp [Stuckness.MaybeReducible]
  iintro %e₂ %σ₂ %eₜ %Hstep
  nomatch Hirr obs e₂ σ₂ eₜ Hstep

@[rocq_alias iriswasm.wp_lift_step]
theorem wp_lift_step (h : toVal e₁ = none) :
    (∀ σ₁ ns obs obs' nt, stateInterp σ₁ ns (obs ++ obs') nt ={E,∅}=∗
      ⌜s.MaybeReducible (e₁, σ₁)⌝ ∗
      ▷ ∀ e₂ σ₂ eₜ, ⌜(e₁, σ₁) -<obs>-> (e₂, σ₂, eₜ)⌝ -∗ £ 1 ={∅,E}=∗
        stateInterp σ₂ (ns + 1) obs' (nt + eₜ.length) ∗
        ∃ a, P a ∗ (P a -∗ wp P s E e₂ Φ) ∗
        [∗list] ef ∈ eₜ, wp P s ⊤ ef ι.forkPost)
    ⊢ wp P s E e₁ Φ := by
  iintro H
  iapply wp_lift_step_fupd P h
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  imod H $$ %_ %_ %_ %_ %_ Hσ with ⟨$, H⟩
  iintro !> %e₂ %σ₂ %eₜ %Hstep Hcred !> !>
  iapply H $$ %_ %_ %_ %Hstep Hcred

@[rocq_alias iriswasm.wp_lift_pure_step_no_fork]
theorem wp_lift_pure_step_no_fork [Inhabited State] (E₂ : CoPset) (a : A) :
    (∀ σ₁, match s with | .NotStuck => PrimStep.Reducible (e₁,σ₁) | _ => toVal e₁ = none) →
    (∀ obs σ₁ e₂ σ₂ eₜ, (e₁, σ₁) -<obs>-> (e₂, σ₂, eₜ) → obs = [] ∧ σ₂ = σ₁ ∧ eₜ = []) →
    (|={E₁}[E₂]▷=> ∀ obs e₂ eₜ σ, ⌜(e₁, σ) -<obs>-> (e₂, σ, eₜ)⌝ -∗ £ 1 -∗
      P a -∗ wp P s E₁ e₂ Φ)
    ⊢ P a -∗ wp P s E₁ e₁ Φ := by
  iintro %Hsafe %Hpure H Ha
  have Hnone : toVal e₁ = none := by grind [Hsafe default]
  iapply wp_lift_step P Hnone
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  imod H
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplit
  · ipureintro; cases s <;> grind
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  obtain ⟨rfl, rfl, rfl⟩ := Hpure _ _ _ _ _ Hstep
  dsimp only [List.nil_append, List.length_nil]
  imod ι.stateInterp_mono $$ Hσ with $
  imod Hclose
  imod H
  imodintro
  simp only [Algebra.BigOpL.bigOpL_nil]
  ispecialize H $$ %_ %_ %_ %_ %Hstep Hcred
  iexists a
  iframe

@[rocq_alias iriswasm.wp_lift_pure_stuck]
theorem wp_lift_pure_stuck [Inhabited State] :
    (∀ σ, PrimStep.Stuck (e,σ)) →
    True ⊢ wp P .MaybeStuck E e Φ := by
  iintro %Hstuck -
  have ⟨toVal_e, _⟩ := Hstuck default
  iapply wp_lift_stuck P toVal_e
  iintro %σ %ns %obs' %nt -
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro -
  ipureintro
  apply Hstuck

@[rocq_alias iriswasm.wp_lift_atomic_step_fupd]
theorem wp_lift_atomic_step_fupd (h : toVal e₁ = none) (E₂ : CoPset) (a : A) :
    (∀ σ₁ ns obs obs' nt, stateInterp σ₁ ns (obs ++ obs') nt ={E₁}=∗
      ⌜s.MaybeReducible (e₁, σ₁)⌝ ∗
      ∀ e₂ σ₂ eₜ, ⌜(e₁, σ₁) -<obs>-> (e₂, σ₂, eₜ)⌝ -∗ £ 1 ={E₁}[E₂]▷=∗
        stateInterp σ₂ (ns + 1) obs' (nt + eₜ.length) ∗
        (∃ v, ⌜(toVal e₂) = some v⌝ ∧ Φ v) ∗ P a ∗
        [∗list] ef ∈ eₜ, wp P s ⊤ ef ι.forkPost)
    ⊢ wp P s E₁ e₁ (fun v => iprop(Φ v ∗ P a)) := by
  iintro H
  iapply wp_lift_step_fupd P h
  iintro %σ₁ %ns %obs %obs' %nt Hσ₁
  imod H $$ Hσ₁ with ⟨$, H⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose %e₂ %σ₂ %eₜ %Hstep Hcred
  imod Hclose with -
  imod H $$ %_ %_ %_ %Hstep Hcred with H
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose !>
  imod Hclose with -
  imod H with ⟨$, ⟨%v, %h, HQ⟩, Ha, $⟩
  imodintro
  iexists a
  iframe Ha
  iintro Ha
  iapply wp_value P ⟨ToVal.coe_of_toVal_eq_some h⟩
  iframe

@[rocq_alias iriswasm.wp_lift_atomic_step]
theorem wp_lift_atomic_step (h : toVal e₁ = none) (a : A) :
    (∀ σ₁ ns obs obs' nt, stateInterp σ₁ ns (obs ++ obs') nt ={E}=∗
      ⌜s.MaybeReducible (e₁, σ₁)⌝ ∗
      ▷ ∀ e₂ σ₂ eₜ, ⌜(e₁, σ₁) -<obs>-> (e₂, σ₂, eₜ)⌝ -∗ £ 1 ={E}=∗
        stateInterp σ₂ (ns + 1) obs' (nt + eₜ.length) ∗
        (∃ v, ⌜(toVal e₂) = some v⌝ ∧ Φ v) ∗ P a ∗
        [∗list] ef ∈ eₜ, wp P s ⊤ ef ι.forkPost)
    ⊢ wp P s E e₁ (fun v => iprop(Φ v ∗ P a)) := by
  iintro H
  iapply wp_lift_atomic_step_fupd P (E₂ := E) h
  iintro %σ₁ %ns %obs %obs' %nt Hσ₁
  imod H $$ [$] with ⟨$, H⟩
  iintro !> %e₂ %σ₂ %eₜ %Hstep Hcred !> !>
  iapply H $$ %_ %_ %_ %Hstep Hcred

@[rocq_alias iriswasm.wp_lift_pure_det_step_no_fork]
theorem wp_lift_pure_det_step_no_fork [Inhabited State] (E₂ : CoPset) (a : A)
    (Hsafe : ∀ σ₁, match s with | .NotStuck => PrimStep.Reducible (e₁, σ₁) | _ => toVal e₁ = none)
    (Hpuredet : ∀ {σ₁ obs e₂' σ₂ eₜ'}, (e₁, σ₁) -<obs>-> (e₂', σ₂, eₜ') →
      obs = [] ∧ σ₂ = σ₁ ∧ e₂' = e₂ ∧ eₜ' = []) :
    (|={E}[E₂]▷=> £ 1 -∗ P a -∗ wp P s E e₂ Φ) ⊢ P a -∗ wp P s E e₁ Φ := by
  iintro H
  iapply wp_lift_pure_step_no_fork P E₂ a Hsafe (by grind only)
  iapply step_fupd_wand $$ H
  iintro H
  iintro %obs %e' %eₜ' %σ %aux
  obtain ⟨rfl, _, rfl, rfl⟩ := Hpuredet aux
  iassumption

@[rocq_alias iriswasm.wp_pure_step_fupd]
theorem wp_pure_step_fupd [Inhabited State] (E₂ : CoPset) (a : A) {φ : Prop} {n : Nat}
    [Hexec : PureExec φ n e₁ e₂] (Hφ : φ) :
    (|={E}[E₂]▷=>^[n] £ n -∗ P a -∗ wp P s E e₂ Φ) ⊢ P a -∗ wp P s E e₁ Φ := by
  replace Hexec := Hexec.pureExec Hφ
  iinduction Hexec using Relation.Iterate.head_induction_on with simp only [step_fupdN]
  | rfl =>
    iintro Hwp Ha
    iapply fupd_wp P
    icases lc_zero with >Hz
    imodintro
    iapply Hwp $$ Hz Ha
  | @head n e₁ e₃ _ _ IH =>
    iintro Hwp
    obtain ⟨Hsafe, Hdet⟩ := ‹e₁ -ᵖ-> e₃›
    iapply wp_lift_pure_det_step_no_fork P E₂ a (e₂ := e₃) ?Hred (by grind)
    case Hred =>
      intro σ
      have _ : PrimStep.Reducible (e₁, σ) := by grind only [reducible_of_reducibleNoObs]
      grind [cases Stuckness]
    iapply step_fupd_wand $$ Hwp
    iintro Hwp Hone
    iapply IH
    iapply step_fupdN_wand $$ Hwp
    iintro Hwp Hc
    iapply Hwp $$ [Hone Hc]
    iapply lc_split
    iframe

@[rocq_alias iriswasm.wp_pure_step_later]
theorem wp_pure_step_later [Inhabited State] (a : A) {φ : Prop} {n : Nat}
    [Hexec : PureExec φ n e₁ e₂] (Hφ : φ) :
    ▷^[n] (£ n -∗ P a -∗ wp P s E e₂ Φ) ⊢ P a -∗ wp P s E e₁ Φ := by
  refine .trans ?_ (wp_pure_step_fupd P E a Hφ)
  suffices Hwp : ∀ (Q : IProp GF), ▷^[n] Q ⊢ |={E}▷=>^[n] Q by iapply Hwp
  intro Q
  clear Hexec
  induction n with
  | zero => exact .rfl
  | succ n IH =>
    simp only [step_fupdN]
    rw [(laterN_succ_left n).to_eq]
    refine (later_mono IH).trans ?_
    exact step_fupd_intro Std.LawfulSet.subset_refl

end Lifting

/-! ## Proof mode classes -/

section ProofModeClasses

open ProofMode

variable {s : Stuckness} {E E₁ E₂ : CoPset} {e : Expr} {Φ Ψ : Val → IProp GF} {Q R : IProp GF}

@[rocq_alias iriswasm.frame_wp]
instance frameWp {p : Bool} [H : ∀ v, FrameInstantiateExistDisabled p R (Φ v) (Ψ v)] :
    Frame p R (wp P s E e Φ) (wp P s E e Ψ) where
  frame := by
    refine (wp_frame_l P).trans ?_
    apply wp_mono
    exact fun v => (H v).frame_instantiatiate_exist_disabled.frame

@[rocq_alias iriswasm.is_except_0_wp]
instance isExcept0Wp : IsExcept0 (wp P s E e Φ) where
  is_except0 :=
    calc iprop(◇ _)
      _ ⊢ ◇ |={E}=> _ := BI.except0_mono fupd_intro
      _ ⊢ |={E}=> _ := BIFUpdate.except0
      _ ⊢ wp P s E e Φ := fupd_wp P

@[rocq_alias iriswasm.elim_modal_fupd_wp]
instance (priority := default + 10) elimModalFupdWp {io} p :
    ElimModal True p io false iprop(|={E}=> Q) Q (wp P s E e Φ) (wp P s E e Φ) where
  elim_modal := by
    iintro %_ ⟨H, G⟩
    icases BI.intuitionisticallyIf_elim $$ H with H
    iapply fupd_wp P
    imod H; imodintro
    iapply G $$ H

@[rocq_alias iriswasm.elim_modal_bupd_wp]
instance elimModalBupdWp {io} p :
    ElimModal True p io false iprop(|==> Q) Q (wp P s E e Φ) (wp P s E e Φ) where
  elim_modal := by
    rintro ⟨⟩
    refine BI.sep_mono (BI.intuitionisticallyIf_mono
      (BIUpdateFUpdate.fupd_of_bupd (E := E))) .rfl |>.trans ?_
    exact (elimModalFupdWp P _).elim_modal ⟨⟩ (io := io)

@[rocq_alias iriswasm.elim_modal_fupd_wp_atomic]
instance elimModalFupdWpAtomic {io} {p} (a : A) :
    ElimModal (Language.Atomic ↑s e) p io false iprop(|={E₁,E₂}=> Q) Q
      (wp P s E₁ e (fun v => iprop(Φ v ∗ P a)))
      (wp P s E₂ e (fun v => iprop(|={E₂,E₁}=> Φ v ∗ P a))) where
  elim_modal := by
    rintro atomic; iintro ⟨H, G⟩
    icases BI.intuitionisticallyIf_elim $$ H with H
    iapply wp_atomic P a
    imod H; imodintro
    iapply G $$ H

@[rocq_alias iriswasm.add_modal_fupd_wp]
instance addModalFupdWp : AddModal iprop(|={E}=> Q) Q (wp P s E e Φ) where
  add_modal := by
    iintro ⟨H1, H2⟩
    imod H1
    iapply H2 $$ H1

@[rocq_alias iriswasm.elim_acc_wp_atomic]
instance (priority := low) elimAcc_wp_atomic {X} (E₁ E₂ : CoPset) α β
    (γ : X → Option (IProp GF)) (a : A) :
    ElimAcc (Language.Atomic ↑s e) (fupd E₁ E₂) (fupd E₂ E₁) α β γ
      (wp P s E₁ e (fun v => iprop(Φ v ∗ P a)))
      (fun x => wp P s E₂ e (fun v => iprop(|={E₂}=> β x ∗ (γ x -∗? Φ v) ∗ P a))) where
  elim_acc := by
    dsimp only [accessor, BIBase.wandM, Option.getD]
    iintro %atomic Hinner >⟨%x, Hα, Hclose⟩
    iapply wp_wand P $$ [Hinner Hα]
    · iapply Hinner $$ Hα
    · iintro %v >⟨Hβ, HΦ, Ha⟩
      ispecialize Hclose $$ Hβ
      imod Hclose
      imodintro
      iframe Ha
      cases (γ x) with
      | none => iexact HΦ
      | some R => iapply HΦ $$ Hclose

@[rocq_alias iriswasm.elim_acc_wp_nonatomic]
instance elimAcc_wp_nonatomic {X} E (α β : X → IProp GF) (γ : X → Option (IProp GF)) :
    ElimAcc True (fupd E E) (fupd E E) α β γ (wp P s E e Φ)
    (fun x => wp P s E e (fun v => iprop(|={E}=> β x ∗ (γ x -∗? Φ v)))) where
  elim_acc := by
    dsimp only [accessor, BIBase.wandM, Option.getD]
    iintro %_ Hinner >⟨%x, Hα, Hclose⟩
    iapply wp_fupd P
    iapply wp_wand P $$ [Hinner Hα]
    · iapply Hinner $$ Hα
    · iintro %v >⟨Hβ, HΦ⟩
      ispecialize Hclose $$ Hβ
      imod Hclose
      imodintro
      cases (γ x) with
      | none => iexact HΦ
      | some R => iapply HΦ $$ Hclose

end ProofModeClasses

end IrisWasm.IrisWp
