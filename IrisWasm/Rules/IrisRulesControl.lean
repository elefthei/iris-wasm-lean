/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Rules.IrisRulesStructural
import IrisWasm.Helpers.Prelude.IrisLfilledProperties
import IrisWasm.Helpers.IrisWasmDeterm
import IrisWasm.Helpers.LfilledReduce

/-! Port of `theories/iris/rules/iris_rules_control.v`.

The Coq proofs redo the same lifting argument for every rule. Here it is factored into a few
generic (non-Coq) helpers: a step that reduces every state to itself with a fixed result
(`wp_det_step_frame`, `wp_det_step_value`, `wp_det_step_equiv`), and its lifting through
evaluation contexts (`wp_ctx_det_step`, `wp_frame_ctx_det_step`). Determinism of such a step
comes from `reduce_det` (`reduce_det_first`). -/

namespace IrisWasm

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm

/-! ### Operations on contexts (Coq section `control_operations`) -/

@[rocq_alias iriswasm.push_base]
def pushBase (lh : Lholed) (n : Nat) (es' vsPre esPost : List AdministrativeInstruction) : Lholed :=
  match lh with
  | .base vsPre' esPost' => .rec_ vsPre' n es' (.base vsPre esPost) esPost'
  | .rec_ vs m es'' lh' es => .rec_ vs m es'' (pushBase lh' n es' vsPre esPost) es

@[rocq_alias iriswasm.frame_base]
def frameBase (lh : Lholed) (l1 l2 : List AdministrativeInstruction) : Lholed :=
  match lh with
  | .base vs es => .base (vs ++ l1) (l2 ++ es)
  | .rec_ vs m es' lh' es => .rec_ vs m es' (frameBase lh' l1 l2) es

@[rocq_alias iriswasm.pull_base]
def pullBase : Lholed → Lholed × List AdministrativeInstruction × List AdministrativeInstruction
  | .base vs es => (.base [] [], vs, es)
  | .rec_ vs m es' lh' es =>
    let (lh'', l1, l2) := pullBase lh'
    (.rec_ vs m es' lh'' es, l1, l2)

@[rocq_alias iriswasm.lfilledInd_push]
theorem lfilledInd_push (i : Nat) :
    ∀ lh n es' es LI l1 l2, constList l1 = true →
      LfilledInd i lh [.label n es' (l1 ++ es ++ l2)] LI →
      LfilledInd (i + 1) (pushBase lh n es' l1 l2) es LI := by
  induction i with
  | zero =>
    intro lh n es' es LI l1 l2 hc h
    cases h with
    | lfilledBase vs _ es'' hvs => exact .lfilledRec 0 vs n es' _ es'' es _ hvs (.lfilledBase l1 es l2 hc)
  | succ i ih =>
    intro lh n es' es LI l1 l2 hc h
    cases h with
    | lfilledRec _ vs m e lh' e'' _ LI0 hvs h' =>
      exact .lfilledRec _ vs m e _ e'' es LI0 hvs (ih lh' n es' es LI0 l1 l2 hc h')

private theorem lfilledInd_zero_pushBase {lh : Lholed} {n : Nat}
    {es' l1 l2 es LI : List AdministrativeInstruction} :
    ¬ LfilledInd 0 (pushBase lh n es' l1 l2) es LI := by
  cases lh <;> intro h <;> cases h

@[rocq_alias iriswasm.iris_rules_control.lfilledInd_push_inv]
theorem lfilledInd_push_inv (i : Nat) :
    ∀ lh n es' es LI l1 l2, constList l1 = true →
      LfilledInd (i + 1) (pushBase lh n es' l1 l2) es LI →
      LfilledInd i lh [.label n es' (l1 ++ es ++ l2)] LI := by
  induction i with
  | zero =>
    intro lh n es' es LI l1 l2 _ h
    cases lh with
    | base vs es'' =>
      cases h with
      | lfilledRec _ _ _ _ _ _ _ LI0 hvs h' =>
        cases h' with
        | lfilledBase _ _ _ hc' => exact .lfilledBase vs _ es'' hvs
    | rec_ vs m e lh' e'' =>
      cases h with
      | lfilledRec _ _ _ _ _ _ _ LI0 _ h' => exact absurd h' lfilledInd_zero_pushBase
  | succ i ih =>
    intro lh n es' es LI l1 l2 hc h
    cases lh with
    | base vs es'' =>
      cases h with
      | lfilledRec _ _ _ _ _ _ _ LI0 _ h' => cases h'
    | rec_ vs m e lh' e'' =>
      cases h with
      | lfilledRec _ _ _ _ _ _ _ LI0 hvs h' =>
        exact .lfilledRec _ vs m e lh' e'' _ LI0 hvs (ih lh' n es' es LI0 l1 l2 hc h')

@[rocq_alias iriswasm.lfilledInd_frame]
theorem lfilledInd_frame (i : Nat) :
    ∀ lh l1 es l2 LI, constList l1 = true →
      LfilledInd i lh (l1 ++ es ++ l2) LI →
      LfilledInd i (frameBase lh l1 l2) es LI := by
  induction i with
  | zero =>
    intro lh l1 es l2 LI hc h
    cases h with
    | lfilledBase vs _ es'' hvs =>
      have := LfilledInd.lfilledBase (vs ++ l1) es (l2 ++ es'') (const_list_concat hvs hc)
      simpa [frameBase, List.append_assoc] using this
  | succ i ih =>
    intro lh l1 es l2 LI hc h
    cases h with
    | lfilledRec _ vs m e lh' e'' _ LI0 hvs h' =>
      exact .lfilledRec _ vs m e _ e'' es LI0 hvs (ih lh' l1 es l2 LI0 hc h')

@[rocq_alias iriswasm.lfilledInd_pull]
theorem lfilledInd_pull (i : Nat) :
    ∀ lh es LI, LfilledInd i lh es LI →
      let (lh', l1, l2) := pullBase lh
      LfilledInd i lh' (l1 ++ es ++ l2) LI := by
  induction i with
  | zero =>
    intro lh es LI h
    cases h with
    | lfilledBase vs _ es'' hvs =>
      have := LfilledInd.lfilledBase [] (vs ++ es ++ es'') [] (by simp [constList])
      simpa [pullBase, List.append_assoc] using this
  | succ i ih =>
    intro lh es LI h
    cases h with
    | lfilledRec _ vs m e lh' e'' _ LI0 hvs h' =>
      have := ih lh' es LI0 h'
      simp only [pullBase]
      rcases hp : pullBase lh' with ⟨lh'', l1, l2⟩
      rw [hp] at this
      exact .lfilledRec _ vs m e lh'' e'' _ LI0 hvs this

@[rocq_alias iriswasm.lfilled_push_base_swap]
theorem lfilled_push_base_swap {i : Nat} {lh : Lholed} {n : Nat}
    {es vs1 es2 es' LI : List AdministrativeInstruction} :
    lfilled (i + 1) (pushBase lh n es vs1 es2) es' LI = true →
    ∃ LI', lfilled i lh es' LI' = true := by
  rw [lfilled_Ind_Equivalent]
  intro h
  simp only [lfilled_Ind_Equivalent]
  induction lh generalizing i LI with
  | base vs es'' =>
    cases h with
    | lfilledRec _ _ _ _ _ _ _ LI0 hvs h' =>
      cases h'
      exact ⟨_, .lfilledBase vs es' es'' hvs⟩
  | rec_ vs m e lh' e'' ih =>
    cases h with
    | lfilledRec _ _ _ _ _ _ _ LI0 hvs h' =>
      cases i with
      | zero => exact absurd h' lfilledInd_zero_pushBase
      | succ i =>
        obtain ⟨LI', h''⟩ := ih h'
        exact ⟨_, .lfilledRec i vs m e lh' e'' es' LI' hvs h''⟩

@[rocq_alias iriswasm.lfilled_push_base_swap_inv]
theorem lfilled_push_base_swap_inv {i : Nat} {lh : Lholed} {n : Nat}
    {es vs1 es2 es' LI : List AdministrativeInstruction} :
    constList vs1 = true →
    lfilled i lh es' LI = true →
    ∃ LI', lfilled (i + 1) (pushBase lh n es vs1 es2) es' LI' = true := by
  intro hc h
  rw [lfilled_Ind_Equivalent] at h
  simp only [lfilled_Ind_Equivalent]
  induction h with
  | lfilledBase vs es0 es'' hvs =>
    exact ⟨_, .lfilledRec 0 vs n es _ es'' es0 _ hvs (.lfilledBase vs1 es0 es2 hc)⟩
  | lfilledRec k vs m e lh' e'' es0 LI0 hvs _ ih =>
    obtain ⟨LI', h'⟩ := ih
    exact ⟨_, .lfilledRec (k + 1) vs m e _ e'' es0 LI' hvs h'⟩

/-! ### Control rules (Coq section `control_rules`) -/

variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF]

/-! #### Generic deterministic-step helpers (not in Coq) -/

/-- A step that is possible from every store and frame, leaving both unchanged, is the only
possible step as soon as the first instruction is neither `grow_memory` nor `trap`. -/
theorem reduce_det_first {e₁ e₂ : Expr} {x : AdministrativeInstruction} {k : Nat}
    (hred : ∀ ws fr, Reduce ws fr e₁ ws fr e₂) (hfi : firstInstr e₁ = some (x, k))
    (hg : x ≠ .basic .growMemory) (ht : x ≠ .trap) :
    ∀ ws fr ws' fr' es', Reduce ws fr e₁ ws' fr' es' → ws' = ws ∧ fr' = fr ∧ es' = e₂ := by
  intro ws fr ws' fr' es' h
  rcases reduce_det (hred ws fr) h with heq | ⟨i, hi⟩ | ⟨i1, _, _, hi, _⟩
  · simp only [Prod.mk.injEq] at heq
    exact ⟨heq.1.symm, heq.2.1.symm, heq.2.2.symm⟩
  · rw [hfi] at hi; cases hi; exact absurd rfl hg
  · rw [hfi] at hi; cases hi; exact absurd rfl ht

theorem firstInstr_const_basic {vs : List AdministrativeInstruction} {b : BasicInstruction}
    (hvs : constList vs = true) (hb : ∀ v, b ≠ .const v) :
    firstInstr (vs ++ [.basic b]) = some (.basic b, 0) := by
  rw [first_instr_const _ _ hvs]
  cases b <;> first | exact (hb _ rfl).elim | simp [firstInstr, firstInstrInstr, findFirstSome]

theorem firstInstr_label_of {n : Nat} {es LI : List AdministrativeInstruction}
    {x : AdministrativeInstruction} {k : Nat} (h : firstInstr LI = some (x, k)) :
    firstInstr [.label n es LI] = some (x, k + 1) := by
  rw [firstInstr_cons, firstInstrInstr_label, h]

/-- A pure deterministic step, paying with (and giving back) the frame resource. -/
theorem wp_det_step_frame {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF}
    {e₁ e₂ : Expr} {f : Frame}
    (hred : ∀ ws fr, Reduce ws fr e₁ ws fr e₂)
    (hdet : ∀ ws fr ws' fr' es', Reduce ws fr e₁ ws' fr' es' → ws' = ws ∧ fr' = fr ∧ es' = e₂) :
    ⊢ iprop(↪[frame] f -∗ ▷ (↪[frame] f -∗ WP e₂ @ s ; E {{ Φ }}) -∗ WP e₁ @ s ; E {{ Φ }}) := by
  have hpd : ∀ {σ₁ : State} {obs e₂' σ₂ eₜ'}, primStep (e₁, σ₁) obs (e₂', σ₂, eₜ') →
      obs = [] ∧ σ₂ = σ₁ ∧ e₂' = e₂ ∧ eₜ' = [] := by
    intro ⟨ws, locs, inst⟩ obs e₂' ⟨ws', locs', inst'⟩ eₜ' ⟨h, ho, he⟩
    obtain ⟨rfl, hf, rfl⟩ := hdet _ _ _ _ _ h
    cases hf
    exact ⟨ho, rfl, rfl, he⟩
  have key := IrisWp.wp_lift_pure_det_step_no_fork (fun f : Frame => iprop(↪[frame] f))
    (ι := wasmIrisGS) (s := s) (e₁ := e₁) (e₂ := e₂) (Φ := Φ) (E := E) E f (by
      intro ⟨ws, locs, inst⟩
      cases s
      · exact ⟨[], e₂, (ws, locs, inst), [], hred ws ⟨locs, inst⟩, rfl, rfl⟩
      · exact val_head_stuck_reduce (hred ws ⟨locs, inst⟩)) hpd
  let := @WasmG.invGS hlc GF _
  iintro Hf H
  iapply key $$ [H] Hf
  iapply step_fupd_intro (Std.LawfulSet.subset_refl)
  inext
  iintro _ Hf
  iapply H $$ Hf

/-- A pure deterministic step to a value, without owning the frame. -/
theorem wp_det_step_value {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF}
    {e₁ e₂ : Expr} {f : Frame} {v : Val}
    (hred : ∀ ws fr, Reduce ws fr e₁ ws fr e₂)
    (hdet : ∀ ws fr ws' fr' es', Reduce ws fr e₁ ws' fr' es' → ws' = ws ∧ fr' = fr ∧ es' = e₂)
    (hv : toVal e₂ = some v) :
    ⊢ iprop(▷ WP e₂ @ s ; E {{ w, Φ w ∗ ↪[frame] f }} -∗
      WP e₁ @ s ; E {{ w, Φ w ∗ ↪[frame] f }}) := by
  have hv1 := val_head_stuck_reduce (hred default default)
  have he := of_to_val _ _ hv
  subst he
  let := @WasmG.invGS hlc GF _
  show ⊢ iprop(▷ IrisWp.wp (ι := wasmIrisGS) (fun f : Frame => iprop(↪[frame] f)) s E (ofVal v)
      (fun w => iprop(Φ w ∗ ↪[frame] f)) -∗
    IrisWp.wp (ι := wasmIrisGS) (fun f : Frame => iprop(↪[frame] f)) s E e₁
      (fun w => iprop(Φ w ∗ ↪[frame] f)))
  iintro H
  iapply IrisWp.wp_lift_atomic_step (ι := wasmIrisGS) (fun f : Frame => iprop(↪[frame] f)) hv1 f
  iintro %σ %ns %obs %obs' %nt Hσ
  imodintro
  isplitr
  · ipureintro
    rcases σ with ⟨ws, locs, inst⟩
    cases s
    · exact ⟨[], _, (ws, locs, inst), [], hred ws ⟨locs, inst⟩, rfl, rfl⟩
    · trivial
  inext
  iintro %e₂' %σ₂ %eₜ %hstep -
  rcases σ with ⟨ws, locs, inst⟩
  rcases σ₂ with ⟨ws', locs', inst'⟩
  obtain ⟨hr, rfl, rfl⟩ := hstep
  obtain ⟨rfl, hf, rfl⟩ := hdet _ _ _ _ _ hr
  cases hf
  ihave H := (IrisWp.wp_value_fupd' (ι := wasmIrisGS) (fun f : Frame => iprop(↪[frame] f))).1 $$ H
  imod H with ⟨HΦ, Hf⟩
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  isplitl [HΦ]
  · iexists v
    isplit
    · ipureintro; exact to_of_val v
    · iexact HΦ
  isplitl [Hf]
  · iexact Hf
  · simp
    iempintro

/-- Two expressions that both step deterministically to the same expression have the same WP. -/
theorem wp_det_step_equiv {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF}
    {e₁ e₂ e' : Expr}
    (h₁ : ∀ ws fr, Reduce ws fr e₁ ws fr e')
    (h₂ : ∀ ws fr, Reduce ws fr e₂ ws fr e')
    (hdet : ∀ ws fr ws' fr' es', Reduce ws fr e₂ ws' fr' es' → ws' = ws ∧ fr' = fr ∧ es' = e') :
    ⊢ iprop(WP e₁ @ s ; E {{ Φ }} -∗ WP e₂ @ s ; E {{ Φ }}) := by
  have hv1 := val_head_stuck_reduce (h₁ default default)
  have hv2 := val_head_stuck_reduce (h₂ default default)
  show ⊢ iprop(IrisWp.wp (ι := wasmIrisGS) (fun f : Frame => iprop(↪[frame] f)) s E e₁ Φ -∗
    IrisWp.wp (ι := wasmIrisGS) (fun f : Frame => iprop(↪[frame] f)) s E e₂ Φ)
  rw [(IrisWp.wp_unfold (ι := wasmIrisGS) (fun f : Frame => iprop(↪[frame] f))).to_eq,
    (IrisWp.wp_unfold (ι := wasmIrisGS) (fun f : Frame => iprop(↪[frame] f))).to_eq]
  dsimp only [IrisWp.wp.pre]
  rw [show ProgramLogic.toVal e₁ = none from hv1, show ProgramLogic.toVal e₂ = none from hv2]
  dsimp only
  let := @WasmG.invGS hlc GF _
  iintro H %σ %ns %obs %obs' %nt Hσ
  imod H $$ %σ %ns %obs %obs' %nt Hσ with ⟨_, H⟩
  imodintro
  isplitr
  · ipureintro
    rcases σ with ⟨ws, locs, inst⟩
    cases s
    · exact ⟨[], e', (ws, locs, inst), [], h₂ ws ⟨locs, inst⟩, rfl, rfl⟩
    · trivial
  iintro %e₂' %σ₂ %eₜ %hstep
  rcases σ with ⟨ws, locs, inst⟩
  rcases σ₂ with ⟨ws', locs', inst'⟩
  obtain ⟨hr, rfl, rfl⟩ := hstep
  obtain ⟨rfl, hf, rfl⟩ := hdet _ _ _ _ _ hr
  cases hf
  iapply H $$ %e₂' %(ws', locs, inst) %([] : List Expr) %(⟨h₁ ws' ⟨locs, inst⟩, rfl, rfl⟩)

/-- `wp_det_step_frame` for a step whose first instruction is neither `grow_memory` nor `trap`. -/
theorem wp_det_first_frame {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF}
    {e₁ e₂ : Expr} {f : Frame} {x : AdministrativeInstruction} {k : Nat}
    (hred : ∀ ws fr, Reduce ws fr e₁ ws fr e₂) (hfi : firstInstr e₁ = some (x, k))
    (hg : x ≠ .basic .growMemory) (ht : x ≠ .trap) :
    ⊢ iprop(↪[frame] f -∗ ▷ (↪[frame] f -∗ WP e₂ @ s ; E {{ Φ }}) -∗ WP e₁ @ s ; E {{ Φ }}) :=
  wp_det_step_frame hred (reduce_det_first hred hfi hg ht)

/-- `wp_det_step_frame` lifted through an evaluation context. -/
theorem wp_ctx_det_step {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF}
    {e₁ e₂ : Expr} {i : Nat} {lh : Lholed} {f : Frame} {x : AdministrativeInstruction} {k : Nat}
    (hred : ∀ ws fr, Reduce ws fr e₁ ws fr e₂) (hfi : firstInstr e₁ = some (x, k))
    (hg : x ≠ .basic .growMemory) (ht : x ≠ .trap) :
    ⊢ iprop(↪[frame] f -∗ ▷ (↪[frame] f -∗ WP e₂ @ s ; E CTX i ; lh {{ Φ }}) -∗
      WP e₁ @ s ; E CTX i ; lh {{ Φ }}) := by
  unfold wpWasmCtx
  iintro Hf H %LI %hLI
  obtain ⟨LI', hLI'⟩ := lfilled_swap e₂ hLI
  have hred' : ∀ ws fr, Reduce ws fr LI ws fr LI' :=
    fun ws fr => Reduce.label e₁ e₂ i lh (hred ws fr) hLI hLI'
  iapply wp_det_step_frame hred'
    (reduce_det_first hred' (starts_with_lfilled x k e₁ i lh LI hfi hLI) hg ht) $$ Hf
  inext
  iintro Hf
  iapply H $$ Hf %LI' %hLI'

/-- `wp_det_step_frame` lifted through an evaluation context inside a local frame. -/
theorem wp_frame_ctx_det_step {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF}
    {e₁ e₂ : Expr} {i : Nat} {lh : Lholed} {n1 : Nat} {f1 f : Frame}
    {x : AdministrativeInstruction} {k : Nat}
    (hred : ∀ ws fr, Reduce ws fr e₁ ws fr e₂) (hfi : firstInstr e₁ = some (x, k))
    (hg : x ≠ .basic .growMemory) (ht : x ≠ .trap) :
    ⊢ iprop(↪[frame] f -∗ ▷ (↪[frame] f -∗ WP e₂ @ s ; E FRAME n1 ; f1 CTX i ; lh {{ Φ }}) -∗
      WP e₁ @ s ; E FRAME n1 ; f1 CTX i ; lh {{ Φ }}) := by
  unfold wpWasmCtxFrame
  iintro Hf H %LI %hLI
  obtain ⟨LI', hLI'⟩ := lfilled_swap e₂ hLI
  have hred' : ∀ ws fr, Reduce ws fr [.local n1 f1 LI] ws fr [.local n1 f1 LI'] :=
    fun ws _ => Reduce.local (Reduce.label e₁ e₂ i lh (hred ws f1) hLI hLI')
  iapply wp_det_step_frame hred'
    (reduce_det_first hred'
      (first_instr_local _ _ _ _ _ (starts_with_lfilled x k e₁ i lh LI hfi hLI)) hg ht) $$ Hf
  inext
  iintro Hf
  iapply H $$ Hf %LI' %hLI'

theorem lfilled_rec_inv {k n : Nat} {vs es es' e LI : List AdministrativeInstruction} {lh : Lholed}
    (h : lfilled (k + 1) (.rec_ vs n es lh es') e LI = true) :
    ∃ LI0, constList vs = true ∧ lfilled k lh e LI0 = true ∧
      LI = vs ++ [.label n es LI0] ++ es' := by
  rw [lfilled_Ind_Equivalent] at h
  cases h with
  | lfilledRec _ _ _ _ _ _ _ LI0 hvs h0 => exact ⟨LI0, hvs, by rw [lfilled_Ind_Equivalent]; exact h0, rfl⟩

/-- The `br` step of a label sitting in a base context. -/
theorem br_label_reduce {j n1 : Nat} {lh : Lholed} {l l0 l1 vs LI0 : List AdministrativeInstruction}
    (hl : constList l = true) (hvs : constList vs = true) (hlen : vs.length = n1)
    (hfill : lfilled j lh (vs ++ [.basic (.br j)]) LI0 = true) :
    ∀ ws fr, Reduce ws fr (l ++ [.label n1 l0 LI0] ++ l1) ws fr (l ++ (vs ++ l0) ++ l1) :=
  fun _ _ => Reduce.label [.label n1 l0 LI0] (vs ++ l0) 0 (.base l l1)
    (.simple (.br j lh hvs hlen hfill))
    (by rw [lfilled_Ind_Equivalent]; exact .lfilledBase _ _ _ hl)
    (by rw [lfilled_Ind_Equivalent]; exact .lfilledBase _ _ _ hl)

/-- `[label m ctx [trap]]` only reduces to `[trap]` (`reduce_det` is too weak here). -/
theorem reduce_label_trap {s f s' f'} {m : Nat} {ctx es' : List AdministrativeInstruction} :
    Reduce s f [.label m ctx [.trap]] s' f' es' → s' = s ∧ f' = f ∧ es' = [.trap] := by
  intro h
  generalize hE : [AdministrativeInstruction.label m ctx [.trap]] = E at h
  induction h with
  | simple hs =>
    cases hs <;> first
      | simp at hE; done
      | (have := congrArg List.getLast? hE; simp at this; done)
      | exact ⟨rfl, rfl, rfl⟩
      | skip
    case labelConst =>
      simp at hE; obtain ⟨-, -, rfl⟩ := hE; simp_all [constList, isConst]
    case br =>
      simp at hE; obtain ⟨-, -, rfl⟩ := hE
      rename_i hfill
      obtain ⟨-, -, h⟩ := filled_singleton _ _ _ _ hfill (by simp) (by simp)
      have := congrArg List.getLast? h; simp at this
  | label es es'' k lh hr hf hf' ih =>
    subst hE
    rw [lfilled_Ind_Equivalent] at hf
    rcases LfilledReduce.singleton_split hf rfl (fun h => empty_no_reduce (h ▸ hr)) with
      ⟨rfl, rfl, rfl⟩ | ⟨k', n, es0, lh', l, rfl, rfl, he, hl'⟩
    · obtain ⟨rfl, rfl, rfl⟩ := ih rfl
      obtain ⟨_, _, h1, _, rfl⟩ := lfilled_zero_inv hf'
      cases h1; simp
    · simp only [AdministrativeInstruction.label.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      rw [← lfilled_Ind_Equivalent] at hl'
      obtain ⟨-, -, rfl⟩ := filled_singleton _ _ _ _ hl' (by simp)
        (fun h => empty_no_reduce (h ▸ hr))
      exact (test_no_reduce_trap hr).elim
  | invokeNative => have := congrArg List.getLast? hE; simp at this
  | invokeHost => have := congrArg List.getLast? hE; simp at this
  | _ => simp at hE

/-! #### Structural lemmas for contexts -/

@[rocq_alias iriswasm.wp_base]
theorem wp_base {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF}
    {vs vs' es'' : List AdministrativeInstruction} :
    iprop(WP (vs' ++ vs ++ es'') @ s ; E {{ Φ }}) ⊢
      iprop(WP vs @ s ; E CTX 0 ; (Lholed.base vs' es'') {{ Φ }}) := by
  unfold wpWasmCtx
  iintro H %LI %hLI
  rw [lfilled_Ind_Equivalent] at hLI
  cases hLI
  iexact H

@[rocq_alias iriswasm.wp_base_push]
theorem wp_base_push {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF}
    {es l1 l2 : List AdministrativeInstruction} {i : Nat} {lh : Lholed}
    (hconst : constList l1 = true) :
    iprop(WP es @ s ; E CTX i ; (frameBase lh l1 l2) {{ Φ }}) ⊢
      iprop(WP (l1 ++ es ++ l2) @ s ; E CTX i ; lh {{ Φ }}) := by
  unfold wpWasmCtx
  iintro H %LI %hLI
  rw [lfilled_Ind_Equivalent] at hLI
  iapply H $$ %LI %(by rw [lfilled_Ind_Equivalent]; exact lfilledInd_frame _ _ _ _ _ _ hconst hLI)

@[rocq_alias iriswasm.wp_base_pull]
theorem wp_base_pull {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF}
    {es : List AdministrativeInstruction} {i : Nat} {lh : Lholed} :
    (let (lh', l1, l2) := pullBase lh
     iprop(WP (l1 ++ es ++ l2) @ s ; E CTX i ; lh' {{ Φ }})) ⊢
      iprop(WP es @ s ; E CTX i ; lh {{ Φ }}) := by
  unfold wpWasmCtx
  have hpull := fun LI (h : LfilledInd i lh es LI) => lfilledInd_pull i lh es LI h
  rcases hp : pullBase lh with ⟨lh', l1, l2⟩
  simp only [hp] at hpull ⊢
  iintro H %LI %hLI
  rw [lfilled_Ind_Equivalent] at hLI
  iapply H $$ %LI %(by rw [lfilled_Ind_Equivalent]; exact hpull LI hLI)

@[rocq_alias iriswasm.wp_label_push]
theorem wp_label_push {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF}
    {es : List AdministrativeInstruction} {i : Nat} {lh : Lholed} {n : Nat}
    {es' l1 l2 : List AdministrativeInstruction} (hconst : constList l1 = true) :
    iprop(WP es @ s ; E CTX (i + 1) ; (pushBase lh n es' l1 l2) {{ Φ }}) ⊢
      iprop(WP [AdministrativeInstruction.label n es' (l1 ++ es ++ l2)] @ s ; E CTX i ; lh
        {{ Φ }}) := by
  unfold wpWasmCtx
  iintro H %LI %hLI
  rw [lfilled_Ind_Equivalent] at hLI
  iapply H $$ %LI %(by rw [lfilled_Ind_Equivalent]; exact lfilledInd_push _ _ _ _ _ _ _ _ hconst hLI)

@[rocq_alias iriswasm.wp_label_push_nil]
theorem wp_label_push_nil {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF}
    {es : List AdministrativeInstruction} {i : Nat} {lh : Lholed} {n : Nat}
    {es' : List AdministrativeInstruction} :
    iprop(WP es @ s ; E CTX (i + 1) ; (pushBase lh n es' [] []) {{ Φ }}) ⊢
      iprop(WP [AdministrativeInstruction.label n es' es] @ s ; E CTX i ; lh {{ Φ }}) := by
  have := wp_label_push (s := s) (E := E) (Φ := Φ) (es := es) (i := i) (lh := lh) (n := n)
    (es' := es') (l1 := []) (l2 := []) rfl
  simp only [List.nil_append, List.append_nil] at this
  exact this

@[rocq_alias iriswasm.wp_label_pull]
theorem wp_label_pull {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF}
    {es : List AdministrativeInstruction} {i : Nat} {lh : Lholed} {n : Nat}
    {es' l1 l2 : List AdministrativeInstruction} (hconst : constList l1 = true) :
    iprop(WP [AdministrativeInstruction.label n es' (l1 ++ es ++ l2)] @ s ; E CTX i ; lh
      {{ Φ }}) ⊢
      iprop(WP es @ s ; E CTX (i + 1) ; (pushBase lh n es' l1 l2) {{ Φ }}) := by
  unfold wpWasmCtx
  iintro H %LI %hLI
  rw [lfilled_Ind_Equivalent] at hLI
  iapply H $$ %LI %(by
    rw [lfilled_Ind_Equivalent]; exact lfilledInd_push_inv _ _ _ _ _ _ _ _ hconst hLI)

@[rocq_alias iriswasm.wp_label_pull_nil]
theorem wp_label_pull_nil {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF}
    {es : List AdministrativeInstruction} {i : Nat} {lh : Lholed} {n : Nat}
    {es' : List AdministrativeInstruction} :
    iprop(WP [AdministrativeInstruction.label n es' es] @ s ; E CTX i ; lh {{ Φ }}) ⊢
      iprop(WP es @ s ; E CTX (i + 1) ; (pushBase lh n es' [] []) {{ Φ }}) := by
  have := wp_label_pull (s := s) (E := E) (Φ := Φ) (es := es) (i := i) (lh := lh) (n := n)
    (es' := es') (l1 := []) (l2 := []) rfl
  simp only [List.nil_append, List.append_nil] at this
  exact this

/-! #### Structural lemmas for contexts within a local scope -/

@[rocq_alias iriswasm.wp_base_push_local]
theorem wp_base_push_local {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF}
    {es l1 l2 : List AdministrativeInstruction} {i : Nat} {lh : Lholed} {n : Nat} {f : Frame}
    (hconst : constList l1 = true) :
    iprop(WP es @ s ; E FRAME n ; f CTX i ; (frameBase lh l1 l2) {{ v, Φ v }}) ⊢
      iprop(WP (l1 ++ es ++ l2) @ s ; E FRAME n ; f CTX i ; lh {{ v, Φ v }}) := by
  unfold wpWasmCtxFrame
  iintro H %LI %hLI
  rw [lfilled_Ind_Equivalent] at hLI
  iapply H $$ %LI %(by rw [lfilled_Ind_Equivalent]; exact lfilledInd_frame _ _ _ _ _ _ hconst hLI)

@[rocq_alias iriswasm.wp_label_push_local]
theorem wp_label_push_local {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF}
    {es : List AdministrativeInstruction} {i : Nat} {lh : Lholed} {n : Nat}
    {es' l1 l2 : List AdministrativeInstruction} {m : Nat} {f : Frame}
    (hconst : constList l1 = true) :
    iprop(WP es @ s ; E FRAME m ; f CTX (i + 1) ; (pushBase lh n es' l1 l2) {{ v, Φ v }}) ⊢
      iprop(WP [AdministrativeInstruction.label n es' (l1 ++ es ++ l2)] @ s ; E FRAME m ; f
        CTX i ; lh {{ v, Φ v }}) := by
  unfold wpWasmCtxFrame
  iintro H %LI %hLI
  rw [lfilled_Ind_Equivalent] at hLI
  iapply H $$ %LI %(by rw [lfilled_Ind_Equivalent]; exact lfilledInd_push _ _ _ _ _ _ _ _ hconst hLI)

@[rocq_alias iriswasm.wp_label_push_nil_local]
theorem wp_label_push_nil_local {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF}
    {es : List AdministrativeInstruction} {i : Nat} {lh : Lholed} {n : Nat}
    {es' : List AdministrativeInstruction} {m : Nat} {f : Frame} :
    iprop(WP es @ s ; E FRAME m ; f CTX (i + 1) ; (pushBase lh n es' [] []) {{ v, Φ v }}) ⊢
      iprop(WP [AdministrativeInstruction.label n es' es] @ s ; E FRAME m ; f CTX i ; lh
        {{ v, Φ v }}) := by
  have := wp_label_push_local (s := s) (E := E) (Φ := Φ) (es := es) (i := i) (lh := lh) (n := n)
    (es' := es') (l1 := []) (l2 := []) (m := m) (f := f) rfl
  simp only [List.nil_append, List.append_nil] at this
  exact this

/-! #### Control flow rules -/

@[rocq_alias iriswasm.wp_return]
theorem wp_return {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF}
    {es vs : List AdministrativeInstruction} {vs0 : List Value} {n : Nat} {f0 f : Frame}
    {i : Nat} {lh : Lholed}
    (hval : toVal vs = some (.immV vs0)) (hlen : vs.length = n)
    (hlf : lfilled i lh (vs ++ [.basic .return_]) es = true) :
    ⊢ iprop(▷ WP vs @ s ; E {{ v, Φ v ∗ ↪[frame] f }} -∗
      WP [AdministrativeInstruction.local n f0 es] @ s ; E {{ v, Φ v ∗ ↪[frame] f }}) := by
  have hcvs := to_val_const_list _ _ hval
  have hred : ∀ ws fr, Reduce ws fr [.local n f0 es] ws fr vs :=
    fun _ _ => .simple (.return_ i lh hcvs hlen hlf)
  exact wp_det_step_value hred (reduce_det_first hred (first_instr_local _ _ _ _ _
    (starts_with_lfilled _ _ _ _ _ _ (firstInstr_const_basic hcvs (by simp)) hlf))
    (by simp) (by simp)) hval

@[rocq_alias iriswasm.wp_frame_return]
theorem wp_frame_return {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF}
    {vs : List AdministrativeInstruction} {vs0 : List Value} {n : Nat} {f0 f : Frame}
    {i : Nat} {lh : Lholed} {LI : List AdministrativeInstruction}
    (hval : toVal vs = some (.immV vs0)) (hlen : vs.length = n)
    (hlf : lfilled i lh (vs ++ [.basic .return_]) LI = true) :
    iprop(▷ WP vs @ s ; E {{ v, Φ v ∗ ↪[frame] f }}) ⊢
      iprop(WP LI @ s ; E FRAME n ; f0 {{ v, Φ v ∗ ↪[frame] f }}) := by
  unfold wpWasmFrame
  iintro H
  iapply wp_return hval hlen hlf $$ H

@[rocq_alias iriswasm.wp_ctx_frame_return]
theorem wp_ctx_frame_return {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF}
    {vs : List AdministrativeInstruction} {vs0 : List Value} {n : Nat} {f0 f : Frame}
    {i : Nat} {lh : Lholed}
    (hval : toVal vs = some (.immV vs0)) (hlen : vs.length = n) :
    iprop(▷ WP vs @ s ; E {{ v, Φ v ∗ ↪[frame] f }}) ⊢
      iprop(WP (vs ++ [.basic .return_]) @ s ; E FRAME n ; f0 CTX i ; lh
        {{ v, Φ v ∗ ↪[frame] f }}) := by
  unfold wpWasmCtxFrame
  iintro H %LI %hLI
  iapply wp_return hval hlen hLI $$ H

@[rocq_alias iriswasm.wp_br]
theorem wp_br {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF} {n : Nat}
    {vs es : List AdministrativeInstruction} {i : Nat} {LI : List AdministrativeInstruction}
    {lh : Lholed} {f : Frame}
    (hvs : constList vs = true) (hlen : vs.length = n)
    (hfill : lfilled i lh (vs ++ [.basic (.br i)]) LI = true) :
    ⊢ iprop(↪[frame] f -∗ ▷ (↪[frame] f -∗ WP (vs ++ es) @ s ; E {{ v, Φ v }}) -∗
      WP [AdministrativeInstruction.label n es LI] @ s ; E {{ v, Φ v }}) := by
  have hred : ∀ ws fr, Reduce ws fr [.label n es LI] ws fr (vs ++ es) :=
    fun _ _ => .simple (.br i lh hvs hlen hfill)
  exact wp_det_step_frame hred (reduce_det_first hred (firstInstr_label_of
    (starts_with_lfilled _ _ _ _ _ _ (firstInstr_const_basic hvs (by simp)) hfill))
    (by simp) (by simp))

@[rocq_alias iriswasm.wp_br_ctx_nested]
theorem wp_br_ctx_nested {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF} {n : Nat}
    {vs es : List AdministrativeInstruction} {i j : Nat} {lh lh' lh'' : Lholed}
    {vs' es' : List AdministrativeInstruction} {f : Frame}
    {vs0' : List AdministrativeInstruction} {n0 : Nat} {es0 es0' : List AdministrativeInstruction}
    (hlt : i + 1 < j)
    (hlayer : getLayer lh' (lhDepth lh' - (i + 1 + 1)) =
      some (vs0', n0, es0, .rec_ vs' n es lh es', es0'))
    (hminus : lhMinus lh' lh'' = some (.rec_ vs' n es lh es'))
    (hvs : constList vs = true) (hlen : vs.length = n) :
    ⊢ iprop(↪[frame] f -∗
      ▷ (↪[frame] f -∗ WP (vs' ++ (vs ++ es) ++ es') @ s ; E CTX (j - (i + 1)) ; lh'' {{ Φ }}) -∗
      WP (vs ++ [.basic (.br i)]) @ s ; E CTX j ; lh' {{ Φ }}) := by
  unfold wpWasmCtx
  iintro Hf H %LI %hLI
  obtain ⟨LI', h1, h2⟩ := lfilled_minus lh' (i + 1) vs0' n0 es0 (.rec_ vs' n es lh es') es0' _ LI
    j lh'' hminus (by rw [lfilled_depth _ _ _ _ hLI]; exact hlt) hlayer hLI
  obtain ⟨LI0, hvs', h0, rfl⟩ := lfilled_rec_inv h1
  have hred := br_label_reduce (l0 := es) (l1 := es') hvs' hvs hlen h0
  obtain ⟨LIr, hLIr⟩ := lfilled_swap (vs' ++ (vs ++ es) ++ es') h2
  have hred' : ∀ ws fr, Reduce ws fr LI ws fr LIr :=
    fun ws fr => Reduce.label _ _ _ lh'' (hred ws fr) h2 hLIr
  have hfi := starts_with_lfilled _ _ _ _ _ _
    (starts_with_lfilled _ _ _ _ _ _ (firstInstr_const_basic hvs (by simp)) h1) h2
  iapply wp_det_first_frame hred' hfi (by simp) (by simp) $$ Hf
  inext
  iintro Hf
  iapply H $$ Hf %LIr %hLIr

@[rocq_alias iriswasm.wp_block]
theorem wp_block {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF}
    {vs : List AdministrativeInstruction} {es : List BasicInstruction} {n m : Nat}
    {t1s t2s : List ValueType} {f : Frame}
    (hvs : constList vs = true) (hlen1 : vs.length = n) (hlen2 : t1s.length = n)
    (hlen3 : t2s.length = m) :
    ⊢ iprop(↪[frame] f -∗
      ▷ (↪[frame] f -∗ WP [AdministrativeInstruction.label m [] (vs ++ toEList es)] @ s ; E
        {{ v, Φ v }}) -∗
      WP (vs ++ [.basic (.block (.tf t1s t2s) es)]) @ s ; E {{ v, Φ v }}) := by
  have hred : ∀ ws fr, Reduce ws fr (vs ++ [.basic (.block (.tf t1s t2s) es)]) ws fr
      [.label m [] (vs ++ toEList es)] :=
    fun _ _ => .simple (.block n hvs hlen1 hlen2 hlen3)
  exact wp_det_step_frame hred
    (reduce_det_first hred (firstInstr_const_basic hvs (by simp)) (by simp) (by simp))

@[rocq_alias iriswasm.wp_label_value]
theorem wp_label_value {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF}
    {es : List AdministrativeInstruction} {m : Nat} {ces : List AdministrativeInstruction}
    {v : List Value} {f : Frame}
    (hval : toVal es = some (.immV v)) :
    ⊢ iprop(↪[frame] f -∗ ▷ Φ (.immV v) -∗
      WP [AdministrativeInstruction.label m ces es] @ s ; E {{ v, Φ v ∗ ↪[frame] f }}) := by
  have hc := to_val_const_list _ _ hval
  have hred : ∀ ws fr, Reduce ws fr [.label m ces es] ws fr es :=
    fun _ _ => .simple (.labelConst hc)
  have hdet := reduce_det_first hred (find_first_const_label es ces m hc) (by simp) (by simp)
  have he := of_to_val _ _ hval
  subst he
  iintro Hf HΦ
  iapply wp_det_step_frame hred hdet $$ Hf
  inext
  iintro Hf
  iapply IrisWp.wp_value' (ι := wasmIrisGS) (fun f : Frame => iprop(↪[frame] f))
  iframe

@[rocq_alias iriswasm.iris_rules_control.wp_label_trap]
theorem wp_label_trap {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF}
    {es : List AdministrativeInstruction} {m : Nat} {ctx : List AdministrativeInstruction}
    {f0 : Frame}
    (hval : toVal es = some .trapV) :
    ⊢ iprop(↪[frame] f0 -∗ ▷ Φ .trapV -∗
      WP [AdministrativeInstruction.label m ctx es] @ s ; E {{ v, Φ v ∗ ↪[frame] f0 }}) := by
  have he := of_to_val _ _ hval
  subst he
  have hred : ∀ ws fr, Reduce ws fr [.label m ctx (ofVal .trapV)] ws fr (ofVal .trapV) :=
    fun _ _ => .simple .labelTrap
  iintro Hf HΦ
  iapply wp_det_step_frame hred (fun _ _ _ _ _ h => reduce_label_trap h) $$ Hf
  inext
  iintro Hf
  iapply IrisWp.wp_value' (ι := wasmIrisGS) (fun f : Frame => iprop(↪[frame] f))
  iframe

@[rocq_alias iriswasm.wp_val_return]
theorem wp_val_return {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF}
    {vs vs' es' es'' : List AdministrativeInstruction} {n : Nat} {f : Frame}
    (hconst : constList vs = true) :
    ⊢ iprop(↪[frame] f -∗ (↪[frame] f -∗ WP (vs' ++ vs ++ es'') @ s ; E {{ v, Φ v }}) -∗
      WP vs @ s ; E CTX 1 ; (Lholed.rec_ vs' n es' (.base [] []) es'') {{ v, Φ v }}) := by
  unfold wpWasmCtx
  iintro Hf H %LI %hLI
  obtain ⟨hvs', rfl⟩ : constList vs' = true ∧ LI = vs' ++ [.label n es' vs] ++ es'' := by
    rw [lfilled_Ind_Equivalent] at hLI
    cases hLI with
    | lfilledRec _ _ _ _ _ _ _ LI0 hvs' h0 => cases h0; simp [hvs']
  have hred : ∀ ws fr, Reduce ws fr (vs' ++ [.label n es' vs] ++ es'') ws fr (vs' ++ vs ++ es'') :=
    fun _ _ => Reduce.label [.label n es' vs] vs 0 (.base vs' es'') (.simple (.labelConst hconst))
      (by rw [lfilled_Ind_Equivalent]; exact .lfilledBase _ _ _ hvs')
      (by rw [lfilled_Ind_Equivalent]; exact .lfilledBase _ _ _ hvs')
  have hfi := starts_with_lfilled _ 0 [.label n es' vs] 0 (.base vs' es'') _
    (find_first_const_label vs es' n hconst)
    (by rw [lfilled_Ind_Equivalent]; exact .lfilledBase _ _ _ hvs')
  iapply wp_det_step_frame hred (reduce_det_first hred hfi (by simp) (by simp)) $$ Hf
  inext
  iexact H

@[rocq_alias iriswasm.wp_block_ctx]
theorem wp_block_ctx {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF} {i : Nat}
    {lh : Lholed} {vs : List AdministrativeInstruction} {t1s t2s : List ValueType}
    {es : List BasicInstruction} {n m : Nat} {f0 : Frame}
    (hconst : constList vs = true) (hn : vs.length = n) (hn' : t1s.length = n)
    (hm : t2s.length = m) :
    ⊢ iprop(↪[frame] f0 -∗
      ▷ (↪[frame] f0 -∗ WP [AdministrativeInstruction.label m [] (vs ++ toEList es)] @ s ; E
        CTX i ; lh {{ Φ }}) -∗
      WP (vs ++ [.basic (.block (.tf t1s t2s) es)]) @ s ; E CTX i ; lh {{ Φ }}) := by
  exact wp_ctx_det_step (fun _ _ => .simple (.block n hconst hn hn' hm)) (firstInstr_const_basic hconst (by simp)) (by simp) (by simp)

@[rocq_alias iriswasm.wp_block_local_ctx]
theorem wp_block_local_ctx {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF} {i : Nat}
    {lh : Lholed} {vs : List AdministrativeInstruction} {t1s t2s : List ValueType}
    {es : List BasicInstruction} {n m n1 : Nat} {f1 f0 : Frame}
    (hconst : constList vs = true) (hn : vs.length = n) (hn' : t1s.length = n)
    (hm : t2s.length = m) :
    ⊢ iprop(↪[frame] f0 -∗
      ▷ (↪[frame] f0 -∗ WP [AdministrativeInstruction.label m [] (vs ++ toEList es)] @ s ; E
        FRAME n1 ; f1 CTX i ; lh {{ v, Φ v }}) -∗
      WP (vs ++ [.basic (.block (.tf t1s t2s) es)]) @ s ; E FRAME n1 ; f1 CTX i ; lh
        {{ v, Φ v }}) := by
  exact wp_frame_ctx_det_step (fun _ _ => .simple (.block n hconst hn hn' hm)) (firstInstr_const_basic hconst (by simp)) (by simp) (by simp)

@[rocq_alias iriswasm.wp_br_ctx]
theorem wp_br_ctx {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF} {n : Nat}
    {vs es : List AdministrativeInstruction} {i : Nat} {lh : Lholed}
    {vs' es' : List AdministrativeInstruction} {f0 : Frame}
    (hvs : constList vs = true) (hlen : vs.length = n) :
    ⊢ iprop(↪[frame] f0 -∗
      ▷ (↪[frame] f0 -∗ WP (vs' ++ vs ++ es ++ es') @ s ; E {{ Φ }}) -∗
      WP (vs ++ [.basic (.br i)]) @ s ; E CTX (i + 1) ; (Lholed.rec_ vs' n es lh es')
        {{ Φ }}) := by
  unfold wpWasmCtx
  iintro Hf H %LI %hLI
  obtain ⟨LI0, hvs', h0, rfl⟩ := lfilled_rec_inv hLI
  rw [show vs' ++ vs ++ es ++ es' = vs' ++ (vs ++ es) ++ es' by simp]
  iapply wp_det_first_frame (br_label_reduce hvs' hvs hlen h0)
    (starts_with_lfilled _ _ _ _ _ _ (firstInstr_const_basic hvs (by simp)) hLI)
    (by simp) (by simp) $$ Hf
  iexact H

@[rocq_alias iriswasm.wp_br_local_ctx]
theorem wp_br_local_ctx {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF} {n : Nat}
    {vs es : List AdministrativeInstruction} {i : Nat} {lh : Lholed}
    {vs' es' : List AdministrativeInstruction} {f0 : Frame} {n1 : Nat} {f1 : Frame}
    (hvs : constList vs = true) (hlen : vs.length = n) :
    ⊢ iprop(↪[frame] f0 -∗
      ▷ (↪[frame] f0 -∗ WP (vs' ++ vs ++ es ++ es') @ s ; E FRAME n1 ; f1 {{ v, Φ v }}) -∗
      WP (vs ++ [.basic (.br i)]) @ s ; E FRAME n1 ; f1 CTX (i + 1) ;
        (Lholed.rec_ vs' n es lh es') {{ v, Φ v }}) := by
  unfold wpWasmCtxFrame wpWasmFrame
  iintro Hf H %LI %hLI
  obtain ⟨LI0, hvs', h0, rfl⟩ := lfilled_rec_inv hLI
  rw [show vs' ++ vs ++ es ++ es' = vs' ++ (vs ++ es) ++ es' by simp]
  have hred := br_label_reduce (l0 := es) (l1 := es') hvs' hvs hlen h0
  iapply wp_det_first_frame (fun ws fr => Reduce.local (f0 := fr) (n := n1) (hred ws f1))
    (first_instr_local _ _ _ _ _
      (starts_with_lfilled _ _ _ _ _ _ (firstInstr_const_basic hvs (by simp)) hLI))
    (by simp) (by simp) $$ Hf
  iexact H

@[rocq_alias iriswasm.wp_loop_ctx]
theorem wp_loop_ctx {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF}
    {vs : List AdministrativeInstruction} {es : List BasicInstruction} {n m : Nat}
    {t1s t2s : List ValueType} {i : Nat} {lh : Lholed} {f0 : Frame}
    (hvs : constList vs = true) (hn : vs.length = n) (hn' : t1s.length = n)
    (hm : t2s.length = m) :
    ⊢ iprop(↪[frame] f0 -∗
      ▷ (↪[frame] f0 -∗ WP [AdministrativeInstruction.label n [.basic (.loop (.tf t1s t2s) es)]
        (vs ++ toEList es)] @ s ; E CTX i ; lh {{ Φ }}) -∗
      WP (vs ++ [.basic (.loop (.tf t1s t2s) es)]) @ s ; E CTX i ; lh {{ Φ }}) := by
  exact wp_ctx_det_step (fun _ _ => .simple (.loop m hvs hn hn' hm)) (firstInstr_const_basic hvs (by simp)) (by simp) (by simp)

@[rocq_alias iriswasm.wp_loop_local_ctx]
theorem wp_loop_local_ctx {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF}
    {vs : List AdministrativeInstruction} {es : List BasicInstruction} {n m : Nat}
    {t1s t2s : List ValueType} {i : Nat} {lh : Lholed} {f0 : Frame} {n1 : Nat} {f1 : Frame}
    (hvs : constList vs = true) (hn : vs.length = n) (hn' : t1s.length = n)
    (hm : t2s.length = m) :
    ⊢ iprop(↪[frame] f0 -∗
      ▷ (↪[frame] f0 -∗ WP [AdministrativeInstruction.label n [.basic (.loop (.tf t1s t2s) es)]
        (vs ++ toEList es)] @ s ; E FRAME n1 ; f1 CTX i ; lh {{ v, Φ v }}) -∗
      WP (vs ++ [.basic (.loop (.tf t1s t2s) es)]) @ s ; E FRAME n1 ; f1 CTX i ; lh
        {{ v, Φ v }}) := by
  exact wp_frame_ctx_det_step (fun _ _ => .simple (.loop m hvs hn hn' hm)) (firstInstr_const_basic hvs (by simp)) (by simp) (by simp)

@[rocq_alias iriswasm.wp_loop]
theorem wp_loop {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF}
    {vs : List AdministrativeInstruction} {es : List BasicInstruction} {n m : Nat}
    {t1s t2s : List ValueType} {f : Frame}
    (hvs : constList vs = true) (hn : vs.length = n) (hn' : t1s.length = n)
    (hm : t2s.length = m) :
    ⊢ iprop(↪[frame] f -∗
      ▷ (↪[frame] f -∗ WP [AdministrativeInstruction.label n [.basic (.loop (.tf t1s t2s) es)]
        (vs ++ toEList es)] @ s ; E {{ w, Φ w }}) -∗
      WP (vs ++ [.basic (.loop (.tf t1s t2s) es)]) @ s ; E {{ w, Φ w }}) := by
  have hred : ∀ ws fr, Reduce ws fr (vs ++ [.basic (.loop (.tf t1s t2s) es)]) ws fr
      [.label n [.basic (.loop (.tf t1s t2s) es)] (vs ++ toEList es)] :=
    fun _ _ => .simple (.loop m hvs hn hn' hm)
  exact wp_det_step_frame hred
    (reduce_det_first hred (firstInstr_const_basic hvs (by simp)) (by simp) (by simp))

@[rocq_alias iriswasm.wp_if_true_ctx]
theorem wp_if_true_ctx {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF} {n : I32}
    {tf : FunctionType} {e1s e2s : List BasicInstruction} {i : Nat} {lh : Lholed} {f0 : Frame}
    (hn : n ≠ Wasm.Int.zero) :
    ⊢ iprop(↪[frame] f0 -∗
      ▷ (↪[frame] f0 -∗ WP [AdministrativeInstruction.basic (.block tf e1s)] @ s ; E CTX i ; lh
        {{ Φ }}) -∗
      WP [AdministrativeInstruction.basic (.const (.int32 n)), .basic (.if_ tf e1s e2s)] @ s ; E
        CTX i ; lh {{ Φ }}) := by
  exact wp_ctx_det_step (e₁ := [.basic (.const (.int32 n)), _]) (fun _ _ => .simple (.ifTrue hn)) (firstInstr_const_basic (vs := [.basic (.const (.int32 n))]) rfl (by simp)) (by simp) (by simp)

@[rocq_alias iriswasm.wp_if_true_local_ctx]
theorem wp_if_true_local_ctx {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF} {n : I32}
    {tf : FunctionType} {e1s e2s : List BasicInstruction} {i : Nat} {lh : Lholed} {f0 : Frame}
    {n1 : Nat} {f1 : Frame}
    (hn : n ≠ Wasm.Int.zero) :
    ⊢ iprop(↪[frame] f0 -∗
      ▷ (↪[frame] f0 -∗ WP [AdministrativeInstruction.basic (.block tf e1s)] @ s ; E
        FRAME n1 ; f1 CTX i ; lh {{ v, Φ v }}) -∗
      WP [AdministrativeInstruction.basic (.const (.int32 n)), .basic (.if_ tf e1s e2s)] @ s ; E
        FRAME n1 ; f1 CTX i ; lh {{ v, Φ v }}) := by
  exact wp_frame_ctx_det_step (e₁ := [.basic (.const (.int32 n)), _]) (fun _ _ => .simple (.ifTrue hn)) (firstInstr_const_basic (vs := [.basic (.const (.int32 n))]) rfl (by simp)) (by simp) (by simp)

@[rocq_alias iriswasm.wp_if_true]
theorem wp_if_true {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF} {c : I32}
    {tf : FunctionType} {e1s e2s : List BasicInstruction} {f : Frame}
    (hc : c ≠ Wasm.Int.zero) :
    ⊢ iprop(↪[frame] f -∗
      ▷ (↪[frame] f -∗ WP [AdministrativeInstruction.basic (.block tf e1s)] @ s ; E
        {{ w, Φ w }}) -∗
      WP [AdministrativeInstruction.basic (.const (.int32 c)), .basic (.if_ tf e1s e2s)] @ s ; E
        {{ w, Φ w }}) := by
  exact wp_det_first_frame (e₁ := [.basic (.const (.int32 c)), _])
    (fun _ _ => .simple (.ifTrue hc)) (firstInstr_const_basic (vs := [.basic (.const (.int32 c))]) rfl (by simp)) (by simp) (by simp)

@[rocq_alias iriswasm.wp_if_false_ctx]
theorem wp_if_false_ctx {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF} {n : I32}
    {tf : FunctionType} {e1s e2s : List BasicInstruction} {i : Nat} {lh : Lholed} {f0 : Frame}
    (hn : n = Wasm.Int.zero) :
    ⊢ iprop(↪[frame] f0 -∗
      ▷ (↪[frame] f0 -∗ WP [AdministrativeInstruction.basic (.block tf e2s)] @ s ; E CTX i ; lh
        {{ Φ }}) -∗
      WP [AdministrativeInstruction.basic (.const (.int32 n)), .basic (.if_ tf e1s e2s)] @ s ; E
        CTX i ; lh {{ Φ }}) := by
  exact wp_ctx_det_step (e₁ := [.basic (.const (.int32 n)), _]) (fun _ _ => .simple (.ifFalse hn)) (firstInstr_const_basic (vs := [.basic (.const (.int32 n))]) rfl (by simp)) (by simp) (by simp)

@[rocq_alias iriswasm.wp_if_false_local_ctx]
theorem wp_if_false_local_ctx {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF} {n : I32}
    {tf : FunctionType} {e1s e2s : List BasicInstruction} {i : Nat} {lh : Lholed} {f0 : Frame}
    {n1 : Nat} {f1 : Frame}
    (hn : n = Wasm.Int.zero) :
    ⊢ iprop(↪[frame] f0 -∗
      ▷ (↪[frame] f0 -∗ WP [AdministrativeInstruction.basic (.block tf e2s)] @ s ; E
        FRAME n1 ; f1 CTX i ; lh {{ v, Φ v }}) -∗
      WP [AdministrativeInstruction.basic (.const (.int32 n)), .basic (.if_ tf e1s e2s)] @ s ; E
        FRAME n1 ; f1 CTX i ; lh {{ v, Φ v }}) := by
  exact wp_frame_ctx_det_step (e₁ := [.basic (.const (.int32 n)), _]) (fun _ _ => .simple (.ifFalse hn)) (firstInstr_const_basic (vs := [.basic (.const (.int32 n))]) rfl (by simp)) (by simp) (by simp)

@[rocq_alias iriswasm.wp_if_false]
theorem wp_if_false {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF} {c : I32}
    {tf : FunctionType} {e1s e2s : List BasicInstruction} {f : Frame}
    (hc : c = Wasm.Int.zero) :
    ⊢ iprop(↪[frame] f -∗
      ▷ (↪[frame] f -∗ WP [AdministrativeInstruction.basic (.block tf e2s)] @ s ; E
        {{ w, Φ w }}) -∗
      WP [AdministrativeInstruction.basic (.const (.int32 c)), .basic (.if_ tf e1s e2s)] @ s ; E
        {{ w, Φ w }}) := by
  exact wp_det_first_frame (e₁ := [.basic (.const (.int32 c)), _])
    (fun _ _ => .simple (.ifFalse hc)) (firstInstr_const_basic (vs := [.basic (.const (.int32 c))]) rfl (by simp)) (by simp) (by simp)

@[rocq_alias iriswasm.wp_br_if_true_ctx]
theorem wp_br_if_true_ctx {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF} {n : I32}
    {i j : Nat} {lh : Lholed} {f0 : Frame}
    (hn : n ≠ Wasm.Int.zero) :
    ⊢ iprop(↪[frame] f0 -∗
      ▷ (↪[frame] f0 -∗ WP [AdministrativeInstruction.basic (.br i)] @ s ; E CTX j ; lh
        {{ Φ }}) -∗
      WP [AdministrativeInstruction.basic (.const (.int32 n)), .basic (.brIf i)] @ s ; E
        CTX j ; lh {{ Φ }}) := by
  exact wp_ctx_det_step (e₁ := [.basic (.const (.int32 n)), _]) (fun _ _ => .simple (.brIfTrue hn)) (firstInstr_const_basic (vs := [.basic (.const (.int32 n))]) rfl (by simp)) (by simp) (by simp)

@[rocq_alias iriswasm.wp_br_if_true_local_ctx]
theorem wp_br_if_true_local_ctx {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF} {n : I32}
    {i j : Nat} {lh : Lholed} {f0 : Frame} {n1 : Nat} {f1 : Frame}
    (hn : n ≠ Wasm.Int.zero) :
    ⊢ iprop(↪[frame] f0 -∗
      ▷ (↪[frame] f0 -∗ WP [AdministrativeInstruction.basic (.br i)] @ s ; E
        FRAME n1 ; f1 CTX j ; lh {{ v, Φ v }}) -∗
      WP [AdministrativeInstruction.basic (.const (.int32 n)), .basic (.brIf i)] @ s ; E
        FRAME n1 ; f1 CTX j ; lh {{ v, Φ v }}) := by
  exact wp_frame_ctx_det_step (e₁ := [.basic (.const (.int32 n)), _]) (fun _ _ => .simple (.brIfTrue hn)) (firstInstr_const_basic (vs := [.basic (.const (.int32 n))]) rfl (by simp)) (by simp) (by simp)

@[rocq_alias iriswasm.wp_br_if_true]
theorem wp_br_if_true {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF} {c : I32} {i : Nat}
    {f : Frame}
    (hc : c ≠ Wasm.Int.zero) :
    ⊢ iprop(↪[frame] f -∗
      ▷ (↪[frame] f -∗ WP [AdministrativeInstruction.basic (.br i)] @ s ; E {{ w, Φ w }}) -∗
      WP [AdministrativeInstruction.basic (.const (.int32 c)), .basic (.brIf i)] @ s ; E
        {{ w, Φ w }}) := by
  exact wp_det_first_frame (e₁ := [.basic (.const (.int32 c)), _])
    (fun _ _ => .simple (.brIfTrue hc)) (firstInstr_const_basic (vs := [.basic (.const (.int32 c))]) rfl (by simp)) (by simp) (by simp)

@[rocq_alias iriswasm.wp_br_if_false]
theorem wp_br_if_false {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF} {c : I32} {i : Nat}
    {f : Frame}
    (hc : c = Wasm.Int.zero) :
    ⊢ iprop(↪[frame] f -∗ ▷ Φ (.immV []) -∗
      WP [AdministrativeInstruction.basic (.const (.int32 c)), .basic (.brIf i)] @ s ; E
        {{ w, Φ w ∗ ↪[frame] f }}) := by
  have hred : ∀ ws fr, Reduce ws fr [.basic (.const (.int32 c)), .basic (.brIf i)] ws fr
      (ofVal (.immV [])) :=
    fun _ _ => .simple (.brIfFalse hc)
  iintro Hf HΦ
  iapply wp_det_first_frame hred
    (firstInstr_const_basic (vs := [.basic (.const (.int32 c))]) rfl (by simp))
    (by simp) (by simp) $$ Hf
  inext
  iintro Hf
  iapply IrisWp.wp_value' (ι := wasmIrisGS) (fun f : Frame => iprop(↪[frame] f))
  iframe

@[rocq_alias iriswasm.wp_br_table_ctx]
theorem wp_br_table_ctx {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF} {iss : List Nat}
    {c : I32} {i j k : Nat} {lh : Lholed} {f0 : Frame}
    (hlen : Wasm.Int.natOfUint c + 1 ≤ iss.length)
    (hj : iss[Wasm.Int.natOfUint c]? = some j) :
    ⊢ iprop(↪[frame] f0 -∗
      ▷ (↪[frame] f0 -∗ WP [AdministrativeInstruction.basic (.br j)] @ s ; E CTX k ; lh
        {{ Φ }}) -∗
      WP [AdministrativeInstruction.basic (.const (.int32 c)), .basic (.brTable iss i)] @ s ; E
        CTX k ; lh {{ Φ }}) := by
  exact wp_ctx_det_step (e₁ := [.basic (.const (.int32 c)), _]) (fun _ _ => .simple (.brTable (by omega) hj)) (firstInstr_const_basic (vs := [.basic (.const (.int32 c))]) rfl (by simp)) (by simp) (by simp)

@[rocq_alias iriswasm.wp_br_table_local_ctx]
theorem wp_br_table_local_ctx {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF}
    {iss : List Nat} {c : I32} {i j k : Nat} {lh : Lholed} {f0 : Frame} {n1 : Nat} {f1 : Frame}
    (hlen : Wasm.Int.natOfUint c + 1 ≤ iss.length)
    (hj : iss[Wasm.Int.natOfUint c]? = some j) :
    ⊢ iprop(↪[frame] f0 -∗
      ▷ (↪[frame] f0 -∗ WP [AdministrativeInstruction.basic (.br j)] @ s ; E
        FRAME n1 ; f1 CTX k ; lh {{ v, Φ v }}) -∗
      WP [AdministrativeInstruction.basic (.const (.int32 c)), .basic (.brTable iss i)] @ s ; E
        FRAME n1 ; f1 CTX k ; lh {{ v, Φ v }}) := by
  exact wp_frame_ctx_det_step (e₁ := [.basic (.const (.int32 c)), _]) (fun _ _ => .simple (.brTable (by omega) hj)) (firstInstr_const_basic (vs := [.basic (.const (.int32 c))]) rfl (by simp)) (by simp) (by simp)

@[rocq_alias iriswasm.wp_br_table]
theorem wp_br_table {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF} {iss : List Nat}
    {c : I32} {i j : Nat} {f : Frame}
    (hj : iss[Wasm.Int.natOfUint c]? = some j) :
    ⊢ iprop(↪[frame] f -∗
      ▷ (↪[frame] f -∗ WP [AdministrativeInstruction.basic (.br j)] @ s ; E {{ w, Φ w }}) -∗
      WP [AdministrativeInstruction.basic (.const (.int32 c)), .basic (.brTable iss i)] @ s ; E
        {{ w, Φ w }}) := by
  exact wp_det_first_frame (e₁ := [.basic (.const (.int32 c)), _])
    (fun _ _ => .simple (.brTable (List.getElem?_eq_some_iff.mp hj).1 hj)) (firstInstr_const_basic (vs := [.basic (.const (.int32 c))]) rfl (by simp)) (by simp) (by simp)

@[rocq_alias iriswasm.wp_br_table_length_ctx]
theorem wp_br_table_length_ctx {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF}
    {iss : List Nat} {c : I32} {i j : Nat} {lh : Lholed} {f0 : Frame}
    (hlen : iss.length ≤ Wasm.Int.natOfUint c) :
    ⊢ iprop(↪[frame] f0 -∗
      ▷ (↪[frame] f0 -∗ WP [AdministrativeInstruction.basic (.br i)] @ s ; E CTX j ; lh
        {{ Φ }}) -∗
      WP [AdministrativeInstruction.basic (.const (.int32 c)), .basic (.brTable iss i)] @ s ; E
        CTX j ; lh {{ Φ }}) := by
  exact wp_ctx_det_step (e₁ := [.basic (.const (.int32 c)), _]) (fun _ _ => .simple (.brTableLength hlen)) (firstInstr_const_basic (vs := [.basic (.const (.int32 c))]) rfl (by simp)) (by simp) (by simp)

@[rocq_alias iriswasm.wp_br_table_length_local_ctx]
theorem wp_br_table_length_local_ctx {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF}
    {iss : List Nat} {c : I32} {i j : Nat} {lh : Lholed} {f0 : Frame} {n1 : Nat} {f1 : Frame}
    (hlen : iss.length ≤ Wasm.Int.natOfUint c) :
    ⊢ iprop(↪[frame] f0 -∗
      ▷ (↪[frame] f0 -∗ WP [AdministrativeInstruction.basic (.br i)] @ s ; E
        FRAME n1 ; f1 CTX j ; lh {{ v, Φ v }}) -∗
      WP [AdministrativeInstruction.basic (.const (.int32 c)), .basic (.brTable iss i)] @ s ; E
        FRAME n1 ; f1 CTX j ; lh {{ v, Φ v }}) := by
  exact wp_frame_ctx_det_step (e₁ := [.basic (.const (.int32 c)), _]) (fun _ _ => .simple (.brTableLength hlen)) (firstInstr_const_basic (vs := [.basic (.const (.int32 c))]) rfl (by simp)) (by simp) (by simp)

@[rocq_alias iriswasm.wp_br_table_length]
theorem wp_br_table_length {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF}
    {iss : List Nat} {c : I32} {i : Nat} {f : Frame}
    (hlen : iss.length ≤ Wasm.Int.natOfUint c) :
    ⊢ iprop(↪[frame] f -∗
      ▷ (↪[frame] f -∗ WP [AdministrativeInstruction.basic (.br i)] @ s ; E {{ w, Φ w }}) -∗
      WP [AdministrativeInstruction.basic (.const (.int32 c)), .basic (.brTable iss i)] @ s ; E
        {{ w, Φ w }}) := by
  exact wp_det_first_frame (e₁ := [.basic (.const (.int32 c)), _])
    (fun _ _ => .simple (.brTableLength hlen)) (firstInstr_const_basic (vs := [.basic (.const (.int32 c))]) rfl (by simp)) (by simp) (by simp)

/-! #### Special shifting rules about break and return -/

@[rocq_alias iriswasm.wp_br_ctx_shift]
theorem wp_br_ctx_shift {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF}
    {vs : List AdministrativeInstruction} {i : Nat} {lh : Lholed} {n : Nat}
    {es vs1 es2 l : List AdministrativeInstruction} {n1 : Nat}
    {l0 l1 : List AdministrativeInstruction}
    (hconst : constList vs = true) (hlen : vs.length = n1) :
    ⊢ iprop(WP (vs ++ [.basic (.br i)]) @ s ; E CTX (i + 1) ; (Lholed.rec_ l n1 l0 lh l1)
        {{ Φ }} -∗
      WP (vs ++ [.basic (.br (i + 1))]) @ s ; E CTX (i + 1 + 1) ;
        (Lholed.rec_ l n1 l0 (pushBase lh n es vs1 es2) l1) {{ Φ }}) := by
  unfold wpWasmCtx
  iintro H %LI %hLI
  obtain ⟨LI0, hl, h0, rfl⟩ := lfilled_rec_inv hLI
  obtain ⟨LI', h1⟩ := lfilled_push_base_swap h0
  obtain ⟨LIi, hi⟩ := lfilled_swap (vs ++ [.basic (.br i)]) h1
  have hfillI : lfilled (i + 1) (.rec_ l n1 l0 lh l1) (vs ++ [.basic (.br i)])
      (l ++ [.label n1 l0 LIi] ++ l1) = true := by
    rw [lfilled_Ind_Equivalent] at hi ⊢; exact .lfilledRec _ _ _ _ _ _ _ _ hl hi
  ispecialize H $$ %_ %hfillI
  have h₂ := br_label_reduce (l0 := l0) (l1 := l1) hl hconst hlen h0
  iapply wp_det_step_equiv (br_label_reduce (l0 := l0) (l1 := l1) hl hconst hlen hi) h₂
    (reduce_det_first h₂
      (starts_with_lfilled _ _ _ _ _ _ (firstInstr_const_basic hconst (by simp)) hLI)
      (by simp) (by simp)) $$ H

@[rocq_alias iriswasm.wp_br_ctx_shift_inv]
theorem wp_br_ctx_shift_inv {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF}
    {vs : List AdministrativeInstruction} {i : Nat} {lh : Lholed} {n : Nat}
    {es vs1 es2 l : List AdministrativeInstruction} {n1 : Nat}
    {l0 l1 : List AdministrativeInstruction}
    (hconst : constList vs = true) (hconst' : constList vs1 = true) (hlen : vs.length = n1) :
    ⊢ iprop(WP (vs ++ [.basic (.br (i + 1))]) @ s ; E CTX (i + 1 + 1) ;
        (Lholed.rec_ l n1 l0 (pushBase lh n es vs1 es2) l1) {{ Φ }} -∗
      WP (vs ++ [.basic (.br i)]) @ s ; E CTX (i + 1) ; (Lholed.rec_ l n1 l0 lh l1)
        {{ Φ }}) := by
  unfold wpWasmCtx
  iintro H %LI %hLI
  obtain ⟨LI0, hl, h0, rfl⟩ := lfilled_rec_inv hLI
  obtain ⟨LI', h1⟩ := lfilled_push_base_swap_inv (n := n) (es := es) (es2 := es2) hconst' h0
  obtain ⟨LIi, hi⟩ := lfilled_swap (vs ++ [.basic (.br (i + 1))]) h1
  have hfillI : lfilled (i + 1 + 1) (.rec_ l n1 l0 (pushBase lh n es vs1 es2) l1)
      (vs ++ [.basic (.br (i + 1))]) (l ++ [.label n1 l0 LIi] ++ l1) = true := by
    rw [lfilled_Ind_Equivalent] at hi ⊢; exact .lfilledRec _ _ _ _ _ _ _ _ hl hi
  ispecialize H $$ %_ %hfillI
  have h₂ := br_label_reduce (l0 := l0) (l1 := l1) hl hconst hlen h0
  iapply wp_det_step_equiv (br_label_reduce (l0 := l0) (l1 := l1) hl hconst hlen hi) h₂
    (reduce_det_first h₂
      (starts_with_lfilled _ _ _ _ _ _ (firstInstr_const_basic hconst (by simp)) hLI)
      (by simp) (by simp)) $$ H

@[rocq_alias iriswasm.wp_ret_shift]
theorem wp_ret_shift {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF} {n : Nat} {f : Frame}
    {i : Nat} {lh : Lholed} {j : Nat} {lh' : Lholed}
    {LI LI' vs : List AdministrativeInstruction}
    (hconst : constList vs = true) (hlen : vs.length = n)
    (hfill1 : lfilled i lh (vs ++ [.basic .return_]) LI = true)
    (hfill2 : lfilled j lh' (vs ++ [.basic .return_]) LI' = true) :
    ⊢ iprop(WP [AdministrativeInstruction.local n f LI] @ s ; E {{ Φ }} -∗
      WP [AdministrativeInstruction.local n f LI'] @ s ; E {{ Φ }}) := by
  have h₁ : ∀ ws fr, Reduce ws fr [.local n f LI] ws fr vs :=
    fun _ _ => .simple (.return_ i lh hconst hlen hfill1)
  have h₂ : ∀ ws fr, Reduce ws fr [.local n f LI'] ws fr vs :=
    fun _ _ => .simple (.return_ j lh' hconst hlen hfill2)
  exact wp_det_step_equiv h₁ h₂ (reduce_det_first h₂ (first_instr_local _ _ _ _ _
    (starts_with_lfilled _ _ _ _ _ _ (firstInstr_const_basic hconst (by simp)) hfill2))
    (by simp) (by simp))

end IrisWasm
