/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Rules.IrisRulesStructural
import IrisWasm.Helpers.Prelude.FirstInstr
import IrisWasm.Helpers.Prelude.IrisWasmLangProperties

/-! Port of `theories/iris/rules/iris_rules_calls.v`. -/

namespace IrisWasm

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm

variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF]

set_option linter.unusedSimpArgs false

@[rocq_alias iriswasm.v_to_e_list_to_val]
theorem v_to_e_list_to_val (es : Expr) (vs : List Value) :
    toVal es = some (.immV vs) → vToEList vs = es :=
  of_to_val es _

/-- The frame fragment agrees with the frame stored in the state interpretation. -/
private theorem frame_agree {f : Frame} {locs : List Value} {inst : Instance} :
    ⊢ (ghost_map_auth (WasmG.frameGName GF) (DFrac.own 1)
        (insert (PartialMap.empty : UnitMapF Frame) () ⟨locs, inst⟩) -∗
      ↪[frame] f -∗ ⌜f = ⟨locs, inst⟩⌝ : IProp GF) := by
  unfold frameOwn
  iintro Ha Hf
  ihave %h := ghost_map_lookup $$ Ha Hf
  ipureintro
  rw [get?_insert_eq rfl] at h
  exact (Option.some.inj h).symm

/-- One deterministic, state-preserving step `es ↦ es'`, enabled by the resources `R` and
the frame `f0`; both are handed back to the continuation. -/
private theorem wp_det_step {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF} {f0 : Frame}
    {es es' : Expr} (R : IProp GF) (hnv : toVal es = none)
    (hred : ∀ ws locs inst, iprop(stateInterp (ws, locs, inst) ∗ R) ⊢
      ⌜Frame.mk locs inst = f0 → Reduce ws f0 es ws f0 es'⌝)
    (hgrow : ∀ i, firstInstr es ≠ some (.basic .growMemory, i))
    (htrap : ∀ i, firstInstr es ≠ some (.trap, i)) :
    ⊢ (R -∗ ↪[frame] f0 -∗ ▷ (R -∗ ↪[frame] f0 -∗ WP es' @ s ; E {{ Φ }}) -∗
      WP es @ s ; E {{ Φ }} : IProp GF) := by
  let := @WasmG.invGS hlc GF _
  iintro HR Hf HΦ
  iapply IrisWp.wp_lift_step (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) hnv
  iintro %σ %ns %obs %obs' %nt Hσ
  rcases σ with ⟨ws, locs, inst⟩
  ihave %Hred : ⌜Frame.mk locs inst = f0 → Reduce ws f0 es ws f0 es'⌝ $$ [Hσ HR]
  · iapply hred; iframe
  ihave %Hfeq : ⌜f0 = ⟨locs, inst⟩⌝ $$ [Hσ Hf]
  · simp only [Iris.StateInterp.stateInterp, IrisWasm.stateInterp]
    icases Hσ with ⟨-, -, -, -, Hfr, -⟩
    iapply frame_agree $$ Hfr Hf
  subst Hfeq
  have Hred := Hred rfl
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hcls
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact ⟨[], _, (ws, locs, inst), [], Hred, rfl, rfl⟩
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep -
  rcases σ₂ with ⟨ws', locs', inst'⟩
  obtain ⟨H, rfl, rfl⟩ := Hstep
  rcases reduce_det H Hred with h | ⟨_, h⟩ | ⟨_, _, _, h, -⟩
  · simp only [Prod.mk.injEq, Frame.mk.injEq] at h
    obtain ⟨rfl, ⟨rfl, rfl⟩, rfl⟩ := h
    imod Hcls
    imodintro
    iframe Hσ
    iexists _
    iframe Hf
    isplitl
    · iintro Hf
      iapply HΦ $$ HR Hf
    simp; exact .rfl
  · exact absurd h (hgrow _)
  · exact absurd h (htrap _)

/-- `[.trap]` is a value: frame the post-condition. -/
private theorem wp_trap_value {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF} :
    Φ .trapV ⊢ WP ([.trap] : Expr) @ s ; E {{ Φ }} :=
  IrisWp.wp_value (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) ⟨rfl⟩

private theorem toVal_lfilled_none {i : Nat} {lh : Lholed} {es LI : Expr}
    (hes : toVal es = none) (h : lfilled i lh es LI = true) : toVal LI = none := by
  cases hLI : toVal LI with
  | none => rfl
  | some _ =>
    have := lfilled_to_val i lh es LI (by simp [hLI]) h
    simp [hes] at this

private theorem stabAddr_of_lookup {ws : StoreRecord} {f : Frame} {j k : Nat} {x : Funcelem}
    (hc : f.inst.tab[0]? = some j) (h : get? (gmapOfTable ws.tables) (j, k) = some x) :
    stabAddr ws f k = x := by
  cases htab : f.inst.tab with
  | nil => simp [htab] at hc
  | cons ta _ =>
    simp only [htab, List.getElem?_cons_zero, Option.some.injEq] at hc
    subst hc
    simp only [gmapOfTable, gmap_of_list_2d_lookup, List.getElem?_map] at h
    cases ht : ws.tables[ta]? <;> simp [ht, tableToList] at h
    simp [stabAddr, htab, stabIndex, optionBind, ht, h]

private theorem stabAddr_none_of_size {ws : StoreRecord} {f : Frame} {j k max : Nat}
    (hc : f.inst.tab[0]? = some j) (h : get? (gmapOfList (ws.tables.map tabSize)) j = some max)
    (hk : max ≤ k) : stabAddr ws f k = none := by
  cases htab : f.inst.tab with
  | nil => simp [htab] at hc
  | cons ta _ =>
    simp only [htab, List.getElem?_cons_zero, Option.some.injEq] at hc
    subst hc
    simp only [gmap_of_list_lookup, List.getElem?_map] at h
    cases ht : ws.tables[ta]? <;> simp [ht, tabSize] at h
    simp [stabAddr, htab, stabIndex, optionBind, ht]
    rw [List.getElem?_eq_none (by omega)]

private theorem stabAddr_notable {ws : StoreRecord} {f : Frame} {k : Nat}
    (hc : f.inst.tab[0]? = none) : stabAddr ws f k = none := by
  cases htab : f.inst.tab with
  | nil => simp [stabAddr, htab]
  | cons ta _ => simp [htab] at hc
/-! ### Native invocations -/

@[rocq_alias iriswasm.wp_invoke_native]
theorem wp_invoke_native (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF) (ves : Expr)
    (vcs : List Value) (t1s t2s ts : List ValueType) (a : Nat) (es : List BasicInstruction)
    (i : Instance) (m : Nat) (f : Frame) :
    toVal ves = some (.immV vcs) → vcs.length = t1s.length → t2s.length = m →
    ⊢ (↪[frame] f -∗
      a ↦[wf] (.funcNative i (.tf t1s t2s) ts es) -∗
      ▷ (↪[frame] f ∗ a ↦[wf] (.funcNative i (.tf t1s t2s) ts es) -∗
        WP ([.local m ⟨vcs ++ nZeros ts, i⟩ [.basic (.block (.tf [] t2s) es)]] : Expr)
          @ s ; E {{ v, Φ v }}) -∗
      WP (ves ++ [.invoke a]) @ s ; E {{ v, Φ v }} : IProp GF) := by
  intro hparams hlen hret
  have hconst := to_val_const_list ves vcs hparams
  have hfi : firstInstr (ves ++ [.invoke a]) = some (.invoke a, 0) := by
    rw [first_instr_const _ _ hconst]; simp [firstInstr_cons, firstInstrInstr]
  have := wp_det_step (s := s) (E := E) (Φ := Φ) (f0 := f) (es := ves ++ [.invoke a])
    (es' := [.local m ⟨vcs ++ nZeros ts, i⟩ [.basic (.block (.tf [] t2s) es)]])
    iprop(a ↦[wf] (.funcNative i (.tf t1s t2s) ts es))
    (to_val_cat_None2 _ _ hconst (by simp [toVal, mergeValuesList, toValInstr, mergeValues, valNotValCombine, valCombine]))
    ?_ (by simp [hfi]) (by simp [hfi])
  · iintro Hf Hi HΦ
    iapply this $$ Hi Hf
    inext
    iintro Hi Hf
    iapply HΦ
    iframe
  · intro ws locs inst
    simp only [IrisWasm.stateInterp]
    iintro ⟨⟨Hfn, -⟩, Hi⟩
    ihave >%Hlook := (letI := WasmG.funcHs (hlc := hlc) (GF := GF); genHeap_valid) $$ [$Hfn $Hi]
    ipureintro
    intro _
    rw [gmap_of_list_lookup] at Hlook
    exact .invokeNative _ t1s ts vcs _ _ _ i Hlook rfl (v_to_e_list_to_val ves vcs hparams).symm
      rfl rfl hlen.symm hret rfl rfl rfl

/-! ### Host invocations -/

@[rocq_alias iriswasm.wp_invoke_host]
theorem wp_invoke_host (s : Stuckness) (E : CoPset) (ves : Expr) (vcs : List Value) (n : Nat)
    (t1s t2s : List ValueType) (a : Nat) (h : Hostfuncidx) (f : Frame) (Φ : Val → IProp GF) :
    ves = vToEList vcs → vcs.length = n → t1s.length = n →
    ⊢ (a ↦[wf] (.funcHost (.tf t1s t2s) h) -∗
      ↪[frame] f -∗
      ▷ (a ↦[wf] (.funcHost (.tf t1s t2s) h) -∗ ↪[frame] f -∗
        WP ([.callHost (.tf t1s t2s) h vcs] : Expr) @ s ; E {{ Φ }}) -∗
      WP (ves ++ [.invoke a]) @ s ; E {{ Φ }} : IProp GF) := by
  intro hves hvcs ht1s
  have hconst : constList ves = true := hves ▸ v_to_e_is_const_list vcs
  have hfi : firstInstr (ves ++ [.invoke a]) = some (.invoke a, 0) := by
    rw [first_instr_const _ _ hconst]; simp [firstInstr_cons, firstInstrInstr]
  have := wp_det_step (s := s) (E := E) (Φ := Φ) (f0 := f) (es := ves ++ [.invoke a])
    (es' := [.callHost (.tf t1s t2s) h vcs])
    iprop(a ↦[wf] (.funcHost (.tf t1s t2s) h))
    (to_val_cat_None2 _ _ hconst (by simp [toVal, mergeValuesList, toValInstr, mergeValues, valNotValCombine, valCombine]))
    ?_ (by simp [hfi]) (by simp [hfi])
  · iintro Ha Hf HΦ
    iapply this $$ Ha Hf
    inext
    iintro Ha Hf
    iapply HΦ $$ Ha Hf
  · intro ws locs inst
    simp only [IrisWasm.stateInterp]
    iintro ⟨⟨Hfn, -⟩, Ha⟩
    ihave >%Hlook := (letI := WasmG.funcHs (hlc := hlc) (GF := GF); genHeap_valid) $$ [$Hfn $Ha]
    ipureintro
    intro _
    rw [gmap_of_list_lookup] at Hlook
    exact .invokeHost _ _ _ Hlook rfl hves rfl (ht1s.trans hvcs.symm) rfl

/-! ### Calls -/

@[rocq_alias iriswasm.wp_call_ctx]
theorem wp_call_ctx (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF) (f0 : Frame) (i a j : Nat)
    (lh : Lholed) :
    f0.inst.funcs[i]? = some a →
    ⊢ (↪[frame] f0 -∗
      ▷ (↪[frame] f0 -∗ WP ([.invoke a] : Expr) @ s ; E CTX j ; lh {{ v, Φ v }}) -∗
      WP ([.basic (.call i)] : Expr) @ s ; E CTX j ; lh {{ v, Φ v }} : IProp GF) := by
  intro hfun
  unfold wpWasmCtx
  iintro Hf HΦ %LI %Hfill
  obtain ⟨LI', hfill'⟩ := lfilled_swap [.invoke a] Hfill
  have hfi := starts_with_lfilled (.basic (.call i)) 0 _ _ _ _ (by simp [firstInstr_cons, firstInstrInstr]) Hfill
  have := wp_det_step (s := s) (E := E) (Φ := Φ) (f0 := f0) (es := LI) (es' := LI') iprop(emp)
    (toVal_lfilled_none (by simp [toVal, mergeValuesList, toValInstr, mergeValues, valNotValCombine, valCombine]) Hfill) ?_
    (by simp [hfi]) (by simp [hfi])
  · iapply this $$ [] Hf
    · iempintro
    inext
    iintro - Hf
    iapply HΦ $$ Hf %LI' %hfill'
  · intro ws locs inst
    iintro -
    ipureintro
    rintro rfl
    exact .label _ _ _ _ (.call hfun) Hfill hfill'

@[rocq_alias iriswasm.wp_call]
theorem wp_call (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF) (f0 : Frame) (i a : Nat) :
    f0.inst.funcs[i]? = some a →
    ⊢ (↪[frame] f0 -∗
      ▷ (↪[frame] f0 -∗ WP ([.invoke a] : Expr) @ s ; E {{ v, Φ v }}) -∗
      WP ([.basic (.call i)] : Expr) @ s ; E {{ v, Φ v }} : IProp GF) := by
  intro h
  iintro Hf HΦ
  iapply (wandIff_equiv (wp_wasm_empty_ctx s E _ _)).2
  iapply wp_call_ctx s E Φ f0 i a 0 _ h $$ Hf
  inext
  iintro Hf
  iapply (wandIff_equiv (wp_wasm_empty_ctx s E _ _)).1
  iapply HΦ $$ Hf

@[rocq_alias iriswasm.wp_call_indirect_success_ctx]
theorem wp_call_indirect_success_ctx (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF)
    (f0 : Frame) (i j a : Nat) (c : I32) (cl : FunctionClosure) (d : Nat) (lh : Lholed) :
    f0.inst.types[i]? = some (clType cl) →
    f0.inst.tab[0]? = some j →
    ⊢ (j ↦[wt][ Wasm.Int.natOfUint c ] (some a) -∗
      a ↦[wf] cl -∗
      ↪[frame] f0 -∗
      ▷ (j ↦[wt][ Wasm.Int.natOfUint c ] (some a) ∗ a ↦[wf] cl ∗ ↪[frame] f0 -∗
        WP ([.invoke a] : Expr) @ s ; E CTX d ; lh {{ v, Φ v }}) -∗
      WP ([.basic (.const (.int32 c)), .basic (.callIndirect i)] : Expr)
        @ s ; E CTX d ; lh {{ v, Φ v }} : IProp GF) := by
  intro htype hc
  unfold wpWasmCtx
  iintro Ha Hcl Hf HΦ %LI %Hfill
  obtain ⟨LI', hfill'⟩ := lfilled_swap [.invoke a] Hfill
  have hfi := starts_with_lfilled (.basic (.callIndirect i)) 0 _ _ _ _
    (by simp [firstInstr_cons, firstInstrInstr]) Hfill
  have := wp_det_step (s := s) (E := E) (Φ := Φ) (f0 := f0) (es := LI) (es' := LI')
    iprop(j ↦[wt][ Wasm.Int.natOfUint c ] (some a) ∗ a ↦[wf] cl)
    (toVal_lfilled_none (by simp [toVal, mergeValuesList, toValInstr, mergeValues, valNotValCombine, valCombine]) Hfill) ?_
    (by simp [hfi]) (by simp [hfi])
  · iapply this $$ [Ha Hcl] Hf
    · iframe
    inext
    iintro ⟨Ha, Hcl⟩ Hf
    iapply HΦ $$ [Ha Hcl Hf] %LI' %hfill'
    iframe
  · intro ws locs inst
    simp only [IrisWasm.stateInterp]
    iintro ⟨⟨Hfn, Htab, -⟩, Ha, Hcl⟩
    ihave >%Hlook := (letI := WasmG.tabHs (hlc := hlc) (GF := GF); genHeap_valid) $$ [$Htab $Ha]
    ihave >%Hlook2 := (letI := WasmG.funcHs (hlc := hlc) (GF := GF); genHeap_valid) $$ [$Hfn $Hcl]
    ipureintro
    rintro rfl
    rw [gmap_of_list_lookup] at Hlook2
    exact .label _ _ _ _ (.callIndirectSuccess cl (stabAddr_of_lookup hc Hlook) Hlook2 htype)
      Hfill hfill'

@[rocq_alias iriswasm.wp_call_indirect_success]
theorem wp_call_indirect_success (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF)
    (f0 : Frame) (i j a : Nat) (c : I32) (cl : FunctionClosure) :
    f0.inst.types[i]? = some (clType cl) →
    f0.inst.tab[0]? = some j →
    ⊢ (j ↦[wt][ Wasm.Int.natOfUint c ] (some a) -∗
      a ↦[wf] cl -∗
      ↪[frame] f0 -∗
      ▷ (j ↦[wt][ Wasm.Int.natOfUint c ] (some a) ∗ a ↦[wf] cl ∗ ↪[frame] f0 -∗
        WP ([.invoke a] : Expr) @ s ; E {{ v, Φ v }}) -∗
      WP ([.basic (.const (.int32 c)), .basic (.callIndirect i)] : Expr)
        @ s ; E {{ v, Φ v }} : IProp GF) := by
  intro htype hc
  iintro Ha Hcl Hf HΦ
  iapply (wandIff_equiv (wp_wasm_empty_ctx s E _ _)).2
  iapply wp_call_indirect_success_ctx s E Φ f0 i j a c cl 0 _ htype hc $$ Ha Hcl Hf
  inext
  iintro H
  iapply (wandIff_equiv (wp_wasm_empty_ctx s E _ _)).1
  iapply HΦ $$ H

@[rocq_alias iriswasm.wp_call_indirect_failure_types]
theorem wp_call_indirect_failure_types (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF)
    (f0 : Frame) (i j a : Nat) (c : I32) (cl : FunctionClosure) :
    f0.inst.types[i]? ≠ some (clType cl) →
    f0.inst.tab[0]? = some j →
    ⊢ (j ↦[wt][ Wasm.Int.natOfUint c ] (some a) -∗
      a ↦[wf] cl -∗
      ↪[frame] f0 -∗
      ▷ Φ .trapV -∗
      WP ([.basic (.const (.int32 c)), .basic (.callIndirect i)] : Expr) @ s ; E
        {{ v, (Φ v ∗ j ↦[wt][ Wasm.Int.natOfUint c ] (some a) ∗ a ↦[wf] cl) ∗ ↪[frame] f0 }}
      : IProp GF) := by
  intro htype hc
  have := wp_det_step (s := s) (E := E) (f0 := f0)
    (Φ := fun v => iprop((Φ v ∗ j ↦[wt][ Wasm.Int.natOfUint c ] (some a) ∗ a ↦[wf] cl) ∗
      ↪[frame] f0))
    (es := [.basic (.const (.int32 c)), .basic (.callIndirect i)]) (es' := [.trap])
    iprop(j ↦[wt][ Wasm.Int.natOfUint c ] (some a) ∗ a ↦[wf] cl)
    (by simp [toVal, mergeValuesList, toValInstr, mergeValues, valNotValCombine, valCombine]) ?_
    (by simp [firstInstr_cons, firstInstrInstr]) (by simp [firstInstr_cons, firstInstrInstr])
  · iintro Ha Hcl Hf HΦ
    iapply this $$ [Ha Hcl] Hf
    · iframe
    inext
    iintro ⟨Ha, Hcl⟩ Hf
    iapply wp_trap_value
    iframe
  · intro ws locs inst
    simp only [IrisWasm.stateInterp]
    iintro ⟨⟨Hfn, Htab, -⟩, Ha, Hcl⟩
    ihave >%Hlook := (letI := WasmG.tabHs (hlc := hlc) (GF := GF); genHeap_valid) $$ [$Htab $Ha]
    ihave >%Hlook2 := (letI := WasmG.funcHs (hlc := hlc) (GF := GF); genHeap_valid) $$ [$Hfn $Hcl]
    ipureintro
    rintro rfl
    rw [gmap_of_list_lookup] at Hlook2
    exact .callIndirectFailure1 a cl (stabAddr_of_lookup hc Hlook) Hlook2 htype

@[rocq_alias iriswasm.wp_call_indirect_failure_notable]
theorem wp_call_indirect_failure_notable (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF)
    (f0 : Frame) (i : Nat) (c : I32) :
    f0.inst.tab[0]? = none →
    ⊢ (↪[frame] f0 -∗
      ▷ Φ .trapV -∗
      WP ([.basic (.const (.int32 c)), .basic (.callIndirect i)] : Expr) @ s ; E
        {{ v, Φ v ∗ ↪[frame] f0 }} : IProp GF) := by
  intro hc
  have := wp_det_step (s := s) (E := E) (f0 := f0) (Φ := fun v => iprop(Φ v ∗ ↪[frame] f0))
    (es := [.basic (.const (.int32 c)), .basic (.callIndirect i)]) (es' := [.trap]) iprop(emp)
    (by simp [toVal, mergeValuesList, toValInstr, mergeValues, valNotValCombine, valCombine]) ?_
    (by simp [firstInstr_cons, firstInstrInstr]) (by simp [firstInstr_cons, firstInstrInstr])
  · iintro Hf HΦ
    iapply this $$ [] Hf
    · iempintro
    inext
    iintro - Hf
    iapply wp_trap_value
    iframe
  · intro ws locs inst
    iintro -
    ipureintro
    rintro rfl
    exact .callIndirectFailure2 (stabAddr_notable hc)

@[rocq_alias iriswasm.wp_call_indirect_failure_noindex]
theorem wp_call_indirect_failure_noindex (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF)
    (f0 : Frame) (i j : Nat) (c : I32) :
    f0.inst.tab[0]? = some j →
    ⊢ (j ↦[wt][ Wasm.Int.natOfUint c ] none -∗
      ↪[frame] f0 -∗
      ▷ Φ .trapV -∗
      WP ([.basic (.const (.int32 c)), .basic (.callIndirect i)] : Expr) @ s ; E
        {{ v, (Φ v ∗ j ↦[wt][ Wasm.Int.natOfUint c ] none) ∗ ↪[frame] f0 }} : IProp GF) := by
  intro hc
  have := wp_det_step (s := s) (E := E) (f0 := f0)
    (Φ := fun v => iprop((Φ v ∗ j ↦[wt][ Wasm.Int.natOfUint c ] none) ∗ ↪[frame] f0))
    (es := [.basic (.const (.int32 c)), .basic (.callIndirect i)]) (es' := [.trap])
    iprop(j ↦[wt][ Wasm.Int.natOfUint c ] none)
    (by simp [toVal, mergeValuesList, toValInstr, mergeValues, valNotValCombine, valCombine]) ?_
    (by simp [firstInstr_cons, firstInstrInstr]) (by simp [firstInstr_cons, firstInstrInstr])
  · iintro Ha Hf HΦ
    iapply this $$ Ha Hf
    inext
    iintro Ha Hf
    iapply wp_trap_value
    iframe
  · intro ws locs inst
    simp only [IrisWasm.stateInterp]
    iintro ⟨⟨-, Htab, -⟩, Ha⟩
    ihave >%Hlook := (letI := WasmG.tabHs (hlc := hlc) (GF := GF); genHeap_valid) $$ [$Htab $Ha]
    ipureintro
    rintro rfl
    exact .callIndirectFailure2 (stabAddr_of_lookup hc Hlook)

@[rocq_alias iriswasm.wp_call_indirect_failure_outofbounds]
theorem wp_call_indirect_failure_outofbounds (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF)
    (f0 : Frame) (i j : Nat) (c : I32) (max : Nat) :
    f0.inst.tab[0]? = some j →
    max ≤ Wasm.Int.natOfUint c →
    ⊢ (j ↪[wtsize] max -∗
      ↪[frame] f0 -∗
      ▷ Φ .trapV -∗
      WP ([.basic (.const (.int32 c)), .basic (.callIndirect i)] : Expr) @ s ; E
        {{ v, Φ v ∗ ↪[frame] f0 }} : IProp GF) := by
  intro hc hk
  have := wp_det_step (s := s) (E := E) (f0 := f0) (Φ := fun v => iprop(Φ v ∗ ↪[frame] f0))
    (es := [.basic (.const (.int32 c)), .basic (.callIndirect i)]) (es' := [.trap])
    iprop(j ↪[wtsize] max)
    (by simp [toVal, mergeValuesList, toValInstr, mergeValues, valNotValCombine, valCombine]) ?_
    (by simp [firstInstr_cons, firstInstrInstr]) (by simp [firstInstr_cons, firstInstrInstr])
  · iintro Ha Hf HΦ
    iapply this $$ Ha Hf
    inext
    iintro - Hf
    iapply wp_trap_value
    iframe
  · intro ws locs inst
    simp only [IrisWasm.stateInterp]
    iintro ⟨⟨-, -, -, -, -, -, Hts, -⟩, Ha⟩
    ihave >%Hlook := (letI := WasmG.tabsizeHs (hlc := hlc) (GF := GF); genHeap_valid) $$ [$Hts $Ha]
    ipureintro
    rintro rfl
    exact .callIndirectFailure2 (stabAddr_none_of_size hc Hlook hk)

end IrisWasm
