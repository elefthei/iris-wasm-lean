/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import Wasm.Properties

/-! Port of `theories/iris/helpers/iris_reduction_core.v`. -/

namespace IrisWasm

open Wasm

#rocq_ignore iriswasm.first_not_const "Ltac used only inside reduction_core's Coq proof"

/-- Number of constants the non-constant instruction `e` consumes when it reduces in store `s`. -/
def redexArity (s : StoreRecord) : AdministrativeInstruction → Nat
  | .basic b =>
    match b with
    | .drop | .unop .. | .testop .. | .cvtop .. | .if_ .. | .brIf _ | .brTable .. | .teeLocal _
    | .setLocal _ | .setGlobal _ | .load .. | .growMemory | .callIndirect _ => 1
    | .binop .. | .relop .. | .store .. => 2
    | .select => 3
    | .block (.tf t1s _) _ | .loop (.tf t1s _) _ => t1s.length
    | _ => 0
  | .invoke a =>
    match s.funcs[a]? with
    | some cl => match clType cl with | .tf t1s _ => t1s.length
    | none => 0
  | _ => 0

/-- Shape of a single reduction: either a redex `vs ++ [e]` (consuming exactly `redexArity s e`
constants) under a constant prefix, or a top-level trap preceded only by constants. -/
def Decomp (s : StoreRecord) (f : Frame) (es : List AdministrativeInstruction)
    (s' : StoreRecord) (f' : Frame) (es' : List AdministrativeInstruction) : Prop :=
  (∃ bc vs e ac core', constList bc = true ∧ constList vs = true ∧ isConst e = false ∧
    e ≠ .trap ∧ vs.length = redexArity s e ∧ es = bc ++ (vs ++ [e]) ++ ac ∧
    es' = bc ++ core' ++ ac ∧ Reduce s f (vs ++ [e]) s' f' core') ∨
  ∃ vs ac, constList vs = true ∧ es = vs ++ .trap :: ac ∧ (s, f) = (s', f')

theorem decomp_self {s : StoreRecord} {f : Frame} {s' : StoreRecord} {f' : Frame}
    {vs : List AdministrativeInstruction} {e : AdministrativeInstruction}
    {es' : List AdministrativeInstruction} (h : Reduce s f (vs ++ [e]) s' f' es')
    (hvs : constList vs = true) (he : isConst e = false) (ht : e ≠ .trap)
    (ha : vs.length = redexArity s e) : Decomp s f (vs ++ [e]) s' f' es' :=
  .inl ⟨[], vs, e, [], es', rfl, hvs, he, ht, ha, by simp, by simp, h⟩

theorem reduce_decomp {s : StoreRecord} {f : Frame} {es : List AdministrativeInstruction}
    {s' : StoreRecord} {f' : Frame} {es' : List AdministrativeInstruction}
    (h : Reduce s f es s' f' es') : Decomp s f es s' f' es' := by
  have h2 := h
  induction h with
  | simple hs =>
    cases hs with
    | block n hc hl ht => exact decomp_self h2 hc rfl (by simp) (by simp [redexArity, *])
    | loop m hc hl ht => exact decomp_self h2 hc rfl (by simp) (by simp [redexArity, *])
    | trap lh _ hl =>
      rw [lfilled_Ind_Equivalent] at hl
      cases hl with
      | lfilledBase vs _ ac hc => exact .inr ⟨vs, ac, hc, by simp, rfl⟩
    | _ =>
      first
      | exact decomp_self (vs := []) h2 rfl rfl (by simp) rfl
      | exact decomp_self (vs := [_]) h2 (by simp_all [constList, isConst]) rfl (by simp) rfl
      | exact decomp_self (vs := [_, _]) h2 rfl rfl (by simp) rfl
      | exact decomp_self (vs := [_, _, _]) h2 rfl rfl (by simp) rfl
  | invokeNative cl t1s ts vcs n k zs i hcl hcl' hves hn =>
    subst hves
    exact decomp_self h2 (v_to_e_is_const_list _) rfl (by simp)
      (by simp_all [redexArity, clType, vToEList])
  | invokeHost cl m n hcl hcl' hves hn =>
    subst hves
    exact decomp_self h2 (v_to_e_is_const_list _) rfl (by simp)
      (by simp_all [redexArity, clType, vToEList])
  | label es es' k lh hr hl hl' ih =>
    rw [lfilled_Ind_Equivalent] at hl hl'
    cases hl with
    | lfilledBase bef _ aft hc =>
      cases hl'
      rcases ih hr with ⟨bc, vs, e, ac, core', hbc, hvs, he, ht, ha, rfl, rfl, hr'⟩ |
        ⟨vs, ac, hvs, rfl, hsf⟩
      · exact .inl ⟨bef ++ bc, vs, e, ac ++ aft, core', by simp_all [constList], hvs, he, ht, ha,
          by simp, by simp, hr'⟩
      · exact .inr ⟨bef ++ vs, ac ++ aft, by simp_all [constList], by simp, hsf⟩
    | lfilledRec k bef n es0 lh' aft _ LI hc hLI =>
      cases hl' with
      | lfilledRec _ _ _ _ _ _ _ LI' _ hLI' =>
        refine .inl ⟨bef, [], .label n es0 LI, aft, [.label n es0 LI'], hc, rfl, rfl,
          by simp, rfl, by simp, by simp, ?_⟩
        refine .label es es' (k + 1) (.rec_ [] n es0 lh' []) hr ?_ ?_ <;>
          rw [lfilled_Ind_Equivalent] <;> simpa using LfilledInd.lfilledRec _ [] _ _ _ [] _ _ rfl ‹_›
  | «local» _ _ => exact decomp_self (vs := []) h2 rfl rfl (by simp) rfl
  | _ =>
    first
    | exact decomp_self (vs := []) h2 rfl rfl (by simp) rfl
    | exact decomp_self (vs := [_]) h2 rfl rfl (by simp) rfl
    | exact decomp_self (vs := [_, _]) h2 rfl rfl (by simp) rfl

@[rocq_alias iriswasm.reduction_core]
theorem reduction_core {bef0 es0 aft0 bef1 es1 aft1 es0' es1' : List AdministrativeInstruction}
    {s : StoreRecord} {f : Frame} {s' : StoreRecord} {f' : Frame} {s0 : StoreRecord} {f0 : Frame} :
    Reduce s f es0 s0 f0 es0' → Reduce s f es1 s' f' es1' →
    constList bef0 = true → constList bef1 = true →
    bef0 ++ es0 ++ aft0 = bef1 ++ es1 ++ aft1 →
    (∃ core bc0 ac0 bc1 ac1 core' : List AdministrativeInstruction,
        constList bc0 = true ∧ constList bc1 = true ∧
        es0 = bc0 ++ core ++ ac0 ∧ es1 = bc1 ++ core ++ ac1 ∧
        bef0 ++ bc0 = bef1 ++ bc1 ∧ ac0 ++ aft0 = ac1 ++ aft1 ∧
        Reduce s f core s' f' core' ∧ bc1 ++ core' ++ ac1 = es1') ∨
    ∃ lh0 lh1 : Lholed, lfilled 0 lh0 [.trap] es0 = true ∧ lfilled 0 lh1 [.trap] es1 = true ∧
      (s, f) = (s', f') := by
  intro hred0 hred1 hbef0 hbef1 heq
  rcases reduce_decomp hred0 with ⟨bc0, vs0, e0, ac0, -, hbc0, hvs0, he0, ht0, ha0, rfl, -, -⟩ |
    ⟨vs0, ac0, hvs0, rfl, -⟩ <;>
  rcases reduce_decomp hred1 with ⟨bc1, vs1, e1, ac1, core', hbc1, hvs1, he1, ht1, ha1, rfl, rfl,
    hr1⟩ | ⟨vs1, ac1, hvs1, rfl, hsf⟩
  · have := first_values (bef0 ++ bc0 ++ vs0) e0 (ac0 ++ aft0) (bef1 ++ bc1 ++ vs1) e1
      (ac1 ++ aft1) he0 he1 (by simp_all [constList]) (by simp_all [constList]) (by simpa using heq)
    obtain ⟨hpre, rfl, hsuf⟩ := this
    obtain ⟨hbc, rfl⟩ := List.append_inj' hpre (by rw [ha0, ha1])
    exact .inl ⟨vs0 ++ [e0], bc0, ac0, bc1, ac1, core', hbc0, hbc1, rfl, rfl,
      by simpa using hbc, hsuf, hr1, rfl⟩
  · exact absurd (first_values (bef0 ++ bc0 ++ vs0) e0 (ac0 ++ aft0) (bef1 ++ vs1) .trap
      (ac1 ++ aft1) he0 rfl (by simp_all [constList]) (by simp_all [constList])
      (by simpa using heq)).2.1 ht0
  · exact absurd (first_values (bef0 ++ vs0) .trap (ac0 ++ aft0) (bef1 ++ bc1 ++ vs1) e1
      (ac1 ++ aft1) rfl he1 (by simp_all [constList]) (by simp_all [constList])
      (by simpa using heq)).2.1.symm ht1
  · exact .inr ⟨.base vs0 ac0, .base vs1 ac1, by simp [lfilled, lfill, hvs0],
      by simp [lfilled, lfill, hvs1], hsf⟩

end IrisWasm
