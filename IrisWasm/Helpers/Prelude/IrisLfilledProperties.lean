/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Helpers.LfillPrelude.LfillPrelude

/-! Port of `theories/iris/helpers/prelude/iris_lfilled_properties.v`. -/

namespace IrisWasm

open Wasm

/-! ## Inversion helpers for `lfilled` (not in Coq; used by the tactics below) -/

theorem lfilled_zero_inv {lh : Lholed} {es LI : List AdministrativeInstruction} :
    lfilled 0 lh es LI = true →
    ∃ vs es', lh = .base vs es' ∧ constList vs = true ∧ LI = vs ++ (es ++ es') := by
  intro h
  cases lh with
  | base vs es' =>
    refine ⟨vs, es', rfl, ?_⟩
    simp only [lfilled, lfill] at h
    by_cases hc : constList vs = true <;> simp_all
  | rec_ => simp [lfilled, lfill] at h

theorem lfilled_zero_base_inv {vs es' es LI : List AdministrativeInstruction} :
    lfilled 0 (.base vs es') es LI = true → constList vs = true ∧ LI = vs ++ (es ++ es') := by
  intro h
  obtain ⟨_, _, he, hc, rfl⟩ := lfilled_zero_inv h
  cases he
  exact ⟨hc, rfl⟩

theorem lfilled_succ_rec_inv {k n : Nat} {vs es' es'' es LI : List AdministrativeInstruction}
    {lh : Lholed} :
    lfilled (k + 1) (.rec_ vs n es' lh es'') es LI = true →
    constList vs = true ∧ ∃ l, lfill k lh es = some l ∧ LI = vs ++ .label n es' l :: es'' := by
  intro h
  simp only [lfilled, lfill] at h
  split at h <;> rename_i h'
  · split at h' <;> rename_i hc
    · split at h' <;> rename_i l hl
      · simp at h' h; subst h' h; exact ⟨hc, l, hl, rfl⟩
      · simp at h'
    · simp at h'
  · simp at h

/-! ## Tactics -/

@[rocq_alias iriswasm.found_intruse]
theorem found_intruse (l1 l2 : List AdministrativeInstruction) (x : AdministrativeInstruction) :
    l1 = l2 → (x ∈ l1 → False) → x ∈ l2 → False := by
  intro h h1 h2; subst h; exact h1 h2

/-- Port of Ltac `false_assumption`: closes the goal from a contradictory hypothesis
(`false = true`, `none = some _`, …). -/
macro "false_assumption" : tactic => `(tactic| (exfalso; contradiction))

/-- Port of Ltac `found_intruse x H Hxl1`: `H : l1 = l2`; proves `False` by showing that `x`
occurs in `l2` but not in `l1`. If `x ∉ l1` cannot be shown by `simp`, the goal `False` is left
with `Hxl1 : x ∈ l1` (and possibly the goal `x ∈ l2`). -/
syntax "found_intruse " term:max ppSpace term:max ppSpace ident : tactic

macro_rules
  | `(tactic| found_intruse $x $H $Hxl1) => `(tactic|
      (exfalso
       first
         | refine IrisWasm.found_intruse _ _ $x $H ?_ (by simp)
         | refine IrisWasm.found_intruse _ _ $x $H ?_ ?_
       intro $Hxl1:ident
       try simp at $Hxl1:ident))

/-- Port of Ltac `filled_trap H Hxl1`: from `H : lfilled 0 lh [.trap] LI = true` (with `.trap ∉ LI`)
proves `False`. If `simp` cannot refute `.trap ∈ LI`, leaves `False` with `Hxl1 : .trap ∈ LI`
and `H : LI = vs ++ ([.trap] ++ es')`. -/
macro "filled_trap " H:ident ppSpace Hxl1:ident : tactic => `(tactic|
  (exfalso
   obtain ⟨_, _, _, _, $H:ident⟩ := IrisWasm.lfilled_zero_inv $H
   found_intruse Wasm.AdministrativeInstruction.trap $H $Hxl1))

/-- Port of Ltac `simple_filled H k lh vs l0 n l1 l3` for `H : lfilled k lh es LI = true`
(`k`, `lh` local variables). Case `k = 0`: `lh := .base vs l0`, `Hvs : constList vs = true`,
`H : LI = vs ++ (es ++ l0)`. Case `k + 1`: `lh := .rec_ vs n l1 lh' l2`, `Hvs`,
`Heqles : lfill k lh' es = some l3`, `H : LI = vs ++ .label n l1 l3 :: l2`, then
`found_intruse (.label n l1 l3) H Hxl1` (leaving `False` with `Hxl1` if it fails). -/
syntax "simple_filled " ident ppSpace ident ppSpace ident ppSpace ident ppSpace ident ppSpace
  ident ppSpace ident ppSpace ident : tactic

/-- Port of Ltac `simple_filled2`: like `simple_filled`, but in case `k + 1` only tries
`found_intruse` (leaving the case untouched if it does not close it). -/
syntax "simple_filled2 " ident ppSpace ident ppSpace ident ppSpace ident ppSpace ident ppSpace
  ident ppSpace ident ppSpace ident : tactic

macro_rules
  | `(tactic| simple_filled $H $k $lh $vs $l0 $n $l1 $l3) => do
    let Hvs := Lean.mkIdent `Hvs
    let lh' := Lean.mkIdent `lh'
    let l2 := Lean.mkIdent `l2
    let Heqles := Lean.mkIdent `Heqles
    let Hxl1 := Lean.mkIdent `Hxl1
    `(tactic|
      focus
        rcases $k:ident with _ | $k:ident
        all_goals
          rcases $lh:ident with ⟨$vs:ident, $l0:ident⟩ | ⟨$vs:ident, $n:ident, $l1:ident, $lh':ident, $l2:ident⟩
        case' $(Lean.mkIdent `zero.rec_):ident => exact absurd $H (by simp [Wasm.lfilled, Wasm.lfill])
        case' $(Lean.mkIdent `succ.base):ident => exact absurd $H (by simp [Wasm.lfilled, Wasm.lfill])
        case' $(Lean.mkIdent `succ.rec_):ident =>
          obtain ⟨$Hvs:ident, $l3:ident, $Heqles:ident, $H:ident⟩ := IrisWasm.lfilled_succ_rec_inv $H
          found_intruse (Wasm.AdministrativeInstruction.label $n $l1 $l3) $H $Hxl1
        case' $(Lean.mkIdent `zero.base):ident =>
          obtain ⟨$Hvs:ident, $H:ident⟩ := IrisWasm.lfilled_zero_base_inv $H)
  | `(tactic| simple_filled2 $H $k $lh $vs $l0 $n $l1 $l3) => do
    let Hvs := Lean.mkIdent `Hvs
    let lh' := Lean.mkIdent `lh'
    let l2 := Lean.mkIdent `l2
    let Heqles := Lean.mkIdent `Heqles
    let Hxl1 := Lean.mkIdent `Hxl1
    `(tactic|
      focus
        rcases $k:ident with _ | $k:ident
        all_goals
          rcases $lh:ident with ⟨$vs:ident, $l0:ident⟩ | ⟨$vs:ident, $n:ident, $l1:ident, $lh':ident, $l2:ident⟩
        case' $(Lean.mkIdent `zero.rec_):ident => exact absurd $H (by simp [Wasm.lfilled, Wasm.lfill])
        case' $(Lean.mkIdent `succ.base):ident => exact absurd $H (by simp [Wasm.lfilled, Wasm.lfill])
        case' $(Lean.mkIdent `succ.rec_):ident =>
          obtain ⟨$Hvs:ident, $l3:ident, $Heqles:ident, $H:ident⟩ := IrisWasm.lfilled_succ_rec_inv $H
          try (found_intruse (Wasm.AdministrativeInstruction.label $n $l1 $l3) $H $Hxl1; done)
        case' $(Lean.mkIdent `zero.base):ident =>
          obtain ⟨$Hvs:ident, $H:ident⟩ := IrisWasm.lfilled_zero_base_inv $H)

@[rocq_alias iriswasm.ai_eq_true]
theorem ai_eq_true (a a0 : AdministrativeInstruction) :
    AdministrativeInstruction.beq a a0 = true ↔ a = a0 :=
  AdministrativeInstruction.beq_iff a a0

@[rocq_alias iriswasm.ai_eqseq_true]
theorem ai_eqseq_true (l1 l2 : List AdministrativeInstruction) : l1 = l2 ↔ (l1 == l2) = true := by
  simp

/-! ## lfilled properties -/

@[rocq_alias iriswasm.base_is_empty]
def BaseIsEmpty : Lholed → Prop
  | .base bef aft => bef = [] ∧ aft = []
  | .rec_ _ _ _ lh _ => BaseIsEmpty lh

@[rocq_alias iriswasm.empty_base]
def emptyBase : Lholed → Lholed × Lholed
  | .base bef aft => (.base [] [], .base bef aft)
  | .rec_ a b c lh d => (.rec_ a b c (emptyBase lh).1 d, (emptyBase lh).2)

@[rocq_alias iriswasm.get_layer]
def getLayer : Lholed → Nat →
    Option (List AdministrativeInstruction × Nat × List AdministrativeInstruction × Lholed ×
      List AdministrativeInstruction)
  | .base _ _, _ => none
  | .rec_ vs' n es lh' es', 0 => some (vs', n, es, lh', es')
  | .rec_ _ _ _ lh' _, n + 1 => getLayer lh' n

@[rocq_alias iriswasm.delete_outer]
def deleteOuter (lh : Lholed) : Lholed :=
  match lh with
  | .base _ _ => lh
  | .rec_ _ _ _ lh _ => lh

@[rocq_alias iriswasm.lh_delete_inner]
def lhDeleteInner (lh : Lholed) : Lholed := (emptyBase lh).1

@[rocq_alias iriswasm.sh_pull_const_r]
def shPullConstR : SimpleValidHoled → List Value → SimpleValidHoled
  | .base bef aft, vs => .base (bef ++ vs) aft
  | .rec_ bef n es sh aft, vs => .rec_ bef n es (shPullConstR sh vs) aft

@[rocq_alias iriswasm.lh_pull_const_r]
def lhPullConstR : Lholed → List AdministrativeInstruction → Lholed
  | .base bef aft, vs => .base (bef ++ vs) aft
  | .rec_ bef n es sh aft, vs => .rec_ bef n es (lhPullConstR sh vs) aft

@[rocq_alias iriswasm.lh_minus_Ind]
inductive LhMinusInd : Lholed → Lholed → Lholed → Prop where
  | minusBase (lh : Lholed) : LhMinusInd lh (.base [] []) lh
  | minusInd (lh lh' lh'' : Lholed) (vs : List AdministrativeInstruction) (n : Nat)
      (es es' : List AdministrativeInstruction) :
    LhMinusInd lh lh' lh'' → LhMinusInd (.rec_ vs n es lh es') (.rec_ vs n es lh' es') lh''

@[rocq_alias iriswasm.to_e_list_fmap]
theorem to_e_list_fmap (l : List Value) :
    l.map (fun v => AdministrativeInstruction.basic (.const v)) = vToEList l := rfl

/-! Private inversion helpers on `LfilledInd`. -/

private theorem ind_base_inv {k : Nat} {vs es' es LI : List AdministrativeInstruction} :
    LfilledInd k (.base vs es') es LI → k = 0 ∧ constList vs = true ∧ LI = vs ++ es ++ es' := by
  intro h; cases h; exact ⟨rfl, ‹_›, rfl⟩

private theorem ind_rec_inv {k n : Nat} {vs es' es'' es LI : List AdministrativeInstruction}
    {lh : Lholed} :
    LfilledInd k (.rec_ vs n es' lh es'') es LI →
    ∃ k' l, k = k' + 1 ∧ constList vs = true ∧ LfilledInd k' lh es l ∧
      LI = vs ++ [.label n es' l] ++ es'' := by
  intro h; cases h; exact ⟨_, _, rfl, ‹_›, ‹_›, rfl⟩

private theorem ind_nil (es : List AdministrativeInstruction) : LfilledInd 0 (.base [] []) es es := by
  simpa using LfilledInd.lfilledBase [] es [] rfl

private theorem ind_inj {k : Nat} {lh : Lholed} {es LI LI' : List AdministrativeInstruction} :
    LfilledInd k lh es LI → LfilledInd k lh es LI' → LI = LI' := by
  simp only [← lfilled_Ind_Equivalent, lfilled]
  split <;> simp_all

private theorem ind_depth {k : Nat} {lh : Lholed} {es LI : List AdministrativeInstruction} :
    LfilledInd k lh es LI → lhDepth lh = k := by
  intro h; induction h <;> simp_all [lhDepth]


private theorem ind_rec {k n : Nat} {vs es' es'' es l : List AdministrativeInstruction}
    {lh : Lholed} (hvs : constList vs = true) (h : LfilledInd k lh es l) :
    LfilledInd (k + 1) (.rec_ vs n es' lh es'') es (vs ++ .label n es' l :: es'') := by
  simpa using LfilledInd.lfilledRec _ _ n es' _ es'' _ _ hvs h

@[rocq_alias iriswasm.can_empty_base]
theorem can_empty_base (k : Nat) (lh : Lholed) (es LI : List AdministrativeInstruction)
    (lh' lh0 : Lholed) :
    emptyBase lh = (lh', lh0) → lfilled k lh es LI = true →
    ∃ es', lfilled 0 lh0 es es' = true ∧ lfilled k lh' es' LI = true ∧ BaseIsEmpty lh' := by
  simp only [lfilled_Ind_Equivalent]
  intro hE hF
  induction hF generalizing lh' lh0 with
  | lfilledBase vs es es' hvs =>
    simp only [emptyBase, Prod.mk.injEq] at hE; obtain ⟨rfl, rfl⟩ := hE
    refine ⟨vs ++ es ++ es', .lfilledBase _ _ _ hvs, ind_nil _, rfl, rfl⟩
  | lfilledRec k vs n es' lh es'' es LI hvs _ ih =>
    simp only [emptyBase, Prod.mk.injEq] at hE; obtain ⟨rfl, rfl⟩ := hE
    obtain ⟨e, h0, h1, he⟩ := ih _ _ rfl
    exact ⟨e, h0, .lfilledRec _ _ _ _ _ _ _ _ hvs h1, he⟩

@[rocq_alias iriswasm.can_fill_base]
theorem can_fill_base (k : Nat) (lh : Lholed) (es es' LI : List AdministrativeInstruction)
    (lh' lh0 : Lholed) :
    emptyBase lh = (lh', lh0) →
    lfilled 0 lh0 es es' = true → lfilled k lh' es' LI = true → lfilled k lh es LI = true := by
  simp only [lfilled_Ind_Equivalent]
  induction lh generalizing k LI lh' lh0 with
  | base bef aft =>
    simp only [emptyBase, Prod.mk.injEq]; rintro ⟨rfl, rfl⟩ h0 h1
    obtain ⟨-, hc, rfl⟩ := ind_base_inv h0
    obtain ⟨rfl, -, rfl⟩ := ind_base_inv h1
    simpa using LfilledInd.lfilledBase _ es _ hc
  | rec_ a b c lh d ih =>
    simp only [emptyBase, Prod.mk.injEq]; rintro ⟨rfl, rfl⟩ h0 h1
    obtain ⟨k', l, rfl, hc, h1', rfl⟩ := ind_rec_inv h1
    exact .lfilledRec _ _ _ _ _ _ _ _ hc (ih k' l _ _ rfl h0 h1')

@[rocq_alias iriswasm.lh_minus]
def lhMinus : Lholed → Lholed → Option Lholed
  | lh1, .base [] [] => some lh1
  | _, .base _ _ => none
  | .base _ _, .rec_ _ _ _ _ _ => none
  | .rec_ bef1 n1 es1 lh1 aft1, .rec_ bef2 n2 es2 lh2 aft2 =>
    if bef1 == bef2 && n1 == n2 && es1 == es2 && aft1 == aft2 then lhMinus lh1 lh2 else none

private theorem lhMinus_base_eq {lh0 lh2 : Lholed} {bef aft : List AdministrativeInstruction} :
    lhMinus lh0 (.base bef aft) = some lh2 ↔ bef = [] ∧ aft = [] ∧ lh2 = lh0 := by
  rcases bef with _ | ⟨_, _⟩ <;> rcases aft with _ | ⟨_, _⟩ <;> simp [lhMinus, eq_comm]

private theorem lhMinus_rec_eq {lh0 lh lh2 : Lholed} {bef es aft : List AdministrativeInstruction}
    {n : Nat} :
    lhMinus lh0 (.rec_ bef n es lh aft) = some lh2 ↔
      ∃ lh0', lh0 = .rec_ bef n es lh0' aft ∧ lhMinus lh0' lh = some lh2 := by
  cases lh0 with
  | base => simp [lhMinus]
  | rec_ =>
    simp only [lhMinus, Bool.and_eq_true, beq_iff_eq, Option.ite_none_right_eq_some,
      Lholed.rec_.injEq]
    constructor
    · rintro ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, h⟩; exact ⟨_, ⟨rfl, rfl, rfl, rfl, rfl⟩, h⟩
    · rintro ⟨_, ⟨rfl, rfl, rfl, rfl, rfl⟩, h⟩; exact ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, h⟩

@[rocq_alias iriswasm.lh_minus_plus]
theorem lh_minus_plus (k0 k1 : Nat) (lh0 lh1 lh2 : Lholed)
    (es0 es1 es2 : List AdministrativeInstruction) :
    lhMinus lh0 lh1 = some lh2 → k0 ≥ k1 →
    lfilled (k0 - k1) lh2 es0 es1 = true → lfilled k1 lh1 es1 es2 = true →
    lfilled k0 lh0 es0 es2 = true := by
  simp only [lfilled_Ind_Equivalent]
  induction lh1 generalizing k0 k1 lh0 es2 with
  | base bef aft =>
    rw [lhMinus_base_eq]; rintro ⟨rfl, rfl, rfl⟩ _ h2 h1
    obtain ⟨rfl, -, rfl⟩ := ind_base_inv h1
    simpa using h2
  | rec_ bef n es lh1 aft ih =>
    rw [lhMinus_rec_eq]; rintro ⟨lh0', rfl, hm⟩ hk h2 h1
    obtain ⟨k1', l, rfl, hc, h1', rfl⟩ := ind_rec_inv h1
    obtain ⟨k0', rfl⟩ : ∃ k0', k0 = k0' + 1 := ⟨k0 - 1, by omega⟩
    exact .lfilledRec _ _ _ _ _ _ _ _ hc
      (ih k0' k1' lh0' l hm (by omega) (by simpa using h2) h1')

@[rocq_alias iriswasm.lh_minus_minus]
theorem lh_minus_minus (k0 k1 : Nat) (lh0 lh1 lh2 : Lholed)
    (es0 es1 es2 : List AdministrativeInstruction) :
    lhMinus lh0 lh1 = some lh2 →
    lfilled k0 lh0 es0 es2 = true → lfilled k1 lh1 es1 es2 = true →
    lfilled (k0 - k1) lh2 es0 es1 = true := by
  simp only [lfilled_Ind_Equivalent]
  induction lh1 generalizing k0 k1 lh0 es2 with
  | base bef aft =>
    rw [lhMinus_base_eq]; rintro ⟨rfl, rfl, rfl⟩ h0 h1
    obtain ⟨rfl, -, rfl⟩ := ind_base_inv h1
    simpa using h0
  | rec_ bef n es lh1 aft ih =>
    rw [lhMinus_rec_eq]; rintro ⟨lh0', rfl, hm⟩ h0 h1
    obtain ⟨k1', l, rfl, -, h1', rfl⟩ := ind_rec_inv h1
    obtain ⟨k0', l', rfl, -, h0', he⟩ := ind_rec_inv h0
    simp at he; subst he
    simpa using ih k0' k1' lh0' l hm h0' h1'

@[rocq_alias iriswasm.lfilled_depth]
theorem lfilled_depth (k : Nat) (lh : Lholed) (es LI : List AdministrativeInstruction) :
    lfilled k lh es LI = true → lhDepth lh = k := by
  rw [lfilled_Ind_Equivalent]; exact ind_depth

@[rocq_alias iriswasm.lfilled_same_index]
theorem lfilled_same_index (k0 k1 : Nat) (lh : Lholed) (es0 es1 LI0 LI1 : List AdministrativeInstruction) :
    lfilled k0 lh es0 LI0 = true → lfilled k1 lh es1 LI1 = true → k0 = k1 := by
  intro h1 h2
  rw [← lfilled_depth _ _ _ _ h1, ← lfilled_depth _ _ _ _ h2]

@[rocq_alias iriswasm.lh_minus_depth]
theorem lh_minus_depth (lh0 lh1 lh2 : Lholed) :
    lhMinus lh0 lh1 = some lh2 → lhDepth lh2 = lhDepth lh0 - lhDepth lh1 := by
  induction lh1 generalizing lh0 with
  | base bef aft => rw [lhMinus_base_eq]; rintro ⟨rfl, rfl, rfl⟩; simp [lhDepth]
  | rec_ bef n es lh1 aft ih =>
    rw [lhMinus_rec_eq]; rintro ⟨lh0', rfl, hm⟩
    simp only [lhDepth, ih _ hm]; omega

@[rocq_alias iriswasm.lh_minus_minus2]
theorem lh_minus_minus2 (k0 k1 : Nat) (lh0 lh1 lh2 : Lholed)
    (es0 es1 es2 : List AdministrativeInstruction) :
    lhMinus lh0 lh1 = some lh2 → k0 ≥ k1 →
    lfilled k0 lh0 es0 es2 = true → lfilled (k0 - k1) lh2 es0 es1 = true →
    lfilled k1 lh1 es1 es2 = true := by
  simp only [lfilled_Ind_Equivalent]
  induction lh1 generalizing k0 k1 lh0 es2 with
  | base bef aft =>
    rw [lhMinus_base_eq]; rintro ⟨rfl, rfl, rfl⟩ hk h0 h2
    have := ind_depth h0; have := ind_depth h2
    obtain rfl : k1 = 0 := by omega
    obtain rfl := ind_inj h0 h2
    exact ind_nil _
  | rec_ bef n es lh1 aft ih =>
    intro hm hk h0 h2
    have hd := lh_minus_depth _ _ _ hm
    rw [lhMinus_rec_eq] at hm; obtain ⟨lh0', rfl, hm⟩ := hm
    obtain ⟨k0', l, rfl, hc, h0', rfl⟩ := ind_rec_inv h0
    rcases k1 with _ | k1
    · have := ind_depth h0'; have := ind_depth h2
      simp only [lhDepth] at hd; omega
    · exact .lfilledRec _ _ _ _ _ _ _ _ hc (ih k0' k1 lh0' l hm (by omega) h0' (by simpa using h2))

@[rocq_alias iriswasm.filled_twice]
theorem filled_twice (k0 k1 : Nat) (lh0 lh1 : Lholed) (es0 es1 LI : List AdministrativeInstruction) :
    lfilled k0 lh0 es0 LI = true → lfilled k1 lh1 es1 LI = true → k0 ≥ k1 → BaseIsEmpty lh1 →
    ∃ lh2, lhMinus lh0 lh1 = some lh2 := by
  simp only [lfilled_Ind_Equivalent]
  induction lh1 generalizing k0 k1 lh0 LI with
  | base bef aft =>
    rintro - - - ⟨rfl, rfl⟩; exact ⟨lh0, lhMinus_base_eq.2 ⟨rfl, rfl, rfl⟩⟩
  | rec_ bef1 n1 nes1 lh1 aft1 ih =>
    intro h0 h1 hk hE
    obtain ⟨k1', l1, rfl, hc1, h1', rfl⟩ := ind_rec_inv h1
    cases lh0 with
    | base => obtain ⟨rfl, -⟩ := ind_base_inv h0; omega
    | rec_ bef0 n0 nes0 lh0 aft0 =>
      obtain ⟨k0', l0, rfl, hc0, h0', he⟩ := ind_rec_inv h0
      simp only [List.append_assoc, List.singleton_append] at he
      obtain ⟨rfl, hl, rfl⟩ := first_values _ _ _ _ _ _ rfl rfl hc1 hc0 he
      cases hl
      obtain ⟨lh2, h⟩ := ih _ _ _ _ h0' h1' (by omega) hE
      exact ⟨lh2, lhMinus_rec_eq.2 ⟨_, rfl, h⟩⟩

private theorem sizeOfInstruction_pos (a : AdministrativeInstruction) : 0 < sizeOfInstruction a := by
  cases a <;> simp [sizeOfInstruction]

private theorem lengthRec_app (l1 l2 : List AdministrativeInstruction) :
    lengthRec (l1 ++ l2) = lengthRec l1 + lengthRec l2 := by
  simp [lengthRec]

private theorem lengthRec_cons (a : AdministrativeInstruction) (l : List AdministrativeInstruction) :
    lengthRec (a :: l) = sizeOfInstruction a + lengthRec l := by
  simp [lengthRec]

@[rocq_alias iriswasm.length_lfilled_rec_or_same]
theorem length_lfilled_rec_or_same (k : Nat) (lh : Lholed) (es LI : List AdministrativeInstruction) :
    lfilled k lh es LI = true → lengthRec es < lengthRec LI ∨ es = LI := by
  rw [lfilled_Ind_Equivalent]
  intro h
  induction h with
  | lfilledBase vs es es' =>
    rcases vs with _ | ⟨a, vs⟩
    · rcases es' with _ | ⟨b, es'⟩
      · simp
      · left; have := sizeOfInstruction_pos b; simp only [lengthRec_app, lengthRec_cons]; omega
    · left; have := sizeOfInstruction_pos a; simp only [lengthRec_app, lengthRec_cons]; omega
  | lfilledRec k vs n es' lh' es'' es LI _ _ ih =>
    left
    have : lengthRec es ≤ lengthRec LI := by rcases ih with h | rfl <;> omega
    simp only [lengthRec_app, lengthRec_cons, sizeOfInstruction]
    simp only [lengthRec] at this ⊢; omega

@[rocq_alias iriswasm.filled_trivial]
theorem filled_trivial (k : Nat) (lh : Lholed) (es : List AdministrativeInstruction) :
    lfilled k lh es es = true → k = 0 ∧ lh = .base [] [] := by
  intro hf
  have hf' := (lfilled_Ind_Equivalent _ _ _ _).1 hf
  cases lh with
  | base vs es' =>
    obtain ⟨rfl, -, he⟩ := ind_base_inv hf'
    have := congrArg List.length he
    simp only [List.length_append] at this
    obtain rfl : vs = [] := List.eq_nil_of_length_eq_zero (by omega)
    obtain rfl : es' = [] := List.eq_nil_of_length_eq_zero (by omega)
    exact ⟨rfl, rfl⟩
  | rec_ vs n es' lh es'' =>
    exfalso
    obtain ⟨k', l, rfl, -, h, he⟩ := ind_rec_inv hf'
    have h1 := length_lfilled_rec_or_same _ _ _ _ ((lfilled_Ind_Equivalent _ _ _ _).2 h)
    have h2 := congrArg lengthRec he
    simp only [lengthRec_app, lengthRec_cons, sizeOfInstruction] at h2
    simp only [lengthRec] at h1 h2
    rcases h1 with h1 | rfl <;> omega


@[rocq_alias iriswasm.lfilled_const]
theorem lfilled_const (k : Nat) (lh : Lholed) (es LI : List AdministrativeInstruction) :
    lfilled k lh es LI = true → constList LI = true → k = 0 ∧ constList es = true := by
  rw [lfilled_Ind_Equivalent]; intro h hc
  cases h with
  | lfilledBase => simp_all [constList]
  | lfilledRec => simp [constList, isConst] at hc

@[rocq_alias iriswasm.filled_singleton]
theorem filled_singleton (k : Nat) (lh : Lholed) (es : List AdministrativeInstruction)
    (e : AdministrativeInstruction) :
    lfilled k lh es [e] = true → (∀ a b c, e = .label a b c → False) → es ≠ [] →
    k = 0 ∧ lh = .base [] [] ∧ es = [e] := by
  rw [lfilled_Ind_Equivalent]; intro h hl hne
  cases lh with
  | base vs es' =>
    obtain ⟨rfl, -, he⟩ := ind_base_inv h
    have := congrArg List.length he
    simp only [List.length_append, List.length_singleton] at this
    have : es.length ≠ 0 := by simpa using hne
    obtain rfl : vs = [] := List.eq_nil_of_length_eq_zero (by omega)
    obtain rfl : es' = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp_all
  | rec_ vs n es' lh es'' =>
    obtain ⟨k', l, rfl, -, -, he⟩ := ind_rec_inv h
    rcases vs with _ | ⟨a, vs⟩
    · simp at he; exact (hl _ _ _ he.1).elim
    · simp at he

@[rocq_alias iriswasm.lh_prepend]
def lhPrepend (lh : Lholed) (v : Value) : Lholed :=
  match lh with
  | .base bef aft => .base (.basic (.const v) :: bef) aft
  | .rec_ bef n es lh aft => .rec_ (.basic (.const v) :: bef) n es lh aft

@[rocq_alias iriswasm.lfilled_prepend]
theorem lfilled_prepend (i : Nat) (lh : Lholed) (es : List AdministrativeInstruction) (v : Value)
    (LI : List AdministrativeInstruction) :
    lfilled i lh es LI = true → lfilled i (lhPrepend lh v) es (.basic (.const v) :: LI) = true := by
  simp only [lfilled_Ind_Equivalent]; intro h
  cases h with
  | lfilledBase vs es es' hc =>
    simpa [lhPrepend] using LfilledInd.lfilledBase (.basic (.const v) :: vs) es es'
      (by simpa [constList, isConst] using hc)
  | lfilledRec k vs n es' lh es'' es LI hc h =>
    simpa [lhPrepend] using LfilledInd.lfilledRec k (.basic (.const v) :: vs) n es' lh es'' es LI
      (by simpa [constList, isConst] using hc) h

@[rocq_alias iriswasm.lfilled_vLI]
theorem lfilled_vLI (i : Nat) (lh : Lholed) (e : AdministrativeInstruction)
    (es : List AdministrativeInstruction) (v : Value) (LI : List AdministrativeInstruction) :
    lfilled i lh (e :: es) (.basic (.const v) :: LI) = true →
    (∃ lh', lhPrepend lh' v = lh ∧ lfilled i lh' (e :: es) LI = true) ∨
      (i = 0 ∧ e = .basic (.const v) ∧ ∃ aft, lh = .base [] aft ∧ es ++ aft = LI) := by
  simp only [lfilled_Ind_Equivalent]; intro h
  cases lh with
  | base vs aft =>
    obtain ⟨rfl, hc, he⟩ := ind_base_inv h
    rcases vs with _ | ⟨a, vs⟩
    · simp at he; obtain ⟨rfl, rfl⟩ := he
      exact .inr ⟨rfl, rfl, aft, rfl, rfl⟩
    · simp at he; obtain ⟨rfl, rfl⟩ := he
      simp only [constList, isConst, List.all_cons, Bool.true_and] at hc
      exact .inl ⟨.base vs aft, rfl, by simpa using LfilledInd.lfilledBase vs (e :: es) aft hc⟩
  | rec_ vs n es' lh es'' =>
    obtain ⟨k', l, rfl, hc, h', he⟩ := ind_rec_inv h
    rcases vs with _ | ⟨a, vs⟩
    · simp at he
    · simp at he; obtain ⟨rfl, rfl⟩ := he
      simp only [constList, isConst, List.all_cons, Bool.true_and] at hc
      exact .inl ⟨.rec_ vs n es' lh es'', rfl, ind_rec hc h'⟩

@[rocq_alias iriswasm.lh_minus_Ind_Equivalent]
theorem lh_minus_Ind_Equivalent (lh lh' lh'' : Lholed) :
    lhMinus lh lh' = some lh'' ↔ LhMinusInd lh lh' lh'' := by
  induction lh' generalizing lh lh'' with
  | base bef aft =>
    rw [lhMinus_base_eq]
    constructor
    · rintro ⟨rfl, rfl, rfl⟩; exact .minusBase _
    · intro h; cases h; exact ⟨rfl, rfl, rfl⟩
  | rec_ bef n es lh' aft ih =>
    rw [lhMinus_rec_eq]
    constructor
    · rintro ⟨lh0, rfl, h⟩; exact .minusInd _ _ _ _ _ _ _ ((ih _ _).1 h)
    · intro h; cases h with
      | minusInd lh0 _ _ _ _ _ _ h => exact ⟨lh0, rfl, (ih _ _).2 h⟩

@[rocq_alias iriswasm.lh_delete_inner_eq]
theorem lh_delete_inner_eq (lh : Lholed) : BaseIsEmpty lh → lhDeleteInner lh = lh := by
  induction lh with
  | base bef aft => rintro ⟨rfl, rfl⟩; rfl
  | rec_ a b c lh d ih =>
    intro h; have := ih h; simp only [lhDeleteInner] at this
    simp [lhDeleteInner, emptyBase, this]

@[rocq_alias iriswasm.base_is_empty_delete_inner]
theorem base_is_empty_delete_inner (lh : Lholed) : BaseIsEmpty (lhDeleteInner lh) := by
  induction lh with
  | base => exact ⟨rfl, rfl⟩
  | rec_ a b c lh d ih => simpa [lhDeleteInner, emptyBase, BaseIsEmpty] using ih

@[rocq_alias iriswasm.lh_minus_eq]
theorem lh_minus_eq (lh : Lholed) : lhMinus lh (.base [] []) = some lh := by
  cases lh <;> rfl

@[rocq_alias iriswasm.get_layer_lh_minus]
theorem get_layer_lh_minus (lh : Lholed) (i : Nat) (vs' : List AdministrativeInstruction) (n : Nat)
    (es : List AdministrativeInstruction) (lh' : Lholed) (es' : List AdministrativeInstruction) :
    getLayer lh i = some (vs', n, es, lh', es') → ∃ lh'', lhMinus lh lh'' = some lh' := by
  induction lh generalizing i with
  | base => simp [getLayer]
  | rec_ a b c lh d ih =>
    cases i with
    | zero =>
      simp only [getLayer, Option.some.injEq, Prod.mk.injEq]
      rintro ⟨rfl, rfl, rfl, rfl, rfl⟩
      exact ⟨.rec_ a b c (.base [] []) d, lhMinus_rec_eq.2 ⟨_, rfl, lh_minus_eq _⟩⟩
    | succ i =>
      intro h; obtain ⟨lh'', h⟩ := ih i h
      exact ⟨.rec_ a b c lh'' d, lhMinus_rec_eq.2 ⟨_, rfl, h⟩⟩

@[rocq_alias iriswasm.LH_rec_circular]
theorem LH_rec_circular (vs' : List AdministrativeInstruction) (m : Nat)
    (es : List AdministrativeInstruction) (lh : Lholed) (es' : List AdministrativeInstruction) :
    Lholed.rec_ vs' m es lh es' = lh → False := by
  intro h; have := congrArg lhDepth h; simp [lhDepth] at this

@[rocq_alias iriswasm.lminus_base_inv]
theorem lminus_base_inv (lh lh' : Lholed) : LhMinusInd lh lh' lh → lh' = .base [] [] := by
  intro h
  cases h with
  | minusBase => rfl
  | minusInd lh0 lh0' _ _ _ _ _ h =>
    have hd := lh_minus_depth _ _ _ ((lh_minus_Ind_Equivalent _ _ _).2 h)
    simp only [lhDepth] at hd; omega

@[rocq_alias iriswasm.lminus_rec_inv]
theorem lminus_rec_inv (vs' : List AdministrativeInstruction) (m : Nat)
    (es : List AdministrativeInstruction) (lh : Lholed) (es' : List AdministrativeInstruction)
    (lh'' : Lholed) :
    lhMinus (.rec_ vs' m es lh es') lh'' = some lh → lh'' = .rec_ vs' m es (.base [] []) es' := by
  rw [lh_minus_Ind_Equivalent]; intro h
  cases h with
  | minusInd _ lh0 _ _ _ _ _ h => rw [lminus_base_inv _ _ h]

@[rocq_alias iriswasm.get_layer_depth]
theorem get_layer_depth (i : Nat) (lh : Lholed)
    (x : List AdministrativeInstruction × Nat × List AdministrativeInstruction × Lholed ×
      List AdministrativeInstruction) :
    getLayer lh i = some x → i < lhDepth lh := by
  induction lh generalizing i with
  | base => simp [getLayer]
  | rec_ a b c lh d ih =>
    cases i with
    | zero => simp [lhDepth]
    | succ i => intro h; have := ih i h; simp only [lhDepth]; omega

@[rocq_alias iriswasm.get_layer_depth_lt]
theorem get_layer_depth_lt (i : Nat) (lh : Lholed) (vs' : List AdministrativeInstruction) (n : Nat)
    (es : List AdministrativeInstruction) (lh' : Lholed) (es' : List AdministrativeInstruction) :
    getLayer lh i = some (vs', n, es, lh', es') → lhDepth lh' < lhDepth lh := by
  induction lh generalizing i with
  | base => simp [getLayer]
  | rec_ a b c lh d ih =>
    cases i with
    | zero =>
      simp only [getLayer, Option.some.injEq, Prod.mk.injEq]
      rintro ⟨rfl, rfl, rfl, rfl, rfl⟩; simp [lhDepth]
    | succ i => intro h; have := ih i h; simp only [lhDepth]; omega

@[rocq_alias iriswasm.get_layer_circular]
theorem get_layer_circular (lh : Lholed) (i : Nat) (vs' : List AdministrativeInstruction) (m : Nat)
    (es es' : List AdministrativeInstruction) :
    getLayer lh i = some (vs', m, es, lh, es') → False := by
  intro h; have := get_layer_depth_lt _ _ _ _ _ _ _ h; omega

/-- The layer at index `j` sits at depth `j + 1`; its inner hole context has the rest. -/
private theorem get_layer_exists (j : Nat) (lh : Lholed) :
    j < lhDepth lh → ∃ vs n es lh' es', getLayer lh j = some (vs, n, es, lh', es') ∧
      lhDepth lh' + j + 1 = lhDepth lh := by
  induction lh generalizing j with
  | base => simp [lhDepth]
  | rec_ a b c lh d ih =>
    cases j with
    | zero => intro _; exact ⟨a, b, c, lh, d, rfl, by simp [lhDepth]⟩
    | succ j =>
      intro h; simp only [lhDepth] at h
      obtain ⟨vs, n, es, lh', es', h1, h2⟩ := ih j (by omega)
      exact ⟨vs, n, es, lh', es', h1, by simp only [lhDepth]; omega⟩

@[rocq_alias iriswasm.get_layer_find]
theorem get_layer_find (i : Nat) (lh' : Lholed) :
    i + 1 < lhDepth lh' →
    ∃ (vs0' : List AdministrativeInstruction) (n0 : Nat) (es0 vs' : List AdministrativeInstruction)
      (n : Nat) (es : List AdministrativeInstruction) (lh : Lholed)
      (es' es0' : List AdministrativeInstruction) (lh'' : Lholed),
      getLayer lh' (lhDepth lh' - (i + 1 + 1)) = some (vs0', n0, es0, .rec_ vs' n es lh es', es0') ∧
        lhMinus lh' lh'' = some (.rec_ vs' n es lh es') ∧ lhDepth lh = i := by
  intro hlt
  obtain ⟨vs0, n0, es0, L, es0', hL, hd⟩ := get_layer_exists (lhDepth lh' - (i + 1 + 1)) lh'
    (by omega)
  cases L with
  | base => simp only [lhDepth] at hd; omega
  | rec_ vs' n es lh es' =>
    obtain ⟨lh'', hm⟩ := get_layer_lh_minus _ _ _ _ _ _ _ hL
    simp only [lhDepth] at hd
    exact ⟨vs0, n0, es0, vs', n, es, lh, es', es0', lh'', hL, hm, by omega⟩

/-- Splitting a fill along `lhMinus`. -/
private theorem lh_minus_split {lh0 lh1 lh2 : Lholed} {k0 : Nat}
    {es0 es2 : List AdministrativeInstruction} :
    lhMinus lh0 lh1 = some lh2 → LfilledInd k0 lh0 es0 es2 →
    ∃ es1, LfilledInd (lhDepth lh2) lh2 es0 es1 ∧ LfilledInd (k0 - lhDepth lh2) lh1 es1 es2 := by
  induction lh1 generalizing lh0 k0 es2 with
  | base bef aft =>
    rw [lhMinus_base_eq]; rintro ⟨rfl, rfl, rfl⟩ h
    obtain rfl := ind_depth h
    exact ⟨es2, h, by simpa using ind_nil es2⟩
  | rec_ bef n es lh1 aft ih =>
    intro hm h
    have hd := lh_minus_depth _ _ _ hm
    rw [lhMinus_rec_eq] at hm; obtain ⟨lh0', rfl, hm⟩ := hm
    obtain ⟨k0', l, rfl, hc, h', rfl⟩ := ind_rec_inv h
    obtain ⟨es1, h1, h2⟩ := ih hm h'
    have := ind_depth h'
    simp only [lhDepth] at hd
    refine ⟨es1, h1, ?_⟩
    rw [show k0' + 1 - lhDepth lh2 = (k0' - lhDepth lh2) + 1 by omega]
    exact .lfilledRec _ _ _ _ _ _ _ _ hc h2

@[rocq_alias iriswasm.lfilled_minus]
theorem lfilled_minus (lh' : Lholed) (i : Nat) (vs' : List AdministrativeInstruction) (n : Nat)
    (es : List AdministrativeInstruction) (lh : Lholed) (es' e LI : List AdministrativeInstruction)
    (j : Nat) (lh'' : Lholed) :
    lhMinus lh' lh'' = some lh → i < lhDepth lh' →
    getLayer lh' (lhDepth lh' - (i + 1)) = some (vs', n, es, lh, es') →
    lfilled j lh' e LI = true →
    ∃ LI', lfilled i lh e LI' = true ∧ lfilled (j - i) lh'' LI' LI = true := by
  simp only [lfilled_Ind_Equivalent]
  intro hm hi hl hf
  obtain ⟨_, _, _, L, _, hL, hd⟩ := get_layer_exists (lhDepth lh' - (i + 1)) lh' (by omega)
  rw [hl] at hL; simp only [Option.some.injEq, Prod.mk.injEq] at hL
  obtain ⟨-, -, -, hLL, -⟩ := hL
  rw [← hLL] at hd
  obtain rfl : lhDepth lh = i := by omega
  exact lh_minus_split hm hf

@[rocq_alias iriswasm.lfilled_split]
theorem lfilled_split (i j : Nat) (lh : Lholed) (e LI : List AdministrativeInstruction) :
    i ≤ j → lfilled j lh e LI = true →
    ∃ lh' lh'' LI', lfilled i lh' e LI' = true ∧ lfilled (j - i) lh'' LI' LI = true := by
  simp only [lfilled_Ind_Equivalent]
  intro hle h
  induction h generalizing i with
  | lfilledBase vs es es' hc =>
    obtain rfl : i = 0 := by omega
    exact ⟨_, _, _, .lfilledBase _ _ _ hc, ind_nil _⟩
  | lfilledRec k vs n es' lh es'' es LI hc h ih =>
    by_cases hik : i = k + 1
    · subst hik
      exact ⟨_, _, _, .lfilledRec _ _ _ _ _ _ _ _ hc h, by simpa using ind_nil _⟩
    · obtain ⟨lh1, lh2, LI', h1, h2⟩ := ih i (by omega)
      refine ⟨lh1, .rec_ vs n es' lh2 es'', LI', h1, ?_⟩
      rw [show k + 1 - i = (k - i) + 1 by omega]
      exact .lfilledRec _ _ _ _ _ _ _ _ hc h2

/-- Local version of `const_es_exists` (`properties.v`). -/
private theorem const_es_exists' (es : List AdministrativeInstruction) :
    constList es = true → ∃ vs, es = vToEList vs := by
  induction es with
  | nil => exact fun _ => ⟨[], rfl⟩
  | cons a es ih =>
    simp only [constList, List.all_cons, Bool.and_eq_true]
    rintro ⟨ha, hes⟩
    obtain ⟨vs, rfl⟩ := ih hes
    match a, ha with
    | .basic (.const v), _ => exact ⟨v :: vs, rfl⟩

@[rocq_alias iriswasm.lfilled_to_sfill]
theorem lfilled_to_sfill (i : Nat) (lh : Lholed) (es LI : List AdministrativeInstruction) :
    lfilled i lh es LI = true → ∃ sh, LI = sfill sh es := by
  rw [lfilled_Ind_Equivalent]; intro h
  induction h with
  | lfilledBase vs es es' hc =>
    obtain ⟨vs', rfl⟩ := const_es_exists' _ hc
    exact ⟨.base vs' es', by simp [sfill]⟩
  | lfilledRec k vs n es' lh es'' es LI hc _ ih =>
    obtain ⟨vs', rfl⟩ := const_es_exists' _ hc
    obtain ⟨sh, rfl⟩ := ih
    exact ⟨.rec_ vs' n es' sh es'', by simp [sfill]⟩

@[rocq_alias iriswasm.sfill_sh_pull_const_r]
theorem sfill_sh_pull_const_r (sh : SimpleValidHoled) :
    ∀ e x, sfill (shPullConstR sh x) e = sfill sh (vToEList x ++ e) := by
  induction sh with
  | base => intro e x; simp [sfill, shPullConstR, vToEList]
  | rec_ bef n es sh aft ih => intro e x; simp [sfill, shPullConstR, ih]

@[rocq_alias iriswasm.const_list_app]
theorem const_list_app (v1 v2 : List AdministrativeInstruction) :
    constList (v1 ++ v2) = true ↔ constList v1 = true ∧ constList v2 = true := by
  simp [constList]

@[rocq_alias iriswasm.lh_pull_const_r_app]
theorem lh_pull_const_r_app (i : Nat) (lh : Lholed) (x : List Value)
    (es es1 : List AdministrativeInstruction) :
    lfilled i lh (vToEList x ++ es) es1 = true → ∃ lh', lfilled i lh' es es1 = true := by
  simp only [lfilled_Ind_Equivalent]
  induction lh generalizing i es1 with
  | base bef aft =>
    intro h; obtain ⟨rfl, hc, rfl⟩ := ind_base_inv h
    refine ⟨.base (bef ++ vToEList x) aft, ?_⟩
    have hx : constList (vToEList x) = true := by simp [constList, vToEList, isConst]
    simpa using LfilledInd.lfilledBase (bef ++ vToEList x) es aft
      ((const_list_app _ _).2 ⟨hc, hx⟩)
  | rec_ bef n es' lh aft ih =>
    intro h; obtain ⟨k', l, rfl, hc, h', rfl⟩ := ind_rec_inv h
    obtain ⟨lh', h''⟩ := ih k' l h'
    exact ⟨.rec_ bef n es' lh' aft, .lfilledRec _ _ _ _ _ _ _ _ hc h''⟩

@[rocq_alias iriswasm.lfilled_flatten]
theorem lfilled_flatten (i : Nat) (lh : Lholed) (e LI l1 : List AdministrativeInstruction)
    (n : Nat) (es l2 : List AdministrativeInstruction) :
    lfilled (i + 1) (.rec_ l1 n es lh l2) e LI = true →
    ∃ LI', lfilled i lh e LI' = true ∧
      lfilled 1 (.rec_ l1 n es (.base [] []) l2) LI' LI = true := by
  simp only [lfilled_Ind_Equivalent]; intro h
  obtain ⟨_, l, he, hc, h', rfl⟩ := ind_rec_inv h
  cases he
  exact ⟨l, h', .lfilledRec _ _ _ _ _ _ _ _ hc (ind_nil _)⟩

end IrisWasm
