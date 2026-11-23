/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Language.Iris.Iris
import IrisWasm.Language.IrisWpDef

/-! Port of `theories/iris/language/iris_atomicity.v`. -/

namespace IrisWasm

open Iris Iris.ProgramLogic Iris.ProgramLogic.Language Wasm Wasm.AdministrativeInstruction

#rocq_ignore iriswasm.is_atomic "Core memory operands can be either integer width"

/-- Atomic expressions; useful for opening invariants. -/
def IsAtomic : Expr → Prop
  | [basic (.const k), basic (.load ..)]
  | [basic (.const k), basic (.const _), basic (.store ..)]
  | [basic (.const k), basic (.growMemory _)] => (AddressOperand.ofValue? k).isSome
  | [basic (.const _), basic (.setGlobal _)] => True
  | [basic (.getGlobal _)] | [basic (.currentMemory _)] => True
  | [trap] => True
  | _ => False

#rocq_ignore iriswasm.destruct_match_goal "Ltac; Lean proofs case on the match directly"

#rocq_ignore iriswasm.is_atomic_eq "Core atomic memory redexes carry an AddressOperand"
theorem is_atomic_eq (e : Expr) (h : IsAtomic e) :
    (∃ k t tp ma, e = [basic (.const (AddressOperand.value k)), basic (.load t tp ma)]) ∨
    (∃ k v t tp ma,
      e = [basic (.const (AddressOperand.value k)), basic (.const v), basic (.store t tp ma)]) ∨
    (∃ k x, e = [basic (.const (AddressOperand.value k)), basic (.growMemory x)]) ∨
    (∃ v g, e = [basic (.const v), basic (.setGlobal g)]) ∨
    (∃ g, e = [basic (.getGlobal g)]) ∨
    (∃ x, e = [basic (.currentMemory x)]) ∨
    e = [trap] := by
  unfold IsAtomic at h
  split at h
  · obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp h
    obtain rfl := AddressOperand.ofValue?_eq_some.mp hk
    exact .inl ⟨k, _, _, _, rfl⟩
  · obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp h
    obtain rfl := AddressOperand.ofValue?_eq_some.mp hk
    exact .inr (.inl ⟨k, _, _, _, _, rfl⟩)
  · obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp h
    obtain rfl := AddressOperand.ofValue?_eq_some.mp hk
    exact .inr (.inr (.inl ⟨k, _, rfl⟩))
  all_goals simp_all

/-- Expressions that can never reduce (used for the no-hole lemmas). -/
private def Stuck (es : Expr) : Prop :=
  constList es = true ∨ (∃ t tp ma, es = [basic (.load t tp ma)]) ∨
  (∃ t tp ma, es = [basic (.store t tp ma)]) ∨
  (∃ v t tp ma, es = [basic (.const v), basic (.store t tp ma)]) ∨
  (∃ g, es = [basic (.setGlobal g)]) ∨ (∃ x, es = [basic (.growMemory x)])

private def okI : AdministrativeInstruction → Bool
  | basic (.const _) | basic (.load ..) | basic (.store ..)
  | basic (.setGlobal _) | basic (.growMemory _) => true
  | _ => false

private theorem stuck_mem {es : Expr} (h : Stuck es) : ∀ x ∈ es, okI x = true := by
  rcases h with h | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    simp [okI]
  intro x hx
  have := List.all_eq_true.1 h x hx
  unfold isConst at this; split at this <;> simp_all

private theorem stuck_infix {vs es es'' : Expr} (hne : es ≠ [])
    (h : Stuck (vs ++ es ++ es'')) : Stuck es := by
  rcases h with h | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
  · left; simp_all [constList, List.all_append]
  all_goals
    rcases vs with _ | ⟨_, _ | ⟨_, _ | _⟩⟩ <;> rcases es with _ | ⟨_, _ | ⟨_, _ | _⟩⟩ <;>
      simp_all [Stuck, constList, isConst]

private theorem reduce_stuck {s f es s' f' es'} (hr : Reduce s f es s' f' es') :
    ¬ Stuck es := by
  induction hr with
  | simple hs =>
    intro h
    have hm := stuck_mem h
    cases hs with
    | trap lh hne hfill =>
      rw [lfilled_Ind_Equivalent] at hfill
      cases hfill
      simpa [okI] using hm trap (by simp)
    | _ => simp [okI, or_imp, forall_and, forall_eq] at hm
  | label es es' k lh hr hfill _ ih =>
    intro h
    rw [lfilled_Ind_Equivalent] at hfill
    cases hfill with
    | lfilledBase vs _ es'' _ => exact ih (stuck_infix (reduce_not_nil hr) (by simpa using h))
    | lfilledRec _ _ n es₁ _ _ _ LI => simpa [okI] using stuck_mem h (label n es₁ LI) (by simp)
  | _ =>
    intro h
    first
    | (have hm := stuck_mem h; simp [okI, or_imp, forall_and, forall_eq] at hm; done)
    | (rcases h with h | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;>
        simp_all [constList, isConst])

/-- Shared shape of the `atomic_no_hole_*` lemmas. -/
private theorem no_hole {s0 f es s' f' es' k lh} {LI : Expr}
    (hlab : ∀ n es' L, label n es' L ∉ LI)
    (hsplit : ∀ vs es es'', es ≠ [] → constList vs = true → vs ++ es ++ es'' = LI →
      (vs = [] ∧ es'' = []) ∨ Stuck es)
    (hr : Reduce s0 f es s' f' es') (hfill : lfilled k lh es LI = true) :
    lh = .base [] [] ∧ k = 0 := by
  rw [lfilled_Ind_Equivalent] at hfill
  cases hfill with
  | lfilledBase vs _ es'' hc =>
    rcases hsplit vs es es'' (reduce_not_nil hr) hc (by simp) with ⟨rfl, rfl⟩ | h
    · simp
    · exact absurd h (reduce_stuck hr)
  | lfilledRec _ _ n es₁ _ _ _ LI => exact absurd (by simp) (hlab n es₁ LI)

macro "no_hole_split" : tactic => `(tactic| (
  intro vs es es'' hne hc h
  rcases vs with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | _⟩⟩⟩ <;>
    rcases es with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | _⟩⟩⟩ <;>
    simp_all [Stuck, constList, isConst]))

#rocq_ignore iriswasm.atomic_no_hole_load "The shape argument works for any constant operand"
theorem atomic_no_hole_load {s0 f es s' f' es' k lh k0 t tp ma}
    (hr : Reduce s0 f es s' f' es')
    (hfill : lfilled k lh es [basic (.const k0), basic (.load t tp ma)] = true) :
    lh = .base [] [] ∧ k = 0 :=
  no_hole (by simp) (by no_hole_split) hr hfill

#rocq_ignore iriswasm.atomic_no_hole_store "The shape argument works for any constant operand"
theorem atomic_no_hole_store {s0 f es s' f' es' k lh k0 v t tp ma}
    (hr : Reduce s0 f es s' f' es')
    (hfill : lfilled k lh es
      [basic (.const k0), basic (.const v), basic (.store t tp ma)] = true) :
    lh = .base [] [] ∧ k = 0 :=
  no_hole (by simp) (by no_hole_split) hr hfill

@[rocq_alias iriswasm.atomic_no_hole_trap]
theorem atomic_no_hole_trap {s0 f es s' f' es' k lh}
    (hr : Reduce s0 f es s' f' es') (hfill : lfilled k lh es [trap] = true) :
    lh = .base [] [] ∧ k = 0 :=
  no_hole (by simp) (by no_hole_split) hr hfill

@[rocq_alias iriswasm.reduce_set_global_false]
theorem reduce_set_global_false {s0 f s' f' es es' g}
    (heq : es = [basic (.setGlobal g)]) (hr : Reduce s0 f es s' f' es') : False :=
  reduce_stuck hr (by simp [Stuck, heq])

@[rocq_alias iriswasm.atomic_no_hole_set_global]
theorem atomic_no_hole_set_global {s0 f es s' f' es' k lh v g}
    (hr : Reduce s0 f es s' f' es')
    (hfill : lfilled k lh es [basic (.const v), basic (.setGlobal g)] = true) :
    lh = .base [] [] ∧ k = 0 :=
  no_hole (by simp) (by no_hole_split) hr hfill

@[rocq_alias iriswasm.atomic_no_hole_get_global]
theorem atomic_no_hole_get_global {s0 f es s' f' es' k lh g}
    (hr : Reduce s0 f es s' f' es')
    (hfill : lfilled k lh es [basic (.getGlobal g)] = true) :
    lh = .base [] [] ∧ k = 0 :=
  no_hole (by simp) (by no_hole_split) hr hfill

private theorem size_no_hole {s f es s' f' es' k lh x}
    (hr : Reduce s f es s' f' es') (h : lfilled k lh es [basic (.currentMemory x)] = true) :
    lh = .base [] [] ∧ k = 0 :=
  no_hole (by simp) (by no_hole_split) hr h

private theorem grow_no_hole {s f es s' f' es' k lh v x} (hr : Reduce s f es s' f' es')
    (h : lfilled k lh es [basic (.const v), basic (.growMemory x)] = true) :
    lh = .base [] [] ∧ k = 0 :=
  no_hole (by simp) (by no_hole_split) hr h

private def atomI : AdministrativeInstruction → Bool
  | basic (.const _) | basic (.load ..) | basic (.store ..) | basic (.setGlobal _)
  | basic (.getGlobal _) | basic (.currentMemory _) | basic (.growMemory _) | trap => true
  | _ => false

private theorem atomic_mem {e : Expr} (ha : IsAtomic e) : ∀ x ∈ e, atomI x = true := by
  rcases is_atomic_eq _ ha with ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ |
    ⟨_, h⟩ | ⟨_, h⟩ | h <;> subst h <;> simp [atomI]

macro "atomic_step_tac" : tactic => `(tactic| first
  | (have hm := atomic_mem ‹_›; simp [atomI, or_imp, forall_and, forall_eq] at hm; done)
  | (rcases is_atomic_eq _ ‹_› with ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ | ⟨_, _, h⟩ |
      ⟨_, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | h <;> simp_all <;>
      first
      | exact congrArg Option.isSome (to_of_val (.immV [_]))
      | exact congrArg Option.isSome (to_of_val (.immV []))
      | exact congrArg Option.isSome (to_of_val .trapV)))

private theorem atomic_step {s f e s' f' e'} (hr : Reduce s f e s' f' e') (ha : IsAtomic e) :
    (toVal e').isSome := by
  induction hr with
  | simple hs =>
    cases hs with
    | trap lh hne hfill =>
      rw [lfilled_Ind_Equivalent] at hfill
      cases hfill with
      | lfilledBase vs _ es'' hc =>
        exfalso; apply hne
        rcases is_atomic_eq _ ha with ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ | ⟨_, _, h⟩ |
          ⟨_, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | h <;>
          rcases vs with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | _⟩⟩⟩ <;> simp_all
    | _ => atomic_step_tac
  | label es es' k lh hr hfill hfill' ih =>
    rcases is_atomic_eq _ ha with ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ | ⟨_, _, h⟩ |
      ⟨_, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | h <;> subst h
    all_goals
      first
      | obtain ⟨rfl, rfl⟩ := atomic_no_hole_load hr hfill
      | obtain ⟨rfl, rfl⟩ := atomic_no_hole_store hr hfill
      | obtain ⟨rfl, rfl⟩ := atomic_no_hole_set_global hr hfill
      | obtain ⟨rfl, rfl⟩ := atomic_no_hole_get_global hr hfill
      | obtain ⟨rfl, rfl⟩ := size_no_hole hr hfill
      | obtain ⟨rfl, rfl⟩ := grow_no_hole hr hfill
      | obtain ⟨rfl, rfl⟩ := atomic_no_hole_trap hr hfill
      simp [lfilled, lfill, constList] at hfill hfill'
      subst hfill hfill'
      exact ih ha
  | _ => atomic_step_tac

@[rocq_alias iriswasm.is_atomic_correct]
theorem is_atomic_correct {a} {e : Expr} (h : IsAtomic e) : Atomic (State := State) a e := by
  apply stronglyAtomic_atomic
  constructor
  rintro ⟨s, locs, inst⟩ obs e' ⟨s', locs', inst'⟩ efs ⟨hr, -, -⟩
  exact atomic_step hr h

/-- Discharges `Atomic a e` for the expressions covered by `IsAtomic`. -/
macro "solve_atomic" : tactic => `(tactic| exact is_atomic_correct (by simp [IsAtomic]))

#rocq_ignore iriswasm.solve_atomic "Ltac; ported as the `solve_atomic` macro"

example {g : Nat} : Atomic (State := State) .WeaklyAtomic [basic (.getGlobal g)] := by
  solve_atomic

example (k : AddressOperand) (t : ValueType) (p : Option (PackedType × Sx)) (ma : MemArg) :
    Atomic (State := State) .StronglyAtomic [basic (.const k.value), basic (.load t p ma)] := by
  solve_atomic

example (x : Nat) : Atomic (State := State) .StronglyAtomic [basic (.currentMemory x)] := by
  solve_atomic

example (x : Nat) (k : AddressOperand) :
    Atomic (State := State) .StronglyAtomic [basic (.const k.value), basic (.growMemory x)] := by
  solve_atomic

end IrisWasm
