/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Helpers.Prelude.IrisReduceDetPrelude

/-! Port of `theories/iris/helpers/reduce_det/reduce_det_label.v`. -/

namespace IrisWasm

open Wasm Helpers.ReduceDetPrelude
open AdministrativeInstruction (basic trap)

@[rocq_alias iriswasm.label_det]
theorem label_det {s : StoreRecord} {f : Frame} {es : List AdministrativeInstruction}
    {s' : StoreRecord} {f' : Frame} {es' les les' : List AdministrativeInstruction} {k : Nat}
    {lh : Lholed} {ws2 : StoreRecord} {f2 : Frame} {es2 : List AdministrativeInstruction} {nnn : Nat} :
    (∀ (f f2 f1 : Frame) (es2 es1 es : List AdministrativeInstruction),
      Reduce s f es s' f1 es1 → Reduce s f es ws2 f2 es2 → lengthRec es < nnn →
        reduceDetGoal s' f1 es1 ws2 f2 es2 es) →
    Reduce s f es s' f' es' →
    lfilled k lh es les = true →
    lfilled k lh es' les' = true →
    Reduce s f les ws2 f2 es2 →
    lengthRec les < nnn + 1 →
    ((∀ (f f2 f1 : Frame) (es2 es1 es : List AdministrativeInstruction),
      Reduce s f es s' f1 es1 → Reduce s f es ws2 f2 es2 → lengthRec es < nnn →
        reduceDetGoal s' f1 es1 ws2 f2 es2 es) →
      Reduce s f es ws2 f2 es2 → lengthRec es < nnn + 1 →
        reduceDetGoal s' f' es' ws2 f2 es2 es) →
    reduceDetGoal s' f' les' ws2 f2 es2 les := by
  intro IHnnn H H1 H2 Hred2 Hlen IHreduce
  cases k with
  | zero =>
    obtain ⟨bef, aft, rfl, hbef, rfl⟩ := lfilled0 H1
    obtain ⟨bef', aft', hh, -, rfl⟩ := lfilled0 H2
    cases hh
    obtain ⟨u, x, w, rfl, hu, hx⟩ := const_nonempty H
    by_cases hxt : x = trap
    · subst hxt
      exact goal_trap (.label _ _ 0 _ H H1 H2) Hred2 (vs := bef ++ u) (rest := w ++ aft) (by simp)
        (const_list_concat hbef hu)
    obtain ⟨vs0, cs, m, hbu, hl, rfl, hr⟩ := reduce_first_decomp Hred2 (vs := bef ++ u)
      (rest := w ++ aft) (by simp) (const_list_concat hbef hu) hx hxt
    obtain ⟨vs0', cs', m', rfl, hl', -, -⟩ := reduce_first_decomp H rfl hu hx hxt
    have hbu' : (bef ++ vs0') ++ cs' = vs0 ++ cs := by simpa using hbu
    obtain ⟨rfl, rfl⟩ := List.append_inj' hbu' (hl'.trans hl.symm)
    have hb1 := lfilled_base' (aft := w) (es := cs' ++ [x]) (const_list_split hu).1
    have hb2 := lfilled_base' (aft := w) (es := m) (const_list_split hu).1
    have hr2 : Reduce s f (vs0' ++ cs' ++ x :: w) ws2 f2 (vs0' ++ m ++ w) :=
      .label (cs' ++ [x]) m 0 (.base vs0' w) hr (by simpa using hb1) hb2
    by_cases hba : bef ++ aft = []
    · obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 hba
      simpa using IHreduce IHnnn (by simpa using Hred2) (by simpa using Hlen)
    have hpos := lengthRec_pos hba
    have g := IHnnn _ _ _ _ _ _ (.label _ _ 0 _ H (lfilled_base.2 rfl) (lfilled_base.2 rfl)) hr2
      (by simp only [lengthRec_append] at Hlen hpos ⊢; omega)
    simpa using goal_lift (rest := aft) hbef g
  | succ j =>
    obtain ⟨bef, n, es0, lh', aft, LI0, rfl, hbef, hf, rfl⟩ := lfilledS H1
    obtain ⟨bef', n', es0', lh'', aft', LI1, hh, -, hf', rfl⟩ := lfilledS H2
    cases hh
    obtain ⟨vs0, cs, m, rfl, hl, rfl, hr⟩ := reduce_first_decomp Hred2 rfl hbef (by simp [isConst])
      (by simp)
    obtain rfl : cs = [] := List.eq_nil_of_length_eq_zero (by simpa [redexArity] using hl)
    rcases inv_label' (by simpa using hr) with ⟨-, -, hst⟩ | ⟨LI', hLI, rfl⟩
    · exact (label_step_no_reduce hst (.label _ _ j lh' H hf hf')).elim
    · have g := IHnnn _ _ _ _ _ _ (.label _ _ j lh' H hf hf') hLI
        (by simp [lengthRec_append, lengthRec_cons, sizeOfInstruction_label] at Hlen; omega)
      have hc : constList vs0 = true := by simpa using hbef
      simpa using goal_lift (rest := aft) hc (goal_label (n := n) (es0 := es0) g)

end IrisWasm
