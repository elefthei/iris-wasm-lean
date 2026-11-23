/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Examples.Stack.StackCommon
import IrisWasm.Examples.Stack.IsEmpty
import IrisWasm.Logrel.IrisFundamental
import IrisWasm.Rules.Proofmode

/-! Port of `theories/iris/examples/stack/function/is_full.v`. -/

namespace IrisWasm.Examples.Stack

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm

/-! ### Code -/

/-- `is_full: [i32] -> [i32]`, locals declared: `[]`. Given a stack pointer, determine if the
stack is full, by reading the stack top pointer and taking its remainder modulo 65536 (65532 for
a full stack). Returns 1 if the stack is full, 0 otherwise. -/
@[rocq_alias iriswasm.is_full_op]
def isFullOp : List BasicInstruction :=
  [ i32const 1,
    i32const 0,
    .getLocal 0,
    .load .i32 none ⟨0, 0, 0⟩,
    i32const 65536,
    .binop .i32 (.i (.rem .u)),
    i32const 65532,
    .relop .i32 (.i .eq),
    .select ]

@[rocq_alias iriswasm.is_full]
def isFull : List BasicInstruction :=
  validateStack 0 ++ validateStackBound 0 ++ isFullOp

section stack
variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF]

private theorem wp_wand_s {s : Stuckness} {E : CoPset} {e : Expr} {Φ Ψ : Val → IProp GF} :
    WP e @ s ; E {{ Φ }} ⊢ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s ; E {{ Ψ }} :=
  IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)

private theorem wp_val_app2 {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF} (c1 c2 : Value)
    (es : Expr) :
    iprop((□ (¬ Φ .trapV)) ∗
      WP es @ Stuckness.NotStuck ; E {{ v, Φ (valCombine (.immV [c1, c2]) v) }})
      ⊢ WP ([.basic (.const c1), .basic (.const c2)] ++ es) @ s ; E {{ v, Φ v }} :=
  wp_val_app' s E Φ [c1, c2] es

private theorem rem_uint (t : Nat) :
    appBinop (.i (.rem .u)) (valueOfUint t) (.int32 (Wasm.Int.intOfZ 65536)) =
      some (valueOfUint (t % 2 ^ 32 % 65536)) := by
  simp only [appBinop, appBinopI, valueOfUint, Wasm.Int.iremU, Wasm.Int.intOfZ, Wasm.Int.repr,
    BitVec.ofInt_natCast]
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))]
  simp only [Option.map_some, Option.some.injEq, Value.int32.injEq]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_umod]
  omega

private theorem eq_65532 (r : Nat) (h : r < 65536) :
    appRelop (.i .eq) (valueOfUint r) (.int32 (Wasm.Int.intOfZ 65532)) = decide (r = 65532) := by
  simp only [appRelop, appRelopI, valueOfUint, Wasm.Int.ieq, Wasm.Int.intOfZ, Wasm.Int.repr,
    BitVec.ofInt_natCast]
  by_cases hr : r = 65532
  · subst hr; rfl
  · simp only [hr, decide_false, beq_eq_false_iff_ne]
    intro he; have := congrArg BitVec.toNat he; simp at this; omega

/-! ### Specs -/

@[rocq_alias iriswasm.spec_is_full_op]
theorem spec_is_full_op (f0 : Frame) (n v : Nat) (s : List I32) (E : CoPset) :
    ⊢ ({{{{ ⌜f0.inst.memory[0]? = some n⌝ ∗ ⌜f0.locs[0]? = some (valueOfUint v)⌝ ∗
          ↪[frame] f0 ∗ isStack v s n }}}}
        (toEList isFullOp) @ E
      {{{{ w, ∃ k : _root_.Int, ⌜w = .immV [valueOfInt k]⌝ ∗ isStack v s n ∗
          ⌜(k = 1 ∧ s.length = two14 - 1) ∨ (k = 0 ∧ s.length < two14 - 1)⌝ ∗
          ↪[frame] f0 }}}} : IProp GF) := by
  iintro !> %Φ ⟨%Hinst, %Hlocv, Hf, Hstack⟩ HΦ
  let c1 : Value := .int32 (Wasm.Int.intOfZ 1)
  let c0 : Value := .int32 (Wasm.Int.intOfZ 0)
  icases stack_pure v s n $$ Hstack with ⟨%Hdiv, %Hvb, %Hlens, Hstack⟩
  simp only [isFullOp, toEList, List.map, i32const]
  take_drop_app_rewrite 3
  iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV [c1, c0, valueOfUint v]⌝ ∗
    ↪[frame] f0))
  isplitr
  · iintro ⟨%h, -⟩; cases h
  isplitl [Hf]
  · take_drop_app_rewrite 2
    iapply wp_val_app2
    isplitr
    · iintro !> ⟨%h, -⟩; cases h
    iapply wp_get_local _ _ _ _ (fun w => iprop(⌜valCombine (.immV [c1, c0]) w =
      .immV [c1, c0, valueOfUint v]⌝)) _ Hlocv $$ [] Hf
    inext; ipureintro; rfl
  iintro %w ⟨%hw, Hf⟩
  subst hw
  take_drop_app_rewrite 4
  iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV [c1, c0,
    valueOfUint (v + s.length * 4)]⌝ ∗ isStack v s n ∗ ↪[frame] f0))
  isplitr
  · iintro ⟨%h, -⟩; cases h
  isplitl [Hf Hstack]
  · take_drop_app_rewrite 2
    iapply wp_val_app2
    isplitr
    · iintro !> ⟨%h, -⟩; cases h
    iapply wp_wand_s $$ [Hf Hstack]
    · iapply stack_load_0 v s n f0 E $$ %Hinst Hstack Hf
    iintro %w ⟨%hw, Hstack, Hf⟩
    subst hw
    iframe; ipureintro; rfl
  iintro %w ⟨%hw, Hstack, Hf⟩
  subst hw
  have hmod : (v + s.length * 4) % 2 ^ 32 % 65536 = s.length * 4 := by
    obtain ⟨q, hq⟩ := Hdiv
    unfold two16 at hq; unfold ffff0000 at Hvb; unfold two14 at Hlens
    subst hq; omega
  take_drop_app_rewrite 5
  iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV [c1, c0,
    valueOfUint (s.length * 4)]⌝ ∗ ↪[frame] f0))
  isplitr
  · iintro ⟨%h, -⟩; cases h
  isplitl [Hf]
  · take_drop_app_rewrite 2
    iapply wp_val_app2
    isplitr
    · iintro !> ⟨%h, -⟩; cases h
    iapply wp_binop (Φ := fun w => iprop(⌜valCombine (.immV [c1, c0]) w =
      .immV [c1, c0, valueOfUint (s.length * 4)]⌝))
      rfl rfl .i32Agree (rem_uint (v + s.length * 4)) $$ Hf
    inext; ipureintro; rw [hmod]; rfl
  iintro %w ⟨%hw, Hf⟩
  subst hw
  have hlt : s.length * 4 < 65536 := by unfold two14 at Hlens; omega
  take_drop_app_rewrite 5
  iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV [c1, c0,
    .int32 (wasmBool (decide (s.length * 4 = 65532)))]⌝ ∗ ↪[frame] f0))
  isplitr
  · iintro ⟨%h, -⟩; cases h
  isplitl [Hf]
  · take_drop_app_rewrite 2
    iapply wp_val_app2
    isplitr
    · iintro !> ⟨%h, -⟩; cases h
    iapply wp_relop (Φ := fun w => iprop(⌜valCombine (.immV [c1, c0]) w =
      .immV [c1, c0, .int32 (wasmBool (decide (s.length * 4 = 65532)))]⌝))
      rfl rfl .i32Agree (eq_65532 _ hlt) $$ Hf
    inext; ipureintro; rfl
  iintro %w ⟨%hw, Hf⟩
  subst hw
  simp only [ofVal, vToEList, List.map, List.cons_append, List.nil_append]
  by_cases hb : s.length * 4 = 65532
  · iapply wp_wand_s $$ [Hf]
    · iapply wp_select_true (Φ := fun w => iprop(⌜w = .immV [valueOfInt 1]⌝))
        (by simp [hb, wasmBool]) $$ Hf
      inext; ipureintro; rfl
    iintro %w ⟨%hw, Hf⟩
    iapply HΦ
    iexists 1
    iframe
    ipureintro
    exact ⟨hw, .inl ⟨rfl, by unfold two14; omega⟩⟩
  · iapply wp_wand_s $$ [Hf]
    · iapply wp_select_false (Φ := fun w => iprop(⌜w = .immV [valueOfInt 0]⌝))
        (by simp [hb, wasmBool]) $$ Hf
      inext; ipureintro; rfl
    iintro %w ⟨%hw, Hf⟩
    iapply HΦ
    iexists 0
    iframe
    ipureintro
    exact ⟨hw, .inr ⟨rfl, by unfold two14 at Hlens ⊢; omega⟩⟩

@[rocq_alias iriswasm.spec_is_full]
theorem spec_is_full (f0 : Frame) (n v : Nat) (s : List I32) (E : CoPset) :
    ⊢ ({{{{ ⌜f0.inst.memory[0]? = some n⌝ ∗ ⌜f0.locs[0]? = some (valueOfUint v)⌝ ∗
          ↪[frame] f0 ∗ isStack v s n }}}}
        (toEList isFull) @ E
      {{{{ w, ∃ k : _root_.Int, ⌜w = .immV [valueOfInt k]⌝ ∗ isStack v s n ∗
          ⌜(k = 1 ∧ s.length = two14 - 1) ∨ (k = 0 ∧ s.length < two14 - 1)⌝ ∗
          ↪[frame] f0 }}}} : IProp GF) := by
  iintro !> %Φ ⟨%Hinst, %Hlocv, Hf, Hstack⟩ HΦ
  rw [show toEList isFull = toEList (validateStack 0) ++
    (toEList (validateStackBound 0) ++ toEList isFullOp) by
      simp [isFull, toEList]]
  iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV []⌝ ∗ isStack v s n ∗ ↪[frame] f0))
  isplitr
  · iintro ⟨%h, -⟩; cases h
  isplitl [Hstack Hf]
  · iapply is_stack_valid v s n f0 E 0
    iframe; ipureintro; exact Hlocv
  iintro %w ⟨%hw, Hstack, Hf⟩
  subst hw
  simp only [ofVal, vToEList, List.map_nil, List.nil_append]
  iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV []⌝ ∗ isStack v s n ∗ ↪[frame] f0))
  isplitr
  · iintro ⟨%h, -⟩; cases h
  isplitl [Hstack Hf]
  · iapply is_stack_bound_valid v s n f0 E 0
    iframe; ipureintro; exact ⟨Hinst, Hlocv⟩
  iintro %w ⟨%hw, Hstack, Hf⟩
  subst hw
  simp only [ofVal, vToEList, List.map_nil, List.nil_append]
  iapply spec_is_full_op f0 n v s E $$ [Hf Hstack] HΦ
  iframe; ipureintro; exact ⟨Hinst, Hlocv⟩

/-! ### Validity -/

section valid
variable [LogrelNaInvs GF]
attribute [local instance] WasmG.invGS

#rocq_ignore iriswasm.valid_is_full "The stack invariant owns memory32 metadata"
theorem valid_is_full (m t : Nat) (funcs : List Funcaddr) :
    let i0 : Instance :=
      { types := [.tf [] [.i32], .tf [.i32] [.i32], .tf [.i32, .i32] []], funcs := funcs,
        tab := [t], memory := [m], globs := [] };
    ⊢ (NonAtomicInvariant.inv (LogrelNaInvs.logrelNais (GF := GF)) stkN
        (stackModuleInv (fun a b => isStack a b m) (fun n => m ↦[wmlength] (.i32, n))) -∗
      interpClosureNative i0 [.i32] [.i32] [] (toEList isFull) [] : IProp GF) := by
  intro i0
  refine stack_valid_unary m i0 rfl [] isFullOp ?_
  intro v stk
  iintro !> %Φ ⟨Hs, Hf⟩ HΦ
  iapply spec_is_full_op (⟨[valueOfUint v] ++ nZeros [], i0⟩ : Frame) m v stk ⊤ $$ [Hs Hf]
  · iframe; ipureintro; exact ⟨rfl, rfl⟩
  iintro %w ⟨%k, %hw, Hs, -, Hf⟩
  iapply HΦ
  subst hw
  iframe
  iapply interpVal_i32 (valueOfInt k) ⟨_, rfl⟩

end valid

end stack

end IrisWasm.Examples.Stack
