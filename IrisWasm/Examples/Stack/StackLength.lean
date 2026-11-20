/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Examples.Stack.StackCommon
import IrisWasm.Logrel.IrisFundamental
import IrisWasm.Rules.Proofmode

/-! Port of `theories/iris/examples/stack/function/stack_length.v`. -/

namespace IrisWasm.Examples.Stack

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm

/-! ### Code -/

/-- `length_stack: [i32] -> [i32]`, locals declared: `[]`. Given a stack pointer, find the length
of the stack by subtracting the stack pointer from the stack top pointer. Returns the length of
the stack as a u32. -/
@[rocq_alias iriswasm.length_stack_op]
def lengthStackOp : List BasicInstruction :=
  [ .getLocal 0,
    .load .i32 none 0 0,
    .getLocal 0,
    .binop .i32 (.i .sub),
    i32const 4,
    .binop .i32 (.i (.div .u)) ]

@[rocq_alias iriswasm.length_stack]
def lengthStack : List BasicInstruction :=
  validateStack 0 ++ validateStackBound 0 ++ lengthStackOp

section stack
variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF]

private theorem wp_wand_s {s : Stuckness} {E : CoPset} {e : Expr} {Φ Ψ : Val → IProp GF} :
    WP e @ s ; E {{ Φ }} ⊢ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s ; E {{ Ψ }} :=
  IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)

private theorem wp_val_app1 {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF} (c : Value)
    (es : Expr) :
    iprop((□ (¬ Φ .trapV)) ∗
      WP es @ Stuckness.NotStuck ; E {{ v, Φ (valCombine (.immV [c]) v) }})
      ⊢ WP ([.basic (.const c)] ++ es) @ s ; E {{ v, Φ v }} :=
  wp_val_app' s E Φ [c] es

private theorem sub_uint (a b : Nat) :
    appBinop (.i .sub) (valueOfUint (a + b)) (valueOfUint a) = some (valueOfUint b) := by
  simp only [appBinop, appBinopI, valueOfUint, Wasm.Int.isub, Wasm.Int.intOfZ, Wasm.Int.repr,
    BitVec.ofInt_natCast, Option.map_some, Option.some.injEq, Value.int32.injEq]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_sub]
  omega

private theorem div4_uint (b : Nat) (h : b * 4 < 2 ^ 32) :
    appBinop (.i (.div .u)) (valueOfUint (b * 4)) (.int32 (Wasm.Int.intOfZ 4)) =
      some (valueOfUint b) := by
  simp only [appBinop, appBinopI, valueOfUint, Wasm.Int.idivU, Wasm.Int.intOfZ, Wasm.Int.repr,
    BitVec.ofInt_natCast]
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))]
  simp only [Option.map_some, Option.some.injEq, Value.int32.injEq]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_udiv]
  omega

/-! ### Specs -/

@[rocq_alias iriswasm.spec_stack_length_op]
theorem spec_stack_length_op (f0 : Frame) (n v : Nat) (s : List I32) (E : CoPset) (len : Nat) :
    ⊢ ({{{{ ⌜f0.inst.memory[0]? = some n⌝ ∗ ⌜f0.locs[0]? = some (valueOfUint v)⌝ ∗
          ⌜s.length = len⌝ ∗ ↪[frame] f0 ∗ isStack v s n }}}}
        (toEList lengthStackOp) @ E
      {{{{ w, ⌜w = .immV [valueOfUint len]⌝ ∗ isStack v s n ∗ ↪[frame] f0 }}}} : IProp GF) := by
  iintro !> %Φ ⟨%Hinst, %Hlocv, %Hlen, Hf, Hstack⟩ HΦ
  subst Hlen
  icases stack_pure v s n $$ Hstack with ⟨%Hdiv, %Hvb, %Hlens, Hstack⟩
  simp only [lengthStackOp, toEList, List.map, i32const]
  take_drop_app_rewrite 1
  iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV [valueOfUint v]⌝ ∗ ↪[frame] f0))
  isplitr
  · iintro ⟨%h, -⟩; cases h
  isplitl [Hf]
  · iapply wp_get_local _ _ _ _ (fun w => iprop(⌜w = .immV [valueOfUint v]⌝)) _ Hlocv $$ [] Hf
    inext; ipureintro; rfl
  iintro %w ⟨%hw, Hf⟩
  subst hw
  take_drop_app_rewrite 2
  iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV [valueOfUint (v + s.length * 4)]⌝ ∗
    isStack v s n ∗ ↪[frame] f0))
  isplitr
  · iintro ⟨%h, -⟩; cases h
  isplitl [Hf Hstack]
  · iapply stack_load_0 v s n f0 E $$ %Hinst Hstack Hf
  iintro %w ⟨%hw, Hstack, Hf⟩
  subst hw
  take_drop_app_rewrite 2
  iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV [valueOfUint (v + s.length * 4),
    valueOfUint v]⌝ ∗ ↪[frame] f0))
  isplitr
  · iintro ⟨%h, -⟩; cases h
  isplitl [Hf]
  · take_drop_app_rewrite 1
    iapply wp_val_app1
    isplitr
    · iintro !> ⟨%h, -⟩; cases h
    iapply wp_get_local _ _ _ _ (fun w => iprop(⌜valCombine (.immV [valueOfUint (v + s.length * 4)])
      w = .immV [valueOfUint (v + s.length * 4), valueOfUint v]⌝)) _ Hlocv $$ [] Hf
    inext; ipureintro; rfl
  iintro %w ⟨%hw, Hf⟩
  subst hw
  take_drop_app_rewrite 3
  iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV [valueOfUint (s.length * 4)]⌝ ∗ ↪[frame] f0))
  isplitr
  · iintro ⟨%h, -⟩; cases h
  isplitl [Hf]
  · iapply wp_binop (sub_uint v (s.length * 4)) $$ Hf
    inext; ipureintro; rfl
  iintro %w ⟨%hw, Hf⟩
  subst hw
  simp only [ofVal, vToEList, List.map, List.cons_append, List.nil_append]
  iapply wp_wand_s $$ [Hf]
  · iapply wp_binop (Φ := fun w => iprop(⌜w = .immV [valueOfUint s.length]⌝))
      (div4_uint _ (by unfold two14 at Hlens; omega)) $$ Hf
    inext; ipureintro; rfl
  iintro %w ⟨%hw, Hf⟩
  iapply HΦ
  iframe
  ipureintro; exact hw

@[rocq_alias iriswasm.spec_stack_length]
theorem spec_stack_length (f0 : Frame) (n v : Nat) (s : List I32) (E : CoPset) (len : Nat) :
    ⊢ ({{{{ ⌜f0.inst.memory[0]? = some n⌝ ∗ ⌜f0.locs[0]? = some (valueOfUint v)⌝ ∗
          ⌜s.length = len⌝ ∗ ↪[frame] f0 ∗ isStack v s n }}}}
        (toEList lengthStack) @ E
      {{{{ w, ⌜w = .immV [valueOfUint len]⌝ ∗ isStack v s n ∗ ↪[frame] f0 }}}} : IProp GF) := by
  iintro !> %Φ ⟨%Hinst, %Hlocv, %Hlen, Hf, Hstack⟩ HΦ
  rw [show toEList lengthStack = toEList (validateStack 0) ++
    (toEList (validateStackBound 0) ++ toEList lengthStackOp) by
      simp [lengthStack, toEList]]
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
  iapply spec_stack_length_op f0 n v s E len $$ [Hf Hstack] HΦ
  iframe; ipureintro; exact ⟨Hinst, Hlocv, Hlen⟩

end stack

end IrisWasm.Examples.Stack
