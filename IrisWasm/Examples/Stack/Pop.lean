/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Examples.Stack.StackCommon
import IrisWasm.Examples.Stack.IsEmpty
import IrisWasm.Logrel.IrisFundamental
import IrisWasm.Rules.Proofmode

/-! Port of `theories/iris/examples/stack/function/pop.v`. -/

namespace IrisWasm.Examples.Stack

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm

/-! ### Code -/

/-- `pop: [i32] -> [i32]`, locals declared: `[i32]`. Given a stack pointer, pop the top i32 value
from the stack; traps if the stack is empty. Local 1 stores the new address of the stack top
pointer. -/
@[rocq_alias iriswasm.pop_op]
def popOp : List BasicInstruction :=
  isEmptyOp ++
  [ .if_ (.result none) [.unreachable] [],
    .getLocal 0,
    .load .i32 none ⟨0, 0, 0⟩,
    .teeLocal 1,
    .load .i32 none ⟨0, 0, 0⟩,
    .getLocal 0,
    .getLocal 1,
    i32const 4,
    .binop .i32 (.i .sub),
    .store .i32 none ⟨0, 0, 0⟩ ]

@[rocq_alias iriswasm.pop]
def pop : List BasicInstruction :=
  validateStack 0 ++ validateStackBound 0 ++ popOp

section stack
variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF]

private theorem wp_wand_s {s : Stuckness} {E : CoPset} {e : Expr} {Φ Ψ : Val → IProp GF} :
    WP e @ s ; E {{ Φ }} ⊢ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s ; E {{ Ψ }} :=
  IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)

private theorem wp_seq_imm {E : CoPset} {Φ : Val → IProp GF} {es1 es2 : Expr} (vs : List Value)
    (P : IProp GF) :
    ⊢ (WP es1 @ E {{ w, ⌜w = .immV vs⌝ ∗ P }} -∗
      (P -∗ WP (vToEList vs ++ es2) @ E {{ w, Φ w }}) -∗
      WP (es1 ++ es2) @ E {{ w, Φ w }} : IProp GF) := by
  iintro H1 H2
  iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV vs⌝ ∗ P))
  isplitr
  · iintro ⟨%h, -⟩; cases h
  isplitl [H1]
  · iexact H1
  iintro %w ⟨%hw, HP⟩
  subst hw
  rw [show ofVal (Val.immV vs) = vToEList vs from rfl]
  iapply H2 $$ HP

/-- A constant followed by an expression returning immediate values. -/
private theorem wp_val_cons_imm {E : CoPset} {es : Expr} (x : Value) (ws : List Value)
    (P : IProp GF) :
    WP es @ E {{ w, ⌜w = .immV ws⌝ ∗ P }} ⊢
      WP (.basic (.const x) :: es) @ E {{ w, ⌜w = .immV (x :: ws)⌝ ∗ P }} := by
  iintro H
  rw [show (.basic (.const x) :: es : Expr) = vToEList [x] ++ es from rfl]
  iapply wp_val_app' _ _ (fun w => iprop(⌜w = .immV (x :: ws)⌝ ∗ P)) [x]
  isplitr
  · imodintro; iintro ⟨%h, -⟩; cases h
  iapply wp_wand_s $$ H
  iintro %w ⟨%hw, HP⟩
  subst hw
  iframe; ipureintro; rfl

private theorem sub4_uint (b : Nat) :
    appBinop (.i .sub) (valueOfUint (b + 4)) (.int32 (Wasm.Int.intOfZ 4)) =
      some (valueOfUint b) := by
  simp only [appBinop, appBinopI, valueOfUint, Wasm.Int.isub, Wasm.Int.intOfZ, Wasm.Int.repr,
    BitVec.ofInt_natCast, Option.map_some, Option.some.injEq, Value.int32.injEq]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_sub]
  omega

/-- An `i32` address below `2^32` survives the `i32` round trip. -/
private theorem addr_eq (a : Nat) (h : a < 4294967296) :
    Wasm.Int.nOfUint (Wasm.Int.intOfZ (w := 32) (a : _root_.Int)) + 0 = a := by
  simp [Wasm.Int.nOfUint, Wasm.Int.intOfZ, Wasm.Int.repr, BitVec.ofInt_natCast]
  omega

/-- Storing the decremented stack top pointer turns `isStack v (a :: s)` into `isStack v s`:
the cell of `a` joins the free bytes. -/
private theorem pop_store (f : Frame) (v n : Nat) (a : I32) (s : List I32) (E : CoPset)
    (hmem : f.inst.memory[0]? = some n) :
    ⊢ (isStack v (a :: s) n -∗ ↪[frame] f -∗
      WP ([.basic (.const (valueOfUint v)), .basic (.const (valueOfUint (v + s.length * 4))),
          .basic (.store .i32 none ⟨0, 0, 0⟩)] : Expr) @ E
        {{ w, ⌜w = .immV []⌝ ∗ isStack v s n ∗ ↪[frame] f }} : IProp GF) := by
  simp only [isStack, List.length_cons]
  iintro ⟨%hdiv, %hvb, %hlen, Hv, ⟨Ha, Hl⟩, ⟨%bs, %hbs, Hb⟩⟩ Hf
  have e := addr_eq v (by simp [ffff0000] at hvb; omega)
  have hser : (serialiseI32 a).length = 4 := length_encodeInt ..
  rw [show v + (s.length + 1) * 4 - 4 * 0 = v + s.length * 4 + 4 by omega,
    show v + (s.length + 1) * 4 + 4 = v + s.length * 4 + 4 + 4 by omega]
  simp only [show ∀ k, v + (s.length + 1) * 4 - 4 * (k + 1) = v + s.length * 4 - 4 * k
    from fun k => by omega]
  ihave Hv := (i32_wms n v _).1 $$ Hv
  ihave Hv := points_to_wms_eq n _ v n _ _ rfl rfl e.symm $$ Hv
  rw [show valueOfUint v = .int32 (Wasm.Int.intOfZ (v : _root_.Int)) from rfl]
  iapply wp_wand_s (Φ := fun w => iprop((⌜w = .immV []⌝ ∗
      n ↦[wms][ Wasm.Int.nOfUint (Wasm.Int.intOfZ (w := 32) (v : _root_.Int)) + 0 ]
        bits (valueOfUint (v + s.length * 4))) ∗ ↪[frame] f)) $$ [Hv Hf]
  · iapply wp_store (x := 0) (fun w => iprop(⌜w = .immV []⌝)) _ _ .i32
      (valueOfUint (v + s.length * 4))
      (serialiseI32 (Wasm.Int.repr ((v + (s.length + 1) * 4 : Nat) : _root_.Int))) 0 0
      (.i32 (Wasm.Int.intOfZ (v : _root_.Int))) n f rfl (length_encodeInt ..) hmem
    isplitr
    · inext; ipureintro; rfl
    isplitl [Hf]
    · iexact Hf
    · iexact Hv
  iintro %w ⟨⟨%hw, Hv⟩, Hf⟩
  rw [show bits (valueOfUint (v + s.length * 4)) =
    serialiseI32 (Wasm.Int.repr ((v + s.length * 4 : Nat) : _root_.Int)) from rfl]
  ihave Hv := points_to_wms_eq n _ _ n _ v rfl rfl e $$ Hv
  ihave Hv := (i32_wms n v _).2 $$ Hv
  ihave Ha := (i32_wms n _ a).1 $$ Ha
  isplitr
  · ipureintro; exact hw
  isplitl [Hv Ha Hl Hb]
  · isplitr
    · ipureintro; exact hdiv
    isplitr
    · ipureintro; exact hvb
    isplitr
    · ipureintro; omega
    isplitl [Hv]
    · iexact Hv
    isplitl [Hl]
    · iexact Hl
    iexists serialiseI32 a ++ bs
    isplitr
    · ipureintro; simp only [List.length_append, hser, hbs]; unfold two16 two14 at *; omega
    simp only [memBlockAtPos]
    iapply BigSepL.bigSepL_append.2
    isplitl [Ha]
    · iexact Ha
    · rw [hser]
      iapply BigSepL.bigSepL_mono_of_forall $$ Hb
      intro k x
      rw [show v + s.length * 4 + 4 + (k + 4) = v + s.length * 4 + 4 + 4 + k by omega]
  · iexact Hf

/-! ### Specs -/

@[rocq_alias iriswasm.spec_pop_op]
theorem spec_pop_op (f0 : Frame) (n v : Nat) (a : I32) (s : List I32) (E : CoPset) :
    ⊢ ({{{{ ⌜f0.inst.memory[0]? = some n⌝ ∗ ⌜f0.locs[0]? = some (valueOfUint v)⌝ ∗
          ⌜f0.locs.length ≥ 2⌝ ∗ isStack v (a :: s) n ∗ ↪[frame] f0 }}}}
        (toEList popOp) @ E
      {{{{ w, ⌜w = .immV [.int32 a]⌝ ∗ isStack v s n ∗
          ∃ f1, ↪[frame] f1 ∗ ⌜f0.inst = f1.inst⌝ }}}} : IProp GF) := by
  iintro !> %Φ ⟨%Hinst, %Hlocv, %Hlocs, Hstack, Hf⟩ HΦ
  icases stack_pure v (a :: s) n $$ Hstack with ⟨%Hdiv, %Hvb, %Hlens, Hstack⟩
  simp only [popOp, toEList, List.map_append, List.map, i32const]
  rw [show List.map AdministrativeInstruction.basic isEmptyOp = toEList isEmptyOp from rfl]
  iapply wp_seq_imm [valueOfInt 0] iprop(isStack v (a :: s) n ∗ ↪[frame] f0) $$ [Hstack Hf]
  · iapply spec_is_empty_op f0 n v (a :: s) E $$ [Hf Hstack]
    · iframe; ipureintro; exact ⟨Hinst, Hlocv⟩
    · iintro %w ⟨%k, %hw, Hstack, %hk, Hf⟩
      iframe; ipureintro
      rcases hk with ⟨_, h⟩ | ⟨rfl, _⟩
      · cases h
      · exact hw
  iintro ⟨Hstack, Hf⟩
  take_drop_app_rewrite 2
  iapply wp_seq_imm [] iprop(↪[frame] f0) $$ [Hf]
  · rw [show valueOfInt 0 = .int32 (Wasm.Int.intOfZ 0) from rfl]
    iapply wp_if_false (c := Wasm.Int.intOfZ 0) (by rfl) $$ Hf
    iintro !> Hf
    rw [show ([.basic (.block (.result none) [])] : Expr) = [] ++ [.basic (.block (.result none) [])]
      from rfl]
    iapply wp_block (bt := .result none) (vs := []) rfl rfl rfl rfl rfl $$ Hf
    iintro !> Hf
    iapply wp_label_value (Φ := fun w => iprop(⌜w = .immV []⌝)) (by rfl) $$ Hf
    inext; ipureintro; rfl
  iintro Hf
  take_drop_app_rewrite 1
  iapply wp_seq_imm [valueOfUint v] iprop(↪[frame] f0) $$ [Hf]
  · iapply wp_get_local _ _ _ _ (fun w => iprop(⌜w = .immV [valueOfUint v]⌝)) _ Hlocv $$ [] Hf
    inext; ipureintro; rfl
  iintro Hf
  take_drop_app_rewrite 2
  iapply wp_seq_imm [valueOfUint (v + (a :: s).length * 4)]
    iprop(isStack v (a :: s) n ∗ ↪[frame] f0) $$ [Hstack Hf]
  · iapply stack_load_0 v (a :: s) n f0 E $$ %Hinst Hstack Hf
  iintro ⟨Hstack, Hf⟩
  take_drop_app_rewrite 2
  iapply wp_seq_imm [valueOfUint (v + (a :: s).length * 4)]
    iprop(↪[frame] (⟨f0.locs.set 1 (valueOfUint (v + (a :: s).length * 4)), f0.inst⟩ : Frame))
    $$ [Hf]
  · iapply wp_tee_local $$ Hf
    iintro !> Hf
    iapply wp_val_cons_imm
    iapply wp_set_local _ _ _ 1 (fun w => iprop(⌜w = .immV []⌝)) _ (by omega) $$ [] Hf
    inext; ipureintro; rfl
  iintro Hf
  generalize hf1 : (⟨f0.locs.set 1 (valueOfUint (v + (a :: s).length * 4)), f0.inst⟩ : Frame) = f1
  have hi1 : f1.inst.memory[0]? = some n := by subst hf1; exact Hinst
  have hl0 : f1.locs[0]? = some (valueOfUint v) := by
    subst hf1; simpa [List.getElem?_set] using Hlocv
  have hl1 : f1.locs[1]? = some (valueOfUint (v + (a :: s).length * 4)) := by
    subst hf1; simp [List.getElem?_set]; omega
  take_drop_app_rewrite 2
  iapply wp_seq_imm [.int32 a] iprop(isStack v (a :: s) n ∗ ↪[frame] f1) $$ [Hstack Hf]
  · iapply stack_load_j_alt v (a :: s) n f1 E 0 (v + (a :: s).length * 4) a
      $$ %hi1 %(by omega) %rfl %⟨Nat.le_refl _, by simp⟩ Hstack Hf
  iintro ⟨Hstack, Hf⟩
  take_drop_app_rewrite 2
  iapply wp_seq_imm [.int32 a, valueOfUint v] iprop(↪[frame] f1) $$ [Hf]
  · iapply wp_val_cons_imm
    iapply wp_get_local _ _ _ _ (fun w => iprop(⌜w = .immV [valueOfUint v]⌝)) _ hl0 $$ [] Hf
    inext; ipureintro; rfl
  iintro Hf
  take_drop_app_rewrite 3
  iapply wp_seq_imm [.int32 a, valueOfUint v, valueOfUint (v + (a :: s).length * 4)]
    iprop(↪[frame] f1) $$ [Hf]
  · iapply wp_val_cons_imm
    iapply wp_val_cons_imm
    iapply wp_get_local _ _ _ _
      (fun w => iprop(⌜w = .immV [valueOfUint (v + (a :: s).length * 4)]⌝)) _ hl1 $$ [] Hf
    inext; ipureintro; rfl
  iintro Hf
  have hb := sub4_uint (v + s.length * 4)
  rw [show v + s.length * 4 + 4 = v + (a :: s).length * 4 by simp; omega] at hb
  take_drop_app_rewrite 5
  iapply wp_seq_imm [.int32 a, valueOfUint v, valueOfUint (v + s.length * 4)]
    iprop(↪[frame] f1) $$ [Hf]
  · iapply wp_val_cons_imm
    iapply wp_val_cons_imm
    iapply wp_binop (t := .i32) (Φ := fun w => iprop(⌜w = .immV [valueOfUint (v + s.length * 4)]⌝))
      rfl rfl .i32Agree hb $$ Hf
    inext; ipureintro; rfl
  iintro Hf
  simp only [vToEList, List.map, List.cons_append, List.nil_append]
  iapply wp_wand_s (Φ := fun w => iprop(⌜w = .immV [.int32 a]⌝ ∗ isStack v s n ∗ ↪[frame] f1))
    $$ [Hstack Hf]
  · iapply wp_val_cons_imm
    iapply pop_store f1 v n a s E hi1 $$ Hstack Hf
  iintro %w ⟨%hw, Hstack, Hf⟩
  iapply HΦ
  iframe
  ipureintro; exact ⟨hw, by subst hf1; rfl⟩

@[rocq_alias iriswasm.spec_pop]
theorem spec_pop (f0 : Frame) (n v : Nat) (a : I32) (s : List I32) (E : CoPset) :
    ⊢ ({{{{ ⌜f0.inst.memory[0]? = some n⌝ ∗ ⌜f0.locs[0]? = some (valueOfUint v)⌝ ∗
          ⌜f0.locs.length ≥ 2⌝ ∗ isStack v (a :: s) n ∗ ↪[frame] f0 }}}}
        (toEList pop) @ E
      {{{{ w, ⌜w = .immV [.int32 a]⌝ ∗ isStack v s n ∗
          ∃ f1, ↪[frame] f1 ∗ ⌜f0.inst = f1.inst⌝ }}}} : IProp GF) := by
  iintro !> %Φ ⟨%Hinst, %Hlocv, %Hlocs, Hstack, Hf⟩ HΦ
  rw [show toEList pop = toEList (validateStack 0) ++
    (toEList (validateStackBound 0) ++ toEList popOp) by
      simp [pop, toEList]]
  iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV []⌝ ∗ isStack v (a :: s) n ∗ ↪[frame] f0))
  isplitr
  · iintro ⟨%h, -⟩; cases h
  isplitl [Hstack Hf]
  · iapply is_stack_valid v (a :: s) n f0 E 0
    iframe; ipureintro; exact Hlocv
  iintro %w ⟨%hw, Hstack, Hf⟩
  subst hw
  simp only [ofVal, vToEList, List.map_nil, List.nil_append]
  iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV []⌝ ∗ isStack v (a :: s) n ∗ ↪[frame] f0))
  isplitr
  · iintro ⟨%h, -⟩; cases h
  isplitl [Hstack Hf]
  · iapply is_stack_bound_valid v (a :: s) n f0 E 0
    iframe; ipureintro; exact ⟨Hinst, Hlocv⟩
  iintro %w ⟨%hw, Hstack, Hf⟩
  subst hw
  simp only [ofVal, vToEList, List.map_nil, List.nil_append]
  iapply spec_pop_op f0 n v a s E $$ [Hf Hstack] HΦ
  iframe; ipureintro; exact ⟨Hinst, Hlocv, Hlocs⟩

/-! ### Validity -/

section valid
variable [LogrelNaInvs GF]
attribute [local instance] WasmG.invGS

#rocq_ignore iriswasm.valid_pop "The stack invariant owns memory32 metadata"
theorem valid_pop (m t : Nat) (funcs : List Funcaddr) :
    let i0 : Instance :=
      { types := [.tf [] [.i32], .tf [.i32] [.i32], .tf [.i32, .i32] []], funcs := funcs,
        tab := [t], memory := [m], globs := [] };
    ⊢ (NonAtomicInvariant.inv (LogrelNaInvs.logrelNais (GF := GF)) stkN
        (stackModuleInv (fun a b => isStack a b m) (fun n => m ↦[wmlength] (.i32, n))) -∗
      interpClosureNative i0 [.i32] [.i32] [.i32] (toEList pop) [] : IProp GF) := by
  intro i0
  refine stack_valid_unary m i0 rfl [.i32] popOp ?_
  intro v stk
  iintro !> %Φ ⟨Hs, Hf⟩ HΦ
  cases stk with
  | cons a s =>
    iapply spec_pop_op (⟨[valueOfUint v] ++ nZeros [.i32], i0⟩ : Frame) m v a s ⊤ $$ [Hs Hf]
    · iframe; ipureintro; exact ⟨rfl, rfl, by simp [nZeros]⟩
    iintro %w ⟨%hw, Hs, %f1, Hf, -⟩
    iapply HΦ
    subst hw
    iframe
    iapply interpVal_i32 (.int32 a) ⟨_, rfl⟩
  | nil =>
    rw [show toEList popOp = toEList isEmptyOp ++ toEList (popOp.drop 4) from rfl]
    iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV [valueOfInt 1]⌝ ∗ isStack v [] m ∗
      ↪[frame] (⟨[valueOfUint v] ++ nZeros [.i32], i0⟩ : Frame)))
    isplitr
    · iintro ⟨%h, -⟩; cases h
    isplitl [Hs Hf]
    · iapply spec_is_empty_op (⟨[valueOfUint v] ++ nZeros [.i32], i0⟩ : Frame) m v [] ⊤ $$ [Hs Hf]
      · iframe; ipureintro; exact ⟨rfl, rfl⟩
      iintro %w ⟨%k, %hw, Hs, %hk, Hf⟩
      rcases hk with ⟨rfl, -⟩ | ⟨-, h⟩
      · iframe; ipureintro; exact hw
      · exact absurd rfl h
    iintro %w ⟨%hw, Hs, Hf⟩
    subst hw
    rw [show ofVal (.immV [valueOfInt 1]) ++ toEList (popOp.drop 4) =
      [.basic (.const (.int32 (Wasm.Int.intOfZ 1))),
        .basic (.if_ (.result none) [.unreachable] [])] ++ toEList (popOp.drop 5) from rfl]
    iapply wp_wand_s $$ [Hf]
    · iapply wp_if_unreachable_trap (Wasm.Int.intOfZ 1) (by decide) _ _ $$ Hf
    iintro %w ⟨%hw, Hf⟩
    iapply HΦ
    subst hw
    iframe
    unfold interpVal; ileft; ipureintro; rfl

end valid

end stack

end IrisWasm.Examples.Stack
