/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Examples.Stack.StackCommon
import IrisWasm.Rules.Proofmode

/-! Port of `theories/iris/examples/stack/function/stack_map.v`. -/

namespace IrisWasm.Examples.Stack

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm

/-! ### Code

`map : [i32, i32] -> []`, locals declared `[i32, i32]`. Given a stack pointer (local 0) and a
function reference from table 0 (local 1, of type `[i32] -> [i32]`), applies the function to all
elements of the stack, storing the results back in place. Local 2 holds the loop variable (the top
address already dealt with), local 3 the loop upper bound (the stack top pointer). -/

@[rocq_alias iriswasm.map_initialise]
def mapInitialise : List BasicInstruction :=
  [ .getLocal 0,
    .load .i32 none 0 0,
    .setLocal 3,
    .getLocal 0,
    .setLocal 2 ]

@[rocq_alias iriswasm.map_loop_body]
def mapLoopBody : List BasicInstruction :=
  [ -- Check if the loop is done
    .getLocal 2,
    .getLocal 3,
    .relop .i32 (.i .eq),
    .brIf 1,
    -- Update the loop variable and add a copy to the stack (for storing later)
    .getLocal 2,
    i32const 4,
    .binop .i32 (.i .add),
    .teeLocal 2,
    -- Load the stack element, apply the function and store the result back to the stack
    .getLocal 2,
    .load .i32 none 0 0,
    .getLocal 1,
    .callIndirect 1,
    .store .i32 none 0 0,
    -- Keep the loop alive
    .br 0 ]

@[rocq_alias iriswasm.map_op]
def mapOp : List BasicInstruction :=
  mapInitialise ++ [ .block (.tf [] []) [.loop (.tf [] []) mapLoopBody] ]

@[rocq_alias iriswasm.stack_map]
def stackMap : List BasicInstruction :=
  validateStack 0 ++ validateStackBound 0 ++ mapOp

/-! ### Specs -/

section specs
variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF]

/-- `wp_seq` specialised to a first part returning the values `vs` and the resource `P`. -/
theorem wp_seq_imm {E : CoPset} {Φ : Val → IProp GF} {es1 es2 : Expr} (vs : List Value)
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

theorem wp_wand' {E : CoPset} {e : Expr} {Φ Ψ : Val → IProp GF} :
    ⊢ (WP e @ E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ E {{ Ψ }} : IProp GF) := by
  iintro H1 H2
  iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ H1 H2

theorem wp_value_s {E : CoPset} {e : Expr} {Φ : Val → IProp GF} (v : Val) (h : ofVal v = e) :
    Φ v ⊢ WP e @ E {{ Φ }} :=
  IrisWp.wp_value (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) ⟨h⟩

/-- `wp_val_app'` specialised to immediate results. -/
theorem wp_val_app_imm {E : CoPset} {es : Expr} (vs ws : List Value) (P : IProp GF) :
    WP es @ E {{ w, ⌜w = .immV ws⌝ ∗ P }} ⊢
      WP (vToEList vs ++ es) @ E {{ w, ⌜w = .immV (vs ++ ws)⌝ ∗ P }} := by
  iintro H
  iapply wp_val_app' _ _ (fun w => iprop(⌜w = .immV (vs ++ ws)⌝ ∗ P))
  isplitr
  · imodintro; iintro ⟨%h, -⟩; cases h
  iapply wp_wand' $$ H
  iintro %w ⟨%hw, HP⟩
  subst hw
  iframe; ipureintro; rfl

/-- A constant followed by an expression returning immediate values. -/
theorem wp_val_cons_imm {E : CoPset} {es : Expr} (x : Value) (ws : List Value) (P : IProp GF) :
    WP es @ E {{ w, ⌜w = .immV ws⌝ ∗ P }} ⊢
      WP (.basic (.const x) :: es) @ E {{ w, ⌜w = .immV (x :: ws)⌝ ∗ P }} :=
  wp_val_app_imm [x] ws P

/-- A constant followed by an expression (general postcondition version of `wp_val_app'`). -/
theorem wp_val_cons {E : CoPset} {Φ : Val → IProp GF} {es : Expr} (x : Value) :
    iprop((□ (¬ Φ .trapV)) ∗ WP es @ E {{ v, Φ (valCombine (.immV [x]) v) }}) ⊢
      WP (.basic (.const x) :: es) @ E {{ v, Φ v }} :=
  wp_val_app' _ _ Φ [x] es

theorem wp_ctx_base_cons {E : CoPset} {Φ : Val → IProp GF} (x : Value) (es : Expr) :
    iprop(WP es @ E CTX 0 ; (Lholed.base [.basic (.const x)] []) {{ Φ }}) ⊢
      WP (.basic (.const x) :: es) @ E {{ Φ }} := by
  iintro H
  iapply wp_build_ctx es 0 _ _ _ _ _ ⟨lfilled_of_lfill (by simp [lfill, constList, isConst])⟩ $$ H

theorem relop_eq_valueOfUint_ne {a b : Nat} (hab : a ≠ b) (ha : a < 4294967296)
    (hb : b < 4294967296) : appRelop (.i .eq) (valueOfUint a) (valueOfUint b) = false := by
  simp only [appRelop, appRelopI, valueOfUint, Wasm.Int.ieq, Wasm.Int.intOfZ, Wasm.Int.repr,
    BitVec.ofInt_natCast, beq_eq_false_iff_ne, ne_eq]
  intro h
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at this
  omega

theorem binop_add4_valueOfUint (a : Nat) :
    appBinop (.i .add) (valueOfUint a) (.int32 (Wasm.Int.intOfZ 4)) =
      some (valueOfUint (a + 4)) := by
  simp only [appBinop, appBinopI, valueOfUint, Wasm.Int.iadd, Wasm.Int.intOfZ, Wasm.Int.repr,
    BitVec.ofInt_natCast]
  simp only [Option.map, Option.some.injEq, Value.int32.injEq]
  rw [show ((4 : _root_.Int)) = ((4 : Nat) : _root_.Int) from rfl, BitVec.ofInt_natCast,
    BitVec.ofNat_add]

/-- The first eleven instructions of `map_loop_body` in the continuing case: the loop test fails,
local 2 is advanced to the address of element `j`, and the element and the function index are
pushed for the indirect call. -/
theorem map_loop_body_prefix (f : Frame) (s : List I32) (v n j : Nat) (sv fn : I32) (E : CoPset)
    (Ξ : Val → IProp GF) (hmem : f.inst.memory[0]? = some n)
    (hl1 : f.locs[1]? = some (.int32 fn))
    (hl2 : f.locs[2]? = some (valueOfUint (v + s.length * 4 - 4 * j - 4)))
    (hl3 : f.locs[3]? = some (valueOfUint (v + s.length * 4))) (hlen : f.locs.length ≥ 4)
    (hj : j < s.length) (hsv : s[j]? = some sv) :
    ⊢ (isStack v s n -∗ ↪[frame] f -∗
      (isStack v s n -∗
        ↪[frame] (⟨f.locs.set 2 (valueOfUint (v + s.length * 4 - 4 * j)), f.inst⟩ : Frame) -∗
        WP ([.basic (.const (valueOfUint (v + s.length * 4 - 4 * j))),
          .basic (.const (.int32 sv)), .basic (.const (.int32 fn)), .basic (.callIndirect 1),
          .basic (.store .i32 none 0 0), .basic (.br 0)] : Expr) @ E {{ Ξ }}) -∗
      WP (toEList mapLoopBody : Expr) @ E {{ Ξ }} : IProp GF) := by
  iintro Hs Hf HK
  icases stack_pure v s n $$ Hs with ⟨%hdiv, %hvb, %hlens, Hs⟩
  simp only [two14, ffff0000] at hvb hlens
  isimp only [mapLoopBody, toEList, i32const, List.map_cons, List.map_nil]
  take_drop_app_rewrite 1
  iapply wp_seq_imm [valueOfUint (v + s.length * 4 - 4 * j - 4)] iprop(↪[frame] f) $$ [Hf]
  · iapply wp_get_local _ _ _ _
      (fun w => iprop(⌜w = .immV [valueOfUint (v + s.length * 4 - 4 * j - 4)]⌝)) _ hl2 $$ [] Hf
    inext; ipureintro; rfl
  iintro Hf
  take_drop_app_rewrite 2
  iapply wp_seq_imm [valueOfUint (v + s.length * 4 - 4 * j - 4), valueOfUint (v + s.length * 4)]
    iprop(↪[frame] f) $$ [Hf]
  · iapply wp_val_cons_imm
    iapply wp_get_local _ _ _ _ (fun w => iprop(⌜w = .immV [valueOfUint (v + s.length * 4)]⌝)) _
      hl3 $$ [] Hf
    inext; ipureintro; rfl
  iintro Hf
  take_drop_app_rewrite 3
  iapply wp_seq_imm [.int32 (wasmBool false)] iprop(↪[frame] f) $$ [Hf]
  · iapply wp_relop (op := .i .eq) (b := false) (relop_eq_valueOfUint_ne (by omega) (by omega)
      (by omega)) $$ Hf
    inext; ipureintro; rfl
  iintro Hf
  take_drop_app_rewrite 2
  iapply wp_seq_imm [] iprop(↪[frame] f) $$ [Hf]
  · iapply wp_br_if_false (c := wasmBool false) (Φ := fun w => iprop(⌜w = .immV []⌝)) rfl $$ Hf
    inext; ipureintro; rfl
  iintro Hf
  take_drop_app_rewrite 1
  iapply wp_seq_imm [valueOfUint (v + s.length * 4 - 4 * j - 4)] iprop(↪[frame] f) $$ [Hf]
  · iapply wp_get_local _ _ _ _
      (fun w => iprop(⌜w = .immV [valueOfUint (v + s.length * 4 - 4 * j - 4)]⌝)) _ hl2 $$ [] Hf
    inext; ipureintro; rfl
  iintro Hf
  take_drop_app_rewrite 3
  iapply wp_seq_imm [valueOfUint (v + s.length * 4 - 4 * j)] iprop(↪[frame] f) $$ [Hf]
  · have hb := binop_add4_valueOfUint (v + s.length * 4 - 4 * j - 4)
    rw [show v + s.length * 4 - 4 * j - 4 + 4 = v + s.length * 4 - 4 * j by omega] at hb
    iapply wp_binop (t := .i32) hb $$ Hf
    inext; ipureintro; rfl
  iintro Hf
  take_drop_app_rewrite 2
  iapply wp_seq_imm [valueOfUint (v + s.length * 4 - 4 * j)]
    iprop(↪[frame] (⟨f.locs.set 2 (valueOfUint (v + s.length * 4 - 4 * j)), f.inst⟩ : Frame))
    $$ [Hf]
  · iapply wp_tee_local $$ Hf
    iintro !> Hf
    iapply wp_val_cons_imm
    iapply wp_set_local _ _ _ 2 (fun w => iprop(⌜w = .immV []⌝)) _ (by omega) $$ [] Hf
    inext; ipureintro; rfl
  iintro Hf
  take_drop_app_rewrite 2
  iapply wp_seq_imm [valueOfUint (v + s.length * 4 - 4 * j), valueOfUint (v + s.length * 4 - 4 * j)]
    iprop(↪[frame] (⟨f.locs.set 2 (valueOfUint (v + s.length * 4 - 4 * j)), f.inst⟩ : Frame))
    $$ [Hf]
  · iapply wp_val_cons_imm
    iapply wp_get_local _ _ (valueOfUint (v + s.length * 4 - 4 * j)) 2
      (fun w => iprop(⌜w = .immV [valueOfUint (v + s.length * 4 - 4 * j)]⌝))
      (⟨f.locs.set 2 (valueOfUint (v + s.length * 4 - 4 * j)), f.inst⟩ : Frame)
      (by simp [List.getElem?_set]; omega) $$ [] Hf
    inext; ipureintro; rfl
  iintro Hf
  take_drop_app_rewrite 3
  iapply wp_seq_imm [valueOfUint (v + s.length * 4 - 4 * j), .int32 sv]
    iprop(isStack v s n ∗
      ↪[frame] (⟨f.locs.set 2 (valueOfUint (v + s.length * 4 - 4 * j)), f.inst⟩ : Frame))
    $$ [Hs Hf]
  · iapply wp_val_cons_imm
    iapply stack_load_j v s n
      (⟨f.locs.set 2 (valueOfUint (v + s.length * 4 - 4 * j)), f.inst⟩ : Frame) E j sv
      $$ %hmem %hsv %⟨Nat.zero_le _, hj⟩ Hs Hf
  iintro ⟨Hs, Hf⟩
  take_drop_app_rewrite 3
  iapply wp_seq_imm [valueOfUint (v + s.length * 4 - 4 * j), .int32 sv, .int32 fn]
    iprop(↪[frame] (⟨f.locs.set 2 (valueOfUint (v + s.length * 4 - 4 * j)), f.inst⟩ : Frame))
    $$ [Hf]
  · iapply wp_val_cons_imm
    iapply wp_val_cons_imm
    iapply wp_get_local _ _ _ _ (fun w => iprop(⌜w = .immV [.int32 fn]⌝)) _
      (by simpa [List.getElem?_set] using hl1) $$ [] Hf
    inext; ipureintro; rfl
  iintro Hf
  isimp only [vToEList, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  iapply HK $$ Hs Hf

/-- The last two instructions of `map_loop_body` (after the indirect call): store the result and
branch back to the loop. -/
theorem map_loop_body_suffix (f1 : Frame) (s : List I32) (v n j : Nat) (sv v0 : I32) (E : CoPset)
    (hmem : f1.inst.memory[0]? = some n) (hj : j < s.length) (hsv : s[j]? = some sv) :
    ⊢ (isStack v s n -∗ ↪[frame] f1 -∗
      WP ([.basic (.const (valueOfUint (v + s.length * 4 - 4 * j))), .basic (.const (.int32 v0)),
          .basic (.store .i32 none 0 0), .basic (.br 0)] : Expr) @ E
        {{ w, ⌜w = .brV (ValidHoled.base [] [] : ValidHoled 0)⌝ ∗ isStack v (s.set j v0) n ∗
          ↪[frame] f1 }} : IProp GF) := by
  iintro Hs Hf
  take_drop_app_rewrite 3
  iapply wp_seq_imm [] iprop(isStack v (s.set j v0) n ∗ ↪[frame] f1) $$ [Hs Hf]
  · iapply stack_store_j $$ %hmem %hsv %⟨Nat.zero_le _, hj⟩ Hs Hf
  iintro ⟨Hs, Hf⟩
  iapply wp_value_s (.brV (ValidHoled.base [] [] : ValidHoled 0)) ?_
  · rfl
  iframe; ipureintro; rfl

@[rocq_alias iriswasm.spec_map_initialise]
theorem spec_map_initialise (f : Frame) (s : List I32) (v n : Nat) (E : CoPset) :
    ⊢ ({{{{ ⌜f.inst.memory[0]? = some n⌝ ∗
          ⌜f.locs[0]? = some (valueOfUint v)⌝ ∗
          ⌜f.locs.length ≥ 4⌝ ∗
          isStack v s n ∗
          ↪[frame] f }}}}
      (toEList mapInitialise) @ E
      {{{{ w, ⌜w = .immV []⌝ ∗
          isStack v s n ∗
          ↪[frame] (⟨(f.locs.set 3 (valueOfUint (v + s.length * 4))).set 2 (valueOfUint v),
            f.inst⟩ : Frame) }}}} : IProp GF) := by
  iintro !> %Ξ ⟨%hmem, %hl0, %hlen, Hs, Hf⟩ HΞ
  take_drop_app_rewrite 1
  iapply wp_seq_imm [valueOfUint v] iprop(↪[frame] f) $$ [Hf]
  · iapply wp_get_local _ _ _ _ (fun w => iprop(⌜w = .immV [valueOfUint v]⌝)) _ hl0 $$ [] Hf
    inext; ipureintro; rfl
  iintro Hf
  take_drop_app_rewrite 2
  iapply wp_seq_imm [valueOfUint (v + s.length * 4)] iprop(isStack v s n ∗ ↪[frame] f)
    $$ [Hs Hf]
  · iapply stack_load_0 $$ %hmem Hs Hf
  iintro ⟨Hs, Hf⟩
  take_drop_app_rewrite 2
  iapply wp_seq_imm [] iprop(isStack v s n ∗
    ↪[frame] (⟨f.locs.set 3 (valueOfUint (v + s.length * 4)), f.inst⟩ : Frame))
    $$ [Hs Hf]
  · iapply wp_wand' $$ [Hf Hs]
    · iapply wp_set_local _ _ _ _ (fun w => iprop(⌜w = .immV []⌝ ∗ isStack v s n)) _ (by omega)
        $$ [Hs] Hf
      inext; iframe; ipureintro; rfl
    · iintro %w ⟨⟨%hw, Hs⟩, Hf⟩
      iframe; ipureintro; exact hw
  iintro ⟨Hs, Hf⟩
  take_drop_app_rewrite 1
  iapply wp_seq_imm [valueOfUint v]
    iprop(↪[frame] (⟨f.locs.set 3 (valueOfUint (v + s.length * 4)), f.inst⟩ : Frame))
    $$ [Hf]
  · iapply wp_get_local _ _ _ _ (fun w => iprop(⌜w = .immV [valueOfUint v]⌝)) _
      (by simpa using hl0) $$ [] Hf
    inext; ipureintro; rfl
  iintro Hf
  isimp only [vToEList, toEList, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  iapply wp_wand' $$ [Hf Hs]
  · iapply wp_set_local _ _ _ _ (fun w => iprop(⌜w = .immV []⌝ ∗ isStack v s n)) _ (by simp; omega)
      $$ [Hs] Hf
    inext; iframe; ipureintro; rfl
  · iintro %w ⟨⟨%hw, Hs⟩, Hf⟩
    iapply HΞ
    iframe; ipureintro; exact hw

@[rocq_alias iriswasm.spec_map_loop_body_terminate]
theorem spec_map_loop_body_terminate (f : Frame) (s : List I32) (v n : Nat) (E : CoPset)
    (j k : _root_.Int) :
    ⊢ ({{{{ ⌜f.inst.memory[0]? = some n⌝ ∗
          ⌜f.locs[0]? = some (valueOfUint v)⌝ ∗
          ⌜f.locs[2]? = some (valueOfInt j)⌝ ∗
          ⌜f.locs[3]? = some (valueOfInt k)⌝ ∗
          ⌜j = k⌝ ∗
          ⌜f.locs.length ≥ 4⌝ ∗
          isStack v s n ∗
          ↪[frame] f }}}}
      (toEList mapLoopBody) @ E
      {{{{ w, ⌜∃ es, w = .brV (ValidHoled.base [] es : ValidHoled 1)⌝ ∗
          isStack v s n ∗ ↪[frame] f }}}} : IProp GF) := by
  iintro !> %Ξ ⟨%hmem, %hl0, %hl2, %hl3, %hjk, %hlen, Hs, Hf⟩ HΞ
  subst hjk
  take_drop_app_rewrite 1
  iapply wp_seq_imm [valueOfInt j] iprop(↪[frame] f) $$ [Hf]
  · iapply wp_get_local _ _ _ _ (fun w => iprop(⌜w = .immV [valueOfInt j]⌝)) _ hl2 $$ [] Hf
    inext; ipureintro; rfl
  iintro Hf
  take_drop_app_rewrite 2
  iapply wp_seq_imm [valueOfInt j, valueOfInt j] iprop(↪[frame] f) $$ [Hf]
  · iapply wp_val_cons_imm
    iapply wp_get_local _ _ _ _ (fun w => iprop(⌜w = .immV [valueOfInt j]⌝)) _ hl3 $$ [] Hf
    inext; ipureintro; rfl
  iintro Hf
  take_drop_app_rewrite 3
  iapply wp_seq_imm [.int32 (wasmBool true)] iprop(↪[frame] f) $$ [Hf]
  · iapply wp_relop (op := .i .eq) (b := true)
      (by simp [appRelop, appRelopI, valueOfInt, Wasm.Int.ieq])
      $$ Hf
    inext; ipureintro; rfl
  iintro Hf
  take_drop_app_rewrite 2
  iapply wp_seq _ _ _ (fun w => iprop(⌜w = .brV (ValidHoled.base [] [] : ValidHoled 1)⌝ ∗
    ↪[frame] f))
  isplitr
  · iintro ⟨%h, -⟩; cases h
  isplitl [Hf]
  · iapply wp_br_if_true (by decide) $$ Hf
    iintro !> Hf
    iapply wp_value_s (.brV (ValidHoled.base [] [] : ValidHoled 1)) ?_
    · rfl
    iframe; ipureintro; rfl
  iintro %w ⟨%hw, Hf⟩
  subst hw
  iapply wp_value_s (.brV (ValidHoled.base [] (toEList (mapLoopBody.drop 4)) : ValidHoled 1)) ?_
  · rfl
  iapply HΞ
  iframe; ipureintro; exact ⟨_, rfl⟩

@[rocq_alias iriswasm.spec_map_loop_body_continue]
theorem spec_map_loop_body_continue (f : Frame) (s : List I32) (v n : Nat) (E : CoPset) (j : Nat)
    (fn sv : I32) (j0 a : Nat) (cl : FunctionClosure) (Φ : I32 → IProp GF)
    (Ψ : I32 → I32 → IProp GF) :
    ⊢ ({{{{ ⌜f.inst.memory[0]? = some n⌝ ∗
          ⌜f.locs[0]? = some (valueOfUint v)⌝ ∗
          ⌜f.locs[1]? = some (.int32 fn)⌝ ∗
          ⌜f.locs[2]? = some (valueOfUint (v + s.length * 4 - 4 * j - 4))⌝ ∗
          ⌜f.locs[3]? = some (valueOfUint (v + s.length * 4))⌝ ∗
          ⌜f.locs.length ≥ 4⌝ ∗
          ⌜0 ≤ j ∧ j < s.length⌝ ∗
          ⌜s[j]? = some sv⌝ ∗
          isStack v s n ∗
          Φ sv ∗
          ⌜f.inst.types[1]? = some (.tf [.i32] [.i32])⌝ ∗
          ⌜f.inst.tab[0]? = some j0⌝ ∗
          j0 ↦[wt][ Wasm.Int.natOfUint fn ] (some a) ∗
          a ↦[wf] cl ∗
          ⌜clType cl = .tf [.i32] [.i32]⌝ ∗
          (∀ (u : I32) (fc : Frame),
            {{{{ Φ u ∗
                ⌜f.inst = fc.inst⌝ ∗
                ↪[frame] fc ∗
                j0 ↦[wt][ Wasm.Int.natOfUint fn ] (some a) ∗
                a ↦[wf] cl }}}}
              ([.basic (.const (.int32 u)), .invoke a] : Expr) @ E
              {{{{ w, (∃ v, ⌜w = .immV [.int32 v]⌝ ∗ Ψ u v) ∗
                  ↪[frame] fc ∗
                  j0 ↦[wt][ Wasm.Int.natOfUint fn ] (some a) ∗
                  a ↦[wf] cl }}}}) ∗
          ↪[frame] f }}}}
      (toEList mapLoopBody) @ E
      {{{{ w, ⌜w = .brV (ValidHoled.base [] [] : ValidHoled 0)⌝ ∗
          (∃ sv' : I32, isStack v (s.set j sv') n ∗ Ψ sv sv') ∗
          j0 ↦[wt][ Wasm.Int.natOfUint fn ] (some a) ∗
          a ↦[wf] cl ∗
          ↪[frame] (⟨f.locs.set 2 (valueOfUint (v + s.length * 4 - 4 * j)), f.inst⟩ : Frame)
      }}}} : IProp GF) := by
  iintro !> %Ξ ⟨%hmem, %hl0, %hl1, %hl2, %hl3, %hlen, %hj, %hsv, Hs, HΦ, %htypes, %htab, Htab,
    Hcl, %hclt, Hspec, Hf⟩ HΞ
  iapply map_loop_body_prefix f s v n j sv fn E _ hmem hl1 hl2 hl3 hlen hj.2 hsv $$ Hs Hf
  iintro Hs Hf
  take_drop_app_rewrite 4
  iapply wp_seq _ _ _ (fun w => iprop(∃ v0, ⌜w = .immV [valueOfUint (v + s.length * 4 - 4 * j),
    .int32 v0]⌝ ∗ Ψ sv v0 ∗
    ↪[frame] (⟨f.locs.set 2 (valueOfUint (v + s.length * 4 - 4 * j)), f.inst⟩ : Frame) ∗
    j0 ↦[wt][ Wasm.Int.natOfUint fn ] (some a) ∗ a ↦[wf] cl))
  isplitr
  · iintro ⟨%v0, %h, -⟩; cases h
  isplitl [HΦ Htab Hcl Hspec Hf]
  · iapply wp_val_cons
    isplitr
    · imodintro; iintro ⟨%v0, %h, -⟩; cases h
    iapply wp_ctx_base_cons
    iapply wp_call_indirect_success_ctx _ _ _
      (⟨f.locs.set 2 (valueOfUint (v + s.length * 4 - 4 * j)), f.inst⟩ : Frame) 1 j0 a fn cl 0 _
      (by simpa [hclt] using htypes)
      htab $$ Htab Hcl Hf
    iintro !> ⟨Htab, Hcl, Hf⟩
    iapply wp_base
    isimp only [vToEList, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.append_nil]
    ispecialize Hspec $$ %sv
      %(⟨f.locs.set 2 (valueOfUint (v + s.length * 4 - 4 * j)), f.inst⟩ : Frame)
    iapply Hspec $$ [HΦ Hf Htab Hcl]
    · iframe; ipureintro; rfl
    iintro %w ⟨⟨%v0, %hw, HΨ⟩, Hf, Htab, Hcl⟩
    subst hw
    iexists v0; iframe; ipureintro; rfl
  iintro %w ⟨%v0, %hw, HΨ, Hf, Htab, Hcl⟩
  subst hw
  isimp only [ofVal, vToEList, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  iapply wp_wand' $$ [Hs Hf]
  · iapply map_loop_body_suffix
      (⟨f.locs.set 2 (valueOfUint (v + s.length * 4 - 4 * j)), f.inst⟩ : Frame) s v n j sv v0 E
      hmem hj.2 hsv $$ Hs Hf
  iintro %w ⟨%hw, Hs, Hf⟩
  iapply HΞ
  iframe; ipureintro; exact hw

/-- The two enclosing labels (`block` and `loop`) of the loop body in `map_op`. -/
local notation "mapLoopLh" => pushBase (Lholed.rec_ [] 0 [] (Lholed.base [] []) []) 0
  [AdministrativeInstruction.basic (BasicInstruction.loop (FunctionType.tf [] []) mapLoopBody)]
  [] []

/-- `br 1` out of the loop body exits the `block`. -/
theorem map_loop_exit (f : Frame) (E : CoPset) (Ξ : Val → IProp GF)
    (es : List AdministrativeInstruction) :
    ⊢ (↪[frame] f -∗ ▷ (↪[frame] f -∗ Ξ (.immV [])) -∗
      WP (ofVal (.brV (ValidHoled.base [] es : ValidHoled 1))) @ E CTX 2 ; mapLoopLh {{ Ξ }}
      : IProp GF) := by
  iintro Hf HK
  isimp only [ofVal, vfill]
  iapply wp_base_push (l1 := vToEList []) rfl
  isimp only [frameBase, pushBase, vToEList, List.map_nil, List.nil_append, List.append_nil]
  rw [show ([AdministrativeInstruction.basic (.br 1)] : Expr) = [] ++ [.basic (.br 1)] from rfl]
  iapply wp_br_ctx rfl rfl $$ Hf
  iintro !> Hf
  iapply wp_value_s (.immV []) ?_
  · rfl
  iapply HK $$ Hf

/-- `br 0` out of the loop body re-enters the `loop`. -/
theorem map_loop_continue (f : Frame) (E : CoPset) (Ξ : Val → IProp GF) :
    ⊢ (↪[frame] f -∗ ▷ (↪[frame] f -∗ WP (toEList mapLoopBody) @ E CTX 2 ; mapLoopLh {{ Ξ }}) -∗
      WP (ofVal (.brV (ValidHoled.base [] [] : ValidHoled 0))) @ E CTX 2 ; mapLoopLh {{ Ξ }}
      : IProp GF) := by
  iintro Hf HK
  rw [show ofVal (.brV (ValidHoled.base [] [] : ValidHoled 0)) = [] ++ [.basic (.br 0)] from rfl]
  iapply wp_br_ctx_nested (j := 2) (lh'' := .rec_ [] 0 [] (.base [] []) []) (by omega) rfl rfl
    rfl rfl $$ Hf
  iintro !> Hf
  isimp only [List.nil_append, List.append_nil]
  rw [show ([AdministrativeInstruction.basic (.loop (.tf [] []) mapLoopBody)] : Expr) =
    [] ++ [.basic (.loop (.tf [] []) mapLoopBody)] from rfl]
  iapply wp_loop_ctx rfl rfl rfl rfl $$ Hf
  iintro !> Hf
  iapply wp_label_push_nil
  simp only [List.nil_append, List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  iapply HK $$ Hf

@[rocq_alias iriswasm.spec_map_loop_j]
theorem spec_map_loop_j (f : Frame) (s : List I32) (v n : Nat) (E : CoPset) (j : Nat) (fn : I32)
    (j0 a : Nat) (cl : FunctionClosure) (Φ : I32 → IProp GF) (Ψ : I32 → I32 → IProp GF)
    (s' : List I32) :
    ⊢ (iprop(⌜f.inst.memory[0]? = some n⌝ ∗
          ⌜f.locs[0]? = some (valueOfUint v)⌝ ∗
          ⌜f.locs[1]? = some (.int32 fn)⌝ ∗
          ⌜f.locs[2]? = some (valueOfUint (v + s.length * 4 - 4 * j))⌝ ∗
          ⌜f.locs[3]? = some (valueOfUint (v + s.length * 4))⌝ ∗
          ⌜f.locs.length ≥ 4⌝ ∗
          ⌜0 ≤ j ∧ j ≤ s.length⌝ ∗
          ⌜j + s'.length = s.length⌝ ∗
          isStack v (s.take j ++ s') n ∗
          stackAll (s.take j) Φ ∗
          stackAll2 (s.drop j) s' Ψ ∗
          ⌜f.inst.types[1]? = some (.tf [.i32] [.i32])⌝ ∗
          ⌜f.inst.tab[0]? = some j0⌝ ∗
          j0 ↦[wt][ Wasm.Int.natOfUint fn ] (some a) ∗
          a ↦[wf] cl ∗
          ⌜clType cl = .tf [.i32] [.i32]⌝ ∗
          (∀ (u : I32) (fc : Frame),
            {{{{ Φ u ∗
                ⌜f.inst = fc.inst⌝ ∗
                ↪[frame] fc ∗
                j0 ↦[wt][ Wasm.Int.natOfUint fn ] (some a) ∗
                a ↦[wf] cl }}}}
              ([.basic (.const (.int32 u)), .invoke a] : Expr) @ E
              {{{{ w, (∃ v, ⌜w = .immV [.int32 v]⌝ ∗ Ψ u v) ∗
                  ↪[frame] fc ∗
                  j0 ↦[wt][ Wasm.Int.natOfUint fn ] (some a) ∗
                  a ↦[wf] cl }}}}) ∗
          ↪[frame] f) -∗
      WP (toEList mapLoopBody : Expr) @ E CTX 2 ;
        (pushBase (.rec_ [] 0 [] (.base [] []) []) 0
          [.basic (.loop (.tf [] []) mapLoopBody)] [] [])
        {{ w, ⌜w = .immV []⌝ ∗
          (∃ s', isStack v s' n ∗ stackAll2 s s' Ψ) ∗
          (∃ f1, ↪[frame] f1 ∗ ⌜f.inst = f1.inst⌝) ∗
          j0 ↦[wt][ Wasm.Int.natOfUint fn ] (some a) ∗
          a ↦[wf] cl }} : IProp GF) := by
  induction j generalizing f s' with
  | zero =>
    iintro ⟨%hmem, %hl0, %hl1, %hl2, %hl3, %hlen, -, %hlen', Hs, -, HΨ, -, -, Htab, Hcl, -, -,
      Hf⟩
    simp only [List.take_zero, List.nil_append, List.drop_zero, Nat.mul_zero, Nat.sub_zero,
      Nat.zero_add] at hl2 hlen' ⊢
    iapply wp_ctx_bind _ _ _ _ _ _ ?_
    · simp [BaseIsEmpty, pushBase]
    iapply spec_map_loop_body_terminate f s' v n E ((v + s.length * 4 : Nat) : _root_.Int)
      ((v + s.length * 4 : Nat) : _root_.Int) $$ [Hs Hf]
    · iframe; ipureintro; exact ⟨hmem, hl0, hl2, hl3, rfl, hlen⟩
    iintro %w ⟨%⟨es, hw⟩, Hs, Hf⟩
    subst hw
    iapply map_loop_exit $$ Hf
    iintro !> Hf
    isplitr
    · ipureintro; rfl
    isplitl [Hs HΨ]
    · iexists s'; iframe
    isplitl [Hf]
    · iexists f; iframe; ipureintro; rfl
    iframe
  | succ j ih =>
    iintro ⟨%hmem, %hl0, %hl1, %hl2, %hl3, %hlen, %hj, %hlen', Hs, HΦ, HΨ, %htypes, %htab,
      Htab, Hcl, %hclt, #Hspec, Hf⟩
    have hjL : j < s.length := by omega
    obtain ⟨sv, hsv⟩ : ∃ sv, s[j]? = some sv := ⟨s[j], List.getElem?_eq_getElem hjL⟩
    have htake : s.take (j + 1) = s.take j ++ [sv] := by
      rw [List.take_add_one, hsv]; rfl
    have hL : (s.take (j + 1) ++ s').length = s.length := by
      simp only [List.length_append, List.length_take]; omega
    have hsv' : (s.take (j + 1) ++ s')[j]? = some sv := by
      rw [List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt (by omega), hsv]
    have hsplit := stackAll_app (GF := GF) (s.take j) [sv] Φ
    rw [← htake] at hsplit
    icases (wandIff_equiv hsplit).1 $$ HΦ with ⟨HΦ, HΦsv⟩
    simp only [stackAll]
    icases HΦsv with ⟨HΦsv, -⟩
    iapply wp_ctx_bind _ _ _ _ _ _ ?_
    · simp [BaseIsEmpty, pushBase]
    iapply spec_map_loop_body_continue f (s.take (j + 1) ++ s') v n E j fn sv j0 a cl Φ Ψ
      $$ [Hs HΦsv Htab Hcl Hf]
    · rw [hL]
      have hl2' : f.locs[2]? = some (valueOfUint (v + s.length * 4 - 4 * j - 4)) := by
        rw [hl2, Nat.mul_add, Nat.sub_add_eq]
      iframe
      repeat (isplitr; · ipureintro; first | assumption | exact ⟨by omega, by omega⟩)
      iexact Hspec
    iintro %w ⟨%hw, ⟨%sv'', Hs, HΨ'⟩, Htab, Hcl, Hf⟩
    subst hw
    iapply map_loop_continue $$ Hf
    iintro !> Hf
    have hset : (s.take (j + 1) ++ s').set j sv'' = s.take j ++ sv'' :: s' := by
      have hl : (s.take j).length = j := by simp; omega
      rw [htake, List.append_assoc, List.set_append_right _ _ (by omega), hl, Nat.sub_self]; rfl
    have hdrop : s.drop j = sv :: s.drop (j + 1) := by
      rw [List.drop_eq_getElem_cons hjL]; congr 1; simpa [List.getElem?_eq_getElem hjL] using hsv
    rw [hset, hL]
    iapply ih (⟨f.locs.set 2 (valueOfUint (v + s.length * 4 - 4 * j)), f.inst⟩ : Frame)
      (sv'' :: s') $$ [Hs HΦ HΨ HΨ' Htab Hcl Hf]
    rw [hdrop]
    simp only [stackAll2]
    iframe
    repeat (isplitr; · ipureintro; first | assumption | exact ⟨by omega, by omega⟩ |
      (simp only [List.length_cons]; omega) | (simp [List.getElem?_set, hl0, hl1, hl3] <;> omega))
    iexact Hspec

@[rocq_alias iriswasm.spec_stack_map]
theorem spec_stack_map (f0 : Frame) (n : Immediate) (f : I32) (v : Nat) (s : List I32) (E : CoPset)
    (j0 a : Nat) (cl : FunctionClosure) (Φ : I32 → IProp GF) (Ψ : I32 → I32 → IProp GF) :
    ⊢ ({{{{ ⌜f0.inst.memory[0]? = some n⌝ ∗
          ⌜f0.locs[0]? = some (valueOfUint v)⌝ ∗
          ⌜f0.locs[1]? = some (.int32 f)⌝ ∗
          ⌜f0.locs.length ≥ 4⌝ ∗
          isStack v s n ∗
          stackAll s Φ ∗
          ⌜f0.inst.types[1]? = some (.tf [.i32] [.i32])⌝ ∗
          ⌜f0.inst.tab[0]? = some j0⌝ ∗
          j0 ↦[wt][ Wasm.Int.natOfUint f ] (some a) ∗
          a ↦[wf] cl ∗
          ⌜clType cl = .tf [.i32] [.i32]⌝ ∗
          (∀ (u : I32) (fc : Frame),
            {{{{ Φ u ∗
                ⌜f0.inst = fc.inst⌝ ∗
                ↪[frame] fc ∗
                j0 ↦[wt][ Wasm.Int.natOfUint f ] (some a) ∗
                a ↦[wf] cl }}}}
              ([.basic (.const (.int32 u)), .invoke a] : Expr) @ E
              {{{{ w, (∃ v, ⌜w = .immV [.int32 v]⌝ ∗ Ψ u v) ∗
                  ↪[frame] fc ∗
                  j0 ↦[wt][ Wasm.Int.natOfUint f ] (some a) ∗
                  a ↦[wf] cl }}}}) ∗
          ↪[frame] f0 }}}}
      (toEList stackMap) @ E
      {{{{ w, ⌜w = .immV []⌝ ∗
          (∃ s', isStack v s' n ∗ stackAll2 s s' Ψ) ∗
          (∃ f1, ↪[frame] f1 ∗ ⌜f0.inst = f1.inst⌝) ∗
          j0 ↦[wt][ Wasm.Int.natOfUint f ] (some a) ∗
          a ↦[wf] cl }}}} : IProp GF) := by
  iintro !> %Ξ ⟨%hmem, %hl0, %hl1, %hlen, Hs, HΦ, %htypes, %htab, Htab, Hcl, %hclt, #Hspec, Hf⟩ HΞ
  rw [show (toEList stackMap : Expr) = toEList (validateStack 0) ++
    (toEList (validateStackBound 0) ++ toEList mapOp) by simp [stackMap, toEList]]
  iapply wp_seq_imm [] iprop(isStack v s n ∗ ↪[frame] f0) $$ [Hs Hf]
  · iapply is_stack_valid v s n f0 E 0
    iframe; ipureintro; exact hl0
  iintro ⟨Hs, Hf⟩
  isimp only [vToEList, List.map_nil, List.nil_append]
  iapply wp_seq_imm [] iprop(isStack v s n ∗ ↪[frame] f0) $$ [Hs Hf]
  · iapply is_stack_bound_valid v s n f0 E 0
    iframe; ipureintro; exact ⟨hmem, hl0⟩
  iintro ⟨Hs, Hf⟩
  let fr : Frame :=
    ⟨(f0.locs.set 3 (valueOfUint (v + s.length * 4))).set 2 (valueOfUint v), f0.inst⟩
  rw [show (toEList mapOp : Expr) = toEList mapInitialise ++
    [.basic (.block (.tf [] []) [.loop (.tf [] []) mapLoopBody])] by simp [mapOp, toEList]]
  isimp only [vToEList, List.map_nil, List.nil_append]
  iapply wp_seq_imm [] iprop(isStack v s n ∗ ↪[frame] fr) $$ [Hs Hf]
  · iapply spec_map_initialise f0 s v n E $$ [Hs Hf]
    · iframe; ipureintro; exact ⟨hmem, hl0, hlen⟩
    iintro %w ⟨%hw, Hs, Hf⟩
    iframe; ipureintro; exact hw
  iintro ⟨Hs, Hf⟩
  isimp only [vToEList, List.map_nil, List.nil_append]
  rw [show ([AdministrativeInstruction.basic (.block (.tf [] []) [.loop (.tf [] []) mapLoopBody])]
    : Expr) = [] ++ [.basic (.block (.tf [] []) [.loop (.tf [] []) mapLoopBody])] from rfl]
  iapply wp_block rfl rfl rfl rfl $$ Hf
  iintro !> Hf
  iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).2
  iapply wp_label_push_nil
  simp only [List.nil_append, toEList, List.map_cons, List.map_nil]
  rw [show ([AdministrativeInstruction.basic (.loop (.tf [] []) mapLoopBody)] : Expr) =
    [] ++ [.basic (.loop (.tf [] []) mapLoopBody)] from rfl]
  iapply wp_loop_ctx rfl rfl rfl rfl $$ Hf
  iintro !> Hf
  iapply wp_label_push_nil
  simp only [List.nil_append, List.length_nil, Nat.reduceAdd]
  have hj := spec_map_loop_j (GF := GF) fr s v n E s.length f j0 a cl Φ Ψ []
  rw [List.take_length, List.append_nil, List.drop_length,
    show v + s.length * 4 - 4 * s.length = v by omega] at hj
  simp only [pushBase, fr] at hj ⊢
  iapply wp_wand_ctx $$ [Hs HΦ Htab Hcl Hf] HΞ
  iapply hj
  simp only [stackAll2]
  iframe
  repeat (isplitr; · ipureintro; first | assumption | exact ⟨by omega, by omega⟩ |
    (simp [List.getElem?_set, hl0, hl1] <;> omega))
  iexact Hspec

end specs

end IrisWasm.Examples.Stack
