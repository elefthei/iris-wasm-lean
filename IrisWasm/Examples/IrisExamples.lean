/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Rules.Proofmode

/-! Port of `theories/iris/examples/iris_examples.v`. -/

namespace IrisWasm.Examples

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm IrisWasm

section Examples
variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF]

/-- Coq `iApply wp_value` for a list of constants (Lean helper). -/
private theorem wp_value_imm {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF} (vs : List Value)
    {e : Expr} (h : e = vToEList vs) : Φ (.immV vs) ⊢ WP e @ s ; E {{ Φ }} := by
  subst h
  exact IrisWp.wp_value (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) ⟨rfl⟩

@[rocq_alias iriswasm.my_add]
def myAdd : Expr :=
  [.basic (.const (xx 3)), .basic (.const (xx 2)), .basic (.binop .i32 (.i .add))]

@[rocq_alias iriswasm.myadd_spec]
theorem myadd_spec (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF) (f0 : Frame) :
    ⊢ iprop(↪[frame] f0 -∗ Φ (.immV [xx 5]) -∗ WP myAdd @ s ; E {{ v, Φ v ∗ ↪[frame] f0 }}) := by
  iintro Hf HP
  unfold myAdd
  iapply wp_binop (v := xx 5) rfl rfl .i32Agree (by decide) $$ Hf
  inext
  iexact HP

/-- An example to show framing from the stack. -/
@[rocq_alias iriswasm.my_add2]
def myAdd2 : Expr :=
  [.basic (.const (xx 1)), .basic (.const (xx 2)), .basic (.binop .i32 (.i .add)),
   .basic (.const (xx 2)), .basic (.binop .i32 (.i .add))]

@[rocq_alias iriswasm.myadd2_spec]
theorem myadd2_spec (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF) (f0 : Frame) :
    ⊢ iprop(↪[frame] f0 -∗ Φ (.immV [xx 5]) -∗ WP myAdd2 @ s ; E {{ v, Φ v ∗ ↪[frame] f0 }}) := by
  iintro Hf0 HΦ
  unfold myAdd2
  take_drop_app_rewrite 3
  iapply wp_seq s E _ (fun v => iprop(⌜v = .immV [xx 3]⌝ ∗ ↪[frame] f0))
  isplitl []
  · iintro ⟨%H, -⟩; cases H
  isplitl [Hf0]
  · iapply wp_binop (v := xx 3) rfl rfl .i32Agree (by decide) $$ Hf0
    inext; ipureintro; rfl
  iintro %w ⟨%hw, Hf0⟩
  subst hw
  simp only [ofVal, vToEList, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  iapply wp_binop (v := xx 5) rfl rfl .i32Agree (by decide) $$ Hf0
  inext
  iexact HΦ

/-! ### Control flow examples

`iris_examples.v` restates the four `iRewrite_nil_*` lemmas of `iris_example_helper.v`. -/

@[rocq_alias iriswasm.iris_examples.iRewrite_nil_l]
theorem iRewrite_nil_l (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF) (e : Expr) :
    iprop(WP ([] ++ e) @ s ; E {{ Φ }}) ⊢ iprop(WP e @ s ; E {{ Φ }}) :=
  IrisWasm.iRewrite_nil_l s E Φ e

@[rocq_alias iriswasm.iris_examples.iRewrite_nil_r]
theorem iRewrite_nil_r (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF) (e : Expr) :
    iprop(WP (e ++ []) @ s ; E {{ Φ }}) ⊢ iprop(WP e @ s ; E {{ Φ }}) :=
  IrisWasm.iRewrite_nil_r s E Φ e

@[rocq_alias iriswasm.iris_examples.iRewrite_nil_l_ctx]
theorem iRewrite_nil_l_ctx (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF) (e : Expr) (i : Nat)
    (lh : Lholed) :
    iprop(WP ([] ++ e) @ s ; E CTX i ; lh {{ Φ }}) ⊢ iprop(WP e @ s ; E CTX i ; lh {{ Φ }}) :=
  IrisWasm.iRewrite_nil_l_ctx s E Φ e i lh

@[rocq_alias iriswasm.iris_examples.iRewrite_nil_r_ctx]
theorem iRewrite_nil_r_ctx (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF) (e : Expr) (i : Nat)
    (lh : Lholed) :
    iprop(WP (e ++ []) @ s ; E CTX i ; lh {{ Φ }}) ⊢ iprop(WP e @ s ; E CTX i ; lh {{ Φ }}) :=
  IrisWasm.iRewrite_nil_r_ctx s E Φ e i lh

/-! Examples of blocks that return normally. -/

theorem label_check_easy (f0 : Frame) (hsig : f0.inst.types[0]? = some (.tf [] [.i32, .i32])) :
    (iprop(↪[frame] f0) : IProp GF) ⊢
      WP ([.basic (.block (.index 0) [.const (xx 2), .const (xx 3)])] : Expr)
        {{ v, ⌜v = Val.immV [xx 2, xx 3]⌝ ∗ ↪[frame] f0 }} := by
  iintro Hf0
  iapply iRewrite_nil_l
  iapply wp_block (bt := .index 0) ?_ ?_ ?_ ?_ hsig $$ Hf0 <;> try (first | decide | rfl)
  inext
  iintro Hf0
  iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).2
  iapply wp_label_push_nil
  simp only [pushBase, toEList, List.map_cons, List.map_nil, List.nil_append]
  iapply wp_val_return (by decide) $$ Hf0
  iintro Hf0
  iapply wp_value_imm [xx 2, xx 3] ?_ <;> try (first | decide | rfl)
  iframe
  ipureintro; rfl

theorem label_check_easy' (f0 : Frame) (hsig : f0.inst.types[0]? = some (.tf [] [.i32, .i32])) :
    (iprop(↪[frame] f0) : IProp GF) ⊢
      WP ([.basic (.block (.index 0)
            [.block (.index 0) [.const (xx 2), .const (xx 3)]])] : Expr)
        {{ v, ⌜v = Val.immV [xx 2, xx 3]⌝ ∗ ↪[frame] f0 }} := by
  iintro Hf0
  iapply iRewrite_nil_l
  iapply wp_block (bt := .index 0) ?_ ?_ ?_ ?_ hsig $$ Hf0 <;> try (first | decide | rfl)
  inext
  iintro Hf0
  iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).2
  iapply wp_label_push_nil
  simp only [pushBase, toEList, List.map_cons, List.map_nil, List.nil_append]
  iapply iRewrite_nil_r_ctx
  iapply wp_seq_ctx _ _ _ (fun v => iprop(⌜v = Val.immV [xx 2, xx 3]⌝ ∗ ↪[frame] f0))
  isplitr
  · iintro ⟨%H, -⟩; cases H
  isplitl [Hf0]
  · iapply label_check_easy f0 hsig; iexact Hf0
  iintro %w ⟨%hw, Hf0⟩
  subst hw
  simp only [ofVal, vToEList, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  iapply wp_val_return (by decide) $$ Hf0
  iintro Hf0
  iapply wp_value_imm [xx 2, xx 3] ?_ <;> try (first | decide | rfl)
  iframe
  ipureintro; rfl

@[rocq_alias iriswasm.br_check_bind_return]
theorem br_check_bind_return (f0 : Frame) :
    (iprop(↪[frame] f0) : IProp GF) ⊢
      WP ([.basic (.block (.result (some .i32))
            [.block (.result none) [.const (xx 3), .br 1]])] : Expr)
        {{ v, ⌜v = Val.immV [xx 3]⌝ ∗ ↪[frame] f0 }} := by
  iintro Hf
  iapply iRewrite_nil_l
  iapply wp_block (bt := .result (some .i32)) ?_ ?_ ?_ ?_ rfl $$ Hf <;> try (first | decide | rfl)
  inext; iintro Hf
  iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).2
  iapply wp_label_push_nil
  simp only [pushBase, toEList, List.map_cons, List.map_nil, List.nil_append]
  iapply iRewrite_nil_l_ctx
  iapply wp_block_ctx (bt := .result none) ?_ ?_ ?_ ?_ rfl $$ Hf <;> try (first | decide | rfl)
  inext; iintro Hf
  iapply wp_label_push_nil
  simp only [pushBase, toEList, List.map_cons, List.map_nil, List.nil_append]
  take_drop_app_rewrite 1
  iapply wp_br_ctx ?_ ?_ $$ Hf <;> try (first | decide | rfl)
  inext; iintro Hf
  iapply wp_value_imm [xx 3] ?_ <;> try (first | decide | rfl)
  iframe
  ipureintro; rfl

@[rocq_alias iriswasm.br_check_bind_return_2]
theorem br_check_bind_return_2 (f0 : Frame) :
    (iprop(↪[frame] f0) : IProp GF) ⊢
      WP ([.basic (.block (.result (some .i32))
            [.block (.result none) [.const (xx 2), .const (xx 3), .br 1]])] : Expr)
        {{ v, ⌜v = Val.immV [xx 3]⌝ ∗ ↪[frame] f0 }} := by
  iintro Hf
  iapply iRewrite_nil_l
  iapply wp_block (bt := .result (some .i32)) ?_ ?_ ?_ ?_ rfl $$ Hf <;> try (first | decide | rfl)
  inext; iintro Hf
  iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).2
  iapply wp_label_push_nil
  simp only [pushBase, toEList, List.map_cons, List.map_nil, List.nil_append]
  iapply iRewrite_nil_l_ctx
  iapply wp_block_ctx (bt := .result none) ?_ ?_ ?_ ?_ rfl $$ Hf <;> try (first | decide | rfl)
  inext; iintro Hf
  iapply wp_label_push_nil
  simp only [pushBase, toEList, List.map_cons, List.map_nil, List.nil_append]
  take_drop_app_rewrite 1
  iapply iRewrite_nil_r_ctx
  iapply wp_base_push ?_ <;> try (first | decide | rfl)
  simp only [frameBase]
  take_drop_app_rewrite 1
  iapply wp_br_ctx ?_ ?_ $$ Hf <;> try (first | decide | rfl)
  inext; iintro Hf
  iapply wp_value_imm [xx 3] ?_ <;> try (first | decide | rfl)
  iframe
  ipureintro; rfl

@[rocq_alias iriswasm.br_check_bind_return_3]
theorem br_check_bind_return_3 (f0 : Frame) :
    (iprop(↪[frame] f0) : IProp GF) ⊢
      WP ([.basic (.block (.result (some .i32))
            [.block (.result none)
              [.const (xx 2), .const (xx 3), .binop .i32 (.i .add), .br 1]])] : Expr)
        {{ v, ⌜v = Val.immV [xx 5]⌝ ∗ ↪[frame] f0 }} := by
  iintro Hf
  iapply iRewrite_nil_l
  iapply wp_block (bt := .result (some .i32)) ?_ ?_ ?_ ?_ rfl $$ Hf <;> try (first | decide | rfl)
  inext; iintro Hf
  iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).2
  iapply wp_label_push_nil
  simp only [pushBase, toEList, List.map_cons, List.map_nil, List.nil_append]
  iapply iRewrite_nil_l_ctx
  iapply wp_block_ctx (bt := .result none) ?_ ?_ ?_ ?_ rfl $$ Hf <;> try (first | decide | rfl)
  inext; iintro Hf
  iapply wp_label_push_nil
  simp only [pushBase, toEList, List.map_cons, List.map_nil, List.nil_append]
  take_drop_app_rewrite 3
  iapply wp_seq_ctx _ _ _ (fun v => iprop(⌜v = Val.immV [xx 5]⌝ ∗ ↪[frame] f0))
  isplitr
  · iintro ⟨%H, -⟩; cases H
  isplitl [Hf]
  · iapply wp_binop (v := xx 5) rfl rfl .i32Agree (by decide) $$ Hf
    inext; ipureintro; rfl
  iintro %w ⟨%hw, Hf⟩
  subst hw
  simp only [ofVal, vToEList, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  take_drop_app_rewrite 1
  iapply wp_br_ctx ?_ ?_ $$ Hf <;> try (first | decide | rfl)
  inext; iintro Hf
  iapply wp_value_imm [xx 5] ?_ <;> try (first | decide | rfl)
  iframe
  ipureintro; rfl

@[rocq_alias iriswasm.br_check_bind_return_4]
theorem br_check_bind_return_4 (f0 : Frame) :
    (iprop(↪[frame] f0) : IProp GF) ⊢
      WP ([.basic (.block (.result (some .i32)) -- this block returns normally
            [.const (xx 1),
             .block (.result (some .i32)) -- this block gets br'ed to
               [.block (.result none) -- this block will never return
                 [.const (xx 2), .const (xx 3), .binop .i32 (.i .add), .br 1,
                  .binop .i32 (.i .add)]], -- this expression gets stuck without br
             .binop .i32 (.i .add)])] : Expr) -- reduces only after the previous block
        {{ v, ⌜v = Val.immV [xx 6]⌝ ∗ ↪[frame] f0 }} := by
  iintro Hf
  iapply iRewrite_nil_l
  iapply wp_block (bt := .result (some .i32)) ?_ ?_ ?_ ?_ rfl $$ Hf <;> try (first | decide | rfl)
  inext; iintro Hf
  iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).2
  iapply wp_label_push_nil
  simp only [pushBase, toEList, List.map_cons, List.map_nil, List.nil_append]
  iapply iRewrite_nil_r_ctx
  iapply wp_seq_ctx _ _ _ (fun v => iprop(⌜v = Val.immV [xx 6]⌝ ∗ ↪[frame] f0))
  isplitr
  · iintro ⟨%H, -⟩; cases H
  isplitl [Hf]
  · take_drop_app_rewrite_twice 1 1
    iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).2
    iapply wp_base_push ?_ <;> try (first | decide | rfl)
    simp only [frameBase, List.nil_append, List.append_nil]
    iapply iRewrite_nil_r_ctx
    iapply wp_seq_ctx _ _ _ (fun v => iprop(⌜v = Val.immV [xx 5]⌝ ∗ ↪[frame] f0))
    isplitr
    · iintro ⟨%H, -⟩; cases H
    isplitl [Hf]
    · iapply iRewrite_nil_l
      iapply wp_block (bt := .result (some .i32)) ?_ ?_ ?_ ?_ rfl $$ Hf <;> try (first | decide | rfl)
      inext; iintro Hf
      iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).2
      iapply wp_label_push_nil
      simp only [pushBase, toEList, List.map_cons, List.map_nil, List.nil_append]
      iapply iRewrite_nil_l_ctx
      iapply wp_block_ctx (bt := .result none) ?_ ?_ ?_ ?_ rfl $$ Hf <;> try (first | decide | rfl)
      inext; iintro Hf
      iapply wp_label_push_nil
      simp only [pushBase, toEList, List.map_cons, List.map_nil, List.nil_append]
      take_drop_app_rewrite 3
      iapply wp_seq_ctx _ _ _ (fun v => iprop(⌜v = Val.immV [xx 5]⌝ ∗ ↪[frame] f0))
      isplitr
      · iintro ⟨%H, -⟩; cases H
      isplitl [Hf]
      · iapply wp_binop (v := xx 5) rfl rfl .i32Agree (by decide) $$ Hf
        inext; ipureintro; rfl
      iintro %w ⟨%hw, Hf⟩
      subst hw
      simp only [ofVal, vToEList, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
      take_drop_app_rewrite_twice 0 1
      iapply wp_base_push (l1 := []) ?_ <;> try (first | decide | rfl)
      simp only [frameBase, List.append_nil]
      take_drop_app_rewrite 1
      iapply wp_br_ctx ?_ ?_ $$ Hf <;> try (first | decide | rfl)
      inext; iintro Hf
      iapply wp_value_imm [xx 5] ?_ <;> try (first | decide | rfl)
      iframe
      ipureintro; rfl
    iintro %w ⟨%hw, Hf⟩
    subst hw
    simp only [ofVal, vToEList, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    iapply wp_base
    simp only [List.cons_append, List.nil_append]
    iapply wp_binop (v := xx 6) rfl rfl .i32Agree (by decide) $$ Hf
    inext; ipureintro; rfl
  iintro %w ⟨%hw, Hf⟩
  subst hw
  simp only [ofVal, vToEList, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  iapply wp_val_return (by decide) $$ Hf
  iintro Hf
  iapply wp_value_imm [xx 6] ?_ <;> try (first | decide | rfl)
  iframe
  ipureintro; rfl

/-! ### Simple call-indirect example -/

/-! Module 1 -/

@[rocq_alias iriswasm.f1_instrs]
def f1Instrs : List BasicInstruction := [.const (xx 0), .load .i32 none ⟨0, 0, 0⟩]

@[rocq_alias iriswasm.f1]
def f1 : Expr := toEList f1Instrs

@[rocq_alias iriswasm.store42_instrs]
def store42Instrs : List BasicInstruction :=
  [.const (xx 0), .const (xx 42), .store .i32 none ⟨0, 0, 0⟩]

@[rocq_alias iriswasm.store42]
def store42 : Expr := toEList store42Instrs

/-! Module 2 -/

@[rocq_alias iriswasm.store11_instrs]
def store11Instrs : List BasicInstruction :=
  [.const (xx 0), .const (xx 11), .store .i32 none ⟨0, 0, 0⟩]

@[rocq_alias iriswasm.store11]
def store11 : Expr := toEList store11Instrs

@[rocq_alias iriswasm.doIt_instrs]
def doItInstrs (i : Nat) : List BasicInstruction := [.const (xx 0), .callIndirect i]

@[rocq_alias iriswasm.doIt]
def doIt (i : Nat) : Expr := toEList (doItInstrs i)

/-! The frame instance differs between the specs of the two modules. -/

@[rocq_alias iriswasm.f1_spec]
theorem f1_spec (f : Frame) (n : Nat) (v : Value) :
    typesAgree .i32 v = true →
    f.inst.memory[0]? = some n →
    ⊢ (iprop(↪[frame] f -∗ n ↦[wms][ 0 ] (bits v) -∗
      WP f1 {{ w, (⌜w = Val.immV [v]⌝ ∗ n ↦[wms][ 0 ] (bits v)) ∗ ↪[frame] f }}) : IProp GF) := by
  intro ht hn
  iintro Hf Hn
  have H := wp_load (GF := GF) (x := 0) (fun w => iprop(⌜w = Val.immV [v]⌝))
    .NotStuck ⊤ .i32 v 0 0
    (.i32 (Wasm.Int.intOfZ 0)) n f ht hn
  rw [show (AddressOperand.i32 (Wasm.Int.intOfZ 0)).unsigned + 0 = 0 from rfl] at H
  simp only [f1, f1Instrs, toEList, List.map_cons, List.map_nil, xx] at H ⊢
  iapply H
  iframe
  inext; ipureintro; trivial

@[rocq_alias iriswasm.store42_spec]
theorem store42_spec (f : Frame) (n : Nat) (c : I32) :
    f.inst.memory[0]? = some n →
    ⊢ (iprop(↪[frame] f -∗ n ↦[wms][ 0 ] (bits (.int32 c)) -∗
      WP store42 {{ w, (⌜w = Val.immV []⌝ ∗ n ↦[wms][ 0 ] (bits (xx 42))) ∗ ↪[frame] f }})
      : IProp GF) := by
  intro hn
  iintro Hf Hn
  have H := wp_store (GF := GF) (x := 0) (fun w => iprop(⌜w = Val.immV []⌝))
    .NotStuck ⊤ .i32 (xx 42)
    (bits (.int32 c)) 0 0 (.i32 (Wasm.Int.intOfZ 0)) n f rfl
    (by simp [bits, lengthT, serialiseI32, length_encodeInt]) hn
  rw [show (AddressOperand.i32 (Wasm.Int.intOfZ 0)).unsigned + 0 = 0 from rfl] at H
  simp only [store42, store42Instrs, toEList, List.map_cons, List.map_nil, xx] at H ⊢
  iapply H
  iframe
  inext; ipureintro; trivial

@[rocq_alias iriswasm.store11_spec]
theorem store11_spec (f : Frame) (n : Nat) (c : I32) :
    f.inst.memory[0]? = some n →
    ⊢ (iprop(↪[frame] f -∗ n ↦[wms][ 0 ] (bits (.int32 c)) -∗
      WP store11 {{ w, (⌜w = Val.immV []⌝ ∗ n ↦[wms][ 0 ] (bits (xx 11))) ∗ ↪[frame] f }})
      : IProp GF) := by
  intro hn
  iintro Hf Hn
  have H := wp_store (GF := GF) (x := 0) (fun w => iprop(⌜w = Val.immV []⌝))
    .NotStuck ⊤ .i32 (xx 11)
    (bits (.int32 c)) 0 0 (.i32 (Wasm.Int.intOfZ 0)) n f rfl
    (by simp [bits, lengthT, serialiseI32, length_encodeInt]) hn
  rw [show (AddressOperand.i32 (Wasm.Int.intOfZ 0)).unsigned + 0 = 0 from rfl] at H
  simp only [store11, store11Instrs, toEList, List.map_cons, List.map_nil, xx] at H ⊢
  iapply H
  iframe
  inext; ipureintro; trivial

@[rocq_alias iriswasm.doIt_spec]
theorem doIt_spec (t : Nat) (i2 : Instance) (f0 : Frame) (a : Nat) (v : Value) (n : Nat) :
    f0.inst.types[t]? = some (.tf [] [.i32]) →
    f0.inst.tab[0]? = some t →
    typesAgree .i32 v = true →
    i2.memory[0]? = some n →
    -- ghost state of the current instance
    ⊢ (iprop(t ↦[wt][ 0 ] (some a) -∗
      a ↦[wf] (.funcNative i2 (.tf [] [.i32]) [] f1Instrs) -∗
      ↪[frame] f0 -∗
      -- ghost state of instance `i2`
      n ↦[wms][ 0 ] (bits v) -∗
      WP (doIt t) {{ _w, True ∗ ↪[frame] f0 }}) : IProp GF) := by
  intro htype ht hv hn
  iintro Ht Ha Hf Hn
  have H := wp_call_indirect_success (GF := GF) .NotStuck ⊤ (fun _w => iprop(True ∗ ↪[frame] f0))
    f0 t t a (Wasm.Int.intOfZ 0) (.funcNative i2 (.tf [] [.i32]) [] f1Instrs) htype ht
  rw [show Wasm.Int.natOfUint (Wasm.Int.intOfZ (w := 32) 0) = 0 from rfl] at H
  simp only [doIt, doItInstrs, toEList, List.map_cons, List.map_nil, xx]
  iapply H $$ Ht Ha Hf
  inext; iintro ⟨Ht, Ha, Hf⟩
  take_drop_app_rewrite 0
  iapply wp_invoke_native _ _ _ [] [] [] [.i32] [] a f1Instrs i2 1 f0 rfl rfl rfl $$ Hf Ha
  inext; iintro ⟨Hf, Ha⟩
  iapply (wp_frame_rewrite _ _ _ _ _ _).1
  iapply (wandIff_equiv (wp_wasm_empty_ctx_frame _ _ _ _ _ _)).2
  take_drop_app_rewrite 1
  let fi : Frame := ⟨[] ++ nZeros [], i2⟩
  iapply wp_seq_ctx_frame _ _ _ (fun w => iprop(⌜w = Val.immV [v]⌝ ∗ n ↦[wms][ 0 ] (bits v)))
    _ _ 0 (.base [] []) 1 fi f0 fi ?_
  · intro LI hLI
    simp [lfilled, lfill, constList] at hLI
    subst hLI; exact toVal_native_frame_none _ _ _
  isplitr
  · iintro ⟨%H, -⟩; cases H
  isplitl [Hf]
  · iexact Hf
  isplitl [Hn]
  · iintro Hf
    iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).2
    iapply wp_label_push_nil
    simp only [pushBase, List.nil_append]
    iapply iRewrite_nil_r_ctx
    iapply wp_seq_ctx _ _ _
      (fun w => iprop((⌜w = Val.immV [v]⌝ ∗ n ↦[wms][ 0 ] (bits v)) ∗ ↪[frame] fi))
    isplitr
    · iintro ⟨⟨%H, -⟩, -⟩; cases H
    isplitl [Hf Hn]
    · have H1 := f1_spec (GF := GF) fi n v hv hn
      unfold f1 at H1
      iapply H1 $$ Hf Hn
    iintro %w ⟨⟨%hw, Hn⟩, Hf⟩
    subst hw
    simp only [ofVal, vToEList, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    iapply wp_val_return rfl $$ Hf
    iintro Hf
    iapply wp_value_imm [v] ?_ <;> try rfl
    iframe
    ipureintro; rfl
  iintro %w ⟨⟨%hw, Hn⟩, Hf⟩
  subst hw
  simp only [ofVal, vToEList, List.map_cons, List.map_nil, List.append_nil]
  iapply (wandIff_equiv (wp_wasm_empty_ctx_frame _ _ _ _ _ _)).1
  iapply wp_frame_value _ _ (fun _ => iprop(True)) [.basic (.const v)] 1 fi f0 [v] (to_of_val (.immV [v])) rfl $$ Hf
  inext; ipureintro; trivial

end Examples

end IrisWasm.Examples
