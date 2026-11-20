/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Rules.IrisRules
import IrisWasm.Rules.IrisExampleHelper
import IrisWasm.Rules.Proofmode
import IrisWasm.Host.IrisHost
import Wasm.TypeCheckerReflectsTyping

/-! Port of `theories/iris/examples/iris_examples_factorial.v`. -/

/-- The factorial function (Coq `ssrnat.factorial`; absent from Lean core). -/
def Nat.factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * Nat.factorial n

namespace IrisWasm.Examples

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm IrisWasm
open scoped Iris.Std.PartialMap

/-! ### Local state example: factorial -/

@[rocq_alias iriswasm.factorial_instrs]
def factorialInstrs (fact : Nat) : List BasicInstruction :=
  [.getLocal 0,
   .const (xx 1),
   .relop .i32 (.i (.le .u)),
   .if_ (.tf [] [.i32])
     [.const (xx 1)]
     [.getLocal 0,
      .const (xx 1),
      .binop .i32 (.i .sub),
      .call fact,
      .getLocal 0,
      .binop .i32 (.i .mul)]]

@[rocq_alias iriswasm.factorial]
def factorial (fact : Nat) : Expr := toEList (factorialInstrs fact)

@[rocq_alias iriswasm.factPred]
theorem factPred (n : Nat) (h : 1 < n) : n * Nat.factorial (n - 1) = Nat.factorial n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rfl

private theorem relop_le1 (n : I32) :
    appRelop (.i (.le .u)) (.int32 n) (xx 1) = decide (n.toNat ≤ 1) := by
  simp only [appRelop, appRelopI, Wasm.Int.ileU, xx, Wasm.Int.intOfZ, Wasm.Int.repr]
  rw [BitVec.ult_eq_decide]
  by_cases h : n.toNat ≤ 1
  · simp [h]
  · simp [h]; omega

private theorem sub1_toNat (n : I32) (h : 1 < n.toNat) :
    (Wasm.Int.isub n (Wasm.Int.intOfZ 1)).toNat = n.toNat - 1 := by
  simp only [Wasm.Int.isub, Wasm.Int.intOfZ, Wasm.Int.repr]
  rw [BitVec.toNat_sub]
  simp
  omega

private theorem binop_mul_fact (n : I32) (h : 1 < n.toNat) :
    appBinop (.i .mul)
      (xx (Nat.factorial (Wasm.Int.natOfUint (Wasm.Int.isub n (Wasm.Int.intOfZ 1)))))
      (.int32 n) = some (xx (Nat.factorial (Wasm.Int.natOfUint n))) := by
  simp only [appBinop, appBinopI, Option.map, Option.some.injEq, xx, Value.int32.injEq,
    Wasm.Int.imul, Wasm.Int.natOfUint, sub1_toNat n h, Wasm.Int.intOfZ, Wasm.Int.repr,
    BitVec.ofInt_natCast]
  rw [← factPred _ h]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, Nat.mul_comm, Nat.mul_mod]

/-- The precondition of the recursive call. -/
private theorem fact_pred_overflow (n : I32) (h : 1 < n.toNat)
    (hov : (Nat.factorial (Wasm.Int.natOfUint n) : _root_.Int) < Wasm.Int.modulus 32) :
    (Nat.factorial (Wasm.Int.natOfUint (Wasm.Int.isub n (Wasm.Int.intOfZ 1))) : _root_.Int) <
      Wasm.Int.modulus 32 := by
  simp only [Wasm.Int.natOfUint, sub1_toNat n h] at hov ⊢
  have := factPred _ h
  have : Nat.factorial (n.toNat - 1) ≤ Nat.factorial n.toNat := by
    rw [← this]; exact Nat.le_mul_of_pos_left _ (by omega)
  omega

private theorem base_fact (n : I32) (h : n.toNat ≤ 1) :
    xx 1 = xx (Nat.factorial (Wasm.Int.natOfUint n)) := by
  simp only [Wasm.Int.natOfUint]
  rcases (by omega : n.toNat = 0 ∨ n.toNat = 1) with h | h <;> rw [h] <;> rfl

section Factorial
variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF]

private theorem wp_value_imm {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF} (vs : List Value)
    {e : Expr} (h : e = vToEList vs) : Φ (.immV vs) ⊢ WP e @ s ; E {{ Φ }} := by
  subst h
  exact IrisWp.wp_value (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) ⟨rfl⟩

private theorem wp_value_of {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF} (v : Val)
    {e : Expr} (h : e = ofVal v) : Φ v ⊢ WP e @ s ; E {{ Φ }} := by
  subst h
  exact IrisWp.wp_value (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) ⟨rfl⟩

private theorem wp_wand_s {s : Stuckness} {E : CoPset} {e : Expr} {Φ Ψ : Val → IProp GF} :
    WP e @ s ; E {{ Φ }} ⊢ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s ; E {{ Ψ }} :=
  IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)

/-- Invoking a native `[i32] → [i32]` function at `a` on the argument `m`, given a spec of its
body in the callee frame (the common part of Coq's proofs of the recursive calls). -/
private theorem wp_invoke_i32 (a : Nat) (i : Instance) (body : List BasicInstruction) (m : I32)
    (f0 : Frame) (w : Value) (R : IProp GF) :
    ⊢ (iprop(↪[frame] f0 -∗
      a ↦[wf] (.funcNative i (.tf [.i32] [.i32]) [] body) -∗
      ▷ (↪[frame] (⟨[.int32 m], i⟩ : Frame) -∗
          a ↦[wf] (.funcNative i (.tf [.i32] [.i32]) [] body) -∗
          WP (toEList body) {{ v, (⌜v = .immV [w]⌝ ∗ R) ∗ ↪[frame] (⟨[.int32 m], i⟩ : Frame) }}) -∗
      WP ([.basic (.const (.int32 m)), .invoke a] : Expr)
        {{ v, (⌜v = .immV [w]⌝ ∗ R) ∗ ↪[frame] f0 }}) : IProp GF) := by
  iintro Hf Ha Hbody
  take_drop_app_rewrite 1
  iapply wp_invoke_native _ _ _ [.basic (.const (.int32 m))] [.int32 m] [.i32] [.i32] [] a body i 1
    f0 (to_of_val (.immV [.int32 m])) rfl rfl $$ Hf Ha
  inext; iintro ⟨Hf, Ha⟩
  rw [show ([Value.int32 m] ++ nZeros []) = [.int32 m] from rfl]
  iapply (wp_frame_rewrite _ _ _ _ _ _).1
  iapply (wandIff_equiv (wp_wasm_empty_ctx_frame _ _ _ _ _ _)).2
  take_drop_app_rewrite 1
  let fi : Frame := ⟨[.int32 m], i⟩
  iapply wp_seq_ctx_frame _ _ _ (fun v => iprop(⌜v = .immV [w]⌝ ∗ R))
    _ _ 0 (.base [] []) 1 fi f0 fi ?_
  · intro LI hLI
    simp [lfilled, lfill, constList] at hLI
    subst hLI; simp [toVal, toValInstr, mergeValuesList]
  isplitr
  · iintro ⟨%H, -⟩; cases H
  isplitl [Hf]
  · iexact Hf
  isplitl [Ha Hbody]
  · iintro Hf
    take_drop_app_rewrite 0
    iapply wp_block ?_ ?_ ?_ ?_ $$ Hf <;> try (first | decide | rfl)
    inext; iintro Hf
    iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).2
    iapply wp_label_push_nil
    simp only [pushBase, List.nil_append]
    iapply iRewrite_nil_r_ctx
    iapply wp_seq_ctx _ _ _ (fun v => iprop((⌜v = .immV [w]⌝ ∗ R) ∗ ↪[frame] fi))
    isplitr
    · iintro ⟨⟨%H, -⟩, -⟩; cases H
    isplitl [Hf Ha Hbody]
    · iapply Hbody $$ Hf Ha
    iintro %v ⟨⟨%hv, HR⟩, Hf⟩
    subst hv
    simp only [ofVal, vToEList, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    iapply wp_val_return rfl $$ Hf
    iintro Hf
    iapply wp_value_imm [w] ?_ <;> try rfl
    iframe; ipureintro; rfl
  iintro %v ⟨⟨%hv, HR⟩, Hf⟩
  subst hv
  simp only [ofVal, vToEList, List.map_cons, List.map_nil, List.append_nil]
  iapply (wandIff_equiv (wp_wasm_empty_ctx_frame _ _ _ _ _ _)).1
  iapply wp_frame_value _ _ (fun v => iprop(⌜v = .immV [w]⌝ ∗ R)) [.basic (.const w)] 1 fi f0 [w]
    (to_of_val (.immV [w])) rfl $$ Hf
  inext; iframe; ipureintro; rfl

@[rocq_alias iriswasm.fact_val]
abbrev factVal (n : I32) : Val → IProp GF :=
  fun v => iprop(⌜v = .immV [xx (Nat.factorial (Wasm.Int.natOfUint n))]⌝)

@[rocq_alias iriswasm.factorial_spec]
theorem factorial_spec (fact : Nat) (n : I32) (i : Instance) (a : Nat) :
    (Nat.factorial (Wasm.Int.natOfUint n) : _root_.Int) < Wasm.Int.modulus 32 → -- no overflow
    i.funcs[fact]? = some a → -- factorial function is in the instance
    0 ≤ Wasm.Int.zOfUint n → -- the parameter must be positive
    ⊢ (iprop(↪[frame] (⟨[.int32 n], i⟩ : Frame) -∗
      a ↦[wf] (.funcNative i (.tf [.i32] [.i32]) [] (factorialInstrs fact)) -∗
      WP (factorial fact) {{ v, (factVal n v ∗
        a ↦[wf] (.funcNative i (.tf [.i32] [.i32]) [] (factorialInstrs fact))) ∗
        ↪[frame] (⟨[.int32 n], i⟩ : Frame) }}) : IProp GF) := by
  intro hov ha hpos
  suffices H : ⊢ (iprop(∀ n : I32,
      ⌜(Nat.factorial (Wasm.Int.natOfUint n) : _root_.Int) < Wasm.Int.modulus 32⌝ -∗
      ↪[frame] (⟨[.int32 n], i⟩ : Frame) -∗
      a ↦[wf] (.funcNative i (.tf [.i32] [.i32]) [] (factorialInstrs fact)) -∗
      WP (factorial fact) {{ v, (factVal n v ∗
        a ↦[wf] (.funcNative i (.tf [.i32] [.i32]) [] (factorialInstrs fact))) ∗
        ↪[frame] (⟨[.int32 n], i⟩ : Frame) }}) : IProp GF) by
    iintro Hf Ha
    iapply H $$ %n %hov Hf Ha
  clear hov hpos n
  iloeb as IH
  iintro %n %hov Hf Ha
  let f : Frame := ⟨[.int32 n], i⟩
  have hfe : factorial fact = [.basic (.getLocal 0), .basic (.const (xx 1)),
      .basic (.relop .i32 (.i (.le .u))), .basic (.if_ (.tf [] [.i32]) [.const (xx 1)]
        [.getLocal 0, .const (xx 1), .binop .i32 (.i .sub), .call fact, .getLocal 0,
         .binop .i32 (.i .mul)])] := rfl
  rw [hfe]
  -- get_local 0
  take_drop_app_rewrite 1
  iapply wp_seq _ _ _ (fun v => iprop(⌜v = .immV [.int32 n]⌝ ∗ ↪[frame] f))
  isplitl []
  · iintro ⟨%H, -⟩; cases H
  isplitl [Hf]
  · iapply wp_get_local _ _ (.int32 n) 0 (fun w => iprop(⌜w = .immV [.int32 n]⌝)) f rfl $$ [] Hf
    inext; ipureintro; rfl
  iintro %w ⟨%hw, Hf⟩
  subst hw
  simp only [ofVal, vToEList, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  -- le
  take_drop_app_rewrite 3
  iapply wp_seq _ _ _ (fun v => iprop(⌜v = .immV [.int32 (wasmBool (decide (n.toNat ≤ 1)))]⌝ ∗
    ↪[frame] f))
  isplitl []
  · iintro ⟨%H, -⟩; cases H
  isplitl [Hf]
  · iapply wp_relop (relop_le1 n) $$ Hf
    inext; ipureintro; rfl
  iintro %w ⟨%hw, Hf⟩
  subst hw
  simp only [ofVal, vToEList, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  -- case distinction
  by_cases hle : n.toNat ≤ 1
  · -- base case
    simp only [hle, decide_true]
    iapply wp_if_true (by decide) $$ Hf
    inext; iintro Hf
    iapply iRewrite_nil_l
    iapply wp_block ?_ ?_ ?_ ?_ $$ Hf <;> try (first | decide | rfl)
    inext; iintro Hf
    iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).2
    iapply wp_label_push_nil
    simp only [pushBase, toEList, List.map_cons, List.map_nil, List.nil_append]
    iapply wp_val_return (by decide) $$ Hf
    iintro Hf
    iapply wp_value_imm [xx 1] ?_ <;> try rfl
    iframe
    unfold factVal
    ipureintro; rw [base_fact n hle]
  · -- inductive step
    have hlt : 1 < n.toNat := by omega
    simp only [hle, decide_false]
    iapply wp_if_false (c := wasmBool false) rfl $$ Hf
    inext; iintro Hf
    iapply iRewrite_nil_l
    iapply wp_block ?_ ?_ ?_ ?_ $$ Hf <;> try (first | decide | rfl)
    inext; iintro Hf
    iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).2
    iapply wp_label_push_nil
    simp only [pushBase, toEList, List.map_cons, List.map_nil, List.nil_append]
    -- get_local 0
    take_drop_app_rewrite 1
    iapply wp_seq_ctx _ _ _ (fun v => iprop(⌜v = .immV [.int32 n]⌝ ∗ ↪[frame] f))
    isplitr
    · iintro ⟨%H, -⟩; cases H
    isplitl [Hf]
    · iapply wp_get_local _ _ (.int32 n) 0 (fun w => iprop(⌜w = .immV [.int32 n]⌝)) f rfl $$ [] Hf
      inext; ipureintro; rfl
    iintro %w ⟨%hw, Hf⟩
    subst hw
    simp only [ofVal, vToEList, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    -- sub
    take_drop_app_rewrite 3
    let n' := Wasm.Int.isub n (Wasm.Int.intOfZ 1)
    iapply wp_seq_ctx _ _ _ (fun v => iprop(⌜v = .immV [.int32 n']⌝ ∗ ↪[frame] f))
    isplitr
    · iintro ⟨%H, -⟩; cases H
    isplitl [Hf]
    · iapply wp_binop (v := .int32 n') rfl $$ Hf
      inext; ipureintro; rfl
    iintro %w ⟨%hw, Hf⟩
    subst hw
    simp only [ofVal, vToEList, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    -- recursive call
    take_drop_app_rewrite 2
    iapply wp_seq_ctx _ _ _ (fun v => iprop((⌜v = .immV [xx (Nat.factorial (Wasm.Int.natOfUint n'))]⌝ ∗
      a ↦[wf] (.funcNative i (.tf [.i32] [.i32]) [] (factorialInstrs fact))) ∗ ↪[frame] f))
    isplitr
    · iintro ⟨⟨%H, -⟩, -⟩; cases H
    isplitl [Hf Ha IH]
    · iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).2
      take_drop_app_rewrite_twice 1 0
      iapply wp_base_push (by rfl)
      simp only [frameBase, List.nil_append, List.append_nil]
      iapply wp_call_ctx _ _ _ f fact a _ _ ha $$ Hf
      inext; iintro Hf
      iapply wp_base
      simp only [List.cons_append, List.nil_append, List.append_nil]
      iapply wp_invoke_i32 a i (factorialInstrs fact) n' f _ _ $$ Hf Ha
      inext; iintro Hf Ha
      rw [show toEList (factorialInstrs fact) = factorial fact from rfl, hfe]
      iapply IH $$ %n' %(fact_pred_overflow n hlt hov) Hf Ha
    iintro %w ⟨⟨%hw, Ha⟩, Hf⟩
    subst hw
    simp only [ofVal, vToEList, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    -- get_local 0
    take_drop_app_rewrite_twice 1 1
    iapply wp_base_push (by rfl)
    simp only [frameBase, List.nil_append, List.append_nil]
    take_drop_app_rewrite 1
    iapply wp_seq_ctx _ _ _ (fun v => iprop(⌜v = .immV [.int32 n]⌝ ∗ ↪[frame] f))
    isplitr
    · iintro ⟨%H, -⟩; cases H
    isplitl [Hf]
    · iapply wp_get_local _ _ (.int32 n) 0 (fun w => iprop(⌜w = .immV [.int32 n]⌝)) f rfl $$ [] Hf
      inext; ipureintro; rfl
    iintro %w ⟨%hw, Hf⟩
    subst hw
    -- mul
    iapply wp_base_pull
    simp only [pullBase, ofVal, vToEList, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, List.append_nil]
    take_drop_app_rewrite 3
    iapply wp_seq_ctx _ _ _ (fun v => iprop(⌜v = .immV [xx (Nat.factorial (Wasm.Int.natOfUint n))]⌝ ∗
      ↪[frame] f))
    isplitr
    · iintro ⟨%H, -⟩; cases H
    isplitl [Hf]
    · iapply wp_binop (binop_mul_fact n hlt) $$ Hf
      inext; ipureintro; rfl
    iintro %w ⟨%hw, Hf⟩
    subst hw
    simp only [ofVal, vToEList, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    iapply wp_val_return (by rfl) $$ Hf
    iintro Hf
    iapply wp_value_imm [xx (Nat.factorial (Wasm.Int.natOfUint n))] ?_ <;> try rfl
    iframe
    unfold factVal
    ipureintro; rfl

@[rocq_alias iriswasm.invoke_factorial_spec]
theorem invoke_factorial_spec (fact : Nat) (n : I32) (i : Instance) (a : Nat) (f0 : Frame) :
    (Nat.factorial (Wasm.Int.natOfUint n) : _root_.Int) < Wasm.Int.modulus 32 → -- no overflow
    i.funcs[fact]? = some a → -- factorial function is in the instance
    0 ≤ Wasm.Int.zOfUint n → -- the parameter must be positive
    ⊢ (iprop(↪[frame] f0 -∗
      a ↦[wf] (.funcNative i (.tf [.i32] [.i32]) [] (factorialInstrs fact)) -∗
      WP ([.basic (.const (.int32 n)), .invoke a] : Expr)
        {{ v, (⌜v = .immV [xx (Nat.factorial (Wasm.Int.natOfUint n))]⌝ ∗
          a ↦[wf] (.funcNative i (.tf [.i32] [.i32]) [] (factorialInstrs fact))) ∗
          ↪[frame] f0 }}) : IProp GF) := by
  intro hov ha hpos
  iintro Hf Ha
  iapply wp_invoke_i32 a i (factorialInstrs fact) n f0 _ _ $$ Hf Ha
  inext; iintro Hf Ha
  rw [show toEList (factorialInstrs fact) = factorial fact from rfl]
  iapply factorial_spec fact n i a hov ha hpos $$ Hf Ha

end Factorial

/-! ### Landin's knot example: factorial -/

@[rocq_alias iriswasm.myrec_instr]
def myrecInstr (hMutTab : Nat) : List BasicInstruction :=
  [.const (xx 0),
   .getLocal 0,
   .call hMutTab]

@[rocq_alias iriswasm.myrec]
def myrec (hMutTab : Nat) : Expr := toEList (myrecInstr hMutTab)

@[rocq_alias iriswasm.F_instr]
def fInstr (recTyp : Nat) : List BasicInstruction :=
  [.getLocal 0,
   .const (xx 1),
   .relop .i32 (.i (.le .u)),
   .if_ (.tf [] [.i32])
     [.const (xx 1)]
     [.getLocal 0,
      .const (xx 1),
      .binop .i32 (.i .sub),
      .const (xx 0),
      .callIndirect recTyp,
      .getLocal 0,
      .binop .i32 (.i .mul)]]

@[rocq_alias iriswasm.F]
def f (recTyp : Nat) : Expr := toEList (fInstr recTyp)

@[rocq_alias iriswasm.fact_instr]
def factInstr (F : Value) (myrec factTyp : Nat) : List BasicInstruction :=
  [.getLocal 0,
   .const F,
   .call myrec,
   .const (xx 0),
   .callIndirect factTyp]

@[rocq_alias iriswasm.fact]
def fact (F : Value) (myrec factTyp : Nat) : Expr := toEList (factInstr F myrec factTyp)

section Factorial
variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF]

@[rocq_alias iriswasm.F_spec]
theorem F_spec (fact recTyp tab : Nat) (n : I32) (i : Instance) (a : Nat) :
    (Nat.factorial (Wasm.Int.natOfUint n) : _root_.Int) < Wasm.Int.modulus 32 → -- no overflow
    0 ≤ Wasm.Int.zOfUint n → -- the parameter must be positive
    i.funcs[fact]? = some a → -- factorial function is in the instance
    i.types[recTyp]? = some (.tf [.i32] [.i32]) →
    i.tab[0]? = some tab →
    ⊢ (iprop(↪[frame] (⟨[.int32 n], i⟩ : Frame) -∗
      tab ↦[wt][ yy 0 ] (some a) -∗
      a ↦[wf] (.funcNative i (.tf [.i32] [.i32]) [] (fInstr recTyp)) -∗
      WP (f recTyp) {{ v, (factVal n v ∗
        tab ↦[wt][ yy 0 ] (some a) ∗
        a ↦[wf] (.funcNative i (.tf [.i32] [.i32]) [] (fInstr recTyp))) ∗
        ↪[frame] (⟨[.int32 n], i⟩ : Frame) }}) : IProp GF) := by
  intro hov hpos ha htyp htab
  suffices H : ⊢ (iprop(∀ n : I32,
      ⌜(Nat.factorial (Wasm.Int.natOfUint n) : _root_.Int) < Wasm.Int.modulus 32⌝ -∗
      ↪[frame] (⟨[.int32 n], i⟩ : Frame) -∗
      tab ↦[wt][ yy 0 ] (some a) -∗
      a ↦[wf] (.funcNative i (.tf [.i32] [.i32]) [] (fInstr recTyp)) -∗
      WP (f recTyp) {{ v, (factVal n v ∗
        tab ↦[wt][ yy 0 ] (some a) ∗
        a ↦[wf] (.funcNative i (.tf [.i32] [.i32]) [] (fInstr recTyp))) ∗
        ↪[frame] (⟨[.int32 n], i⟩ : Frame) }}) : IProp GF) by
    iintro Hf Htab Ha
    iapply H $$ %n %hov Hf Htab Ha
  clear hov hpos n
  iloeb as IH
  iintro %n %hov Hf Htab Ha
  rw [show yy 0 = Wasm.Int.natOfUint (Wasm.Int.intOfZ (w := 32) 0) from rfl]
  let fr : Frame := ⟨[.int32 n], i⟩
  have hfe : f recTyp = [.basic (.getLocal 0), .basic (.const (xx 1)),
      .basic (.relop .i32 (.i (.le .u))), .basic (.if_ (.tf [] [.i32]) [.const (xx 1)]
        [.getLocal 0, .const (xx 1), .binop .i32 (.i .sub), .const (xx 0), .callIndirect recTyp,
         .getLocal 0,
         .binop .i32 (.i .mul)])] := rfl
  rw [hfe]
  -- get_local 0
  take_drop_app_rewrite 1
  iapply wp_seq _ _ _ (fun v => iprop(⌜v = .immV [.int32 n]⌝ ∗ ↪[frame] fr))
  isplitl []
  · iintro ⟨%H, -⟩; cases H
  isplitl [Hf]
  · iapply wp_get_local _ _ (.int32 n) 0 (fun w => iprop(⌜w = .immV [.int32 n]⌝)) fr rfl $$ [] Hf
    inext; ipureintro; rfl
  iintro %w ⟨%hw, Hf⟩
  subst hw
  simp only [ofVal, vToEList, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  -- le
  take_drop_app_rewrite 3
  iapply wp_seq _ _ _ (fun v => iprop(⌜v = .immV [.int32 (wasmBool (decide (n.toNat ≤ 1)))]⌝ ∗
    ↪[frame] fr))
  isplitl []
  · iintro ⟨%H, -⟩; cases H
  isplitl [Hf]
  · iapply wp_relop (relop_le1 n) $$ Hf
    inext; ipureintro; rfl
  iintro %w ⟨%hw, Hf⟩
  subst hw
  simp only [ofVal, vToEList, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  -- case distinction
  by_cases hle : n.toNat ≤ 1
  · -- base case
    simp only [hle, decide_true]
    iapply wp_if_true (by decide) $$ Hf
    inext; iintro Hf
    iapply iRewrite_nil_l
    iapply wp_block ?_ ?_ ?_ ?_ $$ Hf <;> try (first | decide | rfl)
    inext; iintro Hf
    iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).2
    iapply wp_label_push_nil
    simp only [pushBase, toEList, List.map_cons, List.map_nil, List.nil_append]
    iapply wp_val_return (by decide) $$ Hf
    iintro Hf
    iapply wp_value_imm [xx 1] ?_ <;> try rfl
    iframe
    unfold factVal
    ipureintro; rw [base_fact n hle]
  · -- inductive step
    have hlt : 1 < n.toNat := by omega
    simp only [hle, decide_false]
    iapply wp_if_false (c := wasmBool false) rfl $$ Hf
    inext; iintro Hf
    iapply iRewrite_nil_l
    iapply wp_block ?_ ?_ ?_ ?_ $$ Hf <;> try (first | decide | rfl)
    inext; iintro Hf
    iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).2
    iapply wp_label_push_nil
    simp only [pushBase, toEList, List.map_cons, List.map_nil, List.nil_append]
    -- get_local 0
    take_drop_app_rewrite 1
    iapply wp_seq_ctx _ _ _ (fun v => iprop(⌜v = .immV [.int32 n]⌝ ∗ ↪[frame] fr))
    isplitr
    · iintro ⟨%H, -⟩; cases H
    isplitl [Hf]
    · iapply wp_get_local _ _ (.int32 n) 0 (fun w => iprop(⌜w = .immV [.int32 n]⌝)) fr rfl $$ [] Hf
      inext; ipureintro; rfl
    iintro %w ⟨%hw, Hf⟩
    subst hw
    simp only [ofVal, vToEList, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    -- sub
    take_drop_app_rewrite 3
    let n' := Wasm.Int.isub n (Wasm.Int.intOfZ 1)
    iapply wp_seq_ctx _ _ _ (fun v => iprop(⌜v = .immV [.int32 n']⌝ ∗ ↪[frame] fr))
    isplitr
    · iintro ⟨%H, -⟩; cases H
    isplitl [Hf]
    · iapply wp_binop (v := .int32 n') rfl $$ Hf
      inext; ipureintro; rfl
    iintro %w ⟨%hw, Hf⟩
    subst hw
    simp only [ofVal, vToEList, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    -- recursive call: now happens indirectly through the higher order store
    take_drop_app_rewrite 3
    iapply wp_seq_ctx _ _ _ (fun v => iprop((⌜v = .immV [xx (Nat.factorial (Wasm.Int.natOfUint n'))]⌝ ∗
      tab ↦[wt][ Wasm.Int.natOfUint (Wasm.Int.intOfZ (w := 32) 0) ] (some a) ∗
      a ↦[wf] (.funcNative i (.tf [.i32] [.i32]) [] (fInstr recTyp))) ∗ ↪[frame] fr))
    isplitr
    · iintro ⟨⟨%H, -⟩, -⟩; cases H
    isplitl [Hf Htab Ha IH]
    · iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).2
      take_drop_app_rewrite_twice 1 0
      iapply wp_base_push (by rfl)
      simp only [frameBase, List.nil_append, List.append_nil]
      rw [show xx 0 = .int32 (Wasm.Int.intOfZ 0) from rfl]
      iapply wp_call_indirect_success_ctx _ _ _ fr recTyp tab a (Wasm.Int.intOfZ 0)
        (.funcNative i (.tf [.i32] [.i32]) [] (fInstr recTyp)) _ _ htyp htab $$ Htab Ha Hf
      inext; iintro ⟨Htab, Ha, Hf⟩
      iapply wp_base
      simp only [List.cons_append, List.nil_append, List.append_nil]
      iapply wp_invoke_i32 a i (fInstr recTyp) n' fr _
        iprop(tab ↦[wt][ Wasm.Int.natOfUint (Wasm.Int.intOfZ (w := 32) 0) ] (some a) ∗
        a ↦[wf] (.funcNative i (.tf [.i32] [.i32]) [] (fInstr recTyp))) $$ Hf Ha
      inext; iintro Hf Ha
      rw [show toEList (fInstr recTyp) = f recTyp from rfl, hfe,
        show xx 0 = .int32 (Wasm.Int.intOfZ 0) from rfl]
      iapply IH $$ %n' %(fact_pred_overflow n hlt hov) Hf Htab Ha
    iintro %w ⟨⟨%hw, Htab, Ha⟩, Hf⟩
    subst hw
    simp only [ofVal, vToEList, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    -- get_local 0
    take_drop_app_rewrite_twice 1 1
    iapply wp_base_push (by rfl)
    simp only [frameBase, List.nil_append, List.append_nil]
    take_drop_app_rewrite 1
    iapply wp_seq_ctx _ _ _ (fun v => iprop(⌜v = .immV [.int32 n]⌝ ∗ ↪[frame] fr))
    isplitr
    · iintro ⟨%H, -⟩; cases H
    isplitl [Hf]
    · iapply wp_get_local _ _ (.int32 n) 0 (fun w => iprop(⌜w = .immV [.int32 n]⌝)) fr rfl $$ [] Hf
      inext; ipureintro; rfl
    iintro %w ⟨%hw, Hf⟩
    subst hw
    -- mul
    iapply wp_base_pull
    simp only [pullBase, ofVal, vToEList, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, List.append_nil]
    take_drop_app_rewrite 3
    iapply wp_seq_ctx _ _ _ (fun v => iprop(⌜v = .immV [xx (Nat.factorial (Wasm.Int.natOfUint n))]⌝ ∗
      ↪[frame] fr))
    isplitr
    · iintro ⟨%H, -⟩; cases H
    isplitl [Hf]
    · iapply wp_binop (binop_mul_fact n hlt) $$ Hf
      inext; ipureintro; rfl
    iintro %w ⟨%hw, Hf⟩
    subst hw
    simp only [ofVal, vToEList, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    iapply wp_val_return (by rfl) $$ Hf
    iintro Hf
    iapply wp_value_imm [xx (Nat.factorial (Wasm.Int.natOfUint n))] ?_ <;> try rfl
    iframe
    unfold factVal
    ipureintro; rfl

@[rocq_alias iriswasm.myrec_spec]
theorem myrec_spec (hMutTab a : Nat) (mutTab : Hostfuncidx) (fidx : Value) (i : Instance) :
    i.funcs[hMutTab]? = some a → -- modify table host call is in the instance
    ⊢ (iprop(↪[frame] (⟨[fidx], i⟩ : Frame) -∗
      a ↦[wf] (.funcHost (.tf [.i32, .i32] []) mutTab) -∗
      WP (myrec hMutTab) {{ v, (⌜v = .callHostV (.tf [.i32, .i32] []) mutTab [xx 0, fidx]
          (.base [] [])⌝ ∗
        a ↦[wf] (.funcHost (.tf [.i32, .i32] []) mutTab)) ∗
        ↪[frame] (⟨[fidx], i⟩ : Frame) }}) : IProp GF) := by
  intro hh
  iintro Hf Ha
  let fr : Frame := ⟨[fidx], i⟩
  rw [show myrec hMutTab = [.basic (.const (xx 0)), .basic (.getLocal 0), .basic (.call hMutTab)]
    from rfl]
  take_drop_app_rewrite_twice 1 1
  iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).2
  iapply wp_base_push (by rfl)
  simp only [frameBase, List.nil_append, List.append_nil]
  take_drop_app_rewrite 1
  -- get_local 0
  iapply wp_seq_ctx _ _ _ (fun v => iprop(⌜v = .immV [fidx]⌝ ∗ ↪[frame] fr))
  isplitr
  · iintro ⟨%H, -⟩; cases H
  isplitl [Hf]
  · iapply wp_get_local _ _ fidx 0 (fun w => iprop(⌜w = .immV [fidx]⌝)) fr rfl $$ [] Hf
    inext; ipureintro; rfl
  iintro %w ⟨%hw, Hf⟩
  subst hw
  iapply wp_base_pull
  simp only [pullBase, ofVal, vToEList, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.append_nil]
  take_drop_app_rewrite_twice 2 0
  iapply wp_base_push (by rfl)
  simp only [frameBase, List.nil_append, List.append_nil]
  iapply wp_call_ctx _ _ _ fr hMutTab a _ _ hh $$ Hf
  inext; iintro Hf
  iapply wp_base_pull
  simp only [pullBase, List.cons_append, List.nil_append, List.append_nil]
  iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).1
  take_drop_app_rewrite 2
  iapply wp_invoke_host _ _ [.basic (.const (xx 0)), .basic (.const fidx)] [xx 0, fidx] 2 [.i32, .i32] [] a mutTab fr _ rfl rfl rfl $$ Ha Hf
  inext; iintro Ha Hf
  iapply wp_value_of (.callHostV (.tf [.i32, .i32] []) mutTab [xx 0, fidx] (.base [] [])) ?_ <;>
    try rfl
  iframe; ipureintro; rfl

end Factorial

/-! ### The host program -/

@[rocq_alias iriswasm.main_instr]
def mainInstr (fact glob : Nat) : List BasicInstruction :=
  [.getGlobal glob,
   .call fact,
   .setGlobal glob]

@[rocq_alias iriswasm.main]
def main (fact glob : Nat) : Expr := toEList (mainInstr fact glob)

section FactorialHostMain
variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF] [HvisG GF] [HmsG GF] [HasG GF]

@[rocq_alias iriswasm.main_host_spec]
theorem main_host_spec (fact glob : Nat) (F : I32) (myrec tab mutTab fFact fF fMyrec fMutTab
    gGlob tFactTyp mt : Nat) (i : Instance) (tabval : Funcelem) (n : I32) (idnstart : Nat)
    (f : Frame) (Φ : HostVal → IProp GF) :
    i.funcs[fact]? = some fFact →
    i.funcs[Wasm.Int.natOfUint F]? = some fF →
    i.funcs[myrec]? = some fMyrec →
    i.funcs[mutTab]? = some fMutTab →
    i.types[tFactTyp]? = some (.tf [.i32] [.i32]) →
    i.tab[0]? = some tab →
    i.globs[glob]? = some gGlob →
    (Nat.factorial (Wasm.Int.natOfUint n) : _root_.Int) < Wasm.Int.modulus 32 → -- no overflow
    0 ≤ Wasm.Int.zOfUint n → -- the parameter must be positive
    ⊢ (iprop((∀ v : HostVal, ⌜v = .immHV []⌝ ∗
        (∃ w : Value, factVal n (.immV [w]) ∗ gGlob ↦[wg] (⟨.mut, w⟩ : Global)) -∗ Φ v) -∗
      ↪[frame] f -∗
      fFact ↦[wf] (.funcNative i (.tf [.i32] [.i32]) [] (factInstr (.int32 F) myrec tFactTyp)) -∗
      fF ↦[wf] (.funcNative i (.tf [.i32] [.i32]) [] (fInstr tFactTyp)) -∗
      fMyrec ↦[wf] (.funcNative i (.tf [.i32] []) [] (myrecInstr mutTab)) -∗
      fMutTab ↦[wf] (.funcHost (.tf [.i32, .i32] []) (.hostfuncidx mt)) -∗
      mt ↦[ha] HostAction.modifyTable -∗
      tab ↦[wt][ yy 0 ] tabval -∗
      gGlob ↦[wg] (⟨.mut, .int32 n⟩ : Global) -∗
      idnstart ↦[wf] (.funcNative i (.tf [] []) [] (mainInstr fact glob)) -∗
      WP (([], [.invoke idnstart]) : HostExpr) {{ Φ }}) : IProp GF) := by
  intro hfact hF hmyrec hmut htyp htab hglob hov hpos
  iintro HΦ Hf Hfact HF Hmyrec Hmut Hmt Htab Hg Hstart
  rw [show yy 0 = Wasm.Int.nOfUint (Wasm.Int.intOfZ (w := 32) 0) from rfl]
  -- host bind
  iapply wp_lift_wasm
  -- invoke main
  take_drop_app_rewrite 0
  iapply wp_invoke_native _ _ _ [] [] [] [] [] idnstart (mainInstr fact glob) i 0 f
    (to_of_val (.immV [])) rfl rfl $$ Hf Hstart
  inext; iintro ⟨Hf, Hstart⟩
  rw [show ([] ++ nZeros []) = ([] : List Value) from rfl]
  let fm : Frame := ⟨[], i⟩
  -- local bind
  iapply (wp_frame_rewrite _ _ _ _ _ _).1
  iapply wp_frame_bind _ _ _ 0 fm f _ (by simp [toVal, toValInstr, mergeValuesList]) $$ Hf
  iintro Hf
  -- block
  take_drop_app_rewrite 0
  iapply wp_block ?_ ?_ ?_ ?_ $$ Hf <;> try (first | decide | rfl)
  inext; iintro Hf
  -- label bind
  rw [show ([] : List AdministrativeInstruction) ++ toEList (mainInstr fact glob) =
    [.basic (.getGlobal glob), .basic (.call fact), .basic (.setGlobal glob)] from rfl]
  iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).2
  iapply wp_label_push_nil
  simp only [pushBase]
  iapply wp_label_bind
  -- get_global
  bind_seq_base_imm [AdministrativeInstruction.basic (.getGlobal glob)] with [Hg Hf]
  · iapply wp_get_global _ _ (.int32 n) fm glob (fun w => iprop(⌜w = .immV [.int32 n]⌝))
      ⟨.mut, .int32 n⟩ gGlob hglob rfl $$ [] Hf Hg
    inext; ipureintro; rfl
  iintro %w ⟨%hw, Hg, Hf⟩
  subst hw
  simp only [ofVal, vToEList, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  -- call fact
  build_ctx [AdministrativeInstruction.basic (.call fact)]
  iapply wp_call_ctx _ _ _ fm fact fFact _ _ hfact $$ Hf
  inext; iintro Hf
  deconstruct_ctx
  -- invoke f_fact
  let ff : Frame := ⟨[.int32 n], i⟩
  let fr : Frame := ⟨[.int32 F], i⟩
  let tfH : FunctionType := .tf [.i32, .i32] []
  let hcv : List Value := [xx 0, .int32 F]
  let llMyrec : Llholed := .local [] 0 fr (.label [] 0 [] (.base [] []) []) []
  let llY : Llholed := .local [.int32 n] 0 fr (.label [] 0 [] (.base [] []) [])
    [.basic (.const (xx 0)), .basic (.callIndirect tFactTyp)]
  let llX : Llholed := .label [] 1 [] llY []
  let llFact : Llholed := .local [] 1 ff llX []
  let llZ : Llholed := .local [] 1 ff llX [.basic (.setGlobal glob)]
  let llMain : Llholed := .local [] 0 fm (.label [] 0 [] llZ []) []
  iapply bind_seq_base_callhost [.basic (.const (.int32 n)), .invoke fFact]
    (fun _ => iprop(tab ↦[wt][ Wasm.Int.nOfUint (Wasm.Int.intOfZ (w := 32) 0) ] tabval ∗
      fFact ↦[wf] (.funcNative i (.tf [.i32] [.i32]) [] (factInstr (.int32 F) myrec tFactTyp)) ∗
      fMyrec ↦[wf] (.funcNative i (.tf [.i32] []) [] (myrecInstr mutTab)) ∗
      fMutTab ↦[wf] (.funcHost (.tf [.i32, .i32] []) (.hostfuncidx mt)) ∗ ↪[frame] fm))
    _ [] [.basic (.setGlobal glob)] _ _ _ tfH (.hostfuncidx mt) hcv llFact inferInstance
    $$ [Hf Hfact Hmyrec Htab Hmut]
  · -- f_fact
    take_drop_app_rewrite 1
    iapply wp_invoke_native _ _ _ [.basic (.const (.int32 n))] [.int32 n] [.i32] [.i32] [] fFact
      (factInstr (.int32 F) myrec tFactTyp) i 1 fm (to_of_val (.immV [.int32 n])) rfl rfl
      $$ Hf Hfact
    inext; iintro ⟨Hf, Hfact⟩
    rw [show ([Value.int32 n] ++ nZeros []) = [.int32 n] from rfl]
    iapply (wp_frame_rewrite _ _ _ _ _ _).1
    iapply wp_frame_bind _ _ _ 1 ff fm _ (by simp [toVal, toValInstr, mergeValuesList]) $$ Hf
    iintro Hf
    take_drop_app_rewrite 0
    iapply wp_block ?_ ?_ ?_ ?_ $$ Hf <;> try (first | decide | rfl)
    inext; iintro Hf
    rw [show ([] : List AdministrativeInstruction) ++ toEList (factInstr (.int32 F) myrec tFactTyp) =
      [.basic (.getLocal 0), .basic (.const (.int32 F)), .basic (.call myrec),
        .basic (.const (xx 0)), .basic (.callIndirect tFactTyp)] from rfl]
    iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).2
    iapply wp_label_push_nil
    simp only [pushBase]
    iapply wp_label_bind
    -- get_local 0
    bind_seq_base_imm [AdministrativeInstruction.basic (.getLocal 0)] with [Hf]
    · iapply wp_get_local _ _ (.int32 n) 0 (fun w => iprop(⌜w = .immV [.int32 n]⌝)) ff rfl $$ [] Hf
      inext; ipureintro; rfl
    iintro %w ⟨%hw, Hf⟩
    subst hw
    simp only [ofVal, vToEList, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    -- call myrec
    build_ctx [AdministrativeInstruction.basic (.call myrec)]
    iapply wp_call_ctx _ _ _ ff myrec fMyrec _ _ hmyrec $$ Hf
    inext; iintro Hf
    deconstruct_ctx
    -- invoke f_myrec
    iapply bind_seq_base_callhost [.basic (.const (.int32 F)), .invoke fMyrec]
      (fun _ => iprop(fMyrec ↦[wf] (.funcNative i (.tf [.i32] []) [] (myrecInstr mutTab)) ∗
        fMutTab ↦[wf] (.funcHost (.tf [.i32, .i32] []) (.hostfuncidx mt)) ∗ ↪[frame] ff))
      _ [.int32 n] [.basic (.const (xx 0)), .basic (.callIndirect tFactTyp)] _ _ _ tfH
      (.hostfuncidx mt) hcv llMyrec inferInstance $$ [Hf Hmyrec Hmut]
    · -- myrec
      take_drop_app_rewrite 1
      iapply wp_invoke_native _ _ _ [.basic (.const (.int32 F))] [.int32 F] [.i32] [] [] fMyrec
        (myrecInstr mutTab) i 0 ff (to_of_val (.immV [.int32 F])) rfl rfl $$ Hf Hmyrec
      inext; iintro ⟨Hf, Hmyrec⟩
      rw [show ([Value.int32 F] ++ nZeros []) = [.int32 F] from rfl]
      iapply (wp_frame_rewrite _ _ _ _ _ _).1
      iapply wp_frame_bind _ _ _ 0 fr ff _ (by simp [toVal, toValInstr, mergeValuesList]) $$ Hf
      iintro Hf
      take_drop_app_rewrite 0
      iapply wp_block ?_ ?_ ?_ ?_ $$ Hf <;> try (first | decide | rfl)
      inext; iintro Hf
      rw [show ([] : List AdministrativeInstruction) ++ toEList (myrecInstr mutTab) = IrisWasm.Examples.myrec mutTab
        from rfl]
      iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).2
      iapply wp_label_push_nil
      simp only [pushBase]
      iapply wp_label_bind
      iapply wp_wand_s (Φ := fun v => iprop((⌜v = .callHostV (.tf [.i32, .i32] []) (.hostfuncidx mt)
          [xx 0, .int32 F] (.base [] [])⌝ ∗
        fMutTab ↦[wf] (.funcHost (.tf [.i32, .i32] []) (.hostfuncidx mt))) ∗
        ↪[frame] (⟨[.int32 F], i⟩ : Frame))) $$ [Hf Hmut]
      · iapply myrec_spec mutTab fMutTab (.hostfuncidx mt) (.int32 F) i hmut $$ Hf Hmut
      iintro %v ⟨⟨%hv, Hmut⟩, Hf⟩
      subst hv
      deconstruct_ctx
      iapply wp_value_of (.callHostV tfH (.hostfuncidx mt) hcv (.label [] 0 [] (.base [] []) [])) ?_ <;> try rfl
      iexists fr
      isplitr [Hf]
      · iintro Hf
        iapply (wp_frame_rewrite _ _ _ _ _ _).2
        iapply wp_value_of (.callHostV tfH (.hostfuncidx mt) hcv llMyrec) ?_ <;> try rfl
        isplitr
        · ipureintro; rfl
        iframe
      iexact Hf
    iintro %v ⟨%hv, Hmyrec, Hmut, Hf⟩
    subst hv
    iapply wp_value_of (.callHostV tfH (.hostfuncidx mt) hcv llY) ?_ <;> try rfl
    deconstruct_ctx
    iapply wp_value_of (.callHostV tfH (.hostfuncidx mt) hcv llX) ?_ <;> try rfl
    iexists ff
    isplitr [Hf]
    · iintro Hf
      iapply (wp_frame_rewrite _ _ _ _ _ _).2
      iapply wp_value_of (.callHostV tfH (.hostfuncidx mt) hcv llFact) ?_ <;> try rfl
      isplitr
      · ipureintro; rfl
      iframe
    iexact Hf
  iintro %v ⟨%hv, Htab, Hfact, Hmyrec, Hmut, Hf⟩
  subst hv
  iapply wp_value_of (.callHostV tfH (.hostfuncidx mt) hcv llZ) ?_ <;> try rfl
  deconstruct_ctx
  iapply wp_value_of (.callHostV tfH (.hostfuncidx mt) hcv (.label [] 0 [] llZ [])) ?_ <;> try rfl
  iexists fm
  isplitr [Hf]
  · iintro Hf
    iapply (wp_frame_rewrite _ _ _ _ _ _).2
    iapply wp_value_of (.callHostV tfH (.hostfuncidx mt) hcv llMain) ?_ <;> try rfl
    -- host call: modify_table
    iapply wp_call_host_modify_table _ _ (.hostfuncidx mt) mt (Wasm.Int.intOfZ 0) F
      (llfill llMain [.callHost tfH (.hostfuncidx mt) hcv]) (llfill llMain []) llMain f tab tabval
      [] fF Φ rfl rfl rfl hF htab
    isplitl [Hf]
    · iexact Hf
    isplitl [Hmt]
    · iexact Hmt
    isplitl [Htab]
    · iexact Htab
    inext; iintro ⟨Hf, Hmt, Htab⟩
    iapply wp_lift_wasm
    rw [show llfill llMain [] = [.local 0 fm [.label 0 [] [.local 1 ff [.label 1 []
      [.basic (.const (.int32 n)), .local 0 fr [.label 0 [] []], .basic (.const (xx 0)),
        .basic (.callIndirect tFactTyp)]], .basic (.setGlobal glob)]]] from rfl]
    iapply (wp_frame_rewrite _ _ _ _ _ _).1
    iapply wp_frame_bind _ _ _ 0 fm f _
      (by simp [toVal, toValInstr, mergeValuesList, mergeValues, valNotValCombine]) $$ Hf
    iintro Hf
    iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).2
    iapply wp_label_push_nil
    simp only [pushBase]
    iapply wp_label_bind
    iapply bind_seq_base_imm [AdministrativeInstruction.local 1 ff [.label 1 []
        [.basic (.const (.int32 n)), .local 0 fr [.label 0 [] []], .basic (.const (xx 0)),
          .basic (.callIndirect tFactTyp)]]]
      (fun _ => iprop(tab ↦[wt][ yy 0 ] (some fF) ∗
        fF ↦[wf] (.funcNative i (.tf [.i32] [.i32]) [] (fInstr tFactTyp)) ∗ ↪[frame] fm))
      _ [] [.basic (.setGlobal glob)] _ _ _ [xx (Nat.factorial (Wasm.Int.natOfUint n))]
      inferInstance $$ [Hf Htab HF]
    · iapply (wp_frame_rewrite _ _ _ _ _ _).1
      iapply wp_frame_bind _ _ _ 1 ff fm _
        (by simp [toVal, toValInstr, mergeValuesList, mergeValues, valNotValCombine]) $$ Hf
      iintro Hf
      iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).2
      iapply wp_label_push_nil
      simp only [pushBase]
      iapply wp_label_bind
      iapply bind_seq_base_imm [AdministrativeInstruction.local 0 fr [.label 0 [] []]]
        (fun _ => iprop(↪[frame] ff)) _ [.int32 n]
        [.basic (.const (xx 0)), .basic (.callIndirect tFactTyp)] _ _ _ [] inferInstance $$ [Hf]
      · iapply (wp_frame_rewrite _ _ _ _ _ _).1
        iapply wp_frame_bind _ _ _ 0 fr ff _ (by simp [toVal, toValInstr, mergeValuesList]) $$ Hf
        iintro Hf
        iapply wp_wand_s (Φ := fun v => iprop(⌜v = .immV []⌝ ∗ ↪[frame] fr)) $$ [Hf]
        · iapply wp_label_value (es := []) (v := []) (by simp [toVal, mergeValuesList]) $$ Hf
          inext; ipureintro; rfl
        iintro %v ⟨%hv, Hf⟩
        subst hv
        iexists fr
        isplitr [Hf]
        · iintro Hf
          iapply wp_frame_value _ _ (fun v => iprop(⌜v = .immV []⌝)) _ 0 fr ff []
            (to_of_val (.immV [])) rfl $$ Hf
          inext; ipureintro; rfl
        iexact Hf
      iintro %v ⟨%hv, Hf⟩
      subst hv
      simp only [ofVal, vToEList, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
        List.append_nil]
      -- call_indirect
      build_ctx [AdministrativeInstruction.basic (.const (xx 0)), .basic (.callIndirect tFactTyp)]
      rw [show xx 0 = Value.int32 (Wasm.Int.intOfZ 0) from rfl]
      iapply wp_call_indirect_success_ctx _ _ _ ff tFactTyp tab fF (Wasm.Int.intOfZ 0)
        (.funcNative i (.tf [.i32] [.i32]) [] (fInstr tFactTyp)) _ _ htyp htab $$ Htab HF Hf
      inext; iintro ⟨Htab, HF, Hf⟩
      deconstruct_ctx
      -- invoke f_F
      iapply wp_wand_s (Φ := fun v => iprop((⌜v = .immV [xx (Nat.factorial (Wasm.Int.natOfUint n))]⌝ ∗
          (tab ↦[wt][ yy 0 ] (some fF) ∗
            fF ↦[wf] (.funcNative i (.tf [.i32] [.i32]) [] (fInstr tFactTyp)))) ∗ ↪[frame] ff))
        $$ [Htab HF Hf]
      · iapply wp_invoke_i32 fF i (fInstr tFactTyp) n ff _ _ $$ Hf HF
        inext; iintro Hf HF
        rw [show toEList (fInstr tFactTyp) = IrisWasm.Examples.f tFactTyp from rfl]
        rw [show Wasm.Int.natOfUint (Wasm.Int.intOfZ (w := 32) 0) = yy 0 from rfl]
        iapply F_spec (Wasm.Int.natOfUint F) tFactTyp tab n i fF hov hpos hF htyp htab $$ Hf Htab HF
      iintro %v ⟨⟨%hv, Htab, HF⟩, Hf⟩
      subst hv
      simp only [List.map_cons, List.map_nil]
      iapply wp_val_return rfl $$ Hf
      iintro Hf
      iapply wp_value_imm [xx (Nat.factorial (Wasm.Int.natOfUint n))] ?_ <;> try rfl
      iexists ff
      isplitr [Hf]
      · iintro Hf
        iapply (wp_frame_rewrite _ _ _ _ _ _).2
        iapply wp_wand_s (Φ := fun v =>
          iprop(⌜v = .immV [xx (Nat.factorial (Wasm.Int.natOfUint n))]⌝ ∗ ↪[frame] fm)) $$ [Hf]
        · iapply (wp_frame_rewrite _ _ _ _ _ _).1
          simp only [List.map_cons, List.map_nil]
          iapply wp_frame_value _ _
            (fun v => iprop(⌜v = .immV [xx (Nat.factorial (Wasm.Int.natOfUint n))]⌝))
            [.basic (.const (xx (Nat.factorial (Wasm.Int.natOfUint n))))] 1 ff fm _
            (to_of_val (.immV [xx (Nat.factorial (Wasm.Int.natOfUint n))])) rfl $$ Hf
          inext; ipureintro; rfl
        iintro %v ⟨%hv, Hf⟩
        isplitr
        · ipureintro; exact hv
        iframe
      iexact Hf
    iintro %v ⟨%hv, Htab, HF, Hf⟩
    subst hv
    simp only [ofVal, vToEList, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    iapply wp_wand_s (Φ := fun v => iprop(⌜v = .immV []⌝ ∗
      gGlob ↦[wg] (⟨(⟨.mut, .int32 n⟩ : Global).mut_, xx (Nat.factorial (Wasm.Int.natOfUint n))⟩ :
        Global) ∗ ↪[frame] fm)) $$ [Hg Hf]
    · iapply wp_set_global _ _ (xx (Nat.factorial (Wasm.Int.natOfUint n))) fm glob
        (fun v => iprop(⌜v = .immV []⌝)) ⟨.mut, .int32 n⟩ gGlob hglob $$ [] Hf Hg
      inext; ipureintro; rfl
    iintro %v ⟨%hv, Hg, Hf⟩
    subst hv
    simp only [List.map_nil]
    iapply wp_val_return rfl $$ Hf
    iintro Hf
    iapply wp_value_imm [] ?_ <;> try rfl
    iexists fm
    isplitr [Hf]
    · iintro Hf
      iapply (wp_frame_rewrite _ _ _ _ _ _).2
      iapply wp_wand_s (Φ := fun v => iprop(⌜v = .immV []⌝ ∗ ↪[frame] f)) $$ [Hf]
      · iapply (wp_frame_rewrite _ _ _ _ _ _).1
        simp only [List.map_nil]
        iapply wp_frame_value _ _ (fun v => iprop(⌜v = .immV []⌝)) [] 0 fm f []
          (to_of_val (.immV [])) rfl $$ Hf
        inext; ipureintro; rfl
      iintro %v ⟨%hv, Hf⟩
      subst hv
      iapply IrisHost.wp_value _ _ _ (.immHV []) _ rfl
      iapply HΦ
      isplitr
      · ipureintro; rfl
      iexists xx (Nat.factorial (Wasm.Int.natOfUint n))
      isplitr
      · ipureintro; rfl
      iexact Hg
    iexact Hf
  iexact Hf

end FactorialHostMain

/-! ### Instantiation of the factorial module -/

/-- Coq `String.list_byte_of_string` (ASCII names as bytes). -/
private def listByteOfString (s : String) : Name := s.toUTF8.toList.map (·.toBitVec)

@[rocq_alias iriswasm.factorial_module]
def factorialModule : Module where
  types := [.tf [.i32] [.i32], .tf [.i32] [], .tf [.i32, .i32] [], .tf [] []]
  funcs :=
    [{ type := .typeidx 1, locals := [], body := myrecInstr 0 },
     { type := .typeidx 0, locals := [], body := fInstr 0 },
     { type := .typeidx 0, locals := [], body := factInstr (xx 2) 1 0 },
     { type := .typeidx 3, locals := [], body := mainInstr 3 0 }]
  tables := [{ type := { limits := { min := 1, max := none }, elemType := .funcref } }]
  mems := []
  globals := []
  elem := []
  data := []
  start := some ⟨.funcidx 4⟩
  imports :=
    [{ module := listByteOfString "Host", name := listByteOfString "modify_table",
       desc := .func 2 },
     { module := listByteOfString "Host", name := listByteOfString "ret",
       desc := .global { mut_ := .mut, t := .i32 } }]
  exports := []

@[rocq_alias iriswasm.factorial_impts]
def factorialImpts : List ExternT :=
  [.func (.tf [.i32, .i32] []), .glob { mut_ := .mut, t := .i32 }]

@[rocq_alias iriswasm.factorial_module_typing]
theorem factorial_module_typing : ModuleTyping factorialModule factorialImpts [] := by
  refine ⟨[.tf [.i32] [], .tf [.i32] [.i32], .tf [.i32] [.i32], .tf [] []], [], ?_⟩
  refine ⟨.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil))), rfl, rfl, .nil, by simp,
    by simp, rfl, .cons rfl (.cons rfl .nil), .nil⟩
  all_goals exact ⟨by decide, by decide, (b_e_type_checker_reflects_typing _ _ _).1 rfl⟩

@[rocq_alias iriswasm.factorial_module_instantiate]
def factorialModuleInstantiate : List HostE := [.instantiate [] 0 [0, 1]]

section FactorialHost
variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF] [HvisG GF] [HmsG GF] [HasG GF]

omit [HvisG GF] [HmsG GF] [HasG GF] in
/-- An empty resource map together with a true side condition (Lean helper). -/
private theorem empty_map_check {V : Type} (Φ : Nat → V → IProp GF) {φ : Prop} (hφ : φ) :
    ⊢ iprop(([∗map] k ↦ x ∈ (∅ : NatMap V), Φ k x) ∗ ⌜φ⌝) :=
  BI.emp_sep.2.trans (BI.sep_mono BI.BigSepM.bigSepM_empty_intro (BI.pure_intro hφ))

private theorem singleton_get {V : Type} (a : Nat) (v : V) :
    get? (PartialMap.singleton a v : NatMap V) a = some v :=
  get?_insert_eq rfl

private theorem singleton_dom {V : Type} (a : Nat) (v : V) (k : Nat) :
    PartialMap.dom (PartialMap.singleton a v : NatMap V) k ↔ k ∈ [a] := by
  by_cases h : a = k
  · subst h; simp [PartialMap.dom, singleton_get]
  · simp [PartialMap.dom, PartialMap.singleton, get?_insert_ne h, get?_empty, Ne.symm h]

/-- Coq's file-local notation `{{{{ P }}}} es {{{{ v, Q }}}}` is unfolded:
`□ ∀ Φ, P -∗ (∀ v, Q -∗ Φ v) -∗ WP (es : HostExpr) @ NotStuck ; ⊤ {{ v, Φ v }}`. -/
@[rocq_alias iriswasm.instantiate_factorial]
theorem instantiate_factorial (hidx gidx modTab : Nat) (n : I32) :
    (Nat.factorial (Wasm.Int.natOfUint n) : _root_.Int) < Wasm.Int.modulus 32 → -- no overflow
    0 ≤ Wasm.Int.zOfUint n → -- the parameter must be positive
    ⊢ (iprop(□ ∀ Φ : HostVal → IProp GF,
      (hidx ↦[wf] (.funcHost (.tf [.i32, .i32] []) (.hostfuncidx modTab)) ∗
        modTab ↦[ha] HostAction.modifyTable ∗
        gidx ↦[wg] (⟨.mut, .int32 n⟩ : Global) ∗
        0 ↪[mods] factorialModule ∗
        (∃ name, 0 ↪[vis] (⟨name, .func (.funcidx hidx)⟩ : ModuleExport)) ∗
        (∃ name, 1 ↪[vis] (⟨name, .global (.globalidx gidx)⟩ : ModuleExport)) ∗
        ↪[frame] emptyFrame) -∗
      (∀ v, (⌜v = .immHV []⌝ ∗ ∃ w, factVal n (.immV [w]) ∗
        gidx ↦[wg] (⟨.mut, w⟩ : Global)) -∗ Φ v) -∗
      WP ((factorialModuleInstantiate, []) : HostExpr) @ Stuckness.NotStuck ; ⊤ {{ v, Φ v }})
      : IProp GF) := by
  intro hov hpos
  imodintro
  iintro %Φ ⟨Hmodtab, HA, Hglob, Hmod, ⟨%name1, Hvis1⟩, ⟨%name2, Hvis2⟩, Hf⟩ HΦ
  unfold factorialModuleInstantiate
  iapply instantiation_spec_operational_start_seq .NotStuck ⊤ 0 [0, 1]
    [⟨name1, .func ⟨hidx⟩⟩, ⟨name2, .global ⟨gidx⟩⟩] [] factorialModule factorialImpts []
    (PartialMap.singleton hidx (.funcHost (.tf [.i32, .i32] []) (.hostfuncidx modTab)))
    ∅ ∅ (PartialMap.singleton gidx ⟨.mut, .int32 n⟩) 4 Φ [] rfl factorial_module_typing
    ⟨⟨[], rfl⟩, ⟨[], rfl⟩, ⟨[], rfl⟩⟩ $$ Hf [Hmod Hvis1 Hvis2 Hmodtab Hglob]
  · unfold instantiationResourcesPre importResourcesHost exportOwnershipHost
      instantiationResourcesPreWasm importResourcesWasmTypecheck
    unfold_irwt_all
    iframe Hmod
    isplitl [Hvis1 Hvis2]
    · iapply BI.BigSepL2.bigSepL2_cons.2
      isplitl [Hvis1]
      · iexact Hvis1
      iapply BI.BigSepL2.bigSepL2_singleton.2
      iexact Hvis2
    isplitl [Hmodtab Hglob]
    · isplitl
      · isplitl [Hmodtab]
        · isplitl
          · iapply BI.BigSepM.bigSepM_singleton.2; iexact Hmodtab
          ipureintro
          refine ⟨.cons ⟨_, singleton_get _ _, rfl⟩ (.cons trivial .nil), fun k => ?_⟩
          rw [singleton_dom]; simp [extFuncAddrs, extFuncs]
        isplitr
        · iapply empty_map_check _ ⟨.cons trivial (.cons trivial .nil),
            fun k => by simp [PartialMap.dom, get?_empty, extTabAddrs, extTabs]⟩
        isplitr
        · iapply empty_map_check _ ⟨.cons trivial (.cons trivial .nil),
            fun k => by simp [PartialMap.dom, get?_empty, extMemAddrs, extMems]⟩
        isplitl
        · iapply BI.BigSepM.bigSepM_singleton.2; iexact Hglob
        ipureintro
        refine ⟨.cons trivial (.cons ⟨_, _, singleton_get _ _, rfl, ?_⟩ .nil), fun k => ?_⟩
        · rfl
        · rw [singleton_dom]; simp [extGlobAddrs, extGlobs]
      isplitr
      · ipureintro; intro e he; simp [factorialModule] at he
      ipureintro; intro e he; simp [factorialModule] at he
    isplitr
    · iapply BI.BigSepL.bigSepL_nil.2; iempintro
    ipureintro; rfl
  iintro %idnstart Hf Hpost
  unfold instantiationResourcesPost instantiationResourcesPostWasm moduleInstResourcesWasm
    importResourcesWasmTypecheck
  unfold_irwt_all
  icases Hpost with ⟨-, -, %inst, ⟨%g_inits, %tabA, %memA, %globA, %wts', %wms',
    ⟨⟨Hwf, -⟩, -, -, ⟨Hwg, -⟩⟩, %HH, %Htabeq, %-, %-, %-, %-, %-, %-, %-, Hrf, Hrt, -, -⟩, -⟩
  ihave Hwf := BI.BigSepM.bigSepM_singleton.1 $$ Hwf
  ihave Hwg := BI.BigSepM.bigSepM_singleton.1 $$ Hwg
  obtain ⟨htypes, hpf, -, -, hpg, hstart⟩ := HH
  simp [extFuncAddrs, extFuncs, extGlobAddrs, extGlobs] at hpf hpg
  obtain ⟨rest, hrest⟩ := hpf
  obtain ⟨grest, hgrest⟩ := hpg
  have hfc : getImportFuncCount factorialModule = 1 := rfl
  have htc : getImportTableCount factorialModule = 0 := rfl
  subst Htabeq
  rw [hfc, htc, ← hrest,
    show moduleInstBuildTables factorialModule inst = [⟨[none], none⟩] from rfl]
  unfold moduleInstResourcesFunc moduleInstResourcesTab
  ihave ⟨%Hflen, Hrf⟩ := BI.persistent_entails_right BI.BigSepL2.bigSepL2_length $$ Hrf
  ihave ⟨%Htlen, Hrt⟩ := BI.persistent_entails_right BI.BigSepL2.bigSepL2_length $$ Hrt
  rw [htypes]
  simp only [List.drop_zero, List.singleton_append, List.drop_one, List.tail_cons]
  have hlen : rest.length = 4 := by simpa [factorialModule] using Hflen.symm
  rcases rest with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, rest⟩⟩⟩⟩⟩ <;> simp at hlen
  rcases htab : inst.tab with _ | ⟨t0, ts⟩
  · simp [htab] at Htlen
  ihave ⟨Ht, -⟩ := BI.BigSepL2.bigSepL2_cons.1 $$ Hrt
  unfold tabBlock
  icases Ht with ⟨Ht, -, -⟩
  ihave ⟨Ht, -⟩ := BI.BigSepL.bigSepL_cons.1 $$ Ht
  simp only [factorialModule]
  ihave ⟨Hmyrec, Hrf⟩ := BI.BigSepL2.bigSepL2_cons.1 $$ Hrf
  ihave ⟨HF, Hrf⟩ := BI.BigSepL2.bigSepL2_cons.1 $$ Hrf
  ihave ⟨Hfact, Hrf⟩ := BI.BigSepL2.bigSepL2_cons.1 $$ Hrf
  ihave ⟨Hmain, -⟩ := BI.BigSepL2.bigSepL2_cons.1 $$ Hrf
  have hidn : a3 = idnstart := by
    simpa [checkStart, factorialModule, optionBind, ← hrest] using hstart
  subst hidn
  simp only [List.getD_cons_succ, List.getD_cons_zero]
  rw [show xx 2 = Value.int32 (Wasm.Int.intOfZ 2) from rfl]
  iapply main_host_spec 3 0 (Wasm.Int.intOfZ 2) 1 t0 0 a2 a1 a0 hidx gidx 0 modTab inst none n a3
    emptyFrame Φ (by rw [← hrest]; rfl) (by rw [← hrest]; rfl) (by rw [← hrest]; rfl)
    (by rw [← hrest]; rfl) (by rw [htypes]; rfl) (by rw [htab]; rfl) (by rw [← hgrest]; rfl)
    hov hpos $$ HΦ Hf Hfact HF Hmyrec Hwf HA [Ht] Hwg Hmain
  rw [show yy 0 = 0 from rfl]
  iexact Ht

end FactorialHost

end IrisWasm.Examples
