/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Examples.Stack.StackCommon
import IrisWasm.Examples.Stack.IsEmpty
import IrisWasm.Logrel.IrisFundamental
import IrisWasm.Rules.Proofmode

/-! Port of `theories/iris/examples/stack/function/new_stack.v`. -/

namespace IrisWasm.Examples.Stack

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm

/-! ### Code -/

/-- `new_stack: [] -> [i32]`, locals declared: `[i32]`. Attempts to create a new stack of i32s at
the end of memory 0 by allocating a new page. Can fail non-deterministically if `grow_memory`
fails. On success, stores a pointer to the top element of the stack at the start of the stack.
Returns the pointer to the start of the stack, or -1 if allocation fails. Cannot trap. -/
@[rocq_alias iriswasm.new_stack]
def newStack : List BasicInstruction :=
  [ i32const 1,
    .growMemory,
    .teeLocal 0,
    i32const (-1),
    .relop .i32 (.i .eq),
    .if_ (.tf [] [.i32]) [ i32const (-1) ]
      [ .getLocal 0,
        i32const 65536,
        .binop .i32 (.i .mul),
        .teeLocal 0,
        .getLocal 0,
        .store .i32 none 0 0,
        .getLocal 0 ] ]

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

private theorem wp_value_imm {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF} (vs : List Value)
    {e : Expr} (h : e = vToEList vs) : Φ (.immV vs) ⊢ WP e @ s ; E {{ Φ }} := by
  subst h
  exact IrisWp.wp_value (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) ⟨rfl⟩

private theorem wms_app (n k : Nat) (l1 l2 : Bytes) :
    (n ↦[wms][ k ] (l1 ++ l2) : IProp GF) ⊣⊢ n ↦[wms][ k ] l1 ∗ n ↦[wms][ k + l1.length ] l2 := by
  unfold memBlockAtPos
  refine BigSepL.bigSepL_append.trans ?_
  have h : ∀ i, k + (i + l1.length) = k + l1.length + i := by omega
  simp only [h]
  exact .rfl

private theorem nOfUint_one : Wasm.Int.nOfUint (Wasm.Int.intOfZ (w := 32) 1) = 1 := by decide

private theorem nOfUint_nat (len : Nat) (h : len < 2 ^ 32) :
    Wasm.Int.nOfUint (Wasm.Int.intOfZ (w := 32) (len : _root_.Int)) = len := by
  simp only [Wasm.Int.nOfUint, Wasm.Int.intOfZ, Wasm.Int.repr, BitVec.ofInt_natCast,
    BitVec.toNat_ofNat]
  omega

private theorem relop_minus_one :
    appRelop (.i .eq) (.int32 int32MinusOne) (.int32 (Wasm.Int.intOfZ (-1))) = true := by decide

private theorem relop_page (p : Nat) (h : p < 65536) :
    appRelop (.i .eq) (.int32 (Wasm.Int.intOfZ (p : _root_.Int))) (.int32 (Wasm.Int.intOfZ (-1))) =
      false := by
  simp only [appRelop, appRelopI, Wasm.Int.ieq, Wasm.Int.intOfZ, Wasm.Int.repr,
    BitVec.ofInt_natCast, beq_eq_false_iff_ne, ne_eq]
  intro h'
  have := congrArg BitVec.toNat h'
  simp at this
  omega

private theorem mul_page (len : Nat) (h : pageSize ∣ len) :
    appBinop (.i .mul) (.int32 (Wasm.Int.intOfZ ((len / pageSize : Nat) : _root_.Int)))
      (.int32 (Wasm.Int.intOfZ 65536)) = some (.int32 (Wasm.Int.intOfZ (len : _root_.Int))) := by
  simp only [appBinop, appBinopI, Wasm.Int.imul, Wasm.Int.intOfZ, Wasm.Int.repr,
    BitVec.ofInt_natCast, Option.map_some, Option.some.injEq, Value.int32.injEq]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, pageSize] at h ⊢
  omega

private theorem wp_tee0 {s : Stuckness} {E : CoPset} (v : Value) (f : Frame)
    (hf : 0 < f.locs.length) :
    (↪[frame] f : IProp GF) ⊢ WP ([.basic (.const v), .basic (.teeLocal 0)] : Expr) @ s ; E
      {{ w, ⌜w = .immV [v]⌝ ∗ ↪[frame] (⟨f.locs.set 0 v, f.inst⟩ : Frame) }} := by
  iintro Hf
  iapply wp_tee_local _ _ _ _ _ _ $$ Hf
  inext; iintro Hf
  take_drop_app_rewrite 1
  iapply wp_val_app1
  isplitr
  · iintro !> ⟨%h, -⟩; cases h
  iapply wp_set_local _ _ _ _ (fun w => iprop(⌜valCombine (.immV [v]) w = .immV [v]⌝)) _ hf
    $$ [] Hf
  inext; ipureintro; rfl

private theorem wp_tee_relop {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF} (c : I32) (b : Bool)
    (f : Frame) (hf : 0 < f.locs.length)
    (hb : appRelop (.i .eq) (.int32 c) (.int32 (Wasm.Int.intOfZ (-1))) = b) (rest : Expr) :
    iprop(↪[frame] f ∗ (↪[frame] (⟨f.locs.set 0 (.int32 c), f.inst⟩ : Frame) -∗
      WP ([.basic (.const (.int32 (wasmBool b)))] ++ rest) @ s ; E {{ Φ }})) ⊢
    WP ([.basic (.const (.int32 c)), .basic (.teeLocal 0),
      .basic (.const (.int32 (Wasm.Int.intOfZ (-1)))), .basic (.relop .i32 (.i .eq))] ++ rest)
      @ s ; E {{ Φ }} := by
  iintro ⟨Hf, Hk⟩
  take_drop_app_rewrite 2
  iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV [.int32 c]⌝ ∗
    ↪[frame] (⟨f.locs.set 0 (.int32 c), f.inst⟩ : Frame)))
  isplitr
  · iintro ⟨%h, -⟩; cases h
  isplitl [Hf]
  · iapply wp_tee0 _ _ hf $$ Hf
  iintro %w ⟨%hw, Hf⟩
  subst hw
  simp only [ofVal, vToEList, List.map, List.cons_append, List.nil_append]
  take_drop_app_rewrite 3
  iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV [.int32 (wasmBool b)]⌝ ∗
    ↪[frame] (⟨f.locs.set 0 (.int32 c), f.inst⟩ : Frame)))
  isplitr
  · iintro ⟨%h, -⟩; cases h
  isplitl [Hf]
  · iapply wp_relop hb $$ Hf
    inext; ipureintro; rfl
  iintro %w ⟨%hw, Hf⟩
  subst hw
  simp only [ofVal, vToEList, List.map, List.cons_append, List.append_eq, List.nil_append]
  iapply Hk $$ Hf

/-! ### Specs -/

@[rocq_alias iriswasm.spec_new_stack]
theorem spec_new_stack (f0 : Frame) (n len : Nat) (E : CoPset) :
    ⊢ ({{{{ ⌜f0.inst.memory[0]? = some n⌝ ∗ ⌜f0.locs.length ≥ 1⌝ ∗ ⌜pageSize ∣ len⌝ ∗
          ↪[frame] f0 ∗ n ↦[wmlength] len }}}}
        (toEList newStack) @ E
      {{{{ v, ((⌜v = .immV [valueOfInt (-1)]⌝ ∗ n ↦[wmlength] len) ∨
            (⌜v = .immV [valueOfUint len]⌝ ∗ isStack len [] n ∗
              n ↦[wmlength] (len + pageSize))) ∗
          ∃ f1, ↪[frame] f1 ∗ ⌜f1.inst = f0.inst⌝ }}}} : IProp GF) := by
  iintro !> %Φ ⟨%Hinst, %Hflocs, %Hlendiv, Hf, Hlen⟩ HΦ
  simp only [newStack, toEList, List.map, i32const]
  take_drop_app_rewrite 2
  iapply wp_seq _ _ _ (fun w => iprop(((((⌜w = .immV [.int32 (Wasm.Int.intOfZ
      ((len / pageSize : Nat) : _root_.Int))]⌝) ∗
      n ↦[wms][ len ] List.replicate (Wasm.Int.nOfUint (Wasm.Int.intOfZ (w := 32) 1) * pageSize)
        (0 : Byte) ∗
      n ↦[wmlength] (len + Wasm.Int.nOfUint (Wasm.Int.intOfZ (w := 32) 1) * pageSize)) ∗
      ⌜MemInBound (len / pageSize + Wasm.Int.nOfUint (Wasm.Int.intOfZ (w := 32) 1))⌝) ∨
      (⌜w = .immV [.int32 int32MinusOne]⌝ ∗ n ↦[wmlength] len)) ∗ ↪[frame] f0))
  isplitr
  · iintro ⟨(⟨⟨%h, -⟩, -⟩ | ⟨%h, -⟩), -⟩ <;> cases h
  isplitl [Hf Hlen]
  · iapply wp_grow_memory _ _ n f0 len
      (fun w => iprop(⌜w = .immV [.int32 (Wasm.Int.intOfZ ((len / pageSize : Nat) : _root_.Int))]⌝))
      (fun w => iprop(⌜w = .immV [.int32 int32MinusOne]⌝)) _ Hinst
    iframe
    isplit <;> inext <;> ipureintro <;> rfl
  iintro %w ⟨H, Hf⟩
  icases H with (⟨⟨%hw, Hb, Hlen⟩, %Hbound⟩ | ⟨%hw, Hlen⟩)
  · subst hw
    rw [nOfUint_one] at Hbound
    have hdiv := Nat.div_mul_cancel Hlendiv
    have hp : len / pageSize < 65536 := by unfold MemInBound pageLimit at Hbound; omega
    have hlen32 : len ≤ ffff0000 := by unfold ffff0000 pageSize at *; omega
    have hL : Wasm.Int.nOfUint (Wasm.Int.intOfZ (w := 32) (len : _root_.Int)) = len :=
      nOfUint_nat len (by unfold ffff0000 at hlen32; omega)
    rw [show Wasm.Int.nOfUint (Wasm.Int.intOfZ (w := 32) 1) * pageSize = 4 + 65532 by
      rw [nOfUint_one]; rfl, ← List.replicate_append_replicate]
    ihave Hb := (wms_app n len _ _).1 $$ Hb
    icases Hb with ⟨Hb4, Hrest⟩
    simp only [ofVal, vToEList, List.map, List.cons_append, List.nil_append]
    take_drop_app_rewrite 4
    iapply wp_tee_relop _ false f0 (by omega) (relop_page _ hp)
    isplitl [Hf]
    · iexact Hf
    iintro Hf
    simp only [List.cons_append, List.nil_append]
    iapply wp_if_false (c := wasmBool false) rfl $$ Hf
    inext; iintro Hf
    take_drop_app_rewrite 0
    iapply wp_block (vs := []) rfl rfl rfl rfl $$ Hf
    inext; iintro Hf
    iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).2
    iapply wp_label_push_nil
    simp only [pushBase, toEList, List.map, List.nil_append]
    iapply iRewrite_nil_r_ctx
    iapply wp_seq_ctx _ _ _ (fun w => iprop((⌜w = .immV [.int32 (Wasm.Int.intOfZ (len : _root_.Int))]⌝ ∗
      n ↦[wms][ Wasm.Int.nOfUint (Wasm.Int.intOfZ (w := 32) (len : _root_.Int)) + 0 ]
        bits (.int32 (Wasm.Int.intOfZ (len : _root_.Int)))) ∗
      ↪[frame] (⟨(f0.locs.set 0 (.int32 (Wasm.Int.intOfZ ((len / pageSize : Nat) : _root_.Int)))).set 0
        (.int32 (Wasm.Int.intOfZ (len : _root_.Int))), f0.inst⟩ : Frame)))
    isplitr
    · iintro ⟨⟨%h, -⟩, -⟩; cases h
    isplitl [Hf Hb4]
    · take_drop_app_rewrite 1
      iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV [.int32 (Wasm.Int.intOfZ
        ((len / pageSize : Nat) : _root_.Int))]⌝ ∗ ↪[frame] (⟨f0.locs.set 0 (.int32 (Wasm.Int.intOfZ
        ((len / pageSize : Nat) : _root_.Int))), f0.inst⟩ : Frame)))
      isplitr
      · iintro ⟨%h, -⟩; cases h
      isplitl [Hf]
      · iapply wp_get_local _ _ (.int32 (Wasm.Int.intOfZ ((len / pageSize : Nat) : _root_.Int))) 0
          (fun w => iprop(⌜w = .immV [.int32 (Wasm.Int.intOfZ
          ((len / pageSize : Nat) : _root_.Int))]⌝))
          (⟨f0.locs.set 0 (.int32 (Wasm.Int.intOfZ ((len / pageSize : Nat) : _root_.Int))),
            f0.inst⟩ : Frame) (List.getElem?_set_self (by omega)) $$ [] Hf
        inext; ipureintro; rfl
      iintro %w ⟨%hw, Hf⟩
      subst hw
      simp only [ofVal, vToEList, List.map, List.cons_append, List.nil_append]
      take_drop_app_rewrite 3
      iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV [.int32 (Wasm.Int.intOfZ (len : _root_.Int))]⌝ ∗
        ↪[frame] (⟨f0.locs.set 0 (.int32 (Wasm.Int.intOfZ
        ((len / pageSize : Nat) : _root_.Int))), f0.inst⟩ : Frame)))
      isplitr
      · iintro ⟨%h, -⟩; cases h
      isplitl [Hf]
      · iapply wp_binop (mul_page len Hlendiv) $$ Hf
        inext; ipureintro; rfl
      iintro %w ⟨%hw, Hf⟩
      subst hw
      simp only [ofVal, vToEList, List.map, List.cons_append, List.nil_append]
      take_drop_app_rewrite 2
      iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV [.int32 (Wasm.Int.intOfZ (len : _root_.Int))]⌝ ∗
        ↪[frame] (⟨(f0.locs.set 0 (.int32 (Wasm.Int.intOfZ ((len / pageSize : Nat) : _root_.Int)))).set 0
        (.int32 (Wasm.Int.intOfZ (len : _root_.Int))), f0.inst⟩ : Frame)))
      isplitr
      · iintro ⟨%h, -⟩; cases h
      isplitl [Hf]
      · iapply wp_tee0 (.int32 (Wasm.Int.intOfZ (len : _root_.Int)))
          (⟨f0.locs.set 0 (.int32 (Wasm.Int.intOfZ ((len / pageSize : Nat) : _root_.Int))),
            f0.inst⟩ : Frame) (by simp; omega) $$ Hf
      iintro %w ⟨%hw, Hf⟩
      subst hw
      simp only [ofVal, vToEList, List.map, List.cons_append, List.nil_append]
      take_drop_app_rewrite 2
      iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV [.int32 (Wasm.Int.intOfZ (len : _root_.Int)),
        .int32 (Wasm.Int.intOfZ (len : _root_.Int))]⌝ ∗
        ↪[frame] (⟨(f0.locs.set 0 (.int32 (Wasm.Int.intOfZ ((len / pageSize : Nat) : _root_.Int)))).set 0
        (.int32 (Wasm.Int.intOfZ (len : _root_.Int))), f0.inst⟩ : Frame)))
      isplitr
      · iintro ⟨%h, -⟩; cases h
      isplitl [Hf]
      · take_drop_app_rewrite 1
        iapply wp_val_app1
        isplitr
        · iintro !> ⟨%h, -⟩; cases h
        iapply wp_get_local _ _ (.int32 (Wasm.Int.intOfZ (len : _root_.Int))) 0
          (fun w => iprop(⌜valCombine (.immV [.int32 (Wasm.Int.intOfZ
          (len : _root_.Int))]) w = .immV [.int32 (Wasm.Int.intOfZ (len : _root_.Int)),
          .int32 (Wasm.Int.intOfZ (len : _root_.Int))]⌝))
          (⟨(f0.locs.set 0 (.int32 (Wasm.Int.intOfZ ((len / pageSize : Nat) : _root_.Int)))).set 0
            (.int32 (Wasm.Int.intOfZ (len : _root_.Int))), f0.inst⟩ : Frame)
          (by simp only [List.set_set]; exact List.getElem?_set_self (by omega))
          $$ [] Hf
        inext; ipureintro; rfl
      iintro %w ⟨%hw, Hf⟩
      subst hw
      simp only [ofVal, vToEList, List.map, List.cons_append, List.nil_append]
      take_drop_app_rewrite 3
      iapply wp_seq _ _ _ (fun w => iprop((⌜w = .immV []⌝ ∗
        n ↦[wms][ Wasm.Int.nOfUint (Wasm.Int.intOfZ (w := 32) (len : _root_.Int)) + 0 ]
          bits (.int32 (Wasm.Int.intOfZ (len : _root_.Int)))) ∗
        ↪[frame] (⟨(f0.locs.set 0 (.int32 (Wasm.Int.intOfZ ((len / pageSize : Nat) : _root_.Int)))).set 0
        (.int32 (Wasm.Int.intOfZ (len : _root_.Int))), f0.inst⟩ : Frame)))
      isplitr
      · iintro ⟨⟨%h, -⟩, -⟩; cases h
      isplitl [Hf Hb4]
      · iapply wp_store (fun w => iprop(⌜w = .immV []⌝)) _ _ .i32
          (.int32 (Wasm.Int.intOfZ (len : _root_.Int))) (List.replicate 4 0) 0 0
          (Wasm.Int.intOfZ (len : _root_.Int)) n
          (⟨(f0.locs.set 0 (.int32 (Wasm.Int.intOfZ ((len / pageSize : Nat) : _root_.Int)))).set 0
            (.int32 (Wasm.Int.intOfZ (len : _root_.Int))), f0.inst⟩ : Frame) rfl rfl Hinst
        isplitr
        · inext; ipureintro; rfl
        isplitl [Hf]
        · iexact Hf
        iapply points_to_wms_eq n (List.replicate 4 0) len n (List.replicate 4 0)
          (Wasm.Int.nOfUint (Wasm.Int.intOfZ (w := 32) (len : _root_.Int)) + 0) rfl rfl (by omega)
          $$ Hb4
      iintro %w ⟨⟨%hw, Hb4⟩, Hf⟩
      subst hw
      simp only [ofVal, vToEList, List.map, List.nil_append]
      iapply wp_wand_s $$ [Hf]
      · iapply wp_get_local _ _ (.int32 (Wasm.Int.intOfZ (len : _root_.Int))) 0
          (fun w => iprop(⌜w = .immV [.int32 (Wasm.Int.intOfZ (len : _root_.Int))]⌝))
          (⟨(f0.locs.set 0 (.int32 (Wasm.Int.intOfZ ((len / pageSize : Nat) : _root_.Int)))).set 0
            (.int32 (Wasm.Int.intOfZ (len : _root_.Int))), f0.inst⟩ : Frame)
          (by simp only [List.set_set]; exact List.getElem?_set_self (by omega))
          $$ [] Hf
        inext; ipureintro; rfl
      iintro %w ⟨%hw, Hf⟩
      iframe
      ipureintro; exact hw
    iintro %w ⟨⟨%hw, Hb4⟩, Hf⟩
    subst hw
    simp only [ofVal, vToEList, List.map]
    iapply wp_val_return rfl $$ Hf
    iintro Hf
    iapply wp_value_imm [.int32 (Wasm.Int.intOfZ (len : _root_.Int))] ?_ <;> try rfl
    iapply HΦ
    isplitr [Hf]
    · iright
      isplitr
      · ipureintro; rfl
      isplitr [Hlen]
      · simp only [isStack, List.length_nil, Nat.zero_mul, Nat.add_zero]
        isplitr
        · ipureintro; simpa [two16, pageSize] using Hlendiv
        isplitr
        · ipureintro; omega
        isplitr
        · ipureintro; unfold two14; omega
        isplitl [Hb4]
        · iapply (i32_wms n len _).2
          iapply points_to_wms_eq n (bits (.int32 (Wasm.Int.intOfZ (len : _root_.Int))))
            (Wasm.Int.nOfUint (Wasm.Int.intOfZ (w := 32) (len : _root_.Int)) + 0) n
            (serialiseI32 (Wasm.Int.repr (len : _root_.Int))) len rfl rfl (by omega) $$ Hb4
        isplitr
        · iapply BigSepL.bigSepL_nil.2
          iempintro
        iexists List.replicate 65532 0
        isplitr
        · ipureintro; rw [List.length_replicate]; rfl
        iapply points_to_wms_eq n (List.replicate 65532 0) (len + (List.replicate 4 (0 : Byte)).length)
          n (List.replicate 65532 0) (len + 4) rfl rfl (by simp) $$ Hrest
      rw [show (4 + 65532 : Nat) = pageSize from rfl]
      iexact Hlen
    iexists _
    isplitl [Hf]
    · iexact Hf
    ipureintro; rfl
  · subst hw
    simp only [ofVal, vToEList, List.map, List.cons_append, List.nil_append]
    take_drop_app_rewrite 4
    iapply wp_tee_relop _ true f0 (by omega) relop_minus_one
    isplitl [Hf]
    · iexact Hf
    iintro Hf
    simp only [List.cons_append, List.nil_append]
    iapply wp_if_true (by decide) $$ Hf
    inext; iintro Hf
    take_drop_app_rewrite 0
    iapply wp_block (vs := []) rfl rfl rfl rfl $$ Hf
    inext; iintro Hf
    simp only [toEList, List.map, List.nil_append]
    iapply wp_wand_s $$ [Hf]
    · iapply wp_label_value (Φ := fun w => iprop(⌜w = .immV [.int32 (Wasm.Int.intOfZ (-1))]⌝))
        (es := [.basic (.const (.int32 (Wasm.Int.intOfZ (-1))))])
        (to_of_val (.immV [.int32 (Wasm.Int.intOfZ (-1))])) $$ Hf
      inext; ipureintro; rfl
    iintro %w ⟨%hw, Hf⟩
    iapply HΦ
    isplitl [Hlen]
    · ileft
      isplitr
      · ipureintro; exact hw
      iexact Hlen
    iexists _
    isplitl [Hf]
    · iexact Hf
    ipureintro; rfl

/-! ### Validity -/

section valid
variable [LogrelNaInvs GF]
attribute [local instance] WasmG.invGS

omit [LogrelNaInvs GF] in
@[rocq_alias iriswasm.interp_value_of_int]
theorem interp_value_of_int (i : _root_.Int) :
    ⊢ (interpValue .i32 (valueOfInt i) : IProp GF) := by
  unfold interpValue interpValueI32; ipureintro; exact ⟨_, rfl⟩

omit [LogrelNaInvs GF] in
@[rocq_alias iriswasm.interp_value_of_uint]
theorem interp_value_of_uint (i : Nat) :
    ⊢ (interpValue .i32 (valueOfUint i) : IProp GF) := by
  unfold interpValue interpValueI32; ipureintro; exact ⟨_, rfl⟩

@[rocq_alias iriswasm.valid_new_stack]
theorem valid_new_stack (m t : Nat) (funcs : List Funcaddr) :
    let i0 : Instance :=
      { types := [.tf [] [.i32], .tf [.i32] [.i32], .tf [.i32, .i32] []], funcs := funcs,
        tab := [t], memory := [m], globs := [] };
    ⊢ (NonAtomicInvariant.inv (LogrelNaInvs.logrelNais (GF := GF)) stkN
        (stackModuleInv (fun a b => isStack a b m) (fun n => m ↦[wmlength] n)) -∗
      interpClosureNative i0 [] [.i32] [.i32] (toEList newStack) [] : IProp GF) := by
  intro i0
  unfold interpClosureNative
  iintro #Hstk %vcs %f Hv Hown Hf
  have hvcs : (interpVal [] (.immV vcs) : IProp GF) ⊢ ⌜vcs = []⌝ := by
    unfold interpVal interpValues
    iintro (%h | ⟨%ws, %hws, Hws⟩)
    · cases h
    cases hws
    ihave %hlen := BigSepL2.bigSepL2_length $$ Hws
    ipureintro; simpa using hlen
  icases hvcs $$ Hv with %hz
  subst hz
  unfold wpWasmCtxFrame
  iintro %LI %hLI
  simp [lfilled, lfill, constList] at hLI
  subst hLI
  have h1 : toVal (toEList newStack) = none :=
    to_val_None_prepend_const [.basic (.const (.int32 (Wasm.Int.intOfZ 1)))] _ rfl
      (to_val_None_append [.basic .growMemory] _
        (by simp [toVal_singleton, toValInstr, valOfValNotVal]))
  have h2 : toVal [AdministrativeInstruction.local [ValueType.i32].length ⟨[] ++ nZeros [.i32], i0⟩
      [.label [ValueType.i32].length [] (toEList newStack)]] = none := by
    simp [toVal_singleton, toValInstr_local, toValInstr_label, h1, valOfValNotVal]
  have hb := wp_frame_bind (GF := GF) .NotStuck ⊤ (fun v => iprop((interpVal [.i32] v ∨
    interpCallHostCls [] [.i32] v) ∗ NonAtomicInvariant.own (LogrelNaInvs.logrelNais (GF := GF)) ⊤ ∗
    ↪[frame] f)) [ValueType.i32].length ⟨[] ++ nZeros [.i32], i0⟩ f
    [.label [ValueType.i32].length [] (toEList newStack)] h2
  unfold wpWasmFrame at hb
  iapply hb $$ Hf
  iintro Hf
  iapply wp_build_ctx (toEList newStack) 1
    (.rec_ [] [ValueType.i32].length [] (.base [] []) []) _ _ _ _
    ⟨by simp [lfilled, lfill, constList]⟩
  iapply wp_label_bind
  have hfin := fun w f1 => stack_valid_finish (GF := GF) [.i32] f f1 [] w
  unfold wpWasmFrame wpWasmCtx at hfin
  iapply stack_fupd_wp
  imod NonAtomicInvariant.inv_acc CoPset.subseteq_top CoPset.subseteq_top $$ Hstk Hown with
    ⟨>Hres, Hown, Hcls⟩
  unfold stackModuleInv
  icases Hres with ⟨%len, %Hmul, Hlen, Hl⟩
  imodintro
  iapply spec_new_stack (⟨[] ++ nZeros [.i32], i0⟩ : Frame) m len ⊤ $$ [Hf Hlen]
  · iframe; ipureintro; exact ⟨rfl, by simp [nZeros], Hmul⟩
  iintro %w ⟨Hcases, %f1, Hf, -⟩
  unfold wpWasmCtx
  iintro %LI %hLI
  iapply stack_fupd_wp
  icases Hcases with (⟨%hw, Hlen⟩ | ⟨%hw, Hs, Hlen⟩)
  · imod Hcls $$ [Hown Hlen Hl] with Hown
    · iframe
      ipureintro; exact Hmul
    imodintro
    subst hw
    ihave H := hfin (.immV [valueOfInt (-1)]) f1 $$ [Hown Hf]
    · iframe
      iapply interpVal_i32 (valueOfInt (-1)) ⟨_, rfl⟩
    ihave H2 := H $$ %LI %hLI
    iexact H2
  · icases Hl with ⟨%l, %Hmultiple, Hl⟩
    imod Hcls $$ [Hown Hlen Hl Hs] with Hown
    · isplitl [Hlen Hl Hs]
      · inext
        iexists len + pageSize
        isplitr
        · ipureintro; exact Nat.dvd_add Hmul (Nat.dvd_refl _)
        isplitl [Hlen]
        · iexact Hlen
        iexists len :: l
        isplitr
        · ipureintro; exact .ind _ _ _ Hmultiple
        iapply BigSepL.bigSepL_cons.2
        isplitl [Hs]
        · iexists []; iexact Hs
        iexact Hl
      iexact Hown
    imodintro
    subst hw
    ihave H := hfin (.immV [valueOfUint len]) f1 $$ [Hown Hf]
    · iframe
      iapply interpVal_i32 (valueOfUint len) ⟨_, rfl⟩
    ihave H2 := H $$ %LI %hLI
    iexact H2

end valid

end stack

end IrisWasm.Examples.Stack
