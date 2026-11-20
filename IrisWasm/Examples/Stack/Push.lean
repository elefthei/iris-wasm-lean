/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Examples.Stack.StackCommon
import IrisWasm.Examples.Stack.IsFull
import IrisWasm.Logrel.IrisFundamental
import IrisWasm.Rules.Proofmode

/-! Port of `theories/iris/examples/stack/function/push.v`. -/

namespace IrisWasm.Examples.Stack

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm

/-! ### Code -/

/-- `push: [i32, i32] -> []`, locals declared: `[i32]`. Given a stack pointer and an i32, push
the i32 to the top of the stack; traps if the stack pointer is invalid or the stack is full.
Local 2 stores the new address of the stack top pointer. -/
@[rocq_alias iriswasm.push_op]
def pushOp : List BasicInstruction :=
  isFullOp ++
  [ .if_ (.tf [] []) [.unreachable] [],
    .getLocal 0,
    .load .i32 none 0 0,
    i32const 4,
    .binop .i32 (.i .add),
    .teeLocal 2,
    .getLocal 1,
    .store .i32 none 0 0,
    .getLocal 0,
    .getLocal 2,
    .store .i32 none 0 0 ]

@[rocq_alias iriswasm.push]
def push : List BasicInstruction :=
  validateStack 0 ++ validateStackBound 0 ++ pushOp

section stack
variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF]

private theorem wp_wand_s {s : Stuckness} {E : CoPset} {e : Expr} {Φ Ψ : Val → IProp GF} :
    WP e @ s ; E {{ Φ }} ⊢ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s ; E {{ Ψ }} :=
  IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)

/-- `wp_seq` specialised to a first part returning the values `vs` and the resource `P`. -/
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

private theorem binop_add4_valueOfUint (a : Nat) :
    appBinop (.i .add) (valueOfUint a) (.int32 (Wasm.Int.intOfZ 4)) =
      some (valueOfUint (a + 4)) := by
  simp only [appBinop, appBinopI, valueOfUint, Wasm.Int.iadd, Wasm.Int.intOfZ, Wasm.Int.repr,
    BitVec.ofInt_natCast]
  simp only [Option.map, Option.some.injEq, Value.int32.injEq]
  rw [show ((4 : _root_.Int)) = ((4 : Nat) : _root_.Int) from rfl, BitVec.ofInt_natCast,
    BitVec.ofNat_add]

private theorem addr_eq (a : Nat) (h : a < 4294967296) :
    Wasm.Int.nOfUint (Wasm.Int.intOfZ (w := 32) (a : _root_.Int)) + 0 = a := by
  simp [Wasm.Int.nOfUint, Wasm.Int.intOfZ, Wasm.Int.repr, BitVec.ofInt_natCast]
  omega

private theorem wms_split (n k j : Nat) (l : Bytes) (h : j ≤ l.length) :
    (n ↦[wms][ k ] l : IProp GF) ⊢ n ↦[wms][ k ] (l.take j) ∗ n ↦[wms][ k + j ] (l.drop j) := by
  conv => lhs; rw [← List.take_append_drop j l]
  unfold memBlockAtPos
  refine BigSepL.bigSepL_append.1.trans ?_
  have e : ∀ i, k + (i + (l.take j).length) = k + j + i := by intro i; simp; omega
  simp only [e]
  exact .rfl

/-- An i32 store at a `valueOfUint` address, with the post in `wp_seq_imm` shape. -/
private theorem wp_store_uint {E : CoPset} (v : Value) (bs : Bytes) (k n : Nat) (f : Frame)
    (hk : k < 4294967296) (ht : typesAgree .i32 v = true) (hlen : bs.length = 4)
    (hn : f.inst.memory[0]? = some n) :
    (iprop(↪[frame] f ∗ n ↦[wms][ k ] bs) : IProp GF) ⊢
      WP ([.basic (.const (valueOfUint k)), .basic (.const v), .basic (.store .i32 none 0 0)]
        : Expr) @ E {{ w, ⌜w = Val.immV []⌝ ∗ (n ↦[wms][ k ] bits v ∗ ↪[frame] f) }} := by
  iintro ⟨Hf, Hb⟩
  have e := addr_eq k hk
  ihave Hb := points_to_wms_eq n _ _ n _ _ rfl rfl e.symm $$ Hb
  rw [show valueOfUint k = .int32 (Wasm.Int.intOfZ (k : _root_.Int)) from rfl]
  iapply wp_wand_s (Φ := fun w => iprop((⌜w = .immV []⌝ ∗
      n ↦[wms][ Wasm.Int.nOfUint (Wasm.Int.intOfZ (w := 32) (k : _root_.Int)) + 0 ] bits v) ∗
      ↪[frame] f)) $$ [Hf Hb]
  · iapply wp_store (fun w => iprop(⌜w = .immV []⌝)) _ _ .i32 v bs 0 0
      (Wasm.Int.intOfZ (k : _root_.Int)) n f ht hlen hn
    isplitr
    · inext; ipureintro; rfl
    isplitl [Hf]
    · iexact Hf
    · iexact Hb
  iintro %w ⟨⟨%hw, Hb⟩, Hf⟩
  ihave Hb := points_to_wms_eq n _ _ n _ _ rfl rfl e $$ Hb
  iframe
  ipureintro; exact hw

/-- Reassemble the stack after a push. -/
private theorem isStack_push (v n : Nat) (a : I32) (s : List I32) (rest : Bytes)
    (hdiv : two16 ∣ v) (hvb : 0 ≤ v ∧ v ≤ ffff0000) (hlen : s.length + 1 < two14)
    (hrest : rest.length = two16 - 4 - s.length * 4 - 4) :
    iprop(n ↦[wms][ v ] bits (valueOfUint (v + s.length * 4 + 4)) ∗
      n ↦[wms][ v + s.length * 4 + 4 ] bits (.int32 a) ∗
      ([∗list] i ↦ w ∈ s, n ↦[i32][ v + s.length * 4 - 4 * i ] w) ∗
      n ↦[wms][ v + s.length * 4 + 4 + 4 ] rest) ⊢ (isStack v (a :: s) n : IProp GF) := by
  simp only [isStack, List.length_cons]
  rw [show v + (s.length + 1) * 4 = v + s.length * 4 + 4 by omega,
    show bits (valueOfUint (v + s.length * 4 + 4)) =
      serialiseI32 (Wasm.Int.repr ((v + s.length * 4 + 4 : Nat) : _root_.Int)) from rfl,
    show bits (.int32 a) = serialiseI32 a from rfl]
  iintro ⟨Hv, Ha, Hl, Hr⟩
  ihave Hv := (i32_wms n v _).2 $$ Hv
  ihave Ha := (i32_wms n _ a).2 $$ Ha
  isplitr
  · ipureintro; exact hdiv
  isplitr
  · ipureintro; exact hvb
  isplitr
  · ipureintro; exact hlen
  isplitl [Hv]
  · iexact Hv
  isplitl [Ha Hl]
  · iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2
    have h : ∀ k, v + s.length * 4 + 4 - 4 * (k + 1) = v + s.length * 4 - 4 * k := by
      intro k; omega
    isimp only [h, Nat.mul_zero, Nat.sub_zero]
    iframe
  iexists rest
  iframe
  ipureintro; omega

/-! ### Specs -/

@[rocq_alias iriswasm.spec_push_op]
theorem spec_push_op (f0 : Frame) (n v : Nat) (a : I32) (s : List I32) (E : CoPset) :
    ⊢ ({{{{ ⌜f0.inst.memory[0]? = some n⌝ ∗ ⌜f0.locs[0]? = some (valueOfUint v)⌝ ∗
          ⌜f0.locs[1]? = some (.int32 a)⌝ ∗ ⌜f0.locs.length ≥ 3⌝ ∗
          ⌜s.length < two14 - 1⌝ ∗ isStack v s n ∗ ↪[frame] f0 }}}}
        (toEList pushOp) @ E
      {{{{ w, ⌜w = .immV []⌝ ∗ isStack v (a :: s) n ∗
          ∃ f1, ↪[frame] f1 ∗ ⌜f0.inst = f1.inst⌝ }}}} : IProp GF) := by
  iintro !> %Φ ⟨%Hinst, %Hlocv, %Hloca, %Hlocs, %Hlens, Hstack, Hf⟩ HΦ
  icases stack_pure v s n $$ Hstack with ⟨%Hdiv, %Hvb, -, Hstack⟩
  have hx : v + s.length * 4 + 4 < 4294967296 := by unfold two14 ffff0000 at *; omega
  simp only [pushOp, toEList, List.map_append, List.map, i32const]
  rw [show List.map AdministrativeInstruction.basic isFullOp = toEList isFullOp from rfl]
  -- is_full_op: the stack is not full
  iapply wp_seq_imm [valueOfInt 0] iprop(isStack v s n ∗ ↪[frame] f0) $$ [Hf Hstack]
  · iapply spec_is_full_op f0 n v s E $$ [Hf Hstack]
    · iframe; ipureintro; exact ⟨Hinst, Hlocv⟩
    iintro %w ⟨%k, %hw, Hstack, %hk, Hf⟩
    rcases hk with ⟨-, hk⟩ | ⟨rfl, -⟩
    · exact absurd hk (by omega)
    iframe; ipureintro; exact hw
  iintro ⟨Hstack, Hf⟩
  simp only [vToEList, List.map, List.cons_append, List.nil_append, valueOfInt]
  take_drop_app_rewrite 2
  iapply wp_seq_imm [] iprop(↪[frame] f0) $$ [Hf]
  · iapply wp_if_false (show Wasm.Int.intOfZ (w := 32) 0 = Wasm.Int.zero by decide) $$ Hf
    iintro !> Hf
    rw [show ([.basic (.block (.tf [] []) [])] : Expr) = [] ++ [.basic (.block (.tf [] []) [])]
      from rfl]
    iapply wp_block (vs := []) rfl rfl rfl rfl $$ Hf
    iintro !> Hf
    iapply wp_label_value (Φ := fun w => iprop(⌜w = .immV []⌝)) (by rfl) $$ Hf
    inext; ipureintro; rfl
  iintro Hf
  simp only [vToEList, List.map, List.nil_append]
  -- get_local 0; load: the stack top pointer
  take_drop_app_rewrite 1
  iapply wp_seq_imm [valueOfUint v] iprop(↪[frame] f0) $$ [Hf]
  · iapply wp_get_local _ _ _ _ (fun w => iprop(⌜w = .immV [valueOfUint v]⌝)) _ Hlocv $$ [] Hf
    inext; ipureintro; rfl
  iintro Hf
  take_drop_app_rewrite 2
  iapply wp_seq_imm [valueOfUint (v + s.length * 4)] iprop(isStack v s n ∗ ↪[frame] f0)
    $$ [Hf Hstack]
  · iapply stack_load_0 v s n f0 E $$ %Hinst Hstack Hf
  iintro ⟨Hstack, Hf⟩
  -- add 4; tee_local 2
  take_drop_app_rewrite 3
  iapply wp_seq_imm [valueOfUint (v + s.length * 4 + 4)] iprop(↪[frame] f0) $$ [Hf]
  · iapply wp_binop (t := .i32) (binop_add4_valueOfUint _) $$ Hf
    inext; ipureintro; rfl
  iintro Hf
  take_drop_app_rewrite 2
  iapply wp_seq_imm [valueOfUint (v + s.length * 4 + 4)]
    iprop(↪[frame] (⟨f0.locs.set 2 (valueOfUint (v + s.length * 4 + 4)), f0.inst⟩ : Frame))
    $$ [Hf]
  · iapply wp_tee_local $$ Hf
    iintro !> Hf
    iapply wp_val_cons_imm
    iapply wp_set_local _ _ _ 2 (fun w => iprop(⌜w = .immV []⌝)) _ (by omega) $$ [] Hf
    inext; ipureintro; rfl
  iintro Hf
  -- get_local 1; store a into the first free cell
  take_drop_app_rewrite 2
  iapply wp_seq_imm [valueOfUint (v + s.length * 4 + 4), .int32 a]
    iprop(↪[frame] (⟨f0.locs.set 2 (valueOfUint (v + s.length * 4 + 4)), f0.inst⟩ : Frame))
    $$ [Hf]
  · iapply wp_val_cons_imm
    iapply wp_get_local _ _ (.int32 a) 1 (fun w => iprop(⌜w = .immV [.int32 a]⌝))
      (⟨f0.locs.set 2 (valueOfUint (v + s.length * 4 + 4)), f0.inst⟩ : Frame)
      (by simp [Hloca]) $$ [] Hf
    inext; ipureintro; rfl
  iintro Hf
  isimp only [isStack] at Hstack
  icases Hstack with ⟨-, -, -, Hv, Hl, %bs, %Hbs, Hb⟩
  have hbs : 4 ≤ bs.length := by unfold two14 two16 at *; omega
  ihave Hb := wms_split n _ 4 bs hbs $$ Hb
  icases Hb with ⟨Hb4, Hrest⟩
  take_drop_app_rewrite 3
  iapply wp_seq_imm []
    iprop(n ↦[wms][ v + s.length * 4 + 4 ] bits (.int32 a) ∗
      ↪[frame] (⟨f0.locs.set 2 (valueOfUint (v + s.length * 4 + 4)), f0.inst⟩ : Frame))
    $$ [Hf Hb4]
  · iapply wp_store_uint (.int32 a) (bs.take 4) _ n
      (⟨f0.locs.set 2 (valueOfUint (v + s.length * 4 + 4)), f0.inst⟩ : Frame) hx rfl
      (by simp; omega) Hinst
    iframe
  iintro ⟨Ha, Hf⟩
  simp only [vToEList, List.map, List.nil_append]
  -- get_local 0; get_local 2; store the new top pointer
  take_drop_app_rewrite 1
  iapply wp_seq_imm [valueOfUint v]
    iprop(↪[frame] (⟨f0.locs.set 2 (valueOfUint (v + s.length * 4 + 4)), f0.inst⟩ : Frame))
    $$ [Hf]
  · iapply wp_get_local _ _ (valueOfUint v) 0 (fun w => iprop(⌜w = .immV [valueOfUint v]⌝))
      (⟨f0.locs.set 2 (valueOfUint (v + s.length * 4 + 4)), f0.inst⟩ : Frame)
      (by simp [Hlocv]) $$ [] Hf
    inext; ipureintro; rfl
  iintro Hf
  take_drop_app_rewrite 2
  iapply wp_seq_imm [valueOfUint v, valueOfUint (v + s.length * 4 + 4)]
    iprop(↪[frame] (⟨f0.locs.set 2 (valueOfUint (v + s.length * 4 + 4)), f0.inst⟩ : Frame))
    $$ [Hf]
  · iapply wp_val_cons_imm
    iapply wp_get_local _ _ (valueOfUint (v + s.length * 4 + 4)) 2
      (fun w => iprop(⌜w = .immV [valueOfUint (v + s.length * 4 + 4)]⌝))
      (⟨f0.locs.set 2 (valueOfUint (v + s.length * 4 + 4)), f0.inst⟩ : Frame)
      (by simp [List.getElem?_set]; omega) $$ [] Hf
    inext; ipureintro; rfl
  iintro Hf
  ihave Hv := (i32_wms n v _).1 $$ Hv
  simp only [vToEList, List.map, List.cons_append, List.nil_append]
  iapply wp_wand_s (Φ := fun w => iprop(⌜w = Val.immV []⌝ ∗
      (n ↦[wms][ v ] bits (valueOfUint (v + s.length * 4 + 4)) ∗
      ↪[frame] (⟨f0.locs.set 2 (valueOfUint (v + s.length * 4 + 4)), f0.inst⟩ : Frame))))
    $$ [Hf Hv]
  · iapply wp_store_uint (valueOfUint (v + s.length * 4 + 4))
      (serialiseI32 (Wasm.Int.repr ((v + s.length * 4 : Nat) : _root_.Int))) v n
      (⟨f0.locs.set 2 (valueOfUint (v + s.length * 4 + 4)), f0.inst⟩ : Frame)
      (by unfold ffff0000 at Hvb; omega) rfl (length_encodeInt ..) Hinst
    iframe
  iintro %w ⟨%hw, Hv, Hf⟩
  iapply HΦ
  isplitr
  · ipureintro; exact hw
  isplitr [Hf]
  · iapply isStack_push v n a s (bs.drop 4) Hdiv Hvb (by omega) (by simp; omega)
    iframe
  iexists _
  iframe
  ipureintro; rfl

@[rocq_alias iriswasm.spec_push]
theorem spec_push (f0 : Frame) (n v : Nat) (a : I32) (s : List I32) (E : CoPset) :
    ⊢ ({{{{ ⌜f0.inst.memory[0]? = some n⌝ ∗ ⌜f0.locs[0]? = some (valueOfUint v)⌝ ∗
          ⌜f0.locs[1]? = some (.int32 a)⌝ ∗ ⌜f0.locs.length ≥ 3⌝ ∗
          ⌜s.length < two14 - 1⌝ ∗ isStack v s n ∗ ↪[frame] f0 }}}}
        (toEList push) @ E
      {{{{ w, ⌜w = .immV []⌝ ∗ isStack v (a :: s) n ∗
          ∃ f1, ↪[frame] f1 ∗ ⌜f0.inst = f1.inst⌝ }}}} : IProp GF) := by
  iintro !> %Φ ⟨%Hinst, %Hlocv, %Hloca, %Hlocs, %Hlens, Hstack, Hf⟩ HΦ
  rw [show toEList push = toEList (validateStack 0) ++
    (toEList (validateStackBound 0) ++ toEList pushOp) by simp [push, toEList]]
  iapply wp_seq_imm [] iprop(isStack v s n ∗ ↪[frame] f0) $$ [Hstack Hf]
  · iapply is_stack_valid v s n f0 E 0
    iframe; ipureintro; exact Hlocv
  iintro ⟨Hstack, Hf⟩
  simp only [vToEList, List.map_nil, List.nil_append]
  iapply wp_seq_imm [] iprop(isStack v s n ∗ ↪[frame] f0) $$ [Hstack Hf]
  · iapply is_stack_bound_valid v s n f0 E 0
    iframe; ipureintro; exact ⟨Hinst, Hlocv⟩
  iintro ⟨Hstack, Hf⟩
  simp only [vToEList, List.map_nil, List.nil_append]
  iapply spec_push_op f0 n v a s E $$ [Hf Hstack] HΦ
  iframe; ipureintro; exact ⟨Hinst, Hlocv, Hloca, Hlocs, Hlens⟩

/-! ### Validity -/

section valid
variable [LogrelNaInvs GF]
attribute [local instance] WasmG.invGS

/-- Lean helper: `stack_valid_unary` for the two-argument `push` (`[i32, i32] → []`). -/
private theorem stack_valid_binary (m : Nat) (i0 : Instance) (hm : i0.memory[0]? = some m)
    (op : List BasicInstruction)
    (Hop : ∀ v a stk, ⊢ ({{{{ isStack v stk m ∗
        ↪[frame] (⟨[valueOfUint v, .int32 a] ++ nZeros [.i32], i0⟩ : Frame) }}}} (toEList op)
        {{{{ w, interpVal [] w ∗ (∃ stk', isStack v stk' m) ∗ ∃ f1, ↪[frame] f1 }}}} : IProp GF)) :
    ⊢ (NonAtomicInvariant.inv (LogrelNaInvs.logrelNais (GF := GF)) stkN
        (stackModuleInv (fun a b => isStack a b m) (fun n => m ↦[wmlength] n)) -∗
      interpClosureNative i0 [.i32, .i32] [] [.i32]
        (toEList (validateStack 0 ++ validateStackBound 0 ++ op)) [] : IProp GF) := by
  unfold interpClosureNative
  iintro #Hstk %vcs %f Hv Hown Hf
  have hvcs : (interpVal [.i32, .i32] (.immV vcs) : IProp GF) ⊢
      ⌜∃ z0 z1, vcs = [.int32 z0, .int32 z1]⌝ := by
    unfold interpVal interpValues
    iintro (%h | ⟨%ws, %hws, Hws⟩)
    · cases h
    cases hws
    ihave %hlen := BigSepL2.bigSepL2_length $$ Hws
    match vcs, hlen with
    | [w0, w1], _ =>
      icases BigSepL2.bigSepL2_cons.1 $$ Hws with ⟨Hw0, Hws⟩
      icases BigSepL2.bigSepL2_cons.1 $$ Hws with ⟨Hw1, -⟩
      unfold interpValue interpValueI32
      icases Hw0 with %⟨z0, hz0⟩
      icases Hw1 with %⟨z1, hz1⟩
      ipureintro; exact ⟨z0, z1, by rw [hz0, hz1]⟩
  icases hvcs $$ Hv with %⟨z0, z1, hz⟩
  subst hz
  obtain ⟨v, hv⟩ := value_of_uint_repr z0
  rw [hv]
  iapply stack_valid_prefix m i0 hm [] op ([valueOfUint v, .int32 z1] ++ nZeros [.i32]) v rfl f []
    (fun v' stk hloc => by
      have h : valueOfUint v = valueOfUint v' := by simpa using hloc
      rw [h]; exact Hop v' z1 stk) $$ Hstk Hown Hf

@[rocq_alias iriswasm.valid_push]
theorem valid_push (m t : Nat) (funcs : List Funcaddr) :
    let i0 : Instance :=
      { types := [.tf [] [.i32], .tf [.i32] [.i32], .tf [.i32, .i32] []], funcs := funcs,
        tab := [t], memory := [m], globs := [] };
    ⊢ (NonAtomicInvariant.inv (LogrelNaInvs.logrelNais (GF := GF)) stkN
        (stackModuleInv (fun a b => isStack a b m) (fun n => m ↦[wmlength] n)) -∗
      interpClosureNative i0 [.i32, .i32] [] [.i32] (toEList push) [] : IProp GF) := by
  intro i0
  refine stack_valid_binary m i0 rfl pushOp ?_
  intro v a stk
  iintro !> %Φ ⟨Hs, Hf⟩ HΦ
  by_cases hlen : stk.length < two14 - 1
  · iapply spec_push_op (⟨[valueOfUint v, .int32 a] ++ nZeros [.i32], i0⟩ : Frame) m v a stk ⊤
      $$ [Hs Hf]
    · iframe; ipureintro; exact ⟨rfl, rfl, rfl, by simp [nZeros], hlen⟩
    iintro %w ⟨%hw, Hs, %f1, Hf, -⟩
    iapply HΦ
    subst hw
    iframe
    unfold interpVal interpValues; iright; iexists []
    isplitr
    · ipureintro; rfl
    iapply BigSepL2.bigSepL2_nil.2
    iempintro
  · rw [show toEList pushOp = toEList isFullOp ++ toEList (pushOp.drop 9) from rfl]
    iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV [valueOfInt 1]⌝ ∗ isStack v stk m ∗
      ↪[frame] (⟨[valueOfUint v, .int32 a] ++ nZeros [.i32], i0⟩ : Frame)))
    isplitr
    · iintro ⟨%h, -⟩; cases h
    isplitl [Hs Hf]
    · iapply spec_is_full_op (⟨[valueOfUint v, .int32 a] ++ nZeros [.i32], i0⟩ : Frame) m v stk ⊤
        $$ [Hs Hf]
      · iframe; ipureintro; exact ⟨rfl, rfl⟩
      iintro %w ⟨%k, %hw, Hs, %hk, Hf⟩
      rcases hk with ⟨rfl, -⟩ | ⟨-, h⟩
      · iframe; ipureintro; exact hw
      · exact absurd h hlen
    iintro %w ⟨%hw, Hs, Hf⟩
    subst hw
    rw [show ofVal (.immV [valueOfInt 1]) ++ toEList (pushOp.drop 9) =
      [.basic (.const (.int32 (Wasm.Int.intOfZ 1))),
        .basic (.if_ (.tf [] []) [.unreachable] [])] ++ toEList (pushOp.drop 10) from rfl]
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
