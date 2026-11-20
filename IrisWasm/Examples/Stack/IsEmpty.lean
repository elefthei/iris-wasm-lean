/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Examples.Stack.StackCommon
import IrisWasm.Logrel.IrisFundamental
import IrisWasm.Rules.Proofmode

/-! Port of `theories/iris/examples/stack/function/is_empty.v`. -/

namespace IrisWasm.Examples.Stack

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm

/-! ### Code -/

/-- `is_empty: [i32] -> [i32]`, locals declared: `[]`. Given a stack pointer, determine if the
stack is empty, by comparing the stack top pointer against the stack pointer itself. Returns 1 if
the stack is empty, 0 otherwise. -/
@[rocq_alias iriswasm.is_empty_op]
def isEmptyOp : List BasicInstruction :=
  [ .getLocal 0,
    .getLocal 0,
    .load .i32 none 0 0,
    .relop .i32 (.i .eq) ]

@[rocq_alias iriswasm.is_empty]
def isEmpty : List BasicInstruction :=
  validateStack 0 ++ validateStackBound 0 ++ isEmptyOp

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

private theorem eq_top (v l : Nat) (hl : l < two14) :
    ∃ k : _root_.Int, valueOfInt k =
      .int32 (wasmBool (appRelop (.i .eq) (valueOfUint v) (valueOfUint (v + l * 4)))) ∧
      ((k = 1 ∧ l = 0) ∨ (k = 0 ∧ l ≠ 0)) := by
  unfold two14 at hl
  by_cases h : l = 0
  · subst h
    refine ⟨1, ?_, .inl ⟨rfl, rfl⟩⟩
    simp [valueOfInt, valueOfUint, appRelop, appRelopI, Wasm.Int.ieq, wasmBool]
  · refine ⟨0, ?_, .inr ⟨rfl, h⟩⟩
    simp only [valueOfInt, valueOfUint, appRelop, appRelopI, Wasm.Int.ieq, wasmBool,
      Wasm.Int.intOfZ, Wasm.Int.repr, BitVec.ofInt_natCast]
    have : (BitVec.ofNat 32 v == BitVec.ofNat 32 (v + l * 4)) = false := by
      rw [beq_eq_false_iff_ne]; intro he
      have := congrArg BitVec.toNat he; simp at this; omega
    simp only [this]; rfl

/-! ### Specs -/

@[rocq_alias iriswasm.spec_is_empty_op]
theorem spec_is_empty_op (f0 : Frame) (n v : Nat) (s : List I32) (E : CoPset) :
    ⊢ ({{{{ ⌜f0.inst.memory[0]? = some n⌝ ∗ ⌜f0.locs[0]? = some (valueOfUint v)⌝ ∗
          ↪[frame] f0 ∗ isStack v s n }}}}
        (toEList isEmptyOp) @ E
      {{{{ w, ∃ k : _root_.Int, ⌜w = .immV [valueOfInt k]⌝ ∗ isStack v s n ∗
          ⌜(k = 1 ∧ s = []) ∨ (k = 0 ∧ s ≠ [])⌝ ∗ ↪[frame] f0 }}}} : IProp GF) := by
  iintro !> %Φ ⟨%Hinst, %Hlocv, Hf, Hstack⟩ HΦ
  icases stack_pure v s n $$ Hstack with ⟨-, -, %Hlens, Hstack⟩
  simp only [isEmptyOp, toEList, List.map]
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
  iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV [valueOfUint v, valueOfUint v]⌝ ∗ ↪[frame] f0))
  isplitr
  · iintro ⟨%h, -⟩; cases h
  isplitl [Hf]
  · take_drop_app_rewrite 1
    iapply wp_val_app1
    isplitr
    · iintro !> ⟨%h, -⟩; cases h
    iapply wp_get_local _ _ _ _ (fun w => iprop(⌜valCombine (.immV [valueOfUint v]) w =
      .immV [valueOfUint v, valueOfUint v]⌝)) _ Hlocv $$ [] Hf
    inext; ipureintro; rfl
  iintro %w ⟨%hw, Hf⟩
  subst hw
  take_drop_app_rewrite 3
  iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV [valueOfUint v, valueOfUint (v + s.length * 4)]⌝ ∗
    isStack v s n ∗ ↪[frame] f0))
  isplitr
  · iintro ⟨%h, -⟩; cases h
  isplitl [Hf Hstack]
  · take_drop_app_rewrite 1
    iapply wp_val_app1
    isplitr
    · iintro !> ⟨%h, -⟩; cases h
    iapply wp_wand_s $$ [Hf Hstack]
    · iapply stack_load_0 v s n f0 E $$ %Hinst Hstack Hf
    iintro %w ⟨%hw, Hstack, Hf⟩
    subst hw
    iframe; ipureintro; rfl
  iintro %w ⟨%hw, Hstack, Hf⟩
  subst hw
  simp only [ofVal, vToEList, List.map, List.cons_append, List.nil_append]
  obtain ⟨k, hk, hks⟩ := eq_top v s.length Hlens
  iapply wp_wand_s $$ [Hf]
  · iapply wp_relop (Φ := fun w => iprop(⌜w = .immV [valueOfInt k]⌝)) rfl $$ Hf
    inext; ipureintro; rw [hk]
  iintro %w ⟨%hw, Hf⟩
  iapply HΦ
  iexists k
  iframe
  ipureintro
  refine ⟨hw, ?_⟩
  rcases hks with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact .inl ⟨h1, List.eq_nil_of_length_eq_zero h2⟩
  · exact .inr ⟨h1, fun h => h2 (by simp [h])⟩

@[rocq_alias iriswasm.spec_is_empty]
theorem spec_is_empty (f0 : Frame) (n v : Nat) (s : List I32) (E : CoPset) :
    ⊢ ({{{{ ⌜f0.inst.memory[0]? = some n⌝ ∗ ⌜f0.locs[0]? = some (valueOfUint v)⌝ ∗
          ↪[frame] f0 ∗ isStack v s n }}}}
        (toEList isEmpty) @ E
      {{{{ w, ∃ k : _root_.Int, ⌜w = .immV [valueOfInt k]⌝ ∗ isStack v s n ∗
          ⌜(k = 1 ∧ s = []) ∨ (k = 0 ∧ s ≠ [])⌝ ∗ ↪[frame] f0 }}}} : IProp GF) := by
  iintro !> %Φ ⟨%Hinst, %Hlocv, Hf, Hstack⟩ HΦ
  rw [show toEList isEmpty = toEList (validateStack 0) ++
    (toEList (validateStackBound 0) ++ toEList isEmptyOp) by
      simp [isEmpty, toEList]]
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
  iapply spec_is_empty_op f0 n v s E $$ [Hf Hstack] HΦ
  iframe; ipureintro; exact ⟨Hinst, Hlocv⟩

attribute [local instance] WasmG.invGS in
theorem stack_fupd_wp {s : Stuckness} {E : CoPset} {e : Expr} {Φ : Val → IProp GF} :
    (|={E}=> WP e @ s ; E {{ Φ }}) ⊢ WP e @ s ; E {{ Φ }} :=
  IrisWp.fupd_wp (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)

instance pointsToI32_timeless (n i : Nat) (v : I32) : Timeless (n ↦[i32][ i ] v : IProp GF) := by
  unfold pointsToI32; infer_instance

instance isStack_timeless (v : Nat) (s : List I32) (n : Nat) :
    Timeless (isStack v s n : IProp GF) := by
  unfold isStack memBlockAtPos; infer_instance

instance stackModuleInv_timeless (P : Nat → List I32 → IProp GF) (Q : Nat → IProp GF)
    [∀ a b, Timeless (P a b)] [∀ n, Timeless (Q n)] : Timeless (stackModuleInv P Q) := by
  unfold stackModuleInv; infer_instance

/-- Lean helper: `c; if [] [unreachable] []` with `c ≠ 0` traps, whatever follows. -/
theorem wp_if_unreachable_trap (c : I32) (hc : c ≠ Wasm.Int.zero) (f : Frame) (es : Expr) :
    ⊢ (↪[frame] f -∗ WP ([.basic (.const (.int32 c)),
        .basic (.if_ (.tf [] []) [.unreachable] [])] ++ es : Expr)
      {{ w, ⌜w = .trapV⌝ ∗ ↪[frame] f }} : IProp GF) := by
  iintro Hf
  iapply wp_seq_trap _ _ _ _ f f
  iframe
  iintro Hf
  iapply wp_if_true hc $$ Hf
  iintro !> Hf
  rw [show ([.basic (.block (.tf [] []) [.unreachable])] : Expr) =
    [] ++ [.basic (.block (.tf [] []) [.unreachable])] from rfl]
  iapply wp_block (vs := []) rfl rfl rfl rfl $$ Hf
  iintro !> Hf
  iapply wp_wand_s (Φ := fun w => iprop(⌜w = .trapV⌝ ∗ ↪[frame] f)) $$ [Hf]
  · rw [show ([.label ([] : List ValueType).length [] ([] ++ toEList [.unreachable])] : Expr) =
      [] ++ [.label 0 [] [.basic .unreachable]] ++ [] from rfl]
    iapply IrisRulesTrap.wp_label_trap _ _ _ [] _ _ [] _ _ rfl $$ Hf
    iintro Hf
    iapply wp_unreachable (Φ := fun w => iprop(⌜w = .trapV⌝)) $$ Hf
    inext; ipureintro; rfl
  · iintro %w H; iexact H

/-! ### Validity -/

section valid
variable [LogrelNaInvs GF]
attribute [local instance] WasmG.invGS

/-- Lean helper: leaving the function's label and frame with an `interpVal` result. -/
theorem stack_valid_finish (tf2s : List ValueType) (f f1 : Frame)
    (hl : List (Hostfuncidx × FunctionType)) (w : Val) :
    (iprop(interpVal tf2s w ∗ NonAtomicInvariant.own (LogrelNaInvs.logrelNais (GF := GF)) ⊤ ∗ ↪[frame] f1) : IProp GF) ⊢
    WP (ofVal w) CTX 1 ; (Lholed.rec_ [] tf2s.length [] (.base [] []) [])
      {{ w, ∃ f', (↪[frame] f -∗ WP (ofVal w) FRAME tf2s.length ; f'
        {{ v, (interpVal tf2s v ∨ interpCallHostCls hl tf2s v) ∗
          NonAtomicInvariant.own (LogrelNaInvs.logrelNais (GF := GF)) ⊤ ∗ ↪[frame] f }}) ∗ ↪[frame] f' }} := by
  unfold interpVal interpValues
  iintro ⟨Hw, Hown, Hf⟩
  deconstruct_ctx
  isimp only [List.append_nil]
  icases Hw with (%hw | ⟨%ws, %hw, Hws⟩)
  · subst hw
    iapply wp_wand_s $$ [Hf]
    · iapply wp_label_trap (Φ := fun w => iprop(⌜w = .trapV⌝)) (to_of_val _) $$ Hf
      inext; ipureintro; rfl
    iintro %v ⟨%hv, Hf⟩
    subst hv
    iexists f1
    iframe
    iintro Hf
    unfold wpWasmFrame
    simp only [ofVal]
    iapply wp_wand_s $$ [Hf]
    · have h := wp_frame_trap (GF := GF) .NotStuck ⊤ (fun w => iprop(⌜w = .trapV⌝)) tf2s.length f1 f
      unfold wpWasmFrame at h
      iapply h $$ Hf
      inext; ipureintro; rfl
    iintro %v ⟨%hv, Hf⟩
    subst hv
    iframe
    ileft; ileft; ipureintro; rfl
  · subst hw
    ihave %hlen := BigSepL2.bigSepL2_length $$ Hws
    iapply wp_wand_s $$ [Hf]
    · iapply wp_label_value (Φ := fun w => iprop(⌜w = .immV ws⌝)) (to_of_val _) $$ Hf
      inext; ipureintro; rfl
    iintro %v ⟨%hv, Hf⟩
    subst hv
    iexists f1
    iframe
    iintro Hf
    unfold wpWasmFrame
    iapply wp_wand_s $$ [Hf]
    · have h := wp_frame_value (GF := GF) .NotStuck ⊤ (fun w => iprop(⌜w = .immV ws⌝)) _ tf2s.length
        f1 f ws (to_of_val _) (by simp [ofVal, vToEList, hlen])
      unfold wpWasmFrame at h
      iapply h $$ Hf
      inext; ipureintro; rfl
    iintro %v ⟨%hv, Hf⟩
    subst hv
    iframe
    ileft; iright; iexists ws; iframe; ipureintro; rfl

theorem valueOfUint_nOfUint (v : Nat) :
    valueOfUint (Wasm.Int.nOfUint (Wasm.Int.intOfZ (w := 32) (v : _root_.Int))) = valueOfUint v := by
  simp only [valueOfUint, Wasm.Int.nOfUint, Wasm.Int.intOfZ, Wasm.Int.repr, BitVec.ofInt_natCast,
    BitVec.toNat_ofNat, Value.int32.injEq]
  apply BitVec.eq_of_toNat_eq; simp

/-- Lean helper shared by the `valid_*` proofs of the stack functions: run the validation prefix
`validate_stack 0 ++ validate_stack_bound 0` under the stack module invariant, then `op`. -/
theorem stack_valid_prefix (m : Nat) (i0 : Instance) (hm : i0.memory[0]? = some m)
    (tf2s : List ValueType) (op : List BasicInstruction) (locs : List Value) (v : Nat)
    (hl0 : locs[0]? = some (valueOfUint v)) (f : Frame) (hl : List (Hostfuncidx × FunctionType))
    (Hop : ∀ v' stk, locs[0]? = some (valueOfUint v') →
      ⊢ ({{{{ isStack v' stk m ∗ ↪[frame] (⟨locs, i0⟩ : Frame) }}}} (toEList op)
        {{{{ w, interpVal tf2s w ∗ (∃ stk', isStack v' stk' m) ∗ ∃ f1, ↪[frame] f1 }}}} : IProp GF)) :
    ⊢ (NonAtomicInvariant.inv (LogrelNaInvs.logrelNais (GF := GF)) stkN
        (stackModuleInv (fun a b => isStack a b m) (fun n => m ↦[wmlength] n)) -∗
      NonAtomicInvariant.own (LogrelNaInvs.logrelNais (GF := GF)) ⊤ -∗ ↪[frame] f -∗
      WP (toEList (validateStack 0 ++ validateStackBound 0 ++ op)) FRAME tf2s.length ;
        (⟨locs, i0⟩ : Frame) CTX 1 ; (Lholed.rec_ [] tf2s.length [] (.base [] []) [])
        {{ v, (interpVal tf2s v ∨ interpCallHostCls hl tf2s v) ∗
          NonAtomicInvariant.own (LogrelNaInvs.logrelNais (GF := GF)) ⊤ ∗ ↪[frame] f }} : IProp GF) := by
  iintro #Hstk Hown Hf
  unfold wpWasmCtxFrame
  iintro %LI %hLI
  simp [lfilled, lfill, constList] at hLI
  subst hLI
  have h1 : toVal (toEList (validateStack 0 ++ (validateStackBound 0 ++ op))) = none :=
    to_val_None_append [.basic (.getLocal 0)] _ (by simp [toVal_singleton, toValInstr, valOfValNotVal])
  have h2 : toVal [AdministrativeInstruction.local tf2s.length ⟨locs, i0⟩
      [.label tf2s.length [] (toEList (validateStack 0 ++ (validateStackBound 0 ++ op)))]] = none := by
    simp [toVal_singleton, toValInstr_local, toValInstr_label, h1, valOfValNotVal]
  have hb := wp_frame_bind (GF := GF) .NotStuck ⊤ (fun v => iprop((interpVal tf2s v ∨
    interpCallHostCls hl tf2s v) ∗ NonAtomicInvariant.own (LogrelNaInvs.logrelNais (GF := GF)) ⊤ ∗
    ↪[frame] f)) tf2s.length ⟨locs, i0⟩ f
    [.label tf2s.length [] (toEList (validateStack 0 ++ (validateStackBound 0 ++ op)))] h2
  unfold wpWasmFrame at hb
  iapply hb $$ Hf
  iintro Hf
  iapply wp_build_ctx (toEList (validateStack 0 ++ (validateStackBound 0 ++ op))) 1
    (.rec_ [] tf2s.length [] (.base [] []) []) _ _ _ _
    ⟨by simp [lfilled, lfill, constList]⟩
  iapply wp_label_bind
  have hfin := fun w f1 => stack_valid_finish (GF := GF) tf2s f f1 hl w
  unfold wpWasmFrame at hfin
  have hfin2 := hfin
  unfold wpWasmCtx at hfin2
  have happ : ∀ a b : List BasicInstruction, toEList (a ++ b) = toEList a ++ toEList b :=
    fun _ _ => List.map_append
  rw [happ]
  iapply wp_build_ctx (toEList (validateStack 0) ++ toEList (validateStackBound 0 ++ op)) 0
    (.base [] []) _ _ _ _ ⟨by simp [lfilled, lfill, constList]⟩
  iapply wp_seq_can_trap_ctx .NotStuck ⊤ _ (fun w => iprop(⌜w = .immV []⌝ ∗ ⌜65536 ∣ v⌝))
    (toEList (validateStack 0)) (toEList (validateStackBound 0 ++ op)) 0 (.base [] [])
    (fun f0 => iprop(⌜f0 = ⟨locs, i0⟩⌝ ∗ NonAtomicInvariant.own (LogrelNaInvs.logrelNais (GF := GF)) ⊤))
    ⟨locs, i0⟩
  isplitr
  · iintro ⟨%h, -⟩; cases h
  isplitr
  · iintro %f0 ⟨Hf, -, Hown⟩
    iapply hfin .trapV f0
    iframe
    unfold interpVal; ileft; ipureintro; rfl
  isplitl [Hf]
  · iexact Hf
  isplitl [Hown]
  · iintro Hf
    iapply wp_wand_s $$ [Hf]
    · iapply check_stack_valid v ⟨locs, i0⟩ ⊤ 0
      iframe; ipureintro; exact hl0
    iintro %w ⟨Hw, Hf⟩
    isplitl [Hw]
    · iexact Hw
    iexists ⟨locs, i0⟩
    iframe
    ipureintro; rfl
  iintro %w %f0 ⟨⟨%hw, %hdiv⟩, Hf, %hf0, Hown⟩
  subst hw hf0
  iapply wp_deconstruct_ctx _ 0 (.base [] []) (toEList (validateStackBound 0 ++ op)) _ _ _
    ⟨by simp [lfilled, lfill, constList, ofVal, vToEList]⟩
  iapply IrisWp.fupd_wp (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
  imod NonAtomicInvariant.inv_acc CoPset.subseteq_top CoPset.subseteq_top $$ Hstk Hown with
    ⟨>Hres, Hown, Hcls⟩
  unfold stackModuleInv
  icases Hres with ⟨%l, %Hmul, Hlen, %l', %Hmultiple, Hl'⟩
  imodintro
  rw [happ]
  by_cases hk : Wasm.Int.nOfUint (Wasm.Int.intOfZ (w := 32) (v : _root_.Int)) < l
  · have hdiv' := div_mod_i32 v hdiv
    have hin := multiples_upto_in pageSize l l' _ Hmultiple hk (by simpa [pageSize] using hdiv')
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hin
    have hset : l'.set i (Wasm.Int.nOfUint (Wasm.Int.intOfZ (w := 32) (v : _root_.Int))) = l' := by
      obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.1 hi
      rw [← heq]; exact List.set_getElem_self hlt
    have hloc' : locs[0]? = some (valueOfUint
        (Wasm.Int.nOfUint (Wasm.Int.intOfZ (w := 32) (v : _root_.Int)))) := by
      rw [valueOfUint_nOfUint]; exact hl0
    have hacc : ([∗list] s ∈ l', iprop(∃ stk, isStack s stk m) : IProp GF) ⊢
        iprop((∃ stk, isStack (Wasm.Int.nOfUint (Wasm.Int.intOfZ (w := 32) (v : _root_.Int))) stk m) ∗
          ((∃ stk, isStack (Wasm.Int.nOfUint (Wasm.Int.intOfZ (w := 32) (v : _root_.Int))) stk m) -∗
            [∗list] s ∈ l', iprop(∃ stk, isStack s stk m))) := by
      have h := (BigSepL.bigSepL_lookup_acc (Φ := fun _ s => (iprop(∃ stk, isStack s stk m) : IProp GF)) hi).1
      have h2 := h.trans (BI.sep_mono_right (BI.forall_elim
        (Wasm.Int.nOfUint (Wasm.Int.intOfZ (w := 32) (v : _root_.Int)))))
      rw [hset] at h2; exact h2
    icases hacc $$ Hl' with ⟨⟨%stk, Hv⟩, Hl'⟩
    iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV []⌝ ∗
      isStack (Wasm.Int.nOfUint (Wasm.Int.intOfZ (w := 32) (v : _root_.Int))) stk m ∗
      ↪[frame] (⟨locs, i0⟩ : Frame)))
    isplitr
    · iintro ⟨%h, -⟩; cases h
    isplitl [Hv Hf]
    · iapply is_stack_bound_valid _ stk m ⟨locs, i0⟩ ⊤ 0
      iframe; ipureintro; exact ⟨hm, hloc'⟩
    iintro %w ⟨%hw, Hv, Hf⟩
    subst hw
    simp only [show ofVal (Val.immV []) = [] from rfl, List.nil_append]
    iapply Hop _ stk hloc' $$ [Hv Hf]
    · iframe
    iintro %w ⟨Hw, ⟨%stk', Hv⟩, %f1, Hf⟩
    unfold wpWasmCtx
    iintro %LI %hLI
    iapply stack_fupd_wp
    imod Hcls $$ [Hlen Hl' Hv Hown] with Hown
    · iframe
      isplitr
      · ipureintro; exact Hmul
      iexists l'
      isplitr
      · ipureintro; exact Hmultiple
      inext
      iapply Hl'
      iexists stk'
      iexact Hv
    imodintro
    ihave H := hfin2 w f1 $$ [Hw Hown Hf]
    · iframe
    ihave H2 := H $$ %LI %hLI
    iexact H2
  · iapply wp_wand_s $$ [Hlen Hf]
    · iapply fail_stack_bound_valid v m ⟨locs, i0⟩ ⊤ 0 l (toEList op)
      iframe; ipureintro; exact ⟨hm, hl0, by omega⟩
    iintro %w ⟨%hw, Hlen, Hf⟩
    subst hw
    unfold wpWasmCtx
    iintro %LI %hLI
    iapply stack_fupd_wp
    imod Hcls $$ [Hlen Hl' Hown] with Hown
    · iframe
      ipureintro; exact ⟨Hmul, Hmultiple⟩
    imodintro
    ihave H := hfin2 .trapV ⟨locs, i0⟩ $$ [Hown Hf]
    · iframe
      unfold interpVal; ileft; ipureintro; rfl
    ihave H2 := H $$ %LI %hLI
    iexact H2

/-- Lean helper: `valid_*` for a stack function `[i32] → [i32]` built from the validation prefix and
`op` (Coq repeats this proof in each `valid_*` lemma). -/
theorem stack_valid_unary (m : Nat) (i0 : Instance) (hm : i0.memory[0]? = some m)
    (tlocs : List ValueType) (op : List BasicInstruction)
    (Hop : ∀ v stk, ⊢ ({{{{ isStack v stk m ∗
        ↪[frame] (⟨[valueOfUint v] ++ nZeros tlocs, i0⟩ : Frame) }}}} (toEList op)
        {{{{ w, interpVal [.i32] w ∗ (∃ stk', isStack v stk' m) ∗ ∃ f1, ↪[frame] f1 }}}} : IProp GF)) :
    ⊢ (NonAtomicInvariant.inv (LogrelNaInvs.logrelNais (GF := GF)) stkN
        (stackModuleInv (fun a b => isStack a b m) (fun n => m ↦[wmlength] n)) -∗
      interpClosureNative i0 [.i32] [.i32] tlocs
        (toEList (validateStack 0 ++ validateStackBound 0 ++ op)) [] : IProp GF) := by
  unfold interpClosureNative
  iintro #Hstk %vcs %f Hv Hown Hf
  have hvcs : (interpVal [.i32] (.immV vcs) : IProp GF) ⊢ ⌜∃ z, vcs = [.int32 z]⌝ := by
    unfold interpVal interpValues
    iintro (%h | ⟨%ws, %hws, Hws⟩)
    · cases h
    cases hws
    ihave %hlen := BigSepL2.bigSepL2_length $$ Hws
    match vcs, hlen with
    | [w0], _ =>
      icases BigSepL2.bigSepL2_cons.1 $$ Hws with ⟨Hw0, -⟩
      unfold interpValue interpValueI32
      icases Hw0 with %⟨z, hz⟩
      ipureintro; exact ⟨z, by rw [hz]⟩
  icases hvcs $$ Hv with %⟨z, hz⟩
  subst hz
  obtain ⟨v, hv⟩ := value_of_uint_repr z
  rw [hv]
  iapply stack_valid_prefix m i0 hm [.i32] op ([valueOfUint v] ++ nZeros tlocs) v rfl f []
    (fun v' stk hloc => by
      have h : valueOfUint v = valueOfUint v' := by simpa using hloc
      rw [h]; exact Hop v' stk) $$ Hstk Hown Hf

omit [LogrelNaInvs GF] in
/-- Lean helper: a single `i32` is in the value relation of `[i32]`. -/
theorem interpVal_i32 (c : Value) (h : ∃ z, c = .int32 z) :
    ⊢ (interpVal [.i32] (.immV [c]) : IProp GF) := by
  unfold interpVal interpValues; iright; iexists [c]
  isplitr
  · ipureintro; rfl
  iapply BigSepL2.bigSepL2_cons.2
  isplitl []
  · unfold interpValue interpValueI32; ipureintro; exact h
  iapply BigSepL2.bigSepL2_nil.2
  iempintro

@[rocq_alias iriswasm.valid_is_empty]
theorem valid_is_empty (m t : Nat) (funcs : List Funcaddr) :
    let i0 : Instance :=
      { types := [.tf [] [.i32], .tf [.i32] [.i32], .tf [.i32, .i32] []], funcs := funcs,
        tab := [t], memory := [m], globs := [] };
    ⊢ (NonAtomicInvariant.inv (LogrelNaInvs.logrelNais (GF := GF)) stkN
        (stackModuleInv (fun a b => isStack a b m) (fun n => m ↦[wmlength] n)) -∗
      interpClosureNative i0 [.i32] [.i32] [] (toEList isEmpty) [] : IProp GF) := by
  intro i0
  refine stack_valid_unary m i0 rfl [] isEmptyOp ?_
  intro v stk
  iintro !> %Φ ⟨Hs, Hf⟩ HΦ
  iapply spec_is_empty_op (⟨[valueOfUint v] ++ nZeros [], i0⟩ : Frame) m v stk ⊤ $$ [Hs Hf]
  · iframe; ipureintro; exact ⟨rfl, rfl⟩
  iintro %w ⟨%k, %hw, Hs, -, Hf⟩
  iapply HΦ
  subst hw
  iframe
  iapply interpVal_i32 (valueOfInt k) ⟨_, rfl⟩

end valid

end stack

end IrisWasm.Examples.Stack
