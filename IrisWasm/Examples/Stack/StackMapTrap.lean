/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Examples.Stack.StackMap
import IrisWasm.Logrel.IrisLogrel
import IrisWasm.Rules.Proofmode

/-! Port of `theories/iris/examples/stack/function/stack_map_trap.v`.

The Coq file's `Section valid` (`interp_table_persistent` and a second `valid_push`) is entirely
commented out upstream, so it has no Lean counterpart. -/

namespace IrisWasm.Examples.Stack

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm

section specs
variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF] [LogrelNaInvs GF]

attribute [local instance] WasmG.invGS

local notation "logrelNais" => LogrelNaInvs.logrelNais (GF := GF)

/-- The closure part of the trap-aware map specs (the Coq `match a with … end` conjunct): when the
table entry holds `some a`, the closure `a ↦[wf] cl` lives in a non-atomic invariant `γ2` and
satisfies the per-element spec relating `Φ` and `Ψ` (possibly trapping). -/
@[reducible] def mapClosureSpec (finst : Instance) (E : CoPset) (γ1 : Namespace)
    (a : Option Nat) (cl : FunctionClosure) (Φ : I32 → IProp GF) (Ψ : I32 → I32 → IProp GF) :
    IProp GF :=
  match a with
  | some a => iprop(∃ γ2 : Namespace, ⌜(↑γ2 : CoPset) ⊆ E ∧ (↑γ2 : CoPset) ⊆ ⊤ \ ↑γ1⌝ ∗
      NonAtomicInvariant.inv logrelNais γ2 (a ↦[wf] cl) ∗
      ⌜clType cl = .tf [.i32] [.i32]⌝ ∗
      (∀ (u : I32) (fc : Frame),
        {{{{ Φ u ∗ ⌜finst = fc.inst⌝ ∗ ↪[frame] fc ∗ NonAtomicInvariant.own logrelNais ⊤ }}}}
          ([.basic (.const (.int32 u)), .invoke a] : Expr) @ E
          {{{{ w, (⌜w = .trapV⌝ ∨ (∃ v, ⌜w = .immV [.int32 v]⌝ ∗ Ψ u v)) ∗
              NonAtomicInvariant.own logrelNais ⊤ ∗ ↪[frame] fc }}}}))
  | none => iprop(True)

instance mapClosureSpec_persistent (finst : Instance) (E : CoPset) (γ1 : Namespace)
    (a : Option Nat) (cl : FunctionClosure) (Φ : I32 → IProp GF) (Ψ : I32 → I32 → IProp GF) :
    Persistent (mapClosureSpec finst E γ1 a cl Φ Ψ) := by
  cases a <;> unfold mapClosureSpec <;> infer_instance

@[rocq_alias iriswasm.spec_map_loop_body_continue_trap]
theorem spec_map_loop_body_continue_trap (f : Frame) (s : List I32) (v n : Nat) (E : CoPset)
    (j : Nat) (fn sv : I32) (j0 : Nat) (a : Option Nat) (cl : FunctionClosure)
    (Φ : I32 → IProp GF) (Ψ : I32 → I32 → IProp GF) (γ1 : Namespace) :
    (↑γ1 : CoPset) ⊆ E →
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
          NonAtomicInvariant.inv logrelNais γ1 (j0 ↦[wt][ Wasm.Int.natOfUint fn ] a) ∗
          mapClosureSpec f.inst E γ1 a cl Φ Ψ ∗
          NonAtomicInvariant.own logrelNais ⊤ ∗ ↪[frame] f }}}}
      (toEList mapLoopBody) @ E
      {{{{ w, (⌜w = .trapV⌝ ∨ ⌜w = .brV (ValidHoled.base [] [] : ValidHoled 0)⌝ ∗
            (∃ sv' : I32, isStack v (s.set j sv') n ∗ Ψ sv sv')) ∗
          NonAtomicInvariant.own logrelNais ⊤ ∗
          ↪[frame] (⟨f.locs.set 2 (valueOfUint (v + s.length * 4 - 4 * j)), f.inst⟩ : Frame)
      }}}} : IProp GF) := by
  intro hsub
  let f' : Frame := ⟨f.locs.set 2 (valueOfUint (v + s.length * 4 - 4 * j)), f.inst⟩
  let addr := valueOfUint (v + s.length * 4 - 4 * j)
  iintro !> %Ξ ⟨%hmem, %hl0, %hl1, %hl2, %hl3, %hlen, %hj, %hsv, Hs, HΦ, %htypes, %htab, #Htabinv,
    Hcl, Hown, Hf⟩ HΞ
  iapply wp_wand' $$ [-HΞ] HΞ
  iapply map_loop_body_prefix f s v n j sv fn E _ hmem hl1 hl2 hl3 hlen hj.2 hsv $$ Hs Hf
  iintro Hs Hf
  take_drop_app_rewrite 4
  iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).2
  iapply wp_seq_can_trap_ctx _ _ _
    (fun w => iprop(∃ v0, ⌜w = .immV [addr, .int32 v0]⌝ ∗ Ψ sv v0)) _ _ _ _
    (fun f0 => iprop(⌜f0 = f'⌝ ∗ NonAtomicInvariant.own logrelNais ⊤)) f'
  isplitr
  · iintro ⟨%v0, %h, -⟩; cases h
  isplitr
  · iintro %f0 ⟨Hf, %hf0, Hown⟩
    subst hf0
    iframe
    ileft; ipureintro; rfl
  iframe
  isplitl [HΦ Hcl Hown]
  · iintro Hf
    take_drop_app_rewrite 1
    iapply wp_val_can_trap_app _ _ _ [.basic (.const addr)] [addr] _ _ _
      (by simp [toVal, mergeValuesList, toValInstr, mergeValues])
    isplitr
    · imodintro; iintro ⟨%v0, %h, -⟩; cases h
    iframe
    iintro Hf
    iapply IrisWp.fupd_wp (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
    imod NonAtomicInvariant.inv_acc hsub CoPset.subseteq_top $$ Htabinv Hown
      with ⟨Htab, Hown, Hcls'⟩
    imod Htab
    cases a with
    | some a =>
      icases Hcl with ⟨%γ2, %⟨hsub2, hdiff⟩, #Hclinv, %hclt, #Hspec⟩
      imod NonAtomicInvariant.inv_acc hsub2 hdiff $$ Hclinv Hown with ⟨Hcl, Hown, Hcls⟩
      imod Hcl
      imodintro
      iapply wp_ctx_base_cons
      iapply wp_call_indirect_success_ctx _ _ _ f' 1 j0 a fn cl 0 _
        (by simpa [hclt] using htypes) htab $$ Htab Hcl Hf
      iintro !> ⟨Htab, Hcl, Hf⟩
      iapply wp_base
      isimp only [vToEList, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
        List.append_nil]
      iapply IrisWp.fupd_wp (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
      imod Hcls $$ [Hcl Hown] with Hown
      · iframe
      imod Hcls' $$ [Htab Hown] with Hown
      · iframe
      imodintro
      ispecialize Hspec $$ %sv %f'
      iapply Hspec $$ [HΦ Hf Hown]
      · iframe; ipureintro; rfl
      iintro %w ⟨Hret, Hown, Hf⟩
      isplitl [Hret]
      · icases Hret with (%hw | ⟨%v0, %hw, HΨ⟩)
        · ileft; ipureintro; exact hw
        · iright; subst hw; iexists v0; iframe; ipureintro; rfl
      iexists f'; iframe; ipureintro; rfl
    | none =>
      imodintro
      rw [show ([.basic (.const (.int32 sv)), .basic (.const (.int32 fn)), .basic (.callIndirect 1)]
        : Expr) = [.basic (.const (.int32 sv))] ++ [.basic (.const (.int32 fn)),
          .basic (.callIndirect 1)] from rfl]
      iapply wp_val_can_trap_app _ _ _ [.basic (.const (.int32 sv))] [.int32 sv] _ _ _
        (by simp [toVal, mergeValuesList, toValInstr, mergeValues])
      isplitr
      · imodintro; iintro ⟨%v0, %h, -⟩; cases h
      iframe
      iintro Hf
      iapply IrisWp.wp_fupd (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
      iapply wp_wand' $$ [Htab Hf]
      · iapply wp_call_indirect_failure_noindex _ _ (fun w => iprop(⌜w = .trapV⌝)) f' 1 j0 fn
          htab $$ Htab Hf
        inext; ipureintro; rfl
      iintro %w ⟨⟨%hw, Htab⟩, Hf⟩
      imod Hcls' $$ [Htab Hown] with Hown
      · iframe
      imodintro
      isplitr
      · ileft; ipureintro; exact hw
      iexists f'; iframe; ipureintro; rfl
  iintro %w %f0 ⟨⟨%v0, %hw, HΨ⟩, Hf, %hf0, Hown⟩
  subst hw hf0
  iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).1
  isimp only [ofVal, vToEList, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  iapply wp_wand' $$ [Hs Hf]
  · iapply map_loop_body_suffix f' s v n j sv v0 E hmem hj.2 hsv $$ Hs Hf
  iintro %w ⟨%hw, Hs, Hf⟩
  iframe
  iright
  iframe
  ipureintro; exact hw

@[rocq_alias iriswasm.spec_map_loop_j_trap]
theorem spec_map_loop_j_trap (f : Frame) (s : List I32) (v n : Nat) (E : CoPset) (j : Nat)
    (fn : I32) (j0 : Nat) (a : Option Nat) (cl : FunctionClosure) (Φ : I32 → IProp GF)
    (Ψ : I32 → I32 → IProp GF) (s' : List I32) (γ1 : Namespace) :
    (↑γ1 : CoPset) ⊆ E →
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
          NonAtomicInvariant.inv logrelNais γ1 (j0 ↦[wt][ Wasm.Int.natOfUint fn ] a) ∗
          mapClosureSpec f.inst E γ1 a cl Φ Ψ ∗
          NonAtomicInvariant.own logrelNais ⊤ ∗ ↪[frame] f) -∗
      wpWasmCtx .NotStuck E (toEList mapLoopBody)
        (fun w => iprop((⌜w = .trapV⌝ ∨
            (⌜w = .immV []⌝ ∗ (∃ s', isStack v s' n ∗ stackAll2 s s' Ψ))) ∗
          (∃ f1, ↪[frame] f1 ∗ NonAtomicInvariant.own logrelNais ⊤ ∗ ⌜f.inst = f1.inst⌝)))
        2 (pushBase (.rec_ [] 0 [] (.base [] []) []) 0
          [.basic (.loop (.result none) mapLoopBody)] [] [])
      : IProp GF) := by
  intro hsub
  induction j generalizing f s' with
  | zero =>
    iintro ⟨%hmem, %hl0, %hl1, %hl2, %hl3, %hlen, -, %hlen', Hs, -, HΨ, -, -, -, -, Hown, Hf⟩
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
    isplitl [Hs HΨ]
    · iright; isplitr
      · ipureintro; rfl
      iexists s'; iframe
    iexists f; iframe; ipureintro; rfl
  | succ j ih =>
    iintro ⟨%hmem, %hl0, %hl1, %hl2, %hl3, %hlen, %hj, %hlen', Hs, HΦ, HΨ, %htypes, %htab,
      #Htab, #Hcl, Hown, Hf⟩
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
    iapply spec_map_loop_body_continue_trap f (s.take (j + 1) ++ s') v n E j fn sv j0 a cl Φ Ψ γ1
      hsub $$ [Hs HΦsv Hown Hf]
    · rw [hL]
      have hl2' : f.locs[2]? = some (valueOfUint (v + s.length * 4 - 4 * j - 4)) := by
        rw [hl2, Nat.mul_add, Nat.sub_add_eq]
      iframe
      repeat (isplitr; · ipureintro; first | assumption | exact ⟨by omega, by omega⟩)
      isplitr
      · iexact Htab
      iexact Hcl
    iintro %w ⟨Hres, Hown, Hf⟩
    icases Hres with (%hw | ⟨%hw, %sv'', Hs, HΨ'⟩)
    · subst hw
      iapply wp_wand_ctx _ _ _ (fun w => iprop(⌜w = .trapV⌝ ∗
        ↪[frame] (⟨f.locs.set 2 (valueOfUint (v + (s.take (j + 1) ++ s').length * 4 - 4 * j)),
          f.inst⟩ : Frame))) $$ [Hf]
      · rw [show ofVal .trapV = [] ++ [AdministrativeInstruction.trap] ++ [] from rfl]
        iapply wp_trap_ctx _ _ _ _ _ _ _ rfl $$ Hf
      iintro %w ⟨%hw, Hf⟩
      isplitr
      · ileft; ipureintro; exact hw
      iexists _; iframe; ipureintro; rfl
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
      (sv'' :: s') $$ [Hs HΦ HΨ HΨ' Hown Hf]
    rw [hdrop]
    simp only [stackAll2]
    iframe
    repeat (isplitr; · ipureintro; first | assumption | exact ⟨by omega, by omega⟩ |
      (simp only [List.length_cons]; omega) | (simp [List.getElem?_set, hl0, hl1, hl3] <;> omega))
    isplitr
    · iexact Htab
    iexact Hcl

@[rocq_alias iriswasm.spec_stack_map_op_trap]
theorem spec_stack_map_op_trap (f0 : Frame) (n : Immediate) (f : I32) (v : Nat) (s : List I32)
    (E : CoPset) (j0 : Nat) (a : Option Nat) (cl : FunctionClosure) (γ1 : Namespace)
    (Φ : I32 → IProp GF) (Ψ : I32 → I32 → IProp GF) :
    (↑γ1 : CoPset) ⊆ E →
    ⊢ ({{{{ ⌜f0.inst.memory[0]? = some n⌝ ∗
          ⌜f0.locs[0]? = some (valueOfUint v)⌝ ∗
          ⌜f0.locs[1]? = some (.int32 f)⌝ ∗
          ⌜f0.locs.length ≥ 4⌝ ∗
          isStack v s n ∗
          stackAll s Φ ∗
          ⌜f0.inst.types[1]? = some (.tf [.i32] [.i32])⌝ ∗
          ⌜f0.inst.tab[0]? = some j0⌝ ∗
          NonAtomicInvariant.inv logrelNais γ1 (j0 ↦[wt][ Wasm.Int.natOfUint f ] a) ∗
          mapClosureSpec f0.inst E γ1 a cl Φ Ψ ∗
          NonAtomicInvariant.own logrelNais ⊤ ∗ ↪[frame] f0 }}}}
      (toEList mapOp) @ E
      {{{{ w, (⌜w = .trapV⌝ ∨ (⌜w = .immV []⌝ ∗ (∃ s', isStack v s' n ∗ stackAll2 s s' Ψ))) ∗
          (∃ f1, ↪[frame] f1 ∗ NonAtomicInvariant.own logrelNais ⊤ ∗ ⌜f0.inst = f1.inst⌝)
      }}}} : IProp GF) := by
  intro hsub
  iintro !> %Ξ ⟨%hmem, %hl0, %hl1, %hlen, Hs, HΦ, %htypes, %htab, #Htab, #Hcl, Hown, Hf⟩ HΞ
  let fr : Frame :=
    ⟨(f0.locs.set 3 (valueOfUint (v + s.length * 4))).set 2 (valueOfUint v), f0.inst⟩
  rw [show (toEList mapOp : Expr) = toEList mapInitialise ++
    [.basic (.block (.result none) [.loop (.result none) mapLoopBody])] by simp [mapOp, toEList]]
  iapply wp_seq_imm [] iprop(isStack v s n ∗ ↪[frame] fr) $$ [Hs Hf]
  · iapply spec_map_initialise f0 s v n E $$ [Hs Hf]
    · iframe; ipureintro; exact ⟨hmem, hl0, hlen⟩
    iintro %w ⟨%hw, Hs, Hf⟩
    iframe; ipureintro; exact hw
  iintro ⟨Hs, Hf⟩
  isimp only [vToEList, List.map_nil, List.nil_append]
  rw [show ([AdministrativeInstruction.basic (.block (.result none) [.loop (.result none) mapLoopBody])]
    : Expr) = [] ++ [.basic (.block (.result none) [.loop (.result none) mapLoopBody])] from rfl]
  iapply wp_block (bt := .result none) (m := 0) rfl rfl rfl rfl rfl $$ Hf
  iintro !> Hf
  iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).2
  iapply wp_label_push_nil
  simp only [List.nil_append, toEList, List.map_cons, List.map_nil]
  rw [show ([AdministrativeInstruction.basic (.loop (.result none) mapLoopBody)] : Expr) =
    [] ++ [.basic (.loop (.result none) mapLoopBody)] from rfl]
  iapply wp_loop_ctx (bt := .result none) rfl rfl rfl rfl rfl $$ Hf
  iintro !> Hf
  iapply wp_label_push_nil
  simp only [List.nil_append, List.length_nil, Nat.reduceAdd]
  have hj := spec_map_loop_j_trap (GF := GF) fr s v n E s.length f j0 a cl Φ Ψ [] γ1 hsub
  rw [List.take_length, List.append_nil, List.drop_length,
    show v + s.length * 4 - 4 * s.length = v by omega] at hj
  simp only [pushBase, fr] at hj ⊢
  iapply wp_wand_ctx $$ [Hs HΦ Hown Hf] HΞ
  iapply hj
  simp only [stackAll2]
  iframe
  repeat (isplitr; · ipureintro; first | assumption | exact ⟨by omega, by omega⟩ |
    (simp [List.getElem?_set, hl0, hl1] <;> omega))
  isplitr
  · iexact Htab
  iexact Hcl

@[rocq_alias iriswasm.spec_stack_map_trap]
theorem spec_stack_map_trap (f0 : Frame) (n : Immediate) (f : I32) (v : Nat) (s : List I32)
    (E : CoPset) (j0 : Nat) (a : Option Nat) (cl : FunctionClosure) (γ1 : Namespace)
    (Φ : I32 → IProp GF) (Ψ : I32 → I32 → IProp GF) :
    (↑γ1 : CoPset) ⊆ E →
    ⊢ ({{{{ ⌜f0.inst.memory[0]? = some n⌝ ∗
          ⌜f0.locs[0]? = some (valueOfUint v)⌝ ∗
          ⌜f0.locs[1]? = some (.int32 f)⌝ ∗
          ⌜f0.locs.length ≥ 4⌝ ∗
          isStack v s n ∗
          stackAll s Φ ∗
          ⌜f0.inst.types[1]? = some (.tf [.i32] [.i32])⌝ ∗
          ⌜f0.inst.tab[0]? = some j0⌝ ∗
          NonAtomicInvariant.inv logrelNais γ1 (j0 ↦[wt][ Wasm.Int.natOfUint f ] a) ∗
          mapClosureSpec f0.inst E γ1 a cl Φ Ψ ∗
          NonAtomicInvariant.own logrelNais ⊤ ∗ ↪[frame] f0 }}}}
      (toEList stackMap) @ E
      {{{{ w, (⌜w = .trapV⌝ ∨ (⌜w = .immV []⌝ ∗ (∃ s', isStack v s' n ∗ stackAll2 s s' Ψ))) ∗
          (∃ f1, ↪[frame] f1 ∗ NonAtomicInvariant.own logrelNais ⊤ ∗ ⌜f0.inst = f1.inst⌝)
      }}}} : IProp GF) := by
  intro hsub
  iintro !> %Ξ ⟨%hmem, %hl0, %hl1, %hlen, Hs, HΦ, %htypes, %htab, #Htab, #Hcl, Hown, Hf⟩ HΞ
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
  isimp only [vToEList, List.map_nil, List.nil_append]
  iapply spec_stack_map_op_trap f0 n f v s E j0 a cl γ1 Φ Ψ hsub $$ [Hs HΦ Hown Hf] HΞ
  iframe
  repeat (isplitr; · ipureintro; assumption)
  isplitr
  · iexact Htab
  iexact Hcl

end specs

end IrisWasm.Examples.Stack
