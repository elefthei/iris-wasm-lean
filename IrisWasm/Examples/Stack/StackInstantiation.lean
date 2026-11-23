/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Host.IrisHost
import IrisWasm.Logrel.IrisFundamentalHelpers
import IrisWasm.Examples.Stack.StackSpecs
import Wasm.ModuleValidation

/-! Port of `theories/iris/examples/stack/stack_instantiation.v`.

The Coq Ltacs `invert_cllookup` and `resolve_cl_lookup` are proof-local helpers; the Lean
proofs inline them. -/

namespace IrisWasm.Examples.Stack

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm
open scoped Iris.Std.PartialMap

/-- Coq `String.list_byte_of_string`: the ASCII bytes of a string. -/
def nameOfString (s : String) : Name := s.toList.map fun c => BitVec.ofNat 8 c.toNat

/-- Close a goal `∀ xs, lhs = rhs` without free variables by `Eq.refl`, checked by the kernel
only: the elaborator's `whnf` cannot evaluate the type checker on these programs in reasonable time
(Coq: `apply/b_e_type_checker_reflects_typing; by compute`). -/
elab "kernel_rfl" : tactic => do
  let g ← Lean.Elab.Tactic.getMainGoal
  let ty ← Lean.instantiateMVars (← g.getType)
  let val ← Lean.Meta.forallTelescope ty fun xs body => do
    let some (_, _, rhs) := body.eq? | throwError "kernel_rfl: not an equality"
    Lean.Meta.mkLambdaFVars xs (← Lean.Meta.mkEqRefl rhs)
  let name ← Lean.Elab.Term.mkAuxName `kernel_rfl
  Lean.addDecl (.thmDecl { name, levelParams := [], type := ty, value := val })
  g.assign (Lean.mkConst name)
  Lean.Elab.Tactic.replaceMainGoal []

@[rocq_alias iriswasm.stack_module]
def stackModule : Module where
  types := [.tf [] [.i32], .tf [.i32] [.i32], .tf [.i32, .i32] []]
  funcs := [
    { type := .typeidx 0, locals := [.i32], body := newStack },
    { type := .typeidx 1, locals := [], body := isEmpty },
    { type := .typeidx 1, locals := [], body := isFull },
    { type := .typeidx 1, locals := [.i32], body := pop },
    { type := .typeidx 2, locals := [.i32], body := push },
    { type := .typeidx 2, locals := [.i32, .i32], body := stackMap },
    { type := .typeidx 1, locals := [], body := lengthStack } ]
  tables := [{ type := { limits := { min := 1, max := none }, elemType := .funcref } }]
  mems := [{ address := .i32, limits := ⟨0, none⟩ }]
  globals := []
  elem := []
  data := []
  start := none
  imports := []
  exports := [
    { name := nameOfString "new_stack", desc := .func (.funcidx 0) },
    { name := nameOfString "is_empty", desc := .func (.funcidx 1) },
    { name := nameOfString "is_full", desc := .func (.funcidx 2) },
    { name := nameOfString "pop", desc := .func (.funcidx 3) },
    { name := nameOfString "push", desc := .func (.funcidx 4) },
    { name := nameOfString "stack_map", desc := .func (.funcidx 5) },
    { name := nameOfString "stack_length", desc := .func (.funcidx 6) },
    { name := nameOfString "table", desc := .table (.tableidx 0) } ]

@[rocq_alias iriswasm.func_types]
def funcTypes : List FunctionType :=
  [.tf [] [.i32], .tf [.i32] [.i32], .tf [.i32] [.i32], .tf [.i32] [.i32], .tf [.i32, .i32] [],
    .tf [.i32, .i32] [], .tf [.i32] [.i32]]

@[rocq_alias iriswasm.expts]
def expts : List ExternT :=
  funcTypes.map ExternT.func ++
    [.tab { limits := { min := 1, max := none }, elemType := .funcref }]

/-- The typing context shared by the stack functions' typing lemmas. -/
abbrev stackCtx (tt tf : List FunctionType) (tloc : List ValueType) (tlab : List (List ValueType))
    (tret : Option (List ValueType)) : TContext :=
  { typesT := tt, funcT := tf, global := [],
    table := [{ limits := { min := 1, max := none }, elemType := .funcref }],
    memory := [{ address := .i32, limits := ⟨0, none⟩ }], local_ := tloc, label := tlab, return_ := tret }

@[rocq_alias iriswasm.validate_stack_typing]
theorem validate_stack_typing (x : Nat) (tt tf : List FunctionType) (tloc : List ValueType)
    (tlab : List (List ValueType)) (tret : Option (List ValueType)) :
    tloc[x]? = some .i32 → BeTyping (stackCtx tt tf tloc tlab tret) (validateStack x) (.tf [] []) := by
  intro h
  refine bet_composition' (es1 := [.getLocal x]) (es2 := (validateStack x).drop 1) (t2s := [.i32])
    (.getLocal (List.getElem?_eq_some_iff.1 h).1 h) ?_
  clear h; rw [← b_e_type_checker_reflects_typing]; revert x tt tf tloc tlab tret; kernel_rfl

@[rocq_alias iriswasm.validate_stack_bound_typing]
theorem validate_stack_bound_typing (x : Nat) (tt tf : List FunctionType) (tloc : List ValueType)
    (tlab : List (List ValueType)) (tret : Option (List ValueType)) :
    tloc[x]? = some .i32 →
      BeTyping (stackCtx tt tf tloc tlab tret) (validateStackBound x) (.tf [] []) := by
  intro h
  refine bet_composition' (es1 := [.getLocal x]) (es2 := (validateStackBound x).drop 1) (t2s := [.i32])
    (.getLocal (List.getElem?_eq_some_iff.1 h).1 h) ?_
  clear h; rw [← b_e_type_checker_reflects_typing]; revert x tt tf tloc tlab tret; kernel_rfl

@[rocq_alias iriswasm.new_stack_typing]
theorem new_stack_typing (tt tf : List FunctionType) :
    BeTyping (stackCtx tt tf [.i32] [[.i32]] (some [.i32])) newStack (.tf [] [.i32]) := by
  rw [← b_e_type_checker_reflects_typing]; revert tt tf; kernel_rfl

@[rocq_alias iriswasm.is_empty_typing]
theorem is_empty_typing (tt tf : List FunctionType) (tloc : List ValueType)
    (tlab : List (List ValueType)) (tret : Option (List ValueType)) :
    tloc[0]? = some .i32 → BeTyping (stackCtx tt tf tloc tlab tret) isEmpty (.tf [] [.i32]) := by
  intro h
  rcases tloc with _ | ⟨t, rest⟩ <;> simp at h
  subst h; rw [← b_e_type_checker_reflects_typing]; revert tt tf rest tlab tret; kernel_rfl

@[rocq_alias iriswasm.is_full_typing]
theorem is_full_typing (tt tf : List FunctionType) (tlab : List (List ValueType))
    (tret : Option (List ValueType)) :
    BeTyping (stackCtx tt tf [.i32] tlab tret) isFull (.tf [] [.i32]) := by
  rw [← b_e_type_checker_reflects_typing]; revert tt tf tlab tret; kernel_rfl

@[rocq_alias iriswasm.pop_typing]
theorem pop_typing (tt tf : List FunctionType) (tlab : List (List ValueType))
    (tret : Option (List ValueType)) :
    BeTyping (stackCtx tt tf [.i32, .i32] tlab tret) pop (.tf [] [.i32]) := by
  rw [← b_e_type_checker_reflects_typing]; revert tt tf tlab tret; kernel_rfl

@[rocq_alias iriswasm.push_typing]
theorem push_typing (tt tf : List FunctionType) (tlab : List (List ValueType))
    (tret : Option (List ValueType)) :
    BeTyping (stackCtx tt tf [.i32, .i32, .i32] tlab tret) push (.tf [] []) := by
  rw [← b_e_type_checker_reflects_typing]; revert tt tf tlab tret; kernel_rfl

@[rocq_alias iriswasm.stack_map_typing]
theorem stack_map_typing (tf : List FunctionType) :
    BeTyping (stackCtx [.tf [] [.i32], .tf [.i32] [.i32], .tf [.i32, .i32] []] tf
      [.i32, .i32, .i32, .i32] [[]] (some [])) stackMap (.tf [] []) := by
  rw [← b_e_type_checker_reflects_typing]; revert tf; kernel_rfl

@[rocq_alias iriswasm.length_stack_typing]
theorem length_stack_typing (tt tf : List FunctionType) (tlab : List (List ValueType))
    (tret : Option (List ValueType)) :
    BeTyping (stackCtx tt tf [.i32] tlab tret) lengthStack (.tf [] [.i32]) := by
  rw [← b_e_type_checker_reflects_typing]; revert tt tf tlab tret; kernel_rfl

@[rocq_alias iriswasm.module_typing_stack]
theorem module_typing_stack : ModuleTyping stackModule [] expts := by
  apply (validateModule_iff _ ⟨_, _⟩).mp
  kernel_rfl

@[rocq_alias iriswasm.stack_instance]
def stackInstance (idfs : List Funcaddr) (m t : Nat) : Instance :=
  { types := [.tf [] [.i32], .tf [.i32] [.i32], .tf [.i32, .i32] []], funcs := idfs, tab := [t],
    memory := [m], globs := [] }

section StackModule
variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF]

attribute [local instance] WasmG.invGS

@[rocq_alias iriswasm.spec0_new_stack]
def spec0NewStack (idf0 : Nat) (i0 : Instance) (l0 : List ValueType) (f0 : List BasicInstruction)
    (isStack : Nat → List I32 → IProp GF) (nextStackAddrIs : Nat → IProp GF) (E : CoPset) :
    IProp GF :=
  iprop(∀ (f : Frame) (addr : Nat),
    {{{{ ↪[frame] f ∗
        idf0 ↦[wf] (.funcNative i0 (.tf [] [.i32]) l0 f0) ∗
        nextStackAddrIs addr ∗
        ⌜Wasm.Int.modulus 32 - 1 ≠ Wasm.Int.zModModulus 32 ((addr / pageSize : Nat) : _root_.Int)⌝ ∗
        ⌜addr + 4 < 2 ^ 32⌝ ∗
        ⌜pageSize ∣ addr⌝ }}}}
      ([.invoke idf0] : Expr) @ E
    {{{{ v, ((⌜v = .immV [valueOfInt (-1)]⌝ ∗ nextStackAddrIs addr) ∨
          (∃ k, ⌜v = .immV [valueOfUint k]⌝ ∗ ⌜0 ≤ k ∧ k ≤ ffff0000⌝ ∗ isStack k [] ∗
            nextStackAddrIs (addr + pageSize))) ∗
        idf0 ↦[wf] (.funcNative i0 (.tf [] [.i32]) l0 f0) ∗
        ↪[frame] f }}}})

@[rocq_alias iriswasm.spec1_is_empty]
def spec1IsEmpty (idf1 : Nat) (i1 : Instance) (l1 : List ValueType) (f1 : List BasicInstruction)
    (isStack : Nat → List I32 → IProp GF) (E : CoPset) : IProp GF :=
  iprop(∀ (v : Nat) (s : List I32) (f : Frame),
    {{{{ ↪[frame] f ∗
        idf1 ↦[wf] (.funcNative i1 (.tf [.i32] [.i32]) l1 f1) ∗
        isStack v s }}}}
      ([.basic (u32const v), .invoke idf1] : Expr) @ E
    {{{{ w, (∃ k : _root_.Int, ⌜w = .immV [valueOfInt k]⌝ ∗ isStack v s ∗
          ⌜(k = 1 ∧ s = []) ∨ (k = 0 ∧ s ≠ [])⌝) ∗
        idf1 ↦[wf] (.funcNative i1 (.tf [.i32] [.i32]) l1 f1) ∗
        ↪[frame] f }}}})

@[rocq_alias iriswasm.spec2_is_full]
def spec2IsFull (idf2 : Nat) (i2 : Instance) (l2 : List ValueType) (f2 : List BasicInstruction)
    (isStack : Nat → List I32 → IProp GF) (E : CoPset) : IProp GF :=
  iprop(∀ (v : Nat) (s : List I32) (f : Frame),
    {{{{ ↪[frame] f ∗
        idf2 ↦[wf] (.funcNative i2 (.tf [.i32] [.i32]) l2 f2) ∗
        isStack v s }}}}
      ([.basic (u32const v), .invoke idf2] : Expr) @ E
    {{{{ w, (∃ k : _root_.Int, ⌜w = .immV [valueOfInt k]⌝ ∗ isStack v s ∗
          ⌜(k = 1 ∧ s.length = two14 - 1) ∨ (k = 0 ∧ s.length < two14 - 1)⌝) ∗
        idf2 ↦[wf] (.funcNative i2 (.tf [.i32] [.i32]) l2 f2) ∗
        ↪[frame] f }}}})

@[rocq_alias iriswasm.spec3_pop]
def spec3Pop (idf3 : Nat) (i3 : Instance) (l3 : List ValueType) (f3 : List BasicInstruction)
    (isStack : Nat → List I32 → IProp GF) (E : CoPset) : IProp GF :=
  iprop(∀ (a : I32) (v : Nat) (s : List I32) (f : Frame),
    {{{{ ↪[frame] f ∗
        idf3 ↦[wf] (.funcNative i3 (.tf [.i32] [.i32]) l3 f3) ∗
        isStack v (a :: s) }}}}
      ([.basic (u32const v), .invoke idf3] : Expr) @ E
    {{{{ w, ⌜w = .immV [.int32 a]⌝ ∗
        isStack v s ∗
        idf3 ↦[wf] (.funcNative i3 (.tf [.i32] [.i32]) l3 f3) ∗
        ↪[frame] f }}}})

@[rocq_alias iriswasm.spec4_push]
def spec4Push (idf4 : Nat) (i4 : Instance) (l4 : List ValueType) (f4 : List BasicInstruction)
    (isStack : Nat → List I32 → IProp GF) (E : CoPset) : IProp GF :=
  iprop(∀ (a : I32) (v : Nat) (s : List I32) (f : Frame),
    {{{{ ↪[frame] f ∗
        idf4 ↦[wf] (.funcNative i4 (.tf [.i32, .i32] []) l4 f4) ∗
        ⌜s.length < two14 - 1⌝ ∗
        isStack v s }}}}
      ([.basic (u32const v), .basic (.const (.int32 a)), .invoke idf4] : Expr) @ E
    {{{{ w, ⌜w = .immV []⌝ ∗
        isStack v (a :: s) ∗
        idf4 ↦[wf] (.funcNative i4 (.tf [.i32, .i32] []) l4 f4) ∗
        ↪[frame] f }}}})

@[rocq_alias iriswasm.spec5_stack_map]
def spec5StackMap (idf5 : Nat) (i5 : Instance) (l5 : List ValueType) (f5 : List BasicInstruction)
    (isStack : Nat → List I32 → IProp GF) (j0 : Nat) (E : CoPset) : IProp GF :=
  iprop(∀ (f0 : Frame) (f : I32) (v : Nat) (s : List I32) (a : Nat) (cl : FunctionClosure)
      (Φ : I32 → IProp GF) (Ψ : I32 → I32 → IProp GF),
    {{{{ ↪[frame] f0 ∗
        idf5 ↦[wf] (.funcNative i5 (.tf [.i32, .i32] []) l5 f5) ∗
        isStack v s ∗
        stackAll s Φ ∗
        j0 ↦[wt][ Wasm.Int.natOfUint f ] (some a) ∗
        a ↦[wf] cl ∗
        ⌜clType cl = .tf [.i32] [.i32]⌝ ∗
        (∀ (u : I32) (fc : Frame),
          {{{{ Φ u ∗
              ⌜i5 = fc.inst⌝ ∗
              ↪[frame] fc ∗
              j0 ↦[wt][ Wasm.Int.natOfUint f ] (some a) ∗
              a ↦[wf] cl }}}}
            ([.basic (.const (.int32 u)), .invoke a] : Expr) @ E
            {{{{ w, (∃ v, ⌜w = .immV [.int32 v]⌝ ∗ Ψ u v) ∗
                ↪[frame] fc ∗
                j0 ↦[wt][ Wasm.Int.natOfUint f ] (some a) ∗
                a ↦[wf] cl }}}}) }}}}
      ([.basic (u32const v), .basic (.const (.int32 f)), .invoke idf5] : Expr) @ E
    {{{{ w, ⌜w = .immV []⌝ ∗
        (∃ s', isStack v s' ∗ stackAll2 s s' Ψ) ∗
        idf5 ↦[wf] (.funcNative i5 (.tf [.i32, .i32] []) l5 f5) ∗
        ↪[frame] f0 ∗
        j0 ↦[wt][ Wasm.Int.natOfUint f ] (some a) ∗
        a ↦[wf] cl }}}})

/-- A trap-allowing version of `spec5StackMap`, for closures that might trap. -/
@[rocq_alias iriswasm.spec5_stack_map_trap]
def spec5StackMapTrap [LogrelNaInvs GF] (idf5 : Nat) (i5 : Instance) (l5 : List ValueType)
    (f5 : List BasicInstruction) (isStack : Nat → List I32 → IProp GF) (j0 : Nat) (E : CoPset) :
    IProp GF :=
  iprop(∀ (f0 : Frame) (f : I32) (v : Nat) (s : List I32) (a : Option Nat) (cl : FunctionClosure)
      (γ1 : Namespace) (Φ : I32 → IProp GF) (Ψ : I32 → I32 → IProp GF),
    ⌜(↑γ1 : CoPset) ⊆ E⌝ →
    {{{{ idf5 ↦[wf] (.funcNative i5 (.tf [.i32, .i32] []) l5 f5) ∗
        isStack v s ∗
        stackAll s Φ ∗
        NonAtomicInvariant.inv (LogrelNaInvs.logrelNais (GF := GF)) γ1
          (j0 ↦[wt][ Wasm.Int.natOfUint f ] a) ∗
        mapClosureSpec i5 E γ1 a cl Φ Ψ ∗
        NonAtomicInvariant.own (LogrelNaInvs.logrelNais (GF := GF)) ⊤ ∗ ↪[frame] f0 }}}}
      ([.basic (u32const v), .basic (.const (.int32 f)), .invoke idf5] : Expr) @ E
    {{{{ w, (⌜w = .trapV⌝ ∨ (⌜w = .immV []⌝ ∗
          (∃ s', isStack v s' ∗ stackAll2 s s' Ψ) ∗
          idf5 ↦[wf] (.funcNative i5 (.tf [.i32, .i32] []) l5 f5))) ∗
        NonAtomicInvariant.own (LogrelNaInvs.logrelNais (GF := GF)) ⊤ ∗
        ↪[frame] f0 }}}})

@[rocq_alias iriswasm.spec6_stack_length]
def spec6StackLength (idf : Nat) (i : Instance) (l : List ValueType) (fn : List BasicInstruction)
    (isStack : Nat → List I32 → IProp GF) (E : CoPset) : IProp GF :=
  iprop(∀ (v : Nat) (s : List I32) (f : Frame) (len : Nat),
    {{{{ ↪[frame] f ∗
        idf ↦[wf] (.funcNative i (.tf [.i32] [.i32]) l fn) ∗
        ⌜s.length = len⌝ ∗
        isStack v s }}}}
      ([.basic (u32const v), .invoke idf] : Expr) @ E
    {{{{ w, ⌜w = .immV [valueOfUint len]⌝ ∗ isStack v s ∗
        idf ↦[wf] (.funcNative i (.tf [.i32] [.i32]) l fn) ∗
        ↪[frame] f }}}})

private theorem wp_value_of {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF} (v : Val)
    {e : Expr} (h : e = ofVal v) : Φ v ⊢ WP e @ s ; E {{ Φ }} := by
  subst h
  exact IrisWp.wp_value (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) ⟨rfl⟩

/-- Invoking a native function at `a` on the arguments `vcs`, given a spec of its body in the
callee frame; the body may trap. -/
theorem wp_invoke_native_frame (s : Stuckness) (E : CoPset) (a : Nat) (i : Instance)
    (t1s t2s ts : List ValueType) (body : List BasicInstruction) (vcs : List Value) (f0 : Frame)
    (Q : Val → IProp GF) (hlen : vcs.length = t1s.length)
    (hQ : ∀ w, Q w ⊢ ⌜w = .trapV ∨ ∃ ws, w = .immV ws ∧ ws.length = t2s.length⌝) :
    ⊢ (↪[frame] f0 -∗ a ↦[wf] (.funcNative i (.tf t1s t2s) ts body) -∗
      (↪[frame] (⟨vcs ++ nZeros ts, i⟩ : Frame) -∗
        WP (toEList body : Expr) @ s ; E {{ w, Q w ∗ ∃ f1, ↪[frame] f1 }}) -∗
      WP (vToEList vcs ++ [.invoke a]) @ s ; E
        {{ w, (Q w ∗ a ↦[wf] (.funcNative i (.tf t1s t2s) ts body)) ∗ ↪[frame] f0 }} : IProp GF) := by
  iintro Hf Ha Hbody
  iapply wp_invoke_native _ _ _ (vToEList vcs) vcs t1s t2s ts a body i t2s.length f0
    (to_of_val (.immV vcs)) hlen rfl $$ Hf Ha
  inext; iintro ⟨Hf, Ha⟩
  iapply (wp_frame_rewrite _ _ _ _ _ _).1
  iapply wp_frame_bind _ _ _ _ _ _ _ (toVal_native_frame_none _ _ _) $$ Hf
  iintro Hf
  iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).2
  iapply wp_label_push_nil
  simp only [pushBase]
  iapply wp_label_bind
  iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ [Hbody Hf]
  · iapply Hbody $$ Hf
  iintro %w ⟨HQ, %f1, Hf⟩
  ihave %hw : ⌜w = .trapV ∨ ∃ ws, w = .immV ws ∧ ws.length = t2s.length⌝ $$ [HQ]
  · iapply hQ w $$ HQ
  rcases hw with rfl | ⟨ws, rfl, hws⟩
  · rw [show ofVal Val.trapV = ([AdministrativeInstruction.trap] : Expr) from rfl]
    iapply wp_wand_ctx _ _ _ (fun v => iprop(⌜v = .trapV⌝ ∗ ↪[frame] f1)) $$ [Hf]
    · have h := wp_trap_ctx (GF := GF) s E f1 1 (.rec_ [] t2s.length [] (.base [] []) []) [] [] rfl
      simp only [List.nil_append, List.append_nil] at h
      iapply h $$ Hf
    iintro %v ⟨%hv, Hf⟩
    subst hv
    iexists f1
    iframe
    iintro Hf0
    rw [show ofVal Val.trapV = ([AdministrativeInstruction.trap] : Expr) from rfl]
    iapply wp_frame_trap $$ Hf0
    inext; iframe
  · rw [show ofVal (Val.immV ws) = vToEList ws from rfl]
    iapply wp_val_return (vs' := []) (es'' := []) (v_to_e_is_const_list ws) $$ Hf
    iintro Hf
    simp only [List.nil_append, List.append_nil]
    iapply wp_value_of (e := vToEList ws) (.immV ws) rfl
    iexists f1
    iframe
    iintro Hf0
    iapply wp_frame_value _ _ _ _ _ _ _ ws (to_of_val _) (by simp [ofVal, vToEList, hws]) $$ Hf0
    inext; iframe

/-- Calling function `i` of the current instance with the arguments `vs` on the stack. -/
theorem wp_call_vals (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF) (f : Frame) (i a : Nat)
    (vs : List Value) (h : f.inst.funcs[i]? = some a) :
    ⊢ (↪[frame] f -∗ ▷ (↪[frame] f -∗ WP (vToEList vs ++ [.invoke a]) @ s ; E {{ v, Φ v }}) -∗
      WP (vToEList vs ++ [.basic (.call i)]) @ s ; E {{ v, Φ v }} : IProp GF) := by
  iintro Hf H
  have key := wp_call_ctx s E Φ f i a 0 (.base (vToEList vs) []) h
  unfold wpWasmCtx at key
  iapply key $$ Hf [H] %(vToEList vs ++ [.basic (.call i)])
    %(by simp [lfilled, lfill, v_to_e_is_const_list])
  inext; iintro Hf %LI %hLI
  have hLI' : LI = vToEList vs ++ [.invoke a] := by
    simpa [lfilled, lfill, v_to_e_is_const_list] using hLI
  subst hLI'
  iapply H $$ Hf

/-- Invoking a native `[] → []` function whose body may `return`. -/
theorem wp_invoke_native_unit (s : Stuckness) (E : CoPset) (a : Nat) (i : Instance)
    (ts : List ValueType) (body : List BasicInstruction) (f0 : Frame) (R : IProp GF) :
    ⊢ (↪[frame] f0 -∗ a ↦[wf] (.funcNative i (.tf [] []) ts body) -∗
      (↪[frame] (⟨nZeros ts, i⟩ : Frame) -∗
        WP (toEList body : Expr) @ s ; E
          {{ w, (⌜w = .immV []⌝ ∨ ⌜∃ sh, w = .retV sh⌝) ∗ R ∗ ∃ f1, ↪[frame] f1 }}) -∗
      WP ([.invoke a] : Expr) @ s ; E
        {{ w, (⌜w = .immV []⌝ ∗ R ∗ a ↦[wf] (.funcNative i (.tf [] []) ts body)) ∗
          ↪[frame] f0 }} : IProp GF) := by
  iintro Hf Ha Hbody
  rw [show ([.invoke a] : Expr) = vToEList [] ++ [.invoke a] from rfl]
  iapply wp_invoke_native _ _ _ (vToEList []) [] [] [] ts a body i 0 f0
    (to_of_val (.immV [])) rfl rfl $$ Hf Ha
  inext; iintro ⟨Hf, Ha⟩
  iapply (wp_frame_rewrite _ _ _ _ _ _).1
  iapply wp_frame_bind _ _ _ _ _ _ _ (toVal_native_frame_none _ _ _) $$ Hf
  iintro Hf
  iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).2
  iapply wp_label_push_nil
  simp only [pushBase]
  iapply wp_label_bind
  simp only [List.nil_append]
  iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ [Hbody Hf]
  · iapply Hbody $$ Hf
  iintro %w ⟨Hw, HR, %f1, Hf⟩
  icases Hw with (%hw | %hw)
  · subst hw
    rw [show ofVal (Val.immV []) = vToEList [] from rfl]
    iapply wp_val_return (vs' := []) (es'' := []) (v_to_e_is_const_list []) $$ Hf
    iintro Hf
    simp only [List.nil_append, List.append_nil]
    iapply wp_value_of (e := vToEList []) (.immV []) rfl
    iexists f1
    iframe
    iintro Hf0
    iapply wp_frame_value _ _ _ _ 0 _ _ [] (to_of_val _) rfl $$ Hf0
    inext; iframe; ipureintro; rfl
  · obtain ⟨sh, rfl⟩ := hw
    unfold wpWasmCtx
    iintro %LI %hLI
    have hLI' : LI = ofVal (.retV (.rec_ [] 0 [] sh [])) := by
      simpa [lfilled, lfill, constList, ofVal, sfill, vToEList] using hLI
    subst hLI'
    iapply wp_value_of (.retV (.rec_ [] 0 [] sh [])) rfl
    iexists f1
    iframe
    iintro Hf0
    iapply wp_frame_return (vs := []) (vs0 := []) (i := lhDepth (lhOfSh (.rec_ [] 0 [] sh [])))
      (lh := lhOfSh (.rec_ [] 0 [] sh [])) rfl rfl
      (by simpa [ofVal] using sfill_to_lfilled (.rec_ [] 0 [] sh []) [.basic .return_])
    inext
    iapply wp_value_of (e := []) (.immV []) rfl
    iframe; ipureintro; rfl

private theorem spec0_holds (a0 m : Nat) (i0 : Instance) (hm : i0.memory[0]? = some m) (E : CoPset) :
    ⊢ spec0NewStack (GF := GF) a0 i0 [.i32] newStack (fun a b => isStack a b m)
      (fun n => m ↦[wmlength] (.i32, n)) E := by
  unfold spec0NewStack
  iintro %f %addr !> %Φ ⟨Hf, Hcl, Hlen, %h1, %h2, %h3⟩ HΦ
  rw [show ([.invoke a0] : Expr) = vToEList [] ++ [.invoke a0] from rfl]
  iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ [Hf Hcl Hlen]
  · iapply wp_invoke_native_frame .NotStuck E a0 i0 [] [.i32] [.i32] newStack [] f
      (fun v => iprop((⌜v = .immV [valueOfInt (-1)]⌝ ∗ m ↦[wmlength] (.i32, addr)) ∨
        (⌜v = .immV [valueOfUint addr]⌝ ∗ isStack addr [] m ∗ m ↦[wmlength] (.i32, addr + pageSize))))
      rfl ?_ $$ Hf Hcl
    · intro w
      iintro (⟨%h, -⟩ | ⟨%h, -⟩) <;> ipureintro <;> subst h <;> simp
    iintro Hf
    iapply spec_new_stack ⟨[] ++ nZeros [.i32], i0⟩ m addr E $$ [Hf Hlen]
    · iframe; ipureintro; exact ⟨hm, by simp [nZeros], h3⟩
    iintro %w ⟨HQ, %f1, Hf, -⟩
    iframe
  iintro %w ⟨⟨HQ, Hcl⟩, Hf⟩
  iapply HΦ
  iframe
  icases HQ with (⟨%hw, Hlen⟩ | ⟨%hw, Hs, Hlen⟩)
  · ileft; iframe; ipureintro; exact hw
  · ihave ⟨_, %hb, _, Hs⟩ := stack_pure addr [] m $$ Hs
    iright; iexists addr; iframe; ipureintro; exact ⟨hw, hb⟩

private theorem spec1_holds (a1 m : Nat) (i0 : Instance) (hm : i0.memory[0]? = some m) (E : CoPset) :
    ⊢ spec1IsEmpty (GF := GF) a1 i0 [] isEmpty (fun a b => isStack a b m) E := by
  unfold spec1IsEmpty
  iintro %v %s %f !> %Φ ⟨Hf, Hcl, Hs⟩ HΦ
  rw [show ([.basic (u32const v), .invoke a1] : Expr) = vToEList [valueOfUint v] ++ [.invoke a1]
    from rfl]
  iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ [Hf Hcl Hs]
  · iapply wp_invoke_native_frame .NotStuck E a1 i0 [.i32] [.i32] [] isEmpty [valueOfUint v] f
      (fun w => iprop(∃ k : _root_.Int, ⌜w = .immV [valueOfInt k]⌝ ∗ isStack v s m ∗
        ⌜(k = 1 ∧ s = []) ∨ (k = 0 ∧ s ≠ [])⌝))
      rfl ?_ $$ Hf Hcl
    · intro w
      iintro ⟨%k, %h, -⟩; ipureintro; subst h; simp
    iintro Hf
    iapply spec_is_empty ⟨[valueOfUint v] ++ nZeros [], i0⟩ m v s E $$ [Hf Hs]
    · iframe; ipureintro; exact ⟨hm, rfl⟩
    iintro %w ⟨%k, %hw, Hs, %hk, Hf⟩
    iframe; iexists k; iframe; ipureintro; exact ⟨hw, hk⟩
  iintro %w ⟨⟨HQ, Hcl⟩, Hf⟩
  iapply HΦ
  iframe

private theorem spec2_holds (a2 m : Nat) (i0 : Instance) (hm : i0.memory[0]? = some m) (E : CoPset) :
    ⊢ spec2IsFull (GF := GF) a2 i0 [] isFull (fun a b => isStack a b m) E := by
  unfold spec2IsFull
  iintro %v %s %f !> %Φ ⟨Hf, Hcl, Hs⟩ HΦ
  rw [show ([.basic (u32const v), .invoke a2] : Expr) = vToEList [valueOfUint v] ++ [.invoke a2]
    from rfl]
  iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ [Hf Hcl Hs]
  · iapply wp_invoke_native_frame .NotStuck E a2 i0 [.i32] [.i32] [] isFull [valueOfUint v] f
      (fun w => iprop(∃ k : _root_.Int, ⌜w = .immV [valueOfInt k]⌝ ∗ isStack v s m ∗
        ⌜(k = 1 ∧ s.length = two14 - 1) ∨ (k = 0 ∧ s.length < two14 - 1)⌝))
      rfl ?_ $$ Hf Hcl
    · intro w
      iintro ⟨%k, %h, -⟩; ipureintro; subst h; simp
    iintro Hf
    iapply spec_is_full ⟨[valueOfUint v] ++ nZeros [], i0⟩ m v s E $$ [Hf Hs]
    · iframe; ipureintro; exact ⟨hm, rfl⟩
    iintro %w ⟨%k, %hw, Hs, %hk, Hf⟩
    iframe; iexists k; iframe; ipureintro; exact ⟨hw, hk⟩
  iintro %w ⟨⟨HQ, Hcl⟩, Hf⟩
  iapply HΦ
  iframe

private theorem spec3_holds (a3 m : Nat) (i0 : Instance) (hm : i0.memory[0]? = some m) (E : CoPset) :
    ⊢ spec3Pop (GF := GF) a3 i0 [.i32] pop (fun a b => isStack a b m) E := by
  unfold spec3Pop
  iintro %a %v %s %f !> %Φ ⟨Hf, Hcl, Hs⟩ HΦ
  rw [show ([.basic (u32const v), .invoke a3] : Expr) = vToEList [valueOfUint v] ++ [.invoke a3]
    from rfl]
  iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ [Hf Hcl Hs]
  · iapply wp_invoke_native_frame .NotStuck E a3 i0 [.i32] [.i32] [.i32] pop [valueOfUint v] f
      (fun w => iprop(⌜w = .immV [.int32 a]⌝ ∗ isStack v s m))
      rfl ?_ $$ Hf Hcl
    · intro w
      iintro ⟨%h, -⟩; ipureintro; subst h; simp
    iintro Hf
    iapply spec_pop ⟨[valueOfUint v] ++ nZeros [.i32], i0⟩ m v a s E $$ [Hf Hs]
    · iframe; ipureintro; exact ⟨hm, rfl, by simp [nZeros]⟩
    iintro %w ⟨%hw, Hs, %f1, Hf, -⟩
    iframe; ipureintro; exact hw
  iintro %w ⟨⟨HQ, Hcl⟩, Hf⟩
  iapply HΦ
  iframe

private theorem spec4_holds (a4 m : Nat) (i0 : Instance) (hm : i0.memory[0]? = some m) (E : CoPset) :
    ⊢ spec4Push (GF := GF) a4 i0 [.i32] push (fun a b => isStack a b m) E := by
  unfold spec4Push
  iintro %a %v %s %f !> %Φ ⟨Hf, Hcl, %hlen, Hs⟩ HΦ
  rw [show ([.basic (u32const v), .basic (.const (.int32 a)), .invoke a4] : Expr) =
    vToEList [valueOfUint v, .int32 a] ++ [.invoke a4] from rfl]
  iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ [Hf Hcl Hs]
  · iapply wp_invoke_native_frame .NotStuck E a4 i0 [.i32, .i32] [] [.i32] push
      [valueOfUint v, .int32 a] f
      (fun w => iprop(⌜w = .immV []⌝ ∗ isStack v (a :: s) m))
      rfl ?_ $$ Hf Hcl
    · intro w
      iintro ⟨%h, -⟩; ipureintro; subst h; simp
    iintro Hf
    iapply spec_push ⟨[valueOfUint v, .int32 a] ++ nZeros [.i32], i0⟩ m v a s E $$ [Hf Hs]
    · iframe; ipureintro; exact ⟨hm, rfl, rfl, by simp [nZeros], hlen⟩
    iintro %w ⟨%hw, Hs, %f1, Hf, -⟩
    iframe; ipureintro; exact hw
  iintro %w ⟨⟨HQ, Hcl⟩, Hf⟩
  iapply HΦ
  iframe

private theorem spec6_holds (a6 m : Nat) (i0 : Instance) (hm : i0.memory[0]? = some m) (E : CoPset) :
    ⊢ spec6StackLength (GF := GF) a6 i0 [] lengthStack (fun a b => isStack a b m) E := by
  unfold spec6StackLength
  iintro %v %s %f %len !> %Φ ⟨Hf, Hcl, %hlen, Hs⟩ HΦ
  rw [show ([.basic (u32const v), .invoke a6] : Expr) = vToEList [valueOfUint v] ++ [.invoke a6]
    from rfl]
  iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ [Hf Hcl Hs]
  · iapply wp_invoke_native_frame .NotStuck E a6 i0 [.i32] [.i32] [] lengthStack [valueOfUint v] f
      (fun w => iprop(⌜w = .immV [valueOfUint len]⌝ ∗ isStack v s m))
      rfl ?_ $$ Hf Hcl
    · intro w
      iintro ⟨%h, -⟩; ipureintro; subst h; simp
    iintro Hf
    iapply spec_stack_length ⟨[valueOfUint v] ++ nZeros [], i0⟩ m v s E len $$ [Hf Hs]
    · iframe; ipureintro; exact ⟨hm, rfl, hlen⟩
    iintro %w ⟨%hw, Hs, Hf⟩
    iframe; ipureintro; exact hw
  iintro %w ⟨⟨HQ, Hcl⟩, Hf⟩
  iapply HΦ
  iframe

private theorem spec5_holds (a5 m t : Nat) (i0 : Instance) (hm : i0.memory[0]? = some m)
    (hty : i0.types[1]? = some (.tf [.i32] [.i32])) (htab : i0.tab[0]? = some t) (E : CoPset) :
    ⊢ spec5StackMap (GF := GF) a5 i0 [.i32, .i32] stackMap (fun a b => isStack a b m) t E := by
  unfold spec5StackMap
  iintro %f0 %fi %v %s %a %cl %Φ0 %Ψ !> %Φ ⟨Hf, Hcl, Hs, HΦ0, Ht, Ha, %hclt, #Hspec⟩ HΦ
  rw [show ([.basic (u32const v), .basic (.const (.int32 fi)), .invoke a5] : Expr) =
    vToEList [valueOfUint v, .int32 fi] ++ [.invoke a5] from rfl]
  iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ [Hf Hcl Hs HΦ0 Ht Ha]
  · iapply wp_invoke_native_frame .NotStuck E a5 i0 [.i32, .i32] [] [.i32, .i32] stackMap
      [valueOfUint v, .int32 fi] f0
      (fun w => iprop(⌜w = .immV []⌝ ∗ (∃ s', isStack v s' m ∗ stackAll2 s s' Ψ) ∗
        t ↦[wt][ Wasm.Int.natOfUint fi ] (some a) ∗ a ↦[wf] cl))
      rfl ?_ $$ Hf Hcl
    · intro w
      iintro ⟨%h, -⟩; ipureintro; subst h; simp
    iintro Hf
    iapply spec_stack_map ⟨[valueOfUint v, .int32 fi] ++ nZeros [.i32, .i32], i0⟩ m fi v s E t a cl
      Φ0 Ψ $$ [Hf Hs HΦ0 Ht Ha]
    · iframe; iframe Hspec
      ipureintro; exact ⟨hm, rfl, rfl, by simp [nZeros], hty, htab, hclt⟩
    iintro %w ⟨%hw, Hs, ⟨%f1, Hf, -⟩, Ht, Ha⟩
    iframe; ipureintro; exact hw
  iintro %w ⟨⟨⟨%hw, Hs, Ht, Ha⟩, Hcl⟩, Hf⟩
  iapply HΦ
  iframe; ipureintro; exact hw

private theorem spec5_trap_holds [LogrelNaInvs GF] (a5 m t : Nat) (i0 : Instance)
    (hm : i0.memory[0]? = some m) (hty : i0.types[1]? = some (.tf [.i32] [.i32]))
    (htab : i0.tab[0]? = some t) (E : CoPset) :
    ⊢ spec5StackMapTrap (GF := GF) a5 i0 [.i32, .i32] stackMap (fun a b => isStack a b m) t E := by
  unfold spec5StackMapTrap
  iintro %f0 %fi %v %s %a %cl %γ1 %Φ0 %Ψ %hγ !> %Φ ⟨Hcl, Hs, HΦ0, #Hinv, #Hspec, Hown, Hf⟩ HΦ
  rw [show ([.basic (u32const v), .basic (.const (.int32 fi)), .invoke a5] : Expr) =
    vToEList [valueOfUint v, .int32 fi] ++ [.invoke a5] from rfl]
  iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ [Hf Hcl Hs HΦ0 Hown]
  · iapply wp_invoke_native_frame .NotStuck E a5 i0 [.i32, .i32] [] [.i32, .i32] stackMap
      [valueOfUint v, .int32 fi] f0
      (fun w => iprop((⌜w = .trapV⌝ ∨ (⌜w = .immV []⌝ ∗ (∃ s', isStack v s' m ∗ stackAll2 s s' Ψ))) ∗
        NonAtomicInvariant.own (LogrelNaInvs.logrelNais (GF := GF)) ⊤))
      rfl ?_ $$ Hf Hcl
    · intro w
      iintro ⟨(%h | ⟨%h, -⟩), -⟩ <;> ipureintro <;> subst h <;> simp
    iintro Hf
    iapply spec_stack_map_trap ⟨[valueOfUint v, .int32 fi] ++ nZeros [.i32, .i32], i0⟩ m fi v s E t
      a cl γ1 Φ0 Ψ hγ $$ [Hf Hs HΦ0 Hown]
    · iframe; iframe Hinv; iframe Hspec
      ipureintro; exact ⟨hm, rfl, rfl, by simp [nZeros], hty, htab⟩
    iintro %w ⟨Hw, %f1, Hf, Hown, -⟩
    iframe
  iintro %w ⟨⟨⟨Hw, Hown⟩, Hcl⟩, Hf⟩
  iapply HΦ
  iframe
  icases Hw with (%hw | ⟨%hw, Hs⟩)
  · ileft; ipureintro; exact hw
  · iright; iframe; ipureintro; exact hw

@[rocq_alias iriswasm.stack_instantiate_para]
def stackInstantiatePara (exp_addrs : List Nat) (stack_mod_addr : Nat) : List HostE :=
  [.instantiate exp_addrs stack_mod_addr []]

variable [HvisG GF] [HmsG GF] [HasG GF]

@[rocq_alias iriswasm.own_vis_pointers]
def ownVisPointers (exp_addrs : List Nat) : IProp GF :=
  iprop([∗list] exp_addr ∈ exp_addrs, ∃ mexp, exp_addr ↪[vis] mexp)

@[rocq_alias iriswasm.own_vis_pointers_nodup]
theorem own_vis_pointers_nodup (exp_addrs : List Nat) :
    ⊢ (ownVisPointers exp_addrs -∗ ⌜exp_addrs.Nodup⌝ : IProp GF) := by
  induction exp_addrs with
  | nil => iintro -; ipureintro; exact .nil
  | cons e es ih =>
    unfold ownVisPointers
    iintro ⟨⟨%m, He⟩, Hes⟩
    ihave %Hnd : ⌜es.Nodup⌝ $$ [Hes]
    · unfold ownVisPointers at ih; iapply ih $$ Hes
    by_cases hin : e ∈ es
    · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hin
      ihave ⟨%m', Hc⟩ := BigSepL.bigSepL_lookup hi $$ Hes
      unfold visOwn
      ihave %Hne := ghost_map_elem_ne $$ He Hc
      exact (Hne rfl).elim
    · ipureintro; exact List.nodup_cons.2 ⟨hin, Hnd⟩

/-- The similar result does *not* hold for tables and memories, because `wtblock` and `wmblock`
are not necessarily exclusive resources. -/
@[rocq_alias iriswasm.module_inst_resources_func_nodup]
theorem module_inst_resources_func_nodup (ms : List ModuleFunc) (inst : Instance)
    (addrs : List Nat) :
    ⊢ (moduleInstResourcesFunc ms inst addrs -∗ ⌜addrs.Nodup⌝ : IProp GF) := by
  induction addrs generalizing ms with
  | nil => iintro -; ipureintro; exact .nil
  | cons a rest ih =>
    unfold moduleInstResourcesFunc
    iintro Hw
    ihave %Hlen := BigSepL2.bigSepL2_length $$ Hw
    cases ms with
    | nil => cases Hlen
    | cons m ms =>
      icases Hw with ⟨Hf, Hw⟩
      ihave %Hnd : ⌜rest.Nodup⌝ $$ [Hw]
      · unfold moduleInstResourcesFunc at ih; iapply ih $$ Hw
      by_cases hin : a ∈ rest
      · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hin
        obtain ⟨m', hm⟩ : ∃ m', ms[i]? = some m' := by
          have := (List.getElem?_eq_some_iff.mp hi).1
          simp at Hlen
          exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
        ihave Hc := BigSepL2.bigSepL2_lookup hm hi $$ Hw
        ihave %Hne := @pointsTo_ne GF Nat FunctionClosure NatMap _ WasmG.funcHs _ _ _ _ _ $$ Hf Hc
        exact (Hne rfl).elim
      · ipureintro; exact List.nodup_cons.2 ⟨hin, Hnd⟩

/-- The exports of an instantiated stack module, as seen by the host (`inst_vis` in Coq). -/
abbrev stackInstVis (idf0 idf1 idf2 idf3 idf4 idf5 idf6 idt : Nat)
    (name0 name1 name2 name3 name4 name5 name6 name7 : Name) : List ModuleExport :=
  ([(name0, idf0), (name1, idf1), (name2, idf2), (name3, idf3), (name4, idf4), (name5, idf5),
      (name6, idf6)].map fun (name, idf) =>
    ({ name := name, desc := .func (.funcidx idf) } : ModuleExport)) ++
  [{ name := name7, desc := .table (.tableidx idt) }]

/-- The closures of an instantiated stack module (`inst_map` in Coq). -/
abbrev stackInstMap (idf0 idf1 idf2 idf3 idf4 idf5 idf6 : Nat) (i0 : Instance)
    (l0 l1 l2 l3 l4 l5 l6 : List ValueType) (f0 f1 f2 f3 f4 f5 f6 : List BasicInstruction) :
    NatMap FunctionClosure :=
  PartialMap.ofList ([idf0, idf1, idf2, idf3, idf4, idf5, idf6].zip
    [.funcNative i0 (.tf [] [.i32]) l0 f0,
     .funcNative i0 (.tf [.i32] [.i32]) l1 f1,
     .funcNative i0 (.tf [.i32] [.i32]) l2 f2,
     .funcNative i0 (.tf [.i32] [.i32]) l3 f3,
     .funcNative i0 (.tf [.i32, .i32] []) l4 f4,
     .funcNative i0 (.tf [.i32, .i32] []) l5 f5,
     .funcNative i0 (.tf [.i32] [.i32]) l6 f6])

@[rocq_alias iriswasm.instantiate_stack_spec]
theorem instantiate_stack_spec [LogrelNaInvs GF] (s : Stuckness) (E : CoPset)
    (exp_addrs : List Nat) (stack_mod_addr : Nat) :
    exp_addrs.length = 8 →
    -- Knowing that we hold the stack module …
    ⊢ (stack_mod_addr ↪[mods] stackModule -∗
      -- … and we own the vis of the export targets …
      ownVisPointers exp_addrs -∗
      -- … instantiating the stack module yields the following:
      WP ((stackInstantiatePara exp_addrs stack_mod_addr, []) : HostExpr) @ s ; E
        {{ v,
          -- instantiation succeeds
          ⌜v = .immHV []⌝ ∗
          -- we still own the stack module
          stack_mod_addr ↪[mods] stackModule ∗
          ∃ (idf0 idf1 idf2 idf3 idf4 idf5 idf6 idt : Nat)
            (name0 name1 name2 name3 name4 name5 name6 name7 : Name)
            (f0 f1 f2 f3 f4 f5 f6 : List BasicInstruction)
            (i0 : Instance)
            (l0 l1 l2 l3 l4 l5 l6 : List ValueType)
            (tab : Tableinst)
            (isStack : Nat → List I32 → IProp GF)
            (nextStackAddrIs : Nat → IProp GF),
            -- the exports are in the vis stated, and all `wf` point to the right closures,
            -- i.e. a client can import them
            importResourcesHost exp_addrs
              (stackInstVis idf0 idf1 idf2 idf3 idf4 idf5 idf6 idt
                name0 name1 name2 name3 name4 name5 name6 name7) ∗
            importResourcesWasmTypecheckSepL2
              (stackInstVis idf0 idf1 idf2 idf3 idf4 idf5 idf6 idt
                name0 name1 name2 name3 name4 name5 name6 name7) expts
              (stackInstMap idf0 idf1 idf2 idf3 idf4 idf5 idf6 i0
                l0 l1 l2 l3 l4 l5 l6 f0 f1 f2 f3 f4 f5 f6)
              (insert (∅ : NatMap Tableinst) idt tab) ∅ ∅ ∗
            ⌜((stackInstVis idf0 idf1 idf2 idf3 idf4 idf5 idf6 idt
                name0 name1 name2 name3 name4 name5 name6 name7).map (·.desc)).Nodup⌝ ∗
            -- technically redundant, but commonly used by modules importing the stack
            ⌜[idf0, idf1, idf2, idf3, idf4, idf5, idf6].Nodup⌝ ∗
            ⌜tab.data.length ≥ 1⌝ ∗
            -- a token hiding the resources needed by `new_stack`
            nextStackAddrIs 0 ∗
            -- the specs of all exports
            spec0NewStack idf0 i0 l0 f0 isStack nextStackAddrIs E ∗
            spec1IsEmpty idf1 i0 l1 f1 isStack E ∗
            spec2IsFull idf2 i0 l2 f2 isStack E ∗
            spec3Pop idf3 i0 l3 f3 isStack E ∗
            spec4Push idf4 i0 l4 f4 isStack E ∗
            spec5StackMap idf5 i0 l5 f5 isStack idt E ∗
            spec5StackMapTrap idf5 i0 l5 f5 isStack idt E ∗
            spec6StackLength idf6 i0 l6 f6 isStack E }} : IProp GF) := by
  intro hlen
  iintro Hmod Hexps
  ihave %Hnodupexp : ⌜exp_addrs.Nodup⌝ $$ [Hexps]
  · iapply own_vis_pointers_nodup $$ Hexps
  unfold stackInstantiatePara
  iapply Iris.wp_wand $$ [Hmod Hexps]
  · iapply instantiation_spec_operational_no_start s E stack_mod_addr [] [] exp_addrs stackModule []
      expts ∅ ∅ ∅ ∅ rfl module_typing_stack ⟨⟨[], rfl⟩, ⟨[], rfl⟩, ⟨[], rfl⟩⟩
    unfold instantiationResourcesPre
    iframe
    isplitr
    · unfold importResourcesHost; iapply BigSepL2.bigSepL2_nil.2; iempintro
    isplitr
    · unfold instantiationResourcesPreWasm
      isplitr
      · iapply (irwt_nodup_equiv [] [] ∅ ∅ ∅ ∅ .nil).2
        unfold importResourcesWasmTypecheckSepL2 importResourcesWasmDomcheck
        isplitr
        · ipureintro; simp [PartialMap.dom, get?_empty, extFuncAddrs, extTabAddrs, extMemAddrs, extGlobAddrs, extFuncs, extTabs, extMems, extGlobs]
        · iapply BigSepL2.bigSepL2_nil.2; iempintro
      isplitr
      · ipureintro; intro e he; simp [stackModule] at he
      · ipureintro; intro d hd; simp [stackModule] at hd
    isplitl [Hexps]
    · unfold exportOwnershipHost ownVisPointers; iexact Hexps
    · ipureintro; simpa [stackModule] using hlen
  iintro %v ⟨%hv, Hpost⟩
  isplitr
  · ipureintro; exact hv
  unfold instantiationResourcesPost instantiationResourcesPostWasm
  icases Hpost with ⟨Hmod, -, %inst, ⟨%g_inits, %tabA, %memA, %globA, %wts', %wms', -,
    %⟨hty, -, -, -, -, -⟩, %htab, -, -, %hmem, -, -, -, -, Hwasm⟩, Hexphost⟩
  iframe
  subst htab hmem
  unfold moduleInstResourcesWasm
  icases Hwasm with ⟨Hwf, Hwt, Hwm, -⟩
  ihave %Hnodupwf : ⌜_⌝ $$ [Hwf]
  · iapply module_inst_resources_func_nodup $$ Hwf
  unfold moduleInstResourcesFunc moduleInstResourcesTab moduleInstResourcesMem
  ihave %Hiflen := BigSepL2.bigSepL2_length $$ Hwf
  ihave %Hitlen := BigSepL2.bigSepL2_length $$ Hwt
  ihave %Himlen := BigSepL2.bigSepL2_length $$ Hwm
  obtain ⟨types, funcs, tabs, mems, globs⟩ := inst
  simp only at hty
  subst hty
  simp [stackModule, getImportFuncCount, getImportTableCount, getImportMemCount, moduleInstBuildTables, moduleInstBuildMems, moduleInstTableBase, moduleInstMemBase] at Hiflen Hitlen Himlen Hnodupwf
  rcases funcs with _|⟨a0,_|⟨a1,_|⟨a2,_|⟨a3,_|⟨a4,_|⟨a5,_|⟨a6,_|⟨_,_⟩⟩⟩⟩⟩⟩⟩⟩ <;> simp at Hiflen
  rcases tabs with _|⟨t,_|⟨_,_⟩⟩ <;> simp at Hitlen
  rcases mems with _|⟨m,_|⟨_,_⟩⟩ <;> simp at Himlen
  rcases exp_addrs with _|⟨e0,_|⟨e1,_|⟨e2,_|⟨e3,_|⟨e4,_|⟨e5,_|⟨e6,_|⟨e7,_|⟨_,_⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> simp at hlen
  isimp [stackModule, getImportFuncCount, getImportTableCount, getImportMemCount, moduleInstBuildTables,
    moduleInstBuildMems, moduleInstTableBase, moduleInstMemBase, moduleExportResourcesHost,
    moduleInstTableBaseCreate, moduleInstMemBaseFunc, memMk] at Hwf Hwt Hwm Hexphost
  icases Hwf with ⟨Hf0, Hf1, Hf2, Hf3, Hf4, Hf5, Hf6, -⟩
  icases Hwt with ⟨Ht, -⟩
  icases Hwm with ⟨Hm, -⟩
  iunfold memBlock at Hm
  icases Hm with ⟨-, -, Hmlen, -⟩
  icases Hexphost with ⟨⟨%n0, Hx0⟩, ⟨%n1, Hx1⟩, ⟨%n2, Hx2⟩, ⟨%n3, Hx3⟩, ⟨%n4, Hx4⟩, ⟨%n5, Hx5⟩, ⟨%n6, Hx6⟩, ⟨%n7, Hx7⟩, -⟩
  isimp at Hf0 Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hx0 Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7
  let i0 : Instance := ⟨[.tf [] [.i32], .tf [.i32] [.i32], .tf [.i32, .i32] []],
    [a0, a1, a2, a3, a4, a5, a6], [t], [m], globs⟩
  iexists a0, a1, a2, a3, a4, a5, a6, t, n0, n1, n2, n3, n4, n5, n6, n7,
    newStack, isEmpty, isFull, pop, push, stackMap, lengthStack, i0,
    [.i32], [], [], [.i32], [.i32], [.i32, .i32], [], ⟨RunTable.uniform 1 none, none⟩,
    (fun a b => isStack a b m), (fun n => m ↦[wmlength] (.i32, n))
  isplitl [Hx0 Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7]
  · iunfold importResourcesHost
    isimp only [stackInstVis, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    repeat (iapply BigSepL2.bigSepL2_cons.2; iframe)
    iapply BigSepL2.bigSepL2_nil.2; iempintro
  have hnd : NoDupKeys ([a0, a1, a2, a3, a4, a5, a6].zip
      [FunctionClosure.funcNative i0 (.tf [] [.i32]) [.i32] newStack,
       .funcNative i0 (.tf [.i32] [.i32]) [] isEmpty,
       .funcNative i0 (.tf [.i32] [.i32]) [] isFull,
       .funcNative i0 (.tf [.i32] [.i32]) [.i32] pop,
       .funcNative i0 (.tf [.i32, .i32] []) [.i32] push,
       .funcNative i0 (.tf [.i32, .i32] []) [.i32, .i32] stackMap,
       .funcNative i0 (.tf [.i32] [.i32]) [] lengthStack]) := by
    simpa [NoDupKeys] using Hnodupwf
  isplitl [Hf0 Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Ht]
  · iunfold importResourcesWasmTypecheckSepL2, importResourcesWasmDomcheck
    isimp only [stackInstVis, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    isplitr
    · ipureintro
      refine ⟨fun k => ?_, fun k => ?_, fun k => ?_, fun k => ?_⟩
      · simp only [PartialMap.dom, stackInstMap, PartialMap.ofList, List.zip_cons_cons, List.zip_nil_right,
          List.foldr_cons, List.foldr_nil, LawfulPartialMap.get?_insert, get?_empty]
        rw [show extFuncAddrs _ = [a0, a1, a2, a3, a4, a5, a6] from rfl]
        repeat' split
        all_goals simp_all [eq_comm]
      · simp only [PartialMap.dom, LawfulPartialMap.get?_insert, get?_empty]
        rw [show extTabAddrs _ = [t] from rfl]
        split <;> simp_all [eq_comm]
      · simp [PartialMap.dom, get?_empty, extMemAddrs, extMems]
      · simp [PartialMap.dom, get?_empty, extGlobAddrs, extGlobs]
    isimp only [expts, funcTypes, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    iapply BigSepL2.bigSepL2_cons.2
    isplitl [Hf0]
    · iexists _
      isplitl [Hf0]
      · iexact Hf0
      ipureintro; exact ⟨LawfulPartialMap.get?_ofList_some (by simp [i0]) hnd, rfl⟩
    iapply BigSepL2.bigSepL2_cons.2
    isplitl [Hf1]
    · iexists _
      isplitl [Hf1]
      · iexact Hf1
      ipureintro; exact ⟨LawfulPartialMap.get?_ofList_some (by simp [i0]) hnd, rfl⟩
    iapply BigSepL2.bigSepL2_cons.2
    isplitl [Hf2]
    · iexists _
      isplitl [Hf2]
      · iexact Hf2
      ipureintro; exact ⟨LawfulPartialMap.get?_ofList_some (by simp [i0]) hnd, rfl⟩
    iapply BigSepL2.bigSepL2_cons.2
    isplitl [Hf3]
    · iexists _
      isplitl [Hf3]
      · iexact Hf3
      ipureintro; exact ⟨LawfulPartialMap.get?_ofList_some (by simp [i0]) hnd, rfl⟩
    iapply BigSepL2.bigSepL2_cons.2
    isplitl [Hf4]
    · iexists _
      isplitl [Hf4]
      · iexact Hf4
      ipureintro; exact ⟨LawfulPartialMap.get?_ofList_some (by simp [i0]) hnd, rfl⟩
    iapply BigSepL2.bigSepL2_cons.2
    isplitl [Hf5]
    · iexists _
      isplitl [Hf5]
      · iexact Hf5
      ipureintro; exact ⟨LawfulPartialMap.get?_ofList_some (by simp [i0]) hnd, rfl⟩
    iapply BigSepL2.bigSepL2_cons.2
    isplitl [Hf6]
    · iexists _
      isplitl [Hf6]
      · iexact Hf6
      ipureintro; exact ⟨LawfulPartialMap.get?_ofList_some (by simp [i0]) hnd, rfl⟩
    iapply BigSepL2.bigSepL2_cons.2
    isplitl [Ht]
    · iexists _, { limits := { min := 1, max := none }, elemType := .funcref }
      isplitl [Ht]
      · iexact Ht
      ipureintro; exact ⟨get?_insert_eq rfl, rfl, by decide⟩
    iapply BigSepL2.bigSepL2_nil.2; iempintro
  isplitr
  · ipureintro
    rw [show (stackInstVis a0 a1 a2 a3 a4 a5 a6 t n0 n1 n2 n3 n4 n5 n6 n7).map (·.desc) =
      [a0, a1, a2, a3, a4, a5, a6].map (fun x => ModuleExportDesc.func (.funcidx x)) ++
        [.table (.tableidx t)] from rfl]
    exact List.nodup_append.2 ⟨List.Pairwise.map _ (fun a b hab heq => hab (by simpa using heq)) Hnodupwf,
      by simp, by simp⟩
  isplitr
  · ipureintro; exact Hnodupwf
  isplitr
  · ipureintro; decide
  isplitl [Hmlen]
  · isimp only [Wasm.lengthMem, MemoryList.length_make] at Hmlen
    iexact Hmlen
  isplitr
  · iapply spec0_holds a0 m i0 rfl E
  isplitr
  · iapply spec1_holds a1 m i0 rfl E
  isplitr
  · iapply spec2_holds a2 m i0 rfl E
  isplitr
  · iapply spec3_holds a3 m i0 rfl E
  isplitr
  · iapply spec4_holds a4 m i0 rfl E
  isplitr
  · iapply spec5_holds a5 m t i0 rfl rfl rfl E
  isplitr
  · iapply spec5_trap_holds a5 m t i0 rfl rfl rfl E
  iapply spec6_holds a6 m i0 rfl E

end StackModule

end IrisWasm.Examples.Stack
