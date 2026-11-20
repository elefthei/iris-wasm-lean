/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Examples.Stack.StackInstantiation
import IrisWasm.Rules.IrisExampleHelper
import Wasm.TypeCheckerReflectsTyping

/-! Port of `theories/iris/examples/stack/stack_with_reentrancy.v`.

Every Coq name of this file is also declared in `stack_client.v`, so the declarations live in the
sub-namespace `IrisWasm.Examples.Stack.StackWithReentrancy` (aliases
`iriswasm.stack_with_reentrancy.<name>`). -/

namespace IrisWasm.Examples.Stack

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm
open scoped Iris.Std.PartialMap

namespace StackWithReentrancy

/-- Functions imported from the stack module: 0 new_stack, 1 is_empty, 2 is_full, 3 pop, 4 push,
5 map, 6 length; function 7 is a `call_host` that modifies the table; 8 is `main`, 9 is `square`,
10 is `timesTwo`. -/
@[rocq_alias iriswasm.stack_with_reentrancy.main]
def main : List BasicInstruction :=
  [ .call 0,
    .teeLocal 0,
    i32const (-1),
    .relop .i32 (.i .eq),
    -- If new_stack failed, set global v0 to -1 and return
    .if_ (.tf [] []) [i32const (-1), .setGlobal 0, .return_] [],
    .getLocal 0,
    i32const 4,
    .call 4, -- Push 4 onto the stack
    .getLocal 0,
    i32const 6,
    .call 4, -- Push 6 onto the stack
    .getLocal 0,
    i32const 0,
    .call 5, -- Map square onto the stack
    i32const 0,
    i32const 10,
    .call 7, -- Modify the table to now have *2 as the 0th function
    .getLocal 0,
    i32const 0,
    .call 5, -- Map *2 onto the stack
    .getLocal 0,
    .call 3, -- Pop 72
    .getLocal 0,
    .call 3, -- Pop 32
    .binop .i32 (.i .sub), -- Subtract the two, to get 40
    .setGlobal 0 ] -- Assign the 0th global to 40

@[rocq_alias iriswasm.stack_with_reentrancy.square]
def square : List BasicInstruction :=
  [ .getLocal 0,
    .getLocal 0,
    .binop .i32 (.i .mul) ]

@[rocq_alias iriswasm.stack_with_reentrancy.times_two]
def timesTwo : List BasicInstruction :=
  [ .getLocal 0,
    i32const 2,
    .binop .i32 (.i .mul) ]

@[rocq_alias iriswasm.stack_with_reentrancy.client_module]
def clientModule : Module where
  types := [.tf [] [], .tf [] [.i32], .tf [.i32] [.i32], .tf [.i32, .i32] []]
  funcs := [{ type := .typeidx 0, locals := [.i32], body := main },
            { type := .typeidx 2, locals := [], body := square },
            { type := .typeidx 2, locals := [], body := timesTwo }]
  -- the table is imported, and thus only mentioned later
  tables := []
  mems := []
  globals := [{ type := { mut_ := .mut, t := .i32 }, init := [i32const 0] }]
  -- the (imported) table originally contains the square function
  elem := [{ table := .tableidx 0, offset := [i32const 0], init := [.funcidx 9] }]
  data := []
  start := some { func := .funcidx 8 }
  imports := [
    { module := nameOfString "Stack", name := nameOfString "new_stack", desc := .func 1 },
    { module := nameOfString "Stack", name := nameOfString "is_empty", desc := .func 2 },
    { module := nameOfString "Stack", name := nameOfString "is_full", desc := .func 2 },
    { module := nameOfString "Stack", name := nameOfString "pop", desc := .func 2 },
    { module := nameOfString "Stack", name := nameOfString "push", desc := .func 3 },
    { module := nameOfString "Stack", name := nameOfString "stack_map", desc := .func 3 },
    { module := nameOfString "Stack", name := nameOfString "stack_length", desc := .func 2 },
    { module := nameOfString "Stack", name := nameOfString "table",
      desc := .table { limits := { min := 1, max := none }, elemType := .funcref } },
    { module := nameOfString "Host", name := nameOfString "modify_table", desc := .func 3 } ]
  exports := [{ name := nameOfString "answer", desc := .global (.globalidx 0) }]

@[rocq_alias iriswasm.stack_with_reentrancy.module_typing_client]
theorem module_typing_client :
    ModuleTyping clientModule (expts ++ [.func (.tf [.i32, .i32] [])])
      [.glob { mut_ := .mut, t := .i32 }] := by
  refine ⟨[.tf [] [], .tf [.i32] [.i32], .tf [.i32] [.i32]], [{ mut_ := .mut, t := .i32 }], ?_⟩
  refine ⟨.cons ⟨by decide, by decide, ?_⟩ (.cons ⟨by decide, by decide, ?_⟩
      (.cons ⟨by decide, by decide, ?_⟩ .nil)), by decide,
    by decide, .cons ⟨by decide, rfl, ?_⟩ .nil, ?_, by simp, by decide, ?_, .cons (by decide) .nil⟩
  · rw [← b_e_type_checker_reflects_typing]; kernel_rfl
  · rw [← b_e_type_checker_reflects_typing]; kernel_rfl
  · rw [← b_e_type_checker_reflects_typing]; kernel_rfl
  · rw [← b_e_type_checker_reflects_typing]; kernel_rfl
  · simp only [List.mem_singleton, forall_eq]
    refine ⟨by decide, ?_, by decide, by decide⟩
    rw [← b_e_type_checker_reflects_typing]; kernel_rfl
  · repeat' first | exact .nil | refine .cons (by decide) ?_

@[rocq_alias iriswasm.stack_with_reentrancy.module_restrictions_client]
theorem module_restrictions_client : ModuleRestrictions clientModule :=
  ⟨⟨[.int32 (Wasm.Int.intOfZ 0)], rfl⟩, ⟨[Wasm.Int.intOfZ 0], rfl⟩, ⟨[], rfl⟩⟩

/-- The 7th import of the client is the host import. -/
@[rocq_alias iriswasm.stack_with_reentrancy.stack_instantiate]
def stackInstantiate (exp_addrs : List Nat) (stack_mod_addr client_mod_addr : Nat) :
    List HostE :=
  [.instantiate (exp_addrs.take 8) stack_mod_addr [],
   .instantiate [exp_addrs.getD 8 0] client_mod_addr (exp_addrs.take 8 ++ [exp_addrs.getD 9 0])]

end StackWithReentrancy

open StackWithReentrancy

section Client2_main
variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF]

attribute [local instance] WasmG.invGS

private instance (idf0 : Nat) (i : Instance) (l : List ValueType) (fn : List BasicInstruction)
    (isStack : Nat → List I32 → IProp GF) (P : Nat → IProp GF) (E : CoPset) :
    Persistent (spec0NewStack idf0 i l fn isStack P E) := by
  unfold spec0NewStack; infer_instance

private instance (idf : Nat) (i : Instance) (l : List ValueType) (fn : List BasicInstruction)
    (isStack : Nat → List I32 → IProp GF) (E : CoPset) :
    Persistent (spec3Pop idf i l fn isStack E) := by
  unfold spec3Pop; infer_instance

private instance (idf : Nat) (i : Instance) (l : List ValueType) (fn : List BasicInstruction)
    (isStack : Nat → List I32 → IProp GF) (E : CoPset) :
    Persistent (spec4Push idf i l fn isStack E) := by
  unfold spec4Push; infer_instance

private instance (idf : Nat) (i : Instance) (l : List ValueType) (fn : List BasicInstruction)
    (isStack : Nat → List I32 → IProp GF) (j0 : Nat) (E : CoPset) :
    Persistent (spec5StackMap idf i l fn isStack j0 E) := by
  unfold spec5StackMap; infer_instance

private theorem wp_wand_s {s : Stuckness} {E : CoPset} {e : Expr} {Φ Ψ : Val → IProp GF} :
    iprop(WP e @ s ; E {{ Φ }}) ⊢ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s ; E {{ Ψ }} :=
  IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)

private theorem wp_value_of {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF} (v : Val)
    {e : Expr} (h : e = ofVal v) : Φ v ⊢ WP e @ s ; E {{ Φ }} := by
  subst h
  exact IrisWp.wp_value (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) ⟨rfl⟩

/-- Calling a function after pushing constant arguments. -/
private theorem wp_call_consts {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF} (f1 : Frame)
    (vs : Expr) (hc : constList vs = true) (i a : Nat) (h : f1.inst.funcs[i]? = some a) :
    ⊢ ↪[frame] f1 -∗ ▷ (↪[frame] f1 -∗ WP (vs ++ [.invoke a]) @ s ; E {{ Φ }}) -∗
      WP (vs ++ [.basic (.call i)]) @ s ; E {{ Φ }} := by
  iintro Hf H
  iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).2
  rw [show vs ++ [.basic (.call i)] = vs ++ [.basic (.call i)] ++ [] from (List.append_nil _).symm]
  iapply wp_base_push hc
  simp only [frameBase, List.nil_append, List.append_nil]
  iapply wp_call_ctx _ _ _ f1 i a _ _ h $$ Hf
  inext; iintro Hf
  iapply wp_base_pull
  simp only [pullBase, List.append_nil]
  iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).1
  iapply H $$ Hf

/-- Invoking a native `[] → []` function whose body may `return` or stop at a host call
(Lean helper; the Coq proof does this inline). -/
private theorem wp_invoke_native_unit_ch (s : Stuckness) (E : CoPset) (a : Nat) (i : Instance)
    (ts : List ValueType) (body : List BasicInstruction) (f0 : Frame) (R : IProp GF)
    (R' : Frame → IProp GF) (tf : FunctionType) (h : Hostfuncidx) (vcs : List Value)
    (rest : Expr) :
    ⊢ (↪[frame] f0 -∗ a ↦[wf] (.funcNative i (.tf [] []) ts body) -∗
      (↪[frame] (⟨nZeros ts, i⟩ : Frame) -∗
        WP (toEList body : Expr) @ s ; E
          {{ w, ∃ f1, ↪[frame] f1 ∗ (((⌜w = .immV []⌝ ∨ ⌜∃ sh, w = .retV sh⌝) ∗ R) ∨
            (⌜w = .callHostV tf h vcs (.base [] rest)⌝ ∗ R' f1)) }}) -∗
      WP ([.invoke a] : Expr) @ s ; E
        {{ w, (((⌜w = .immV []⌝ ∗ R) ∨ (∃ f1, ⌜w = .callHostV tf h vcs
            (.local [] 0 f1 (.label [] 0 [] (.base [] rest) []) [])⌝ ∗ R' f1)) ∗
          a ↦[wf] (.funcNative i (.tf [] []) ts body)) ∗ ↪[frame] f0 }} : IProp GF) := by
  iintro Hf Ha Hbody
  rw [show ([.invoke a] : Expr) = vToEList [] ++ [.invoke a] from rfl]
  iapply wp_invoke_native _ _ _ (vToEList []) [] [] [] ts a body i 0 f0
    (to_of_val (.immV [])) rfl rfl $$ Hf Ha
  inext; iintro ⟨Hf, Ha⟩
  iapply (wp_frame_rewrite _ _ _ _ _ _).1
  iapply wp_frame_bind _ _ _ _ _ _ _ ?_ $$ Hf
  · simp [toVal, toValInstr, mergeValuesList]
  iintro Hf
  rw [← List.nil_append [AdministrativeInstruction.basic (.block (.tf [] []) body)]]
  iapply wp_block (n := 0) (t1s := []) rfl rfl rfl rfl $$ Hf
  inext; iintro Hf
  rw [List.nil_append]
  iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).2
  iapply wp_label_push_nil
  simp only [pushBase]
  iapply wp_label_bind
  simp only [List.nil_append]
  iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ [Hbody Hf]
  · iapply Hbody $$ Hf
  iintro %w ⟨%f1, Hf, Hw⟩
  icases Hw with (⟨(%hw | %hw), HR⟩ | ⟨%hw, HR⟩)
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
    inext; iframe; ileft; iframe; ipureintro; rfl
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
    iframe; ileft; iframe; ipureintro; rfl
  · subst hw
    unfold wpWasmCtx
    iintro %LI %hLI
    have hLI' : LI = ofVal (.callHostV tf h vcs (.label [] 0 [] (.base [] rest) [])) := by
      simpa [lfilled, lfill, constList, ofVal, llfill, vToEList] using hLI
    subst hLI'
    iapply wp_value_of (.callHostV tf h vcs (.label [] 0 [] (.base [] rest) [])) rfl
    iexists f1
    iframe Hf
    iintro Hf0
    iapply (wp_frame_rewrite _ _ _ _ _ _).2
    iapply wp_value_of
      (.callHostV tf h vcs (.local [] 0 f1 (.label [] 0 [] (.base [] rest) []) [])) ?_
    · rfl
    iframe Hf0 Ha
    iright; iexists f1; iframe HR; ipureintro; rfl

/-- Resuming a `[] → []` function after a host call (Lean helper). -/
private theorem wp_resume_unit (s : Stuckness) (E : CoPset) (f0 f1 : Frame) (rest : Expr)
    (R : IProp GF) (hrest : toVal ([.local 0 f1 [.label 0 [] rest]] : Expr) = none) :
    ⊢ (↪[frame] f0 -∗
      (↪[frame] f1 -∗ WP rest @ s ; E {{ w, ⌜w = .immV []⌝ ∗ R ∗ ∃ f2, ↪[frame] f2 }}) -∗
      WP ([.local 0 f1 [.label 0 [] rest]] : Expr) @ s ; E
        {{ w, (⌜w = .immV []⌝ ∗ R) ∗ ↪[frame] f0 }} : IProp GF) := by
  iintro Hf Hbody
  iapply (wp_frame_rewrite _ _ _ _ _ _).1
  iapply wp_frame_bind _ _ _ _ _ _ _ hrest $$ Hf
  iintro Hf
  iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).2
  iapply wp_label_push_nil
  simp only [pushBase]
  iapply wp_label_bind
  iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ [Hbody Hf]
  · iapply Hbody $$ Hf
  iintro %w ⟨%hw, HR, %f2, Hf⟩
  subst hw
  rw [show ofVal (Val.immV []) = vToEList [] from rfl]
  iapply wp_val_return (vs' := []) (es'' := []) (v_to_e_is_const_list []) $$ Hf
  iintro Hf
  simp only [List.nil_append, List.append_nil]
  iapply wp_value_of (e := vToEList []) (.immV []) rfl
  iexists f2
  iframe
  iintro Hf0
  iapply wp_frame_value _ _ _ _ 0 _ _ [] (to_of_val _) rfl $$ Hf0
  inext; iframe; ipureintro; rfl

/-- `[get_local 0; X; i32.mul]` where `X` pushes `x` (the bodies of `square` and `timesTwo`). -/
private theorem wp_mul_body (E : CoPset) (f : Frame) (u x : I32) (X : AdministrativeInstruction)
    (hloc : f.locs[0]? = some (.int32 u))
    (hX : ⊢ (↪[frame] f -∗ WP ([X] : Expr) @ E {{ w, ⌜w = .immV [.int32 x]⌝ ∗ ↪[frame] f }} :
      IProp GF)) :
    ⊢ (↪[frame] f -∗ WP ([.basic (.getLocal 0), X, .basic (.binop .i32 (.i .mul))] : Expr) @ E
      {{ w, ⌜w = .immV [.int32 (u * x)]⌝ ∗ ↪[frame] f }} : IProp GF) := by
  iintro Hf
  rw [show ([.basic (.getLocal 0), X, .basic (.binop .i32 (.i .mul))] : Expr) =
    [.basic (.getLocal 0)] ++ [X, .basic (.binop .i32 (.i .mul))] from rfl]
  iapply wp_seq_imm [.int32 u] iprop(↪[frame] f) $$ [Hf]
  · iapply wp_get_local _ _ _ 0 (fun w => iprop(⌜w = .immV [.int32 u]⌝)) f hloc $$ [] Hf
    inext; ipureintro; rfl
  iintro Hf
  rw [show vToEList [.int32 u] ++ [X, .basic (.binop .i32 (.i .mul))] =
    ([.basic (.const (.int32 u)), X] : Expr) ++ [.basic (.binop .i32 (.i .mul))] from rfl]
  iapply wp_seq_imm [.int32 u, .int32 x] iprop(↪[frame] f) $$ [Hf]
  · iapply wp_val_cons_imm (.int32 u) [.int32 x]
    iapply hX $$ Hf
  iintro Hf
  rw [show vToEList [.int32 u, .int32 x] ++ [.basic (.binop .i32 (.i .mul))] =
    ([.basic (.const (.int32 u)), .basic (.const (.int32 x)), .basic (.binop .i32 (.i .mul))] :
      Expr) from rfl]
  iapply wp_binop (v := .int32 (u * x)) rfl $$ Hf
  inext; ipureintro; rfl

private theorem wp_square_body (E : CoPset) (inst : Instance) (u : I32) :
    ⊢ (↪[frame] (⟨[.int32 u], inst⟩ : Frame) -∗ WP (toEList square : Expr) @ E
      {{ w, ⌜w = .immV [.int32 (u * u)]⌝ ∗ ↪[frame] (⟨[.int32 u], inst⟩ : Frame) }} : IProp GF) :=
  wp_mul_body E _ u u _ rfl (by
    iintro Hf
    iapply wp_get_local _ _ _ 0 (fun w => iprop(⌜w = .immV [.int32 u]⌝)) _ rfl $$ [] Hf
    inext; ipureintro; rfl)

private theorem wp_times_two_body (E : CoPset) (inst : Instance) (u : I32) :
    ⊢ (↪[frame] (⟨[.int32 u], inst⟩ : Frame) -∗ WP (toEList timesTwo : Expr) @ E
      {{ w, ⌜w = .immV [.int32 (u * Wasm.Int.intOfZ 2)]⌝ ∗ ↪[frame] (⟨[.int32 u], inst⟩ : Frame) }} :
      IProp GF) :=
  wp_mul_body E _ u _ _ rfl (by
    iintro Hf
    iapply wp_value_of (e := [.basic (i32const 2)]) (.immV [.int32 (Wasm.Int.intOfZ 2)]) rfl
    iframe; ipureintro; rfl)

/-- The callback obligation of `spec5StackMap` for a native closure `[i32] → [i32]` with no
locals computing `F` (Lean helper). -/
private theorem callback_spec (E : CoPset) (i5 inst : Instance) (j0 : Nat) (f : I32) (a : Nat)
    (body : List BasicInstruction) (F : I32 → I32) (Φ : I32 → IProp GF) (Ψ : I32 → I32 → IProp GF)
    (hΨ : ∀ u, ⊢ Ψ u (F u))
    (hbody : ∀ u : I32, ⊢ (↪[frame] (⟨[.int32 u], inst⟩ : Frame) -∗ WP (toEList body : Expr) @ E
      {{ w, ⌜w = .immV [.int32 (F u)]⌝ ∗ ↪[frame] (⟨[.int32 u], inst⟩ : Frame) }} : IProp GF)) :
    ⊢ (∀ (u : I32) (fc : Frame),
        {{{{ Φ u ∗
            ⌜i5 = fc.inst⌝ ∗
            ↪[frame] fc ∗
            j0 ↦[wt][ Wasm.Int.natOfUint f ] (some a) ∗
            a ↦[wf] (.funcNative inst (.tf [.i32] [.i32]) [] body) }}}}
          ([.basic (.const (.int32 u)), .invoke a] : Expr) @ E
          {{{{ w, (∃ v, ⌜w = .immV [.int32 v]⌝ ∗ Ψ u v) ∗
              ↪[frame] fc ∗
              j0 ↦[wt][ Wasm.Int.natOfUint f ] (some a) ∗
              a ↦[wf] (.funcNative inst (.tf [.i32] [.i32]) [] body) }}}} : IProp GF) := by
  iintro %u %fc
  imodintro
  iintro %Φ' ⟨-, -, Hf, Ht, Hcl⟩ HΦ'
  rw [show ([.basic (.const (.int32 u)), .invoke a] : Expr) = vToEList [.int32 u] ++ [.invoke a]
    from rfl]
  iapply wp_wand_s $$ [Hf Hcl]
  · iapply wp_invoke_native_frame _ E a inst [.i32] [.i32] [] body [.int32 u] fc
      (fun w => iprop(⌜w = .immV [.int32 (F u)]⌝)) rfl ?_ $$ Hf Hcl
    · intro w; iintro %hw; ipureintro; exact .inr ⟨_, hw, rfl⟩
    rw [show ([Value.int32 u] ++ nZeros []) = [Value.int32 u] from rfl]
    iintro Hf
    iapply wp_wand_s $$ [Hf]
    · iapply hbody u $$ Hf
    iintro %w ⟨%hw, Hf⟩
    isplitr
    · ipureintro; exact hw
    iexists _; iexact Hf
  iintro %w ⟨⟨%hw, Hcl⟩, Hf⟩
  subst hw
  iapply HΦ'
  iframe
  iexists F u
  isplitr
  · ipureintro; rfl
  iapply hΨ

/-- The result relation of `stack_map F` on a two-element stack. -/
private theorem stackAll2_map (F : I32 → I32) (a b : I32) (s' : List I32) :
    stackAll2 [a, b] s' (fun u v => iprop(⌜v = F u⌝)) ⊢ (⌜s' = [F a, F b]⌝ : IProp GF) := by
  match s' with
  | [x, y] =>
    simp only [stackAll2]
    iintro ⟨%hx, %hy, -⟩
    ipureintro; rw [hx, hy]
  | [] => simp only [stackAll2]; iintro H; iexfalso; iexact H
  | [_] => simp only [stackAll2]; iintro ⟨-, H⟩; iexfalso; iexact H
  | _ :: _ :: _ :: _ => simp only [stackAll2]; iintro ⟨-, -, H⟩; iexfalso; iexact H

/-- The client's `main` up to the host call `modify_table` (Coq: first part of the proof of
`instantiate_stack_client_spec`). -/
private theorem main_part1 (E : CoPset) (inst istack : Instance)
    (idnstart idf0 idf4 idf5 idmodtab a9 idt g ha : Nat) (l0 l4 l5 : List ValueType)
    (f0 f4 f5 : List BasicInstruction) (isStack : Nat → List I32 → IProp GF)
    (nextStackAddrIs : Nat → IProp GF) (vg : Value)
    (hf0 : inst.funcs[0]? = some idf0) (hf4 : inst.funcs[4]? = some idf4)
    (hf5 : inst.funcs[5]? = some idf5) (hf7 : inst.funcs[7]? = some idmodtab)
    (hg : inst.globs[0]? = some g) :
    ⊢ (↪[frame] emptyFrame -∗
      idnstart ↦[wf] (.funcNative inst (.tf [] []) [.i32] main) -∗
      spec0NewStack idf0 istack l0 f0 isStack nextStackAddrIs E -∗
      spec4Push idf4 istack l4 f4 isStack E -∗
      spec5StackMap idf5 istack l5 f5 isStack idt E -∗
      idf0 ↦[wf] (.funcNative istack (.tf [] [.i32]) l0 f0) -∗
      idf4 ↦[wf] (.funcNative istack (.tf [.i32, .i32] []) l4 f4) -∗
      idf5 ↦[wf] (.funcNative istack (.tf [.i32, .i32] []) l5 f5) -∗
      nextStackAddrIs 0 -∗
      g ↦[wg] (⟨.mut, vg⟩ : Global) -∗
      idt ↦[wt][ 0 ] (some a9) -∗
      a9 ↦[wf] (.funcNative inst (.tf [.i32] [.i32]) [] square) -∗
      idmodtab ↦[wf] (.funcHost (.tf [.i32, .i32] []) (.hostfuncidx ha)) -∗
      WP ([.invoke idnstart] : Expr) @ E
        {{ w, (((⌜w = .immV []⌝ ∗ g ↦[wg] (⟨.mut, valueOfInt (-1)⟩ : Global)) ∨
          (∃ f1, ⌜w = .callHostV (.tf [.i32, .i32] []) (.hostfuncidx ha)
              [.int32 (Wasm.Int.intOfZ 0), .int32 (Wasm.Int.intOfZ 10)]
              (.local [] 0 f1 (.label [] 0 [] (.base [] (toEList (main.drop 17))) []) [])⌝ ∗
            ∃ k, ⌜f1 = ⟨[valueOfUint k], inst⟩⌝ ∗
              isStack k [Wasm.Int.intOfZ 6 * Wasm.Int.intOfZ 6,
                Wasm.Int.intOfZ 4 * Wasm.Int.intOfZ 4] ∗
              g ↦[wg] (⟨.mut, vg⟩ : Global) ∗
              idt ↦[wt][ 0 ] (some a9) ∗
              idf5 ↦[wf] (.funcNative istack (.tf [.i32, .i32] []) l5 f5))) ∗
          idnstart ↦[wf] (.funcNative inst (.tf [] []) [.i32] main)) ∗ ↪[frame] emptyFrame }}
      : IProp GF) := by
  iintro Hf Hmain #Hnewstack #Hpush #Hmap Hidf0 Hidf4 Hidf5 Hnsa Hg Ht Ha9 Hmt
  iapply wp_invoke_native_unit_ch _ E idnstart inst [.i32] main emptyFrame
    iprop(g ↦[wg] (⟨.mut, valueOfInt (-1)⟩ : Global))
    (fun f1 => iprop(∃ k, ⌜f1 = ⟨[valueOfUint k], inst⟩⌝ ∗
      isStack k [Wasm.Int.intOfZ 6 * Wasm.Int.intOfZ 6, Wasm.Int.intOfZ 4 * Wasm.Int.intOfZ 4] ∗
      g ↦[wg] (⟨.mut, vg⟩ : Global) ∗
      idt ↦[wt][ 0 ] (some a9) ∗
      idf5 ↦[wf] (.funcNative istack (.tf [.i32, .i32] []) l5 f5)))
    _ _ _ _ $$ Hf Hmain
  iintro Hf
  generalize hf : (⟨nZeros [.i32], inst⟩ : Frame) = f
  have hfinst : f.inst = inst := by subst hf; rfl
  have hflocs : f.locs = nZeros [.i32] := by subst hf; rfl
  rw [← hfinst] at hf0
  -- call new_stack
  rw [show toEList main = ([.basic (.call 0)] : Expr) ++ toEList (main.drop 1) from rfl]
  iapply wp_seq _ _ _ (fun v => iprop((((⌜v = .immV [valueOfInt (-1)]⌝ ∗ nextStackAddrIs 0) ∨
      (∃ k, ⌜v = .immV [valueOfUint k]⌝ ∗ ⌜0 ≤ k ∧ k ≤ ffff0000⌝ ∗ isStack k [] ∗
        nextStackAddrIs (0 + pageSize))) ∗
      idf0 ↦[wf] (.funcNative istack (.tf [] [.i32]) l0 f0)) ∗ ↪[frame] f))
  isplitr
  · iintro ⟨⟨(⟨%H, -⟩ | ⟨%k, %H, -⟩), -⟩, -⟩ <;> cases H
  isplitl [Hf Hidf0 Hnsa]
  · iapply wp_call _ _ _ f 0 idf0 hf0 $$ Hf
    inext; iintro Hf
    iunfold spec0NewStack at Hnewstack
    iapply Hnewstack $$ %f %0 [Hf Hidf0 Hnsa]
    · iframe
      ipureintro
      refine ⟨by decide, by decide, Nat.dvd_zero _⟩
    iintro %v ⟨Hres, Hidf, Hf⟩
    iframe
  iintro %w ⟨⟨Hres, -⟩, Hf⟩
  ihave %Hw : ⌜∃ k', w = .immV [.int32 k']⌝ $$ [Hres]
  · icases Hres with (⟨%H, -⟩ | ⟨%r, %H, -⟩) <;> ipureintro <;> exact ⟨_, H⟩
  obtain ⟨k', rfl⟩ := Hw
  -- tee_local
  rw [show ofVal (.immV [.int32 k']) ++ toEList (main.drop 1) =
    ([.basic (.const (.int32 k')), .basic (.teeLocal 0)] : Expr) ++ toEList (main.drop 2) from rfl]
  iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV [.int32 k']⌝ ∗
    ↪[frame] (⟨f.locs.set 0 (.int32 k'), f.inst⟩ : Frame)))
  isplitr
  · iintro ⟨%H, -⟩; cases H
  isplitl [Hf]
  · iapply wp_tee_local _ _ _ _ _ f $$ Hf
    inext; iintro Hf
    iapply wp_val
    isplitr
    · iintro ⟨%H, -⟩; cases H
    iapply wp_wand_s $$ [Hf]
    · iapply wp_set_local _ _ _ 0 (fun w => iprop(⌜w = .immV []⌝)) f (by simp [hflocs, nZeros])
        $$ [] Hf
      inext; ipureintro; rfl
    iintro %w ⟨%Hw, Hf⟩
    subst Hw
    iframe
    ipureintro; rfl
  iintro %w ⟨%Hw, Hf⟩
  subst Hw
  -- relop
  rw [show ofVal (.immV [.int32 k']) ++ toEList (main.drop 2) =
    ([.basic (.const (.int32 k')), .basic (.const (.int32 (Wasm.Int.intOfZ (-1)))),
      .basic (.relop .i32 (.i .eq))] : Expr) ++ toEList (main.drop 4) from rfl]
  iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV [.int32 (wasmBool
      (appRelop (.i .eq) (.int32 k') (.int32 (Wasm.Int.intOfZ (-1)))))]⌝ ∗
    ↪[frame] (⟨f.locs.set 0 (.int32 k'), f.inst⟩ : Frame)))
  isplitr
  · iintro ⟨%H, -⟩; cases H
  isplitl [Hf]
  · iapply wp_relop rfl $$ Hf
    inext; ipureintro; rfl
  iintro %w ⟨%Hw, Hf⟩
  subst Hw
  generalize hf1 : (⟨f.locs.set 0 (.int32 k'), f.inst⟩ : Frame) = f1
  have hinst : f1.inst = inst := by subst hf1; exact hfinst
  rw [← hinst] at hf4 hf5 hf7 hg
  rw [show ∀ c : I32, ofVal (.immV [.int32 c]) ++ toEList (main.drop 4) =
    ([.basic (.const (.int32 c)), .basic (.if_ (.tf [] [])
      [i32const (-1), .setGlobal 0, .return_] [])] : Expr) ++
      toEList (main.drop 5) from fun _ => rfl]
  icases Hres with (⟨%Heq, -⟩ | ⟨%r, %Heq, %Hle, Hst, -⟩)
  · -- new stack failed: set the global to -1 and return
    simp only [valueOfInt, Val.immV.injEq, List.cons.injEq, Value.int32.injEq, _root_.and_true]
      at Heq
    subst Heq
    iapply wp_seq _ _ _ (fun w => iprop(⌜∃ sh, w = .retV sh⌝ ∗
      g ↦[wg] (⟨.mut, valueOfInt (-1)⟩ : Global) ∗ ↪[frame] f1))
    isplitr
    · iintro ⟨⟨%sh, %H⟩, -⟩; cases H
    isplitl [Hf Hg]
    · iapply wp_if_true (by decide) $$ Hf
      inext; iintro Hf
      rw [show ([.basic (.block (.tf [] []) [i32const (-1), .setGlobal 0, .return_])] : Expr) =
        [] ++ [.basic (.block (.tf [] []) [i32const (-1), .setGlobal 0, .return_])] from rfl]
      iapply wp_block (vs := []) rfl rfl rfl rfl $$ Hf
      inext; iintro Hf
      iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).2
      iapply wp_label_push_nil
      simp only [pushBase]
      iapply wp_label_bind
      rw [show ([] : Expr) ++ toEList [i32const (-1), .setGlobal 0, .return_] =
        ([.basic (.const (valueOfInt (-1))), .basic (.setGlobal 0)] : Expr) ++ [.basic .return_]
          from rfl]
      iapply wp_seq_imm [] iprop(g ↦[wg] (⟨.mut, valueOfInt (-1)⟩ : Global) ∗ ↪[frame] f1)
        $$ [Hf Hg]
      · iapply wp_wand_s $$ [Hf Hg]
        · iapply wp_set_global _ _ (valueOfInt (-1)) f1 0 (fun w => iprop(⌜w = .immV []⌝)) _ g hg
            $$ [] Hf Hg
          inext; ipureintro; rfl
        iintro %w ⟨%Hw, Hg, Hf⟩
        iframe; ipureintro; exact Hw
      iintro ⟨Hg, Hf⟩
      iapply wp_value_of (e := vToEList [] ++ [.basic .return_]) (.retV (.base [] [])) rfl
      unfold wpWasmCtx
      iintro %LI %hLI
      have hLI' : LI = ofVal (.retV (.rec_ [] 0 [] (.base [] []) [])) := by
        simpa [lfilled, lfill, constList, ofVal, sfill, vToEList] using hLI
      subst hLI'
      iapply wp_value_of (.retV (.rec_ [] 0 [] (.base [] []) [])) rfl
      iframe
      ipureintro; exact ⟨_, rfl⟩
    iintro %w ⟨%Hw, Hg, Hf⟩
    obtain ⟨sh, rfl⟩ := Hw
    rw [of_val_ret_app_r]
    iapply wp_value_of (.retV (shAppend sh (toEList (main.drop 5)))) rfl
    iexists f1
    iframe Hf
    ileft
    iframe Hg
    iright; ipureintro; exact ⟨_, rfl⟩
  -- new stack succeeded
  simp only [valueOfUint, Val.immV.injEq, List.cons.injEq, Value.int32.injEq, _root_.and_true]
    at Heq
  subst Heq
  have hne : Wasm.Int.intOfZ (w := 32) (r : _root_.Int) ≠ Wasm.Int.intOfZ (-1) := by
    intro h
    have := congrArg BitVec.toNat h
    simp [Wasm.Int.intOfZ, BitVec.toNat_ofInt] at this
    simp only [ffff0000] at Hle
    omega
  have hloc : f1.locs[0]? = some (.int32 (Wasm.Int.intOfZ (r : _root_.Int))) := by
    subst hf1; simp [hflocs, nZeros]
  have hf1eq : f1 = ⟨[valueOfUint r], inst⟩ := by
    subst hf1; simp [hflocs, nZeros, hfinst, valueOfUint]
  -- if
  iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV []⌝ ∗ ↪[frame] f1))
  isplitr
  · iintro ⟨%H, -⟩; cases H
  isplitl [Hf]
  · iapply wp_if_false (by simp only [wasmBool, appRelop, appRelopI, Wasm.Int.ieq,
      beq_eq_false_iff_ne.2 hne, Bool.false_eq_true, ite_false]) $$ Hf
    inext; iintro Hf
    rw [show ([.basic (.block (.tf [] []) [])] : Expr) = [] ++ [.basic (.block (.tf [] []) [])]
      from rfl]
    iapply wp_block (vs := []) rfl rfl rfl rfl $$ Hf
    inext; iintro Hf
    iapply wp_label_value rfl $$ Hf
    inext; ipureintro; rfl
  iintro %w ⟨%Hw, Hf⟩
  subst Hw
  -- push 4
  rw [show ofVal (.immV []) ++ toEList (main.drop 5) =
    ([.basic (.getLocal 0)] : Expr) ++ toEList (main.drop 6) from rfl]
  iapply wp_seq_imm [.int32 (Wasm.Int.intOfZ (r : _root_.Int))] iprop(↪[frame] f1) $$ [Hf]
  · iapply wp_get_local _ _ _ 0
      (fun w => iprop(⌜w = .immV [.int32 (Wasm.Int.intOfZ (r : _root_.Int))]⌝)) f1 hloc $$ [] Hf
    inext; ipureintro; rfl
  iintro Hf
  rw [show vToEList [.int32 (Wasm.Int.intOfZ (r : _root_.Int))] ++ toEList (main.drop 6) =
    ([.basic (u32const r), .basic (.const (.int32 (Wasm.Int.intOfZ 4)))] ++
      [.basic (.call 4)] : Expr) ++ toEList (main.drop 8) from rfl]
  iapply wp_seq_imm [] iprop(isStack r [Wasm.Int.intOfZ 4] ∗
    idf4 ↦[wf] (.funcNative istack (.tf [.i32, .i32] []) l4 f4) ∗ ↪[frame] f1) $$ [Hf Hidf4 Hst]
  · iapply wp_call_consts f1 _ rfl 4 idf4 hf4 $$ Hf
    inext; iintro Hf
    simp only [List.cons_append, List.nil_append]
    iunfold spec4Push at Hpush
    iapply Hpush $$ %(Wasm.Int.intOfZ 4) %r %([]) %f1 [Hf Hidf4 Hst]
    · iframe; ipureintro; decide
    iintro %w ⟨%Hw, H⟩; iframe; ipureintro; exact Hw
  iintro ⟨Hst, Hidf4, Hf⟩
  -- push 6
  rw [show vToEList [] ++ toEList (main.drop 8) =
    ([.basic (.getLocal 0)] : Expr) ++ toEList (main.drop 9) from rfl]
  iapply wp_seq_imm [.int32 (Wasm.Int.intOfZ (r : _root_.Int))] iprop(↪[frame] f1) $$ [Hf]
  · iapply wp_get_local _ _ _ 0
      (fun w => iprop(⌜w = .immV [.int32 (Wasm.Int.intOfZ (r : _root_.Int))]⌝)) f1 hloc $$ [] Hf
    inext; ipureintro; rfl
  iintro Hf
  rw [show vToEList [.int32 (Wasm.Int.intOfZ (r : _root_.Int))] ++ toEList (main.drop 9) =
    ([.basic (u32const r), .basic (.const (.int32 (Wasm.Int.intOfZ 6)))] ++
      [.basic (.call 4)] : Expr) ++ toEList (main.drop 11) from rfl]
  iapply wp_seq_imm [] iprop(isStack r [Wasm.Int.intOfZ 6, Wasm.Int.intOfZ 4] ∗
    idf4 ↦[wf] (.funcNative istack (.tf [.i32, .i32] []) l4 f4) ∗ ↪[frame] f1) $$ [Hf Hidf4 Hst]
  · iapply wp_call_consts f1 _ rfl 4 idf4 hf4 $$ Hf
    inext; iintro Hf
    simp only [List.cons_append, List.nil_append]
    iunfold spec4Push at Hpush
    iapply Hpush $$ %(Wasm.Int.intOfZ 6) %r %([Wasm.Int.intOfZ 4]) %f1 [Hf Hidf4 Hst]
    · iframe; ipureintro; decide
    iintro %w ⟨%Hw, H⟩; iframe; ipureintro; exact Hw
  iintro ⟨Hst, -, Hf⟩
  -- map square
  rw [show vToEList [] ++ toEList (main.drop 11) =
    ([.basic (.getLocal 0)] : Expr) ++ toEList (main.drop 12) from rfl]
  iapply wp_seq_imm [.int32 (Wasm.Int.intOfZ (r : _root_.Int))] iprop(↪[frame] f1) $$ [Hf]
  · iapply wp_get_local _ _ _ 0
      (fun w => iprop(⌜w = .immV [.int32 (Wasm.Int.intOfZ (r : _root_.Int))]⌝)) f1 hloc $$ [] Hf
    inext; ipureintro; rfl
  iintro Hf
  rw [show vToEList [.int32 (Wasm.Int.intOfZ (r : _root_.Int))] ++ toEList (main.drop 12) =
    ([.basic (u32const r), .basic (.const (.int32 (Wasm.Int.intOfZ 0)))] ++
      [.basic (.call 5)] : Expr) ++ toEList (main.drop 14) from rfl]
  iapply wp_seq_imm [] iprop((∃ s', isStack r s' ∗
      stackAll2 [Wasm.Int.intOfZ 6, Wasm.Int.intOfZ 4] s' (fun u v => iprop(⌜v = u * u⌝))) ∗
    idf5 ↦[wf] (.funcNative istack (.tf [.i32, .i32] []) l5 f5) ∗ ↪[frame] f1 ∗
    idt ↦[wt][ Wasm.Int.natOfUint (Wasm.Int.intOfZ (w := 32) 0) ] (some a9) ∗
    a9 ↦[wf] (.funcNative inst (.tf [.i32] [.i32]) [] square)) $$ [Hf Hidf5 Hst Ht Ha9]
  · iapply wp_call_consts f1 _ rfl 5 idf5 hf5 $$ Hf
    inext; iintro Hf
    simp only [List.cons_append, List.nil_append]
    iunfold spec5StackMap at Hmap
    iapply Hmap $$ %f1 %(Wasm.Int.intOfZ 0) %r %([Wasm.Int.intOfZ 6, Wasm.Int.intOfZ 4])
      %a9 %(.funcNative inst (.tf [.i32] [.i32]) [] square) %(fun _ => iprop(True))
      %(fun u v => iprop(⌜v = u * u⌝)) [Hf Hidf5 Hst Ht Ha9]
    · iframe
      isplitr
      · simp only [stackAll]
        isplitr
        · ipureintro; trivial
        isplitr <;> ipureintro <;> trivial
      isplitl [Ht]
      · rw [show Wasm.Int.natOfUint (Wasm.Int.intOfZ (w := 32) 0) = 0 from rfl]; iexact Ht
      isplitr
      · ipureintro; rfl
      iapply callback_spec E istack inst idt (Wasm.Int.intOfZ 0) a9 square (fun u => u * u)
      · intro u; iintro; ipureintro; rfl
      · intro u; exact wp_square_body E inst u
    iintro %w ⟨%Hw, H⟩; iframe; ipureintro; exact Hw
  iintro ⟨⟨%s', Hst, Hall⟩, Hidf5, Hf, Ht, -⟩
  ihave %Hs' := stackAll2_map (fun u => u * u) (Wasm.Int.intOfZ 6) (Wasm.Int.intOfZ 4) s' $$ Hall
  subst Hs'
  -- host call modify_table
  rw [show vToEList [] ++ toEList (main.drop 14) =
    ([.basic (.const (.int32 (Wasm.Int.intOfZ 0))), .basic (.const (.int32 (Wasm.Int.intOfZ 10)))] ++
      [.basic (.call 7)] : Expr) ++ toEList (main.drop 17) from rfl]
  iapply wp_seq _ _ _ (fun w => iprop(⌜w = .callHostV (.tf [.i32, .i32] []) (.hostfuncidx ha)
      [.int32 (Wasm.Int.intOfZ 0), .int32 (Wasm.Int.intOfZ 10)] (.base [] [])⌝ ∗ ↪[frame] f1))
  isplitr
  · iintro ⟨%H, -⟩; cases H
  isplitl [Hf Hmt]
  · iapply wp_call_consts f1 _ rfl 7 idmodtab hf7 $$ Hf
    inext; iintro Hf
    rw [show ([.basic (.const (.int32 (Wasm.Int.intOfZ 0))),
        .basic (.const (.int32 (Wasm.Int.intOfZ 10)))] : Expr) ++ [.invoke idmodtab] =
      vToEList [.int32 (Wasm.Int.intOfZ 0), .int32 (Wasm.Int.intOfZ 10)] ++ [.invoke idmodtab]
      from rfl]
    iapply wp_invoke_host _ _ _ [.int32 (Wasm.Int.intOfZ 0), .int32 (Wasm.Int.intOfZ 10)] 2
      [.i32, .i32] [] idmodtab (.hostfuncidx ha) f1 _ rfl rfl rfl $$ Hmt Hf
    inext; iintro - Hf
    iapply wp_value_of (e := [.callHost (.tf [.i32, .i32] []) (.hostfuncidx ha)
      [.int32 (Wasm.Int.intOfZ 0), .int32 (Wasm.Int.intOfZ 10)]])
      (.callHostV (.tf [.i32, .i32] []) (.hostfuncidx ha)
        [.int32 (Wasm.Int.intOfZ 0), .int32 (Wasm.Int.intOfZ 10)] (.base [] [])) rfl
    iframe; ipureintro; rfl
  iintro %w ⟨%Hw, Hf⟩
  subst Hw
  rw [show ofVal (.callHostV (.tf [.i32, .i32] []) (.hostfuncidx ha)
      [.int32 (Wasm.Int.intOfZ 0), .int32 (Wasm.Int.intOfZ 10)] (.base [] [])) ++
      toEList (main.drop 17) =
    ofVal (.callHostV (.tf [.i32, .i32] []) (.hostfuncidx ha)
      [.int32 (Wasm.Int.intOfZ 0), .int32 (Wasm.Int.intOfZ 10)] (.base [] (toEList (main.drop 17))))
    by simp [ofVal, llfill]]
  iapply wp_value_of (.callHostV (.tf [.i32, .i32] []) (.hostfuncidx ha)
    [.int32 (Wasm.Int.intOfZ 0), .int32 (Wasm.Int.intOfZ 10)] (.base [] (toEList (main.drop 17))))
    rfl
  iexists f1
  iframe Hf
  iright
  isplitr
  · ipureintro; rfl
  iexists r
  iframe
  isplitr
  · ipureintro; exact hf1eq
  rw [show (0 : Nat) = Wasm.Int.natOfUint (Wasm.Int.intOfZ (w := 32) 0) from rfl]
  iexact Ht

/-- The client's `main` after the host call `modify_table` returned (Coq: second part of the proof
of `instantiate_stack_client_spec`). -/
private theorem main_part2 (E : CoPset) (inst istack : Instance)
    (k idf3 idf5 a10 idt g : Nat) (l3 l5 : List ValueType)
    (f3 f5 : List BasicInstruction) (isStack : Nat → List I32 → IProp GF) (vg : Value)
    (hf3 : inst.funcs[3]? = some idf3) (hf5 : inst.funcs[5]? = some idf5)
    (hg : inst.globs[0]? = some g) :
    ⊢ (↪[frame] (⟨[valueOfUint k], inst⟩ : Frame) -∗
      spec3Pop idf3 istack l3 f3 isStack E -∗
      spec5StackMap idf5 istack l5 f5 isStack idt E -∗
      idf3 ↦[wf] (.funcNative istack (.tf [.i32] [.i32]) l3 f3) -∗
      idf5 ↦[wf] (.funcNative istack (.tf [.i32, .i32] []) l5 f5) -∗
      isStack k [Wasm.Int.intOfZ 6 * Wasm.Int.intOfZ 6, Wasm.Int.intOfZ 4 * Wasm.Int.intOfZ 4] -∗
      g ↦[wg] (⟨.mut, vg⟩ : Global) -∗
      idt ↦[wt][ 0 ] (some a10) -∗
      a10 ↦[wf] (.funcNative inst (.tf [.i32] [.i32]) [] timesTwo) -∗
      WP (toEList (main.drop 17) : Expr) @ E
        {{ w, ⌜w = .immV []⌝ ∗ g ↦[wg] (⟨.mut, valueOfInt 40⟩ : Global) ∗ ∃ f2, ↪[frame] f2 }}
      : IProp GF) := by
  iintro Hf #Hpop #Hmap Hidf3 Hidf5 Hst Hg Ht Ha10
  generalize hf1 : (⟨[valueOfUint k], inst⟩ : Frame) = f1
  have hinst : f1.inst = inst := by subst hf1; rfl
  have hloc : f1.locs[0]? = some (.int32 (Wasm.Int.intOfZ (k : _root_.Int))) := by
    subst hf1; rfl
  rw [← hinst] at hf3 hf5 hg
  -- map timesTwo
  rw [show toEList (main.drop 17) =
    ([.basic (.getLocal 0)] : Expr) ++ toEList (main.drop 18) from rfl]
  iapply wp_seq_imm [.int32 (Wasm.Int.intOfZ (k : _root_.Int))] iprop(↪[frame] f1) $$ [Hf]
  · iapply wp_get_local _ _ _ 0
      (fun w => iprop(⌜w = .immV [.int32 (Wasm.Int.intOfZ (k : _root_.Int))]⌝)) f1 hloc $$ [] Hf
    inext; ipureintro; rfl
  iintro Hf
  rw [show vToEList [.int32 (Wasm.Int.intOfZ (k : _root_.Int))] ++ toEList (main.drop 18) =
    ([.basic (u32const k), .basic (.const (.int32 (Wasm.Int.intOfZ 0)))] ++
      [.basic (.call 5)] : Expr) ++ toEList (main.drop 20) from rfl]
  iapply wp_seq_imm [] iprop((∃ s', isStack k s' ∗
      stackAll2 [Wasm.Int.intOfZ 6 * Wasm.Int.intOfZ 6, Wasm.Int.intOfZ 4 * Wasm.Int.intOfZ 4] s'
        (fun u v => iprop(⌜v = u * Wasm.Int.intOfZ 2⌝))) ∗ ↪[frame] f1) $$ [Hf Hidf5 Hst Ht Ha10]
  · iapply wp_call_consts f1 _ rfl 5 idf5 hf5 $$ Hf
    inext; iintro Hf
    simp only [List.cons_append, List.nil_append]
    iunfold spec5StackMap at Hmap
    iapply Hmap $$ %f1 %(Wasm.Int.intOfZ 0) %k
      %([Wasm.Int.intOfZ 6 * Wasm.Int.intOfZ 6, Wasm.Int.intOfZ 4 * Wasm.Int.intOfZ 4])
      %a10 %(.funcNative inst (.tf [.i32] [.i32]) [] timesTwo) %(fun _ => iprop(True))
      %(fun u v => iprop(⌜v = u * Wasm.Int.intOfZ 2⌝)) [Hf Hidf5 Hst Ht Ha10]
    · iframe
      isplitr
      · simp only [stackAll]
        isplitr
        · ipureintro; trivial
        isplitr <;> ipureintro <;> trivial
      isplitl [Ht]
      · rw [show Wasm.Int.natOfUint (Wasm.Int.intOfZ (w := 32) 0) = 0 from rfl]; iexact Ht
      isplitr
      · ipureintro; rfl
      iapply callback_spec E istack inst idt (Wasm.Int.intOfZ 0) a10 timesTwo
        (fun u => u * Wasm.Int.intOfZ 2)
      · intro u; iintro; ipureintro; rfl
      · intro u; exact wp_times_two_body E inst u
    iintro %w ⟨%Hw, Hs, -, Hf, -⟩; iframe; ipureintro; exact Hw
  iintro ⟨⟨%s', Hst, Hall⟩, Hf⟩
  ihave %Hs' := stackAll2_map (fun u => u * Wasm.Int.intOfZ 2) _ _ s' $$ Hall
  subst Hs'
  -- pop 72
  rw [show vToEList [] ++ toEList (main.drop 20) =
    ([.basic (.getLocal 0)] : Expr) ++ toEList (main.drop 21) from rfl]
  iapply wp_seq_imm [.int32 (Wasm.Int.intOfZ (k : _root_.Int))] iprop(↪[frame] f1) $$ [Hf]
  · iapply wp_get_local _ _ _ 0
      (fun w => iprop(⌜w = .immV [.int32 (Wasm.Int.intOfZ (k : _root_.Int))]⌝)) f1 hloc $$ [] Hf
    inext; ipureintro; rfl
  iintro Hf
  rw [show vToEList [.int32 (Wasm.Int.intOfZ (k : _root_.Int))] ++ toEList (main.drop 21) =
    ([.basic (u32const k)] ++ [.basic (.call 3)] : Expr) ++ toEList (main.drop 22) from rfl]
  iapply wp_seq_imm [.int32 (Wasm.Int.intOfZ 6 * Wasm.Int.intOfZ 6 * Wasm.Int.intOfZ 2)]
    iprop(isStack k [(Wasm.Int.intOfZ 4 * Wasm.Int.intOfZ 4 * Wasm.Int.intOfZ 2)] ∗
      idf3 ↦[wf] (.funcNative istack (.tf [.i32] [.i32]) l3 f3) ∗ ↪[frame] f1) $$ [Hf Hidf3 Hst]
  · iapply wp_call_consts f1 _ rfl 3 idf3 hf3 $$ Hf
    inext; iintro Hf
    simp only [List.cons_append, List.nil_append]
    iunfold spec3Pop at Hpop
    iapply Hpop $$ %_ %k %_ %f1 [Hf Hidf3 Hst]
    · iframe
    iintro %w ⟨%Hw, H⟩; iframe; ipureintro; exact Hw
  iintro ⟨Hst, Hidf3, Hf⟩
  -- pop 32
  rw [show vToEList [.int32 (Wasm.Int.intOfZ 6 * Wasm.Int.intOfZ 6 * Wasm.Int.intOfZ 2)] ++ toEList (main.drop 22) =
    ([.basic (.const (.int32 (Wasm.Int.intOfZ 6 * Wasm.Int.intOfZ 6 * Wasm.Int.intOfZ 2))), .basic (.getLocal 0)] : Expr) ++ toEList (main.drop 23)
    from rfl]
  iapply wp_seq_imm [.int32 (Wasm.Int.intOfZ 6 * Wasm.Int.intOfZ 6 * Wasm.Int.intOfZ 2), .int32 (Wasm.Int.intOfZ (k : _root_.Int))] iprop(↪[frame] f1) $$ [Hf]
  · iapply wp_val_cons_imm (.int32 (Wasm.Int.intOfZ 6 * Wasm.Int.intOfZ 6 * Wasm.Int.intOfZ 2)) [.int32 (Wasm.Int.intOfZ (k : _root_.Int))]
    iapply wp_get_local _ _ _ 0 (fun w => iprop(⌜w = .immV [.int32 (Wasm.Int.intOfZ (k : _root_.Int))]⌝)) f1 hloc $$ [] Hf
    inext; ipureintro; rfl
  iintro Hf
  rw [show vToEList [.int32 (Wasm.Int.intOfZ 6 * Wasm.Int.intOfZ 6 * Wasm.Int.intOfZ 2), .int32 (Wasm.Int.intOfZ (k : _root_.Int))] ++ toEList (main.drop 23) =
    ([.basic (.const (.int32 (Wasm.Int.intOfZ 6 * Wasm.Int.intOfZ 6 * Wasm.Int.intOfZ 2))), .basic (u32const k)] ++ [.basic (.call 3)] : Expr) ++
      toEList (main.drop 24) from rfl]
  iapply wp_seq_imm [.int32 (Wasm.Int.intOfZ 6 * Wasm.Int.intOfZ 6 * Wasm.Int.intOfZ 2), .int32 (Wasm.Int.intOfZ 4 * Wasm.Int.intOfZ 4 * Wasm.Int.intOfZ 2)] iprop(isStack k [] ∗ ↪[frame] f1) $$ [Hf Hidf3 Hst]
  · iapply wp_call_consts f1 _ rfl 3 idf3 hf3 $$ Hf
    inext; iintro Hf
    simp only [List.cons_append, List.nil_append]
    iapply wp_val_cons_imm (.int32 (Wasm.Int.intOfZ 6 * Wasm.Int.intOfZ 6 * Wasm.Int.intOfZ 2)) [.int32 (Wasm.Int.intOfZ 4 * Wasm.Int.intOfZ 4 * Wasm.Int.intOfZ 2)]
    iunfold spec3Pop at Hpop
    iapply Hpop $$ %_ %k %_ %f1 [Hf Hidf3 Hst]
    · iframe
    iintro %w ⟨%Hw, Hst, -, Hf⟩; iframe; ipureintro; exact Hw
  iintro ⟨-, Hf⟩
  -- sub and set the global
  rw [show vToEList [.int32 (Wasm.Int.intOfZ 6 * Wasm.Int.intOfZ 6 * Wasm.Int.intOfZ 2), .int32 (Wasm.Int.intOfZ 4 * Wasm.Int.intOfZ 4 * Wasm.Int.intOfZ 2)] ++ toEList (main.drop 24) =
    ([.basic (.const (.int32 (Wasm.Int.intOfZ 6 * Wasm.Int.intOfZ 6 * Wasm.Int.intOfZ 2))), .basic (.const (.int32 (Wasm.Int.intOfZ 4 * Wasm.Int.intOfZ 4 * Wasm.Int.intOfZ 2))),
      .basic (.binop .i32 (.i .sub))] : Expr) ++ [.basic (.setGlobal 0)] from rfl]
  iapply wp_seq_imm [valueOfInt 40] iprop(↪[frame] f1) $$ [Hf]
  · iapply wp_binop (v := valueOfInt 40) (by decide) $$ Hf
    inext; ipureintro; rfl
  iintro Hf
  rw [show vToEList [valueOfInt 40] ++ [.basic (.setGlobal 0)] =
    ([.basic (.const (valueOfInt 40)), .basic (.setGlobal 0)] : Expr) from rfl]
  iapply wp_wand_s $$ [Hf Hg]
  · iapply wp_set_global _ _ (valueOfInt 40) f1 0 (fun w => iprop(⌜w = .immV []⌝)) _ g hg
      $$ [] Hf Hg
    inext; ipureintro; rfl
  iintro %w ⟨%Hw, Hg, Hf⟩
  iframe
  ipureintro; exact Hw

end Client2_main

section Client2
variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF] [HvisG GF] [HmsG GF] [HasG GF]
  [LogrelNaInvs GF]

attribute [local instance] WasmG.invGS

omit [WasmG hlc GF] [HvisG GF] [HmsG GF] [HasG GF] [LogrelNaInvs GF] in
private theorem nodupKeys_zip (ks : List Nat) (l : List FunctionClosure) (h : ks.Nodup) :
    NoDupKeys (ks.zip l) := by
  induction ks generalizing l with
  | nil => exact .nil
  | cons k ks ih =>
    cases l with
    | nil => exact .nil
    | cons v l =>
      obtain ⟨hk, hks⟩ := List.nodup_cons.1 h
      refine List.nodup_cons.2 ⟨fun hm => hk ?_, ih l hks⟩
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.1 hm
      exact (List.of_mem_zip hab).1

omit [LogrelNaInvs GF] in
/-- `wp_seq_host_nostart` for a first instantiation that returns `immHV []` together with a
resource `R` (Lean helper). -/
private theorem wp_seq_host_nostart_imm (E : CoPset) (Φ : HostVal → IProp GF) (R : IProp GF)
    (v_exps : List Vi) (modi : Nat) (v_imps : List Vimp) (m : Module) (es : List HostE)
    (hstart : m.start = none) :
    ⊢ modi ↪[mods] m -∗
      (modi ↪[mods] m -∗ WP (([.instantiate v_exps modi v_imps], []) : HostExpr)
        @ Stuckness.NotStuck ; E {{ w, ⌜w = .immHV []⌝ ∗ modi ↪[mods] m ∗ R }}) -∗
      (R -∗ modi ↪[mods] m -∗ WP ((es, []) : HostExpr) @ E {{ v, Φ v }}) -∗
      WP ((.instantiate v_exps modi v_imps :: es, []) : HostExpr) @ E {{ v, Φ v }} := by
  iintro Hmod Hes1 Hes2
  iapply wp_seq_host_nostart .NotStuck E Φ (fun w => iprop(⌜w = .immHV []⌝ ∗ R)) v_exps modi
    v_imps m es [] hstart rfl $$ [] Hmod [Hes1] [Hes2]
  · iintro ⟨%H, -⟩; cases H
  · iintro Hmod
    iapply Iris.wp_wand $$ [Hes1 Hmod]
    · iapply Hes1 $$ Hmod
    iintro %w ⟨%Hw, Hmod, HR⟩
    iframe
    ipureintro; exact Hw
  · iintro %w ⟨%Hw, HR⟩ Hmod
    iapply Hes2 $$ HR Hmod

@[rocq_alias iriswasm.stack_with_reentrancy.instantiate_stack_client_spec]
theorem StackWithReentrancy.instantiate_stack_client_spec (_s : Stuckness) (E : CoPset)
    (name : Name) (idmodtab : Nat) (exp_addrs : List Nat) (stack_mod_addr client_mod_addr : Nat)
    (ha_mod_table_addr : Nat) :
    exp_addrs.length = 10 →
    ⊢ (↪[frame] emptyFrame -∗
      stack_mod_addr ↪[mods] stackModule -∗
      client_mod_addr ↪[mods] clientModule -∗
      ownVisPointers (exp_addrs.take 9) -∗
      -- the host import does indeed point to the desired modify_table host-instruction
      exp_addrs.getD 9 0 ↪[vis] ({ name := name, desc := .func (.funcidx idmodtab) } :
        ModuleExport) -∗
      idmodtab ↦[wf] FunctionClosure.funcHost (.tf [.i32, .i32] [])
        (.hostfuncidx ha_mod_table_addr) -∗
      ha_mod_table_addr ↦[ha] HostAction.modifyTable -∗
      WP ((stackInstantiate exp_addrs stack_mod_addr client_mod_addr, []) : HostExpr)
        @ Stuckness.NotStuck ; E
        {{ v, ⌜v = .immHV []⌝ ∗
          ↪[frame] emptyFrame ∗
          stack_mod_addr ↪[mods] stackModule ∗
          client_mod_addr ↪[mods] clientModule ∗
          ∃ (idg : Nat) (name : Name),
            exp_addrs.getD 8 0 ↪[vis] ({ name := name, desc := .global (.globalidx idg) } :
              ModuleExport) ∗
            (idg ↦[wg] ({ mut_ := .mut, val := valueOfInt 40 } : Global) ∨
              idg ↦[wg] ({ mut_ := .mut, val := valueOfInt (-1) } : Global)) }} : IProp GF) := by
  intro hlen
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, rfl⟩ : ∃ e0 e1 e2 e3 e4 e5 e6 e7 e8 e9,
      exp_addrs = [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9] := by
    match exp_addrs, hlen with
    | [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9], _ => exact ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, rfl⟩
  simp only [stackInstantiate, List.take_succ_cons, List.take_zero, List.getD_cons_succ,
    List.getD_cons_zero, List.cons_append, List.nil_append]
  rw [show [e0, e1, e2, e3, e4, e5, e6, e7, e8] = [e0, e1, e2, e3, e4, e5, e6, e7] ++ [e8]
    from rfl]
  unfold ownVisPointers
  iintro Hemptyframe Hmod0 Hmod1 Hvis Hvishost Hwfcallhost Hha
  icases BI.BigSepL.bigSepL_append.1 $$ Hvis with ⟨Hvis, Hvisglob, -⟩
  iapply wp_seq_host_nostart_imm E _ _ _ stack_mod_addr [] stackModule _ rfl $$ Hmod0 [Hvis]
  · iintro Hmod0
    have Hstk := instantiate_stack_spec (GF := GF) .NotStuck E [e0, e1, e2, e3, e4, e5, e6, e7]
      stack_mod_addr rfl
    simp only [stackInstantiatePara] at Hstk
    iapply Hstk $$ Hmod0 [Hvis]
    unfold ownVisPointers; iexact Hvis
  iintro ⟨%idf0, %idf1, %idf2, %idf3, %idf4, %idf5, %idf6, %idt, %nm0, %nm1, %nm2, %nm3, %nm4, %nm5,
    %nm6, %nm7, %f0, %f1, %f2, %f3, %f4, %f5, %f6, %istack, %l0, %l1, %l2, %l3, %l4, %l5, %l6,
    %stacktab, %isStack, %nextStackAddrIs, HimpsH, HimpsW, %Hnodup, %Hfnodup, %Htablen, Hnext,
    #Hspec0, -, -, #Hspec3, #Hspec4, #Hspec5, -, -⟩ Hmod0
  simp only [importResourcesWasmTypecheckSepL2, importResourcesHost, stackInstVis, expts, funcTypes,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  icases HimpsW with ⟨-, ⟨%cl0, Hcl0, %Hcl0⟩, ⟨%cl1, Hcl1, %Hcl1⟩, ⟨%cl2, Hcl2, %Hcl2⟩,
    ⟨%cl3, Hcl3, %Hcl3⟩, ⟨%cl4, Hcl4, %Hcl4⟩, ⟨%cl5, Hcl5, %Hcl5⟩, ⟨%cl6, Hcl6, %Hcl6⟩,
    ⟨%tab0, %tt0, Htab, %Htab0⟩, -⟩
  icases HimpsH with ⟨Hvis0, Hvis1, Hvis2, Hvis3, Hvis4, Hvis5, Hvis6, Hvis7, -⟩
  have hk := nodupKeys_zip _ [FunctionClosure.funcNative istack (.tf [] [.i32]) l0 f0,
       .funcNative istack (.tf [.i32] [.i32]) l1 f1,
       .funcNative istack (.tf [.i32] [.i32]) l2 f2,
       .funcNative istack (.tf [.i32] [.i32]) l3 f3,
       .funcNative istack (.tf [.i32, .i32] []) l4 f4,
       .funcNative istack (.tf [.i32, .i32] []) l5 f5,
       .funcNative istack (.tf [.i32] [.i32]) l6 f6] Hfnodup
  obtain rfl := Option.some.inj ((LawfulPartialMap.get?_ofList_some (k := idf0)
    (v := (.funcNative istack (.tf [] [.i32]) l0 f0 : FunctionClosure)) (by simp) hk).symm.trans Hcl0.1)
  obtain rfl := Option.some.inj ((LawfulPartialMap.get?_ofList_some (k := idf1)
    (v := (.funcNative istack (.tf [.i32] [.i32]) l1 f1 : FunctionClosure)) (by simp) hk).symm.trans Hcl1.1)
  obtain rfl := Option.some.inj ((LawfulPartialMap.get?_ofList_some (k := idf2)
    (v := (.funcNative istack (.tf [.i32] [.i32]) l2 f2 : FunctionClosure)) (by simp) hk).symm.trans Hcl2.1)
  obtain rfl := Option.some.inj ((LawfulPartialMap.get?_ofList_some (k := idf3)
    (v := (.funcNative istack (.tf [.i32] [.i32]) l3 f3 : FunctionClosure)) (by simp) hk).symm.trans Hcl3.1)
  obtain rfl := Option.some.inj ((LawfulPartialMap.get?_ofList_some (k := idf4)
    (v := (.funcNative istack (.tf [.i32, .i32] []) l4 f4 : FunctionClosure)) (by simp) hk).symm.trans Hcl4.1)
  obtain rfl := Option.some.inj ((LawfulPartialMap.get?_ofList_some (k := idf5)
    (v := (.funcNative istack (.tf [.i32, .i32] []) l5 f5 : FunctionClosure)) (by simp) hk).symm.trans Hcl5.1)
  obtain rfl := Option.some.inj ((LawfulPartialMap.get?_ofList_some (k := idf6)
    (v := (.funcNative istack (.tf [.i32] [.i32]) l6 f6 : FunctionClosure)) (by simp) hk).symm.trans Hcl6.1)
  obtain ⟨Htab0, Htt0, Htt0'⟩ := Htab0
  rw [get?_insert_eq rfl] at Htab0
  cases Htab0
  ihave %Hne0 : ⌜idf0 ≠ idmodtab⌝ $$ [Hcl0 Hwfcallhost]
  · iapply @pointsTo_ne GF Nat FunctionClosure NatMap _ WasmG.funcHs _ _ _ _ _ $$ Hcl0 Hwfcallhost
  ihave %Hne1 : ⌜idf1 ≠ idmodtab⌝ $$ [Hcl1 Hwfcallhost]
  · iapply @pointsTo_ne GF Nat FunctionClosure NatMap _ WasmG.funcHs _ _ _ _ _ $$ Hcl1 Hwfcallhost
  ihave %Hne2 : ⌜idf2 ≠ idmodtab⌝ $$ [Hcl2 Hwfcallhost]
  · iapply @pointsTo_ne GF Nat FunctionClosure NatMap _ WasmG.funcHs _ _ _ _ _ $$ Hcl2 Hwfcallhost
  ihave %Hne3 : ⌜idf3 ≠ idmodtab⌝ $$ [Hcl3 Hwfcallhost]
  · iapply @pointsTo_ne GF Nat FunctionClosure NatMap _ WasmG.funcHs _ _ _ _ _ $$ Hcl3 Hwfcallhost
  ihave %Hne4 : ⌜idf4 ≠ idmodtab⌝ $$ [Hcl4 Hwfcallhost]
  · iapply @pointsTo_ne GF Nat FunctionClosure NatMap _ WasmG.funcHs _ _ _ _ _ $$ Hcl4 Hwfcallhost
  ihave %Hne5 : ⌜idf5 ≠ idmodtab⌝ $$ [Hcl5 Hwfcallhost]
  · iapply @pointsTo_ne GF Nat FunctionClosure NatMap _ WasmG.funcHs _ _ _ _ _ $$ Hcl5 Hwfcallhost
  ihave %Hne6 : ⌜idf6 ≠ idmodtab⌝ $$ [Hcl6 Hwfcallhost]
  · iapply @pointsTo_ne GF Nat FunctionClosure NatMap _ WasmG.funcHs _ _ _ _ _ $$ Hcl6 Hwfcallhost
  have hnd8 : [idf0, idf1, idf2, idf3, idf4, idf5, idf6, idmodtab].Nodup := by
    simp at Hfnodup ⊢; grind
  have hk8 := nodupKeys_zip _ [FunctionClosure.funcNative istack (.tf [] [.i32]) l0 f0,
       .funcNative istack (.tf [.i32] [.i32]) l1 f1,
       .funcNative istack (.tf [.i32] [.i32]) l2 f2,
       .funcNative istack (.tf [.i32] [.i32]) l3 f3,
       .funcNative istack (.tf [.i32, .i32] []) l4 f4,
       .funcNative istack (.tf [.i32, .i32] []) l5 f5,
       .funcNative istack (.tf [.i32] [.i32]) l6 f6,
       .funcHost (.tf [.i32, .i32] []) (.hostfuncidx ha_mod_table_addr)] hnd8
  have hvnd : (List.map (·.desc) ([⟨nm0, .func ⟨idf0⟩⟩, ⟨nm1, .func ⟨idf1⟩⟩, ⟨nm2, .func ⟨idf2⟩⟩, ⟨nm3, .func ⟨idf3⟩⟩,
      ⟨nm4, .func ⟨idf4⟩⟩, ⟨nm5, .func ⟨idf5⟩⟩, ⟨nm6, .func ⟨idf6⟩⟩, ⟨nm7, .table ⟨idt⟩⟩,
      ⟨name, .func ⟨idmodtab⟩⟩] : List ModuleExport)).Nodup := by
    simp at hnd8 ⊢; grind
  iapply instantiation_spec_operational_start .NotStuck E client_mod_addr
    [e0, e1, e2, e3, e4, e5, e6, e7, e9] [⟨nm0, .func ⟨idf0⟩⟩, ⟨nm1, .func ⟨idf1⟩⟩, ⟨nm2, .func ⟨idf2⟩⟩, ⟨nm3, .func ⟨idf3⟩⟩,
      ⟨nm4, .func ⟨idf4⟩⟩, ⟨nm5, .func ⟨idf5⟩⟩, ⟨nm6, .func ⟨idf6⟩⟩, ⟨nm7, .table ⟨idt⟩⟩,
      ⟨name, .func ⟨idmodtab⟩⟩] [e8] clientModule
    (expts ++ [.func (.tf [.i32, .i32] [])]) [.glob { mut_ := .mut, t := .i32 }]
    (PartialMap.ofList ([idf0, idf1, idf2, idf3, idf4, idf5, idf6, idmodtab].zip [FunctionClosure.funcNative istack (.tf [] [.i32]) l0 f0,
       .funcNative istack (.tf [.i32] [.i32]) l1 f1,
       .funcNative istack (.tf [.i32] [.i32]) l2 f2,
       .funcNative istack (.tf [.i32] [.i32]) l3 f3,
       .funcNative istack (.tf [.i32, .i32] []) l4 f4,
       .funcNative istack (.tf [.i32, .i32] []) l5 f5,
       .funcNative istack (.tf [.i32] [.i32]) l6 f6,
       .funcHost (.tf [.i32, .i32] []) (.hostfuncidx ha_mod_table_addr)]))
    (insert (∅ : NatMap Tableinst) idt stacktab) ∅ ∅ 8 _ rfl module_typing_client
    module_restrictions_client $$ Hemptyframe
    [Hmod1 Hvis0 Hvis1 Hvis2 Hvis3 Hvis4 Hvis5 Hvis6 Hvis7 Hvishost Hcl0 Hcl1 Hcl2 Hcl3 Hcl4 Hcl5
      Hcl6 Htab Hwfcallhost Hvisglob]
  · unfold instantiationResourcesPre importResourcesHost exportOwnershipHost
      instantiationResourcesPreWasm
    iframe Hmod1
    isplitl [Hvis0 Hvis1 Hvis2 Hvis3 Hvis4 Hvis5 Hvis6 Hvis7 Hvishost]
    · iapply BI.BigSepL2.bigSepL2_cons.2
      iframe
      iapply BI.BigSepL2.bigSepL2_nil.2
      iempintro
    isplitl [Hcl0 Hcl1 Hcl2 Hcl3 Hcl4 Hcl5 Hcl6 Htab Hwfcallhost]
    · isplitl
      · iapply (irwt_nodup_equiv _ _ _ _ _ _ hvnd).2
        simp only [importResourcesWasmTypecheckSepL2, importResourcesWasmDomcheck, expts, funcTypes,
          List.map_cons, List.map_nil, List.cons_append, List.nil_append]
        isplitr
        · ipureintro
          simp only [List.zip_cons_cons, List.zip_nil_left, LawfulPartialMap.ofList_cons,
            LawfulPartialMap.dom_insert_iff]
          simp [PartialMap.ofList, PartialMap.dom, get?_empty, extFuncAddrs,
            extTabAddrs, extMemAddrs, extGlobAddrs, extFuncs, extTabs, extMems, extGlobs]
          refine ⟨fun k => ?_, fun k => ?_⟩ <;> omega
        iapply BI.BigSepL2.bigSepL2_cons.2
        isplitl [Hcl0]
        · iexists _; iframe Hcl0
          ipureintro; exact ⟨LawfulPartialMap.get?_ofList_some (by simp) hk8, rfl⟩
        iapply BI.BigSepL2.bigSepL2_cons.2
        isplitl [Hcl1]
        · iexists _; iframe Hcl1
          ipureintro; exact ⟨LawfulPartialMap.get?_ofList_some (by simp) hk8, rfl⟩
        iapply BI.BigSepL2.bigSepL2_cons.2
        isplitl [Hcl2]
        · iexists _; iframe Hcl2
          ipureintro; exact ⟨LawfulPartialMap.get?_ofList_some (by simp) hk8, rfl⟩
        iapply BI.BigSepL2.bigSepL2_cons.2
        isplitl [Hcl3]
        · iexists _; iframe Hcl3
          ipureintro; exact ⟨LawfulPartialMap.get?_ofList_some (by simp) hk8, rfl⟩
        iapply BI.BigSepL2.bigSepL2_cons.2
        isplitl [Hcl4]
        · iexists _; iframe Hcl4
          ipureintro; exact ⟨LawfulPartialMap.get?_ofList_some (by simp) hk8, rfl⟩
        iapply BI.BigSepL2.bigSepL2_cons.2
        isplitl [Hcl5]
        · iexists _; iframe Hcl5
          ipureintro; exact ⟨LawfulPartialMap.get?_ofList_some (by simp) hk8, rfl⟩
        iapply BI.BigSepL2.bigSepL2_cons.2
        isplitl [Hcl6]
        · iexists _; iframe Hcl6
          ipureintro; exact ⟨LawfulPartialMap.get?_ofList_some (by simp) hk8, rfl⟩
        iapply BI.BigSepL2.bigSepL2_cons.2
        isplitl [Htab]
        · iexists stacktab, tt0; iframe Htab
          ipureintro; exact ⟨get?_insert_eq rfl, Htt0, Htt0'⟩
        iapply BI.BigSepL2.bigSepL2_cons.2
        isplitl [Hwfcallhost]
        · iexists _; iframe Hwfcallhost
          ipureintro; exact ⟨LawfulPartialMap.get?_ofList_some (by simp) hk8, rfl⟩
        iapply BI.BigSepL2.bigSepL2_nil.2
        iempintro
      isplit
      · ipureintro
        intro e he
        simp only [clientModule, List.mem_singleton] at he
        subst he
        simp [assertConst1I32, i32const, extTabs, get?_insert_eq, natOfInt]
        omega
      · ipureintro
        intro d hd
        simp [clientModule] at hd
    isplitl [Hvisglob]
    · iapply BI.BigSepL.bigSepL_singleton.2
      iexact Hvisglob
    ipureintro; rfl
  iintro %idnstart Hf Hpost
  unfold instantiationResourcesPost instantiationResourcesPostWasm
  icases Hpost with ⟨Hmod1, -, %inst, ⟨%g_inits, %tabA, %memA, %globA, %wts', %wms', Himpres,
    %Hinst, %Htab, %Hwts', %-, %Hmem, %Hwms', %-, %Hgv, %Hglob, Hres⟩, Hexp⟩
  obtain ⟨types, funcs, tabs, mems, globs⟩ := inst
  obtain ⟨Htypes, ⟨frest, hfr⟩, ⟨trest, htr⟩, -, -, Hstart⟩ := Hinst
  simp only [extFuncAddrs, extTabAddrs, extFuncs, extTabs, Function.comp, List.map_cons,
    List.map_nil, List.filterMap_cons, List.filterMap_nil] at hfr htr
  subst hfr htr Htab Hmem Hwts' Hwms' Hglob
  dsimp only at Htypes
  subst Htypes
  unfold moduleInstResourcesWasm moduleInstResourcesFunc moduleInstResourcesTab
    moduleInstResourcesMem moduleInstResourcesGlob
  icases Hres with ⟨Hresf, Hrest, Hresm, Hresg⟩
  ihave %Hlf := BI.BigSepL2.bigSepL2_length $$ Hresf
  ihave %Hlt := BI.BigSepL2.bigSepL2_length $$ Hrest
  ihave %Hlm := BI.BigSepL2.bigSepL2_length $$ Hresm
  ihave %Hlg := BI.BigSepL2.bigSepL2_length $$ Hresg
  have hgv : g_inits = [.int32 (Wasm.Int.intOfZ 0)] := Option.some.inj (Hgv.2.symm.trans
    (rfl : moduleGlobInitValue clientModule.globals = some [.int32 (Wasm.Int.intOfZ 0)]))
  subst hgv
  have hbt : moduleInstBuildTables clientModule ⟨clientModule.types,
      [idf0, idf1, idf2, idf3, idf4, idf5, idf6, idmodtab] ++ frest, [idt] ++ trest, mems, globs⟩ =
      [] := rfl
  have hbm : moduleInstBuildMems clientModule ⟨clientModule.types,
      [idf0, idf1, idf2, idf3, idf4, idf5, idf6, idmodtab] ++ frest, [idt] ++ trest, mems, globs⟩ =
      [] := rfl
  have hgifc : getImportFuncCount clientModule = 8 := rfl
  have hgitc : getImportTableCount clientModule = 1 := rfl
  have hgimc : getImportMemCount clientModule = 0 := rfl
  have hgigc : getImportGlobalCount clientModule = 0 := rfl
  simp only [hbt, hbm, hgifc, hgitc, hgimc, hgigc] at Hlf Hlt Hlm Hlg ⊢
  simp only [List.length_append, List.length_cons, List.length_nil, List.drop_append, List.drop_zero, List.length_nil] at Hlf Hlt Hlm Hlg
  obtain ⟨a8, a9, a10, rfl⟩ : ∃ a8 a9 a10, frest = [a8, a9, a10] := by
    match frest, Hlf with
    | [a8, a9, a10], _ => exact ⟨a8, a9, a10, rfl⟩
  obtain rfl : trest = [] := by simpa using Hlt.symm
  obtain rfl : mems = [] := by simpa using Hlm.symm
  obtain ⟨g, rfl⟩ : ∃ g, globs = [g] := by
    match globs, Hlg with
    | [g], _ => exact ⟨g, rfl⟩
  obtain rfl : a8 = idnstart := by simpa [checkStart, clientModule, optionBind] using Hstart
  simp only [List.cons_append, List.nil_append, List.drop_succ_cons, List.drop_zero]
  rw [show clientModule.funcs = [{ type := .typeidx 0, locals := [.i32], body := main },
      { type := .typeidx 2, locals := [], body := square },
      { type := .typeidx 2, locals := [], body := timesTwo }] from rfl,
    show moduleInstGlobalInit (moduleInstBuildGlobals clientModule.globals)
      [Value.int32 (Wasm.Int.intOfZ 0)] = [{ mut_ := .mut, val := .int32 (Wasm.Int.intOfZ 0) }]
      from rfl]
  icases Hresf with ⟨Hmain, Hsq, Hdbl, -⟩
  icases Hresg with ⟨Hg, -⟩
  unfold moduleExportResourcesHost
  rw [show clientModule.exports = [{ name := nameOfString "answer", desc := .global (.globalidx 0) }]
    from rfl]
  icases Hexp with ⟨⟨%nmg, Hexp⟩, -⟩
  ihave Himp := (irwt_nodup_equiv _ _ _ _ _ _ hvnd).1 $$ Himpres
  simp only [importResourcesWasmTypecheckSepL2, expts, funcTypes, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  icases Himp with ⟨-, ⟨%c0, Hc0, %Hc0⟩, -, -, ⟨%c3, Hc3, %Hc3⟩, ⟨%c4, Hc4, %Hc4⟩, ⟨%c5, Hc5, %Hc5⟩, -,
    ⟨%tab1, %tt1, Htab1, %Htab1⟩, ⟨%c7, Hc7, %Hc7⟩, -⟩
  obtain rfl := Option.some.inj ((LawfulPartialMap.get?_ofList_some (k := idf0)
    (v := (.funcNative istack (.tf [] [.i32]) l0 f0 : FunctionClosure)) (by simp) hk8).symm.trans Hc0.1)
  obtain rfl := Option.some.inj ((LawfulPartialMap.get?_ofList_some (k := idf3)
    (v := (.funcNative istack (.tf [.i32] [.i32]) l3 f3 : FunctionClosure)) (by simp) hk8).symm.trans Hc3.1)
  obtain rfl := Option.some.inj ((LawfulPartialMap.get?_ofList_some (k := idf4)
    (v := (.funcNative istack (.tf [.i32, .i32] []) l4 f4 : FunctionClosure)) (by simp) hk8).symm.trans Hc4.1)
  obtain rfl := Option.some.inj ((LawfulPartialMap.get?_ofList_some (k := idf5)
    (v := (.funcNative istack (.tf [.i32, .i32] []) l5 f5 : FunctionClosure)) (by simp) hk8).symm.trans Hc5.1)
  obtain rfl := Option.some.inj ((LawfulPartialMap.get?_ofList_some (k := idmodtab)
    (v := (.funcHost (.tf [.i32, .i32] []) (.hostfuncidx ha_mod_table_addr) : FunctionClosure)) (by simp) hk8).symm.trans Hc7.1)
  obtain ⟨Htab1, -, -⟩ := Htab1
  unfold moduleImportInitTabs at Htab1
  rw [show clientModule.elem = [{ table := .tableidx 0, offset := [i32const 0], init := [.funcidx 9] }]
    from rfl] at Htab1
  simp [hgitc, get?_insert_eq, lookupFuncaddr] at Htab1
  have htab1 : tab1.data[0]? = some (some a9) := by
    subst Htab1
    rw [show assertConst1I32ToNat [i32const 0] = 0 from rfl]
    simp only [tableInitReplaceSingle, List.take_zero, List.nil_append, List.cons_append,
      List.length_cons, List.length_nil]
    cases h : stacktab.data with
    | nil => simp [h] at Htablen
    | cons x xs => simp
  unfold tabBlock
  icases Htab1 with ⟨Hwt, -, -⟩
  ihave Hwt0 := BI.BigSepL.bigSepL_lookup htab1 $$ Hwt
  rw [show clientModule.types.getD 0 (FunctionType.tf [] []) = .tf [] [] from rfl,
    show clientModule.types.getD 2 (FunctionType.tf [] []) = .tf [.i32] [.i32] from rfl,
    show [g].getD 0 0 = g from rfl]
  iapply wp_lift_wasm .NotStuck E [] [.invoke a8]
  iapply wp_wand_s $$ [Hf Hmain Hc0 Hc4 Hc5 Hnext Hg Hwt0 Hsq Hc7]
  · iapply main_part1 E (⟨clientModule.types, [idf0, idf1, idf2, idf3, idf4, idf5, idf6, idmodtab, a8, a9, a10], [idt], [], [g]⟩ : Instance) istack a8 idf0 idf4 idf5 idmodtab a9 idt g
      ha_mod_table_addr l0 l4 l5 f0 f4 f5 isStack nextStackAddrIs (.int32 (Wasm.Int.intOfZ 0))
      rfl rfl rfl rfl rfl $$ Hf Hmain Hspec0 Hspec4 Hspec5 Hc0 Hc4 Hc5 Hnext Hg Hwt0 Hsq Hc7
  iintro %w ⟨⟨Hres, Hmain⟩, Hf⟩
  icases Hres with (⟨%Hw, Hg⟩ | ⟨%f1, %Hw, %k, %Hf1, Hst, Hg, Hwt0, Hc5⟩)
  · subst Hw
    iapply IrisHost.wp_value .NotStuck E _ (.immHV []) _
      (show hostToVal (([], ofVal (Val.immV [])) : HostExpr) = some (.immHV []) from
        IrisHost.to_of_val (.immHV []))
    iframe
    ipureintro; rfl
  subst Hw Hf1
  simp only [ofVal]
  iapply wp_call_host_modify_table .NotStuck E (.hostfuncidx ha_mod_table_addr) ha_mod_table_addr
    (Wasm.Int.intOfZ 0) (Wasm.Int.intOfZ 10) _ _
    (.local [] 0 ⟨[valueOfUint k], (⟨clientModule.types, [idf0, idf1, idf2, idf3, idf4, idf5, idf6, idmodtab, a8, a9, a10], [idt], [], [g]⟩ : Instance)⟩
      (.label [] 0 [] (.base [] (toEList (main.drop 17))) []) [])
    emptyFrame idt (some a9) [] a10 _ rfl rfl rfl rfl rfl
  rw [show Wasm.Int.nOfUint (Wasm.Int.intOfZ (w := 32) 0) = 0 from rfl]
  iframe Hf Hha Hwt0
  inext
  iintro ⟨Hf, Hha, Hwt0⟩
  simp only [llfill, vToEList, List.map_nil, List.nil_append, List.append_nil]
  iapply wp_lift_wasm .NotStuck E []
  iapply wp_wand_s $$ [Hf Hst Hg Hwt0 Hdbl Hc3 Hc5]
  · iapply wp_resume_unit .NotStuck E emptyFrame ⟨[valueOfUint k], (⟨clientModule.types, [idf0, idf1, idf2, idf3, idf4, idf5, idf6, idmodtab, a8, a9, a10], [idt], [], [g]⟩ : Instance)⟩
      (toEList (main.drop 17)) iprop(g ↦[wg] ⟨.mut, valueOfInt 40⟩)
      (by simp [toVal, toValInstr, mergeValuesList, main, toEList]) $$ Hf
    iintro Hf
    iapply main_part2 E (⟨clientModule.types, [idf0, idf1, idf2, idf3, idf4, idf5, idf6, idmodtab, a8, a9, a10], [idt], [], [g]⟩ : Instance) istack k idf3 idf5 a10 idt g l3 l5 f3 f5 isStack
      (.int32 (Wasm.Int.intOfZ 0)) rfl rfl rfl $$ Hf Hspec3 Hspec5 Hc3 Hc5 Hst Hg Hwt0 Hdbl
  iintro %w ⟨⟨%Hw, Hg⟩, Hf⟩
  subst Hw
  iapply IrisHost.wp_value .NotStuck E _ (.immHV []) _
    (show hostToVal (([], ofVal (Val.immV [])) : HostExpr) = some (.immHV []) from
      IrisHost.to_of_val (.immHV []))
  iframe
  ipureintro; rfl

end Client2

end IrisWasm.Examples.Stack
