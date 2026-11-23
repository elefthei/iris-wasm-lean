/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Examples.Stack.StackInstantiation
import IrisWasm.Rules.IrisExampleHelper
import Wasm.ModuleValidation

/-! Port of `theories/iris/examples/stack/stack_client.v`.

Every Coq name of this file is also declared in `stack_with_reentrancy.v`, so the declarations
live in the sub-namespace `IrisWasm.Examples.Stack.StackClient` (aliases
`iriswasm.stack_client.<name>`). -/

namespace IrisWasm.Examples.Stack

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm
open scoped Iris.Std.PartialMap

namespace StackClient

/-- Functions imported from the stack module: 0 new_stack, 1 is_empty, 2 is_full, 3 pop, 4 push,
5 map, 6 length. -/
@[rocq_alias iriswasm.stack_client.main]
def main : List BasicInstruction :=
  [ .call 0,
    .teeLocal 0,
    i32const (-1),
    .relop .i32 (.i .eq),
    -- If new_stack failed, set global v0 to -1 and return
    .if_ (.result none) [i32const (-1), .setGlobal 0, .return_] [],
    .getLocal 0,
    i32const 4,
    .call 4, -- Push 4 onto the stack
    .getLocal 0,
    i32const 6,
    .call 4, -- Push 6 onto the stack
    .getLocal 0,
    i32const 0,
    .call 5, -- Map square onto the stack
    .getLocal 0,
    .call 3, -- Pop 36
    .getLocal 0,
    .call 3, -- Pop 16
    .binop .i32 (.i .sub), -- Subtract those two, to get 20
    .setGlobal 0 ] -- Assign the 0th global the value 20

@[rocq_alias iriswasm.stack_client.square]
def square : List BasicInstruction :=
  [ .getLocal 0,
    .getLocal 0,
    .binop .i32 (.i .mul) ]

@[rocq_alias iriswasm.stack_client.client_module]
def clientModule : Module where
  types := [.tf [] [], .tf [] [.i32], .tf [.i32] [.i32], .tf [.i32, .i32] []]
  funcs := [{ type := .typeidx 0, locals := [.i32], body := main },
            { type := .typeidx 2, locals := [], body := square }]
  tables := []
  mems := []
  globals := [{ type := { mut_ := .mut, t := .i32 }, init := [i32const 0] }]
  elem := [{ table := .tableidx 0, offset := [i32const 0], init := [.funcidx 8] }]
  data := []
  start := some { func := .funcidx 7 }
  imports := [
    { module := nameOfString "Stack", name := nameOfString "new_stack", desc := .func 1 },
    { module := nameOfString "Stack", name := nameOfString "is_empty", desc := .func 2 },
    { module := nameOfString "Stack", name := nameOfString "is_full", desc := .func 2 },
    { module := nameOfString "Stack", name := nameOfString "pop", desc := .func 2 },
    { module := nameOfString "Stack", name := nameOfString "push", desc := .func 3 },
    { module := nameOfString "Stack", name := nameOfString "stack_map", desc := .func 3 },
    { module := nameOfString "Stack", name := nameOfString "stack_length", desc := .func 2 },
    { module := nameOfString "Stack", name := nameOfString "table",
      desc := .table { limits := { min := 1, max := none }, elemType := .funcref } } ]
  exports := [{ name := nameOfString "answer", desc := .global (.globalidx 0) }]

@[rocq_alias iriswasm.stack_client.module_typing_client]
theorem module_typing_client :
    ModuleTyping clientModule expts [.glob { mut_ := .mut, t := .i32 }] := by
  apply (validateModule_iff _ ⟨_, _⟩).mp
  kernel_rfl

@[rocq_alias iriswasm.stack_client.module_restrictions_client]
theorem module_restrictions_client : ModuleRestrictions clientModule :=
  ⟨⟨[.int32 (Wasm.Int.intOfZ 0)], rfl⟩, ⟨[Wasm.Int.intOfZ 0], rfl⟩, ⟨[], rfl⟩⟩

@[rocq_alias iriswasm.stack_client.stack_instantiate]
def stackInstantiate (vis_addrs : List Nat) (stack_mod_addr client_mod_addr : Nat) :
    List HostE :=
  [.instantiate (vis_addrs.take 8) stack_mod_addr [],
   .instantiate (vis_addrs.drop 8) client_mod_addr (vis_addrs.take 8)]

section Helpers
variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF]
attribute [local instance] WasmG.invGS

private theorem wp_value_of {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF} (v : Val)
    {e : Expr} (h : e = ofVal v) : Φ v ⊢ WP e @ s ; E {{ Φ }} := by
  subst h
  exact IrisWp.wp_value (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) ⟨rfl⟩

private theorem wp_wand_s {s : Stuckness} {E : CoPset} {e : Expr} {Φ Ψ : Val → IProp GF} :
    WP e @ s ; E {{ Φ }} ⊢ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s ; E {{ Ψ }} :=
  IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)

/-- `tee_local i` on a value `v`: the value stays on the stack and local `i` becomes `v`. -/
theorem wp_tee_local' (s : Stuckness) (E : CoPset) (v : Value) (i : Nat) (f : Frame)
    (hi : i < f.locs.length) :
    ⊢ (↪[frame] f -∗ WP ([.basic (.const v), .basic (.teeLocal i)] : Expr) @ s ; E
      {{ w, ⌜w = .immV [v]⌝ ∗ ↪[frame] (⟨f.locs.set i v, f.inst⟩ : Frame) }} : IProp GF) := by
  iintro Hf
  iapply wp_tee_local $$ Hf
  inext; iintro Hf
  rw [show ([.basic (.const v), .basic (.const v), .basic (.setLocal i)] : Expr) =
    vToEList [v] ++ [.basic (.const v), .basic (.setLocal i)] from rfl]
  iapply wp_val_app' _ _ _ [v]
  isplitr
  · imodintro; iintro ⟨%h, -⟩; cases h
  iapply wp_wand_s $$ [Hf]
  · iapply wp_set_local _ _ v i (fun w => iprop(⌜w = .immV []⌝)) f hi $$ [] Hf
    inext; ipureintro; rfl
  iintro %w ⟨%hw, Hf⟩
  subst hw
  iframe; ipureintro; rfl


private theorem wp_val_app1 {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF} (c : Value)
    (es : Expr) :
    iprop((□ (¬ Φ .trapV)) ∗
      WP es @ Stuckness.NotStuck ; E {{ v, Φ (valCombine (.immV [c]) v) }})
      ⊢ WP ([.basic (.const c)] ++ es) @ s ; E {{ v, Φ v }} :=
  wp_val_app' s E Φ [c] es

/-- The body of `square` (local 0 holds `u`). -/
private theorem square_body_spec (E : CoPset) (u : I32) (f : Frame)
    (hf : f.locs[0]? = some (.int32 u)) :
    ⊢ (↪[frame] f -∗ WP (toEList square : Expr) @ Stuckness.NotStuck ; E
      {{ w, ⌜w = .immV [.int32 (Wasm.Int.imul u u)]⌝ ∗ ∃ f1, ↪[frame] f1 }} : IProp GF) := by
  iintro Hf
  simp only [square, toEList, List.map]
  take_drop_app_rewrite 1
  iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV [.int32 u]⌝ ∗ ↪[frame] f))
  isplitr
  · iintro ⟨%h, -⟩; cases h
  isplitl [Hf]
  · iapply wp_get_local _ _ _ _ (fun w => iprop(⌜w = .immV [.int32 u]⌝)) _ hf $$ [] Hf
    inext; ipureintro; rfl
  iintro %w ⟨%hw, Hf⟩
  subst hw
  simp only [ofVal, vToEList, List.map, List.cons_append, List.nil_append]
  take_drop_app_rewrite 2
  iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV [.int32 u, .int32 u]⌝ ∗ ↪[frame] f))
  isplitr
  · iintro ⟨%h, -⟩; cases h
  isplitl [Hf]
  · take_drop_app_rewrite 1
    iapply wp_val_app1
    isplitr
    · iintro !> ⟨%h, -⟩; cases h
    iapply wp_get_local _ _ _ _ (fun w => iprop(⌜valCombine (.immV [.int32 u]) w =
      .immV [.int32 u, .int32 u]⌝)) _ hf $$ [] Hf
    inext; ipureintro; rfl
  iintro %w ⟨%hw, Hf⟩
  subst hw
  simp only [ofVal, vToEList, List.map, List.cons_append, List.nil_append]
  iapply wp_wand_s $$ [Hf]
  · iapply wp_binop (Φ := fun w => iprop(⌜w = .immV [.int32 (Wasm.Int.imul u u)]⌝))
      rfl rfl .i32Agree rfl $$ Hf
    inext; ipureintro; rfl
  iintro %w ⟨%hw, Hf⟩
  iframe; ipureintro; exact hw

/-- The spec of the `square` closure, in the shape required by `spec5StackMap`. -/
private theorem square_spec (E : CoPset) (i5 inst : Instance) (a j0 j : Nat) :
    ⊢ (∀ (u : I32) (fc : Frame),
        {{{{ iprop(True) ∗ ⌜i5 = fc.inst⌝ ∗ ↪[frame] fc ∗
            j0 ↦[wt][ j ] (some a) ∗
            a ↦[wf] (.funcNative inst (.tf [.i32] [.i32]) [] square) }}}}
          ([.basic (.const (.int32 u)), .invoke a] : Expr) @ E
          {{{{ w, (∃ v, ⌜w = .immV [.int32 v]⌝ ∗ ⌜v = Wasm.Int.imul u u⌝) ∗
              ↪[frame] fc ∗ j0 ↦[wt][ j ] (some a) ∗
              a ↦[wf] (.funcNative inst (.tf [.i32] [.i32]) [] square) }}}} : IProp GF) := by
  iintro %u %fc !> %Φ ⟨-, -, Hf, Ht, Ha⟩ HΦ
  rw [show ([.basic (.const (.int32 u)), .invoke a] : Expr) = vToEList [.int32 u] ++ [.invoke a]
    from rfl]
  iapply wp_wand_s $$ [Hf Ha]
  · iapply wp_invoke_native_frame .NotStuck E a inst [.i32] [.i32] [] square [.int32 u] fc
      (fun w => iprop(⌜w = .immV [.int32 (Wasm.Int.imul u u)]⌝)) rfl ?_ $$ Hf Ha
    · intro w; iintro %h; ipureintro; subst h; simp
    iintro Hf
    iapply square_body_spec E u _ rfl $$ Hf
  iintro %w ⟨⟨%hw, Ha⟩, Hf⟩
  iapply HΦ
  iframe
  iexists _
  ipureintro; exact ⟨hw, rfl⟩


private theorem stackAll2_square (s s' : List I32) :
    stackAll2 (GF := GF) s s' (fun u v => iprop(⌜v = Wasm.Int.imul u u⌝)) ⊢
      ⌜s' = s.map (fun u => Wasm.Int.imul u u)⌝ := by
  induction s generalizing s' with
  | nil =>
    cases s' with
    | nil => iintro -; ipureintro; rfl
    | cons => simp only [stackAll2]; iintro H; iexfalso; iexact H
  | cons a s ih =>
    cases s' with
    | nil => simp only [stackAll2]; iintro H; iexfalso; iexact H
    | cons b s' =>
      simp only [stackAll2]
      iintro ⟨%h, H⟩
      ihave %h' := ih s' $$ H
      ipureintro; simp [h, h']

private theorem relop_eq_m1 (k : Nat) (hk : k ≤ ffff0000) :
    appRelop (.i .eq) (valueOfUint k) (.int32 (Wasm.Int.intOfZ (-1))) = false := by
  simp only [appRelop, appRelopI, valueOfUint, Wasm.Int.ieq, Wasm.Int.intOfZ, Wasm.Int.repr,
    BitVec.ofInt_natCast, beq_eq_false_iff_ne, ne_eq]
  intro h
  have := congrArg BitVec.toNat h
  simp at this
  unfold ffff0000 at hk
  omega

private theorem sub_squares :
    appBinop (.i .sub) (.int32 (Wasm.Int.imul (Wasm.Int.intOfZ 6) (Wasm.Int.intOfZ 6))) (.int32 (Wasm.Int.imul (Wasm.Int.intOfZ 4) (Wasm.Int.intOfZ 4))) = some (.int32 (Wasm.Int.intOfZ 20)) := by
  decide

private theorem main_spec (E : CoPset) (inst i0 : Instance) (idf0 idf3 idf4 idf5 fsq g idt : Nat)
    (l0 l3 l4 l5 : List ValueType) (b0 b3 b4 b5 : List BasicInstruction)
    (isStack : Nat → List I32 → IProp GF) (nextStackAddrIs : Nat → IProp GF) (vg : Value)
    (hf0 : inst.funcs[0]? = some idf0) (hf3 : inst.funcs[3]? = some idf3)
    (hf4 : inst.funcs[4]? = some idf4) (hf5 : inst.funcs[5]? = some idf5)
    (hg : inst.globs[0]? = some g) :
    ⊢ (↪[frame] (⟨nZeros [.i32], inst⟩ : Frame) -∗
      g ↦[wg] ({ mut_ := .mut, val := vg } : Global) -∗
      idt ↦[wt][ 0 ] (some fsq) -∗
      fsq ↦[wf] (.funcNative inst (.tf [.i32] [.i32]) [] square) -∗
      idf0 ↦[wf] (.funcNative i0 (.tf [] [.i32]) l0 b0) -∗
      idf3 ↦[wf] (.funcNative i0 (.tf [.i32] [.i32]) l3 b3) -∗
      idf4 ↦[wf] (.funcNative i0 (.tf [.i32, .i32] []) l4 b4) -∗
      idf5 ↦[wf] (.funcNative i0 (.tf [.i32, .i32] []) l5 b5) -∗
      nextStackAddrIs 0 -∗
      spec0NewStack idf0 i0 l0 b0 isStack nextStackAddrIs E -∗
      spec3Pop idf3 i0 l3 b3 isStack E -∗
      spec4Push idf4 i0 l4 b4 isStack E -∗
      spec5StackMap idf5 i0 l5 b5 isStack idt E -∗
      WP (toEList main : Expr) @ Stuckness.NotStuck ; E
        {{ w, (⌜w = .immV []⌝ ∨ ⌜∃ sh, w = .retV sh⌝) ∗
          (g ↦[wg] ({ mut_ := .mut, val := valueOfInt 20 } : Global) ∨
            g ↦[wg] ({ mut_ := .mut, val := valueOfInt (-1) } : Global)) ∗
          ∃ f1, ↪[frame] f1 }} : IProp GF) := by
  unfold spec0NewStack spec3Pop spec4Push spec5StackMap
  simp only [valueOfInt]
  iintro Hf Hg Ht Hsq H0 H3 H4 H5 Hnext #Hs0 #Hs3 #Hs4 #Hs5
  simp only [main, toEList, List.map, i32const]
  take_drop_app_rewrite 1
  iapply wp_seq _ _ _ (fun w => iprop((⌜w = .immV [(.int32 (Wasm.Int.intOfZ (-1)) : Value)]⌝ ∨
      (∃ k, ⌜w = .immV [valueOfUint k]⌝ ∗ ⌜k ≤ ffff0000⌝ ∗ isStack k [])) ∗
    ↪[frame] (⟨nZeros [.i32], inst⟩ : Frame)))
  isplitr
  · iintro ⟨(%h | ⟨%k, %h, -⟩), -⟩ <;> cases h
  isplitl [Hf H0 Hnext]
  · rw [show ([.basic (.call 0)] : Expr) = vToEList [] ++ [.basic (.call 0)] from rfl]
    iapply wp_call_vals _ _ _ _ 0 idf0 [] hf0 $$ Hf
    inext; iintro Hf
    simp only [vToEList, List.map_nil, List.nil_append]
    iapply Hs0 $$ %_ %0 [Hf H0 Hnext]
    · iframe; ipureintro; refine ⟨?_, ?_, ?_⟩
      · decide
      · decide
      · exact Nat.dvd_zero _
    iintro %w ⟨Hw, -, Hf⟩
    iframe
    icases Hw with (⟨%hw, -⟩ | ⟨%k, %hw, %hk, Hs, -⟩)
    · ileft; ipureintro; exact hw
    · iright; iexists k; iframe; ipureintro; exact ⟨hw, hk.2⟩
  iintro %w ⟨Hw, Hf⟩
  icases Hw with (%hw | ⟨%k, %hw, %hk, Hs⟩)
  · subst hw
    simp only [ofVal, vToEList, List.map, List.cons_append, List.nil_append]
    take_drop_app_rewrite 2
    iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV [(.int32 (Wasm.Int.intOfZ (-1)) : Value)]⌝ ∗
      ↪[frame] (⟨(nZeros [.i32]).set 0 ((.int32 (Wasm.Int.intOfZ (-1)) : Value)), inst⟩ : Frame)))
    isplitr
    · iintro ⟨%h, -⟩; cases h
    isplitl [Hf]
    · iapply wp_tee_local' _ _ _ 0 ⟨nZeros [.i32], inst⟩ (by simp [nZeros]) $$ Hf
    iintro %w ⟨%hw, Hf⟩
    subst hw
    simp only [ofVal, vToEList, List.map, List.cons_append, List.nil_append]
    take_drop_app_rewrite 3
    iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV [.int32 (wasmBool true)]⌝ ∗
      ↪[frame] (⟨(nZeros [.i32]).set 0 ((.int32 (Wasm.Int.intOfZ (-1)) : Value)), inst⟩ : Frame)))
    isplitr
    · iintro ⟨%h, -⟩; cases h
    isplitl [Hf]
    · iapply wp_relop (Φ := fun w => iprop(⌜w = .immV [.int32 (wasmBool true)]⌝))
        rfl rfl .i32Agree rfl $$ Hf
      inext; ipureintro; rfl
    iintro %w ⟨%hw, Hf⟩
    subst hw
    simp only [ofVal, vToEList, List.map, List.cons_append, List.nil_append]
    take_drop_app_rewrite 2
    iapply wp_seq _ _ _ (fun w => iprop((⌜(∃ sh, w = Val.retV sh : Prop)⌝ ∗
      g ↦[wg] ({ mut_ := .mut, val := (.int32 (Wasm.Int.intOfZ (-1)) : Value) } : Global)) ∗
      ↪[frame] (⟨(nZeros [.i32]).set 0 ((.int32 (Wasm.Int.intOfZ (-1)) : Value)), inst⟩ : Frame)))
    isplitr
    · iintro ⟨⟨⟨%sh, %h⟩, -⟩, -⟩; cases h
    isplitl [Hf Hg]
    · iapply wp_if_true (c := wasmBool true) (Φ := fun w => iprop((⌜∃ sh, w = Val.retV sh⌝ ∗
        g ↦[wg] ({ mut_ := .mut, val := (.int32 (Wasm.Int.intOfZ (-1)) : Value) } : Global)) ∗
        ↪[frame] (⟨(nZeros [.i32]).set 0 ((.int32 (Wasm.Int.intOfZ (-1)) : Value)), inst⟩ : Frame))) (by decide) $$ Hf
      inext; iintro Hf
      rw [← List.nil_append [AdministrativeInstruction.basic (.block (.result none) _)]]
      iapply wp_block (bt := .result none) (n := 0) (t1s := []) rfl rfl rfl rfl rfl $$ Hf
      inext; iintro Hf
      iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).2
      iapply wp_label_push_nil
      simp only [pushBase]
      iapply wp_label_bind
      simp only [toEList, List.map, List.nil_append]
      rw [show ([.basic (.const (.int32 (Wasm.Int.intOfZ (-1)))), .basic (.setGlobal 0),
        .basic .return_] : Expr) = [.basic (.const (.int32 (Wasm.Int.intOfZ (-1)))),
        .basic (.setGlobal 0)] ++ [.basic .return_] from rfl]
      iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV []⌝ ∗
        g ↦[wg] ({ mut_ := .mut, val := (.int32 (Wasm.Int.intOfZ (-1)) : Value) } : Global) ∗
        ↪[frame] (⟨(nZeros [.i32]).set 0 ((.int32 (Wasm.Int.intOfZ (-1)) : Value)), inst⟩ : Frame)))
      isplitr
      · iintro ⟨%h, -⟩; cases h
      isplitl [Hf Hg]
      · iapply wp_wand_s $$ [Hf Hg]
        · iapply wp_set_global _ _ (.int32 (Wasm.Int.intOfZ (-1))) _ 0
            (fun w => iprop(⌜w = .immV []⌝)) _ g hg $$ [] Hf Hg
          inext; ipureintro; rfl
        iintro %w ⟨%hw, Hg, Hf⟩
        iframe; ipureintro; exact hw
      iintro %w ⟨%hw, Hg, Hf⟩
      subst hw
      iapply wp_value_of (e := ofVal (Val.immV []) ++ [AdministrativeInstruction.basic .return_])
        (.retV (.base [] [])) rfl
      unfold wpWasmCtx
      iintro %LI %hLI
      have hLI' : LI = ofVal (.retV (.rec_ [] 0 [] (.base [] []) [])) := by
        simpa [lfilled, lfill, constList, ofVal, sfill, vToEList] using hLI
      subst hLI'
      iapply wp_value_of _ rfl
      iframe
      ipureintro; exact ⟨_, rfl⟩
    iintro %w ⟨⟨%hw, Hg⟩, Hf⟩
    obtain ⟨sh, rfl⟩ := hw
    iapply wp_value_of _ (of_to_val _ _ (extend_retV sh _)).symm
    isplitr
    · iright; ipureintro; exact ⟨_, rfl⟩
    isplitl [Hg]
    · iright; iexact Hg
    iexists _; iexact Hf
  · subst hw
    simp only [ofVal, vToEList, List.map, List.cons_append, List.nil_append]
    take_drop_app_rewrite 2
    iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV [valueOfUint k]⌝ ∗
      ↪[frame] (⟨(nZeros [.i32]).set 0 (valueOfUint k), inst⟩ : Frame)))
    isplitr
    · iintro ⟨%h, -⟩; cases h
    isplitl [Hf]
    · iapply wp_tee_local' _ _ _ 0 ⟨nZeros [.i32], inst⟩ (by simp [nZeros]) $$ Hf
    iintro %w ⟨%hw, Hf⟩
    subst hw
    generalize hF : (⟨(nZeros [.i32]).set 0 (valueOfUint k), inst⟩ : Frame) = F
    have hF0 : F.locs[0]? = some (valueOfUint k) := by subst hF; rfl
    have hFi : F.inst = inst := by subst hF; rfl
    simp only [ofVal, vToEList, List.map, List.cons_append, List.nil_append]
    take_drop_app_rewrite 3
    iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV [.int32 (wasmBool false)]⌝ ∗ ↪[frame] F))
    isplitr
    · iintro ⟨%h, -⟩; cases h
    isplitl [Hf]
    · iapply wp_relop (Φ := fun w => iprop(⌜w = .immV [.int32 (wasmBool false)]⌝))
        rfl rfl .i32Agree (relop_eq_m1 k hk) $$ Hf
      inext; ipureintro; rfl
    iintro %w ⟨%hw, Hf⟩
    subst hw
    simp only [ofVal, vToEList, List.map, List.cons_append, List.nil_append]
    take_drop_app_rewrite 2
    iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV []⌝ ∗ ↪[frame] F))
    isplitr
    · iintro ⟨%h, -⟩; cases h
    isplitl [Hf]
    · iapply wp_if_false (c := wasmBool false) rfl $$ Hf
      inext; iintro Hf
      rw [← List.nil_append [AdministrativeInstruction.basic (.block (.result none) [])]]
      iapply wp_block (bt := .result none) (n := 0) (t1s := []) rfl rfl rfl rfl rfl $$ Hf
      inext; iintro Hf
      iapply wp_label_value (v := []) rfl $$ Hf
      inext; ipureintro; rfl
    iintro %w ⟨%hw, Hf⟩
    subst hw
    simp only [ofVal, vToEList, List.map, List.nil_append]
    -- push 4
    take_drop_app_rewrite 1
    iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV [valueOfUint k]⌝ ∗ ↪[frame] F))
    isplitr
    · iintro ⟨%h, -⟩; cases h
    isplitl [Hf]
    · iapply wp_get_local _ _ _ _ (fun w => iprop(⌜w = .immV [valueOfUint k]⌝)) F hF0 $$ [] Hf
      inext; ipureintro; rfl
    iintro %w ⟨%hw, Hf⟩
    subst hw
    simp only [ofVal, vToEList, List.map, List.cons_append, List.nil_append]
    take_drop_app_rewrite 3
    iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV []⌝ ∗ isStack k [Wasm.Int.intOfZ 4] ∗
      idf4 ↦[wf] (.funcNative i0 (.tf [.i32, .i32] []) l4 b4) ∗ ↪[frame] F))
    isplitr
    · iintro ⟨%h, -⟩; cases h
    isplitl [Hf H4 Hs]
    · rw [show ([.basic (.const (valueOfUint k)), .basic (.const (.int32 (Wasm.Int.intOfZ 4))),
        .basic (.call 4)] : Expr) = vToEList [valueOfUint k, .int32 (Wasm.Int.intOfZ 4)] ++
        [.basic (.call 4)] from rfl]
      iapply wp_call_vals _ _ _ _ 4 idf4 _ (hFi ▸ hf4) $$ Hf
      inext; iintro Hf
      rw [show (vToEList [valueOfUint k, .int32 (Wasm.Int.intOfZ 4)] ++ [.invoke idf4] : Expr) =
        [.basic (u32const k), .basic (.const (.int32 (Wasm.Int.intOfZ 4))), .invoke idf4] from rfl]
      iapply Hs4 $$ %(Wasm.Int.intOfZ 4) %k %([] : List I32) %F [Hf H4 Hs]
      · iframe; ipureintro; decide
      iintro %w ⟨%hw, Hs, H4, Hf⟩
      iframe; ipureintro; exact hw
    iintro %w ⟨%hw, Hs, H4, Hf⟩
    subst hw
    simp only [ofVal, vToEList, List.map, List.nil_append]
    -- push 6
    take_drop_app_rewrite 1
    iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV [valueOfUint k]⌝ ∗ ↪[frame] F))
    isplitr
    · iintro ⟨%h, -⟩; cases h
    isplitl [Hf]
    · iapply wp_get_local _ _ _ _ (fun w => iprop(⌜w = .immV [valueOfUint k]⌝)) F hF0 $$ [] Hf
      inext; ipureintro; rfl
    iintro %w ⟨%hw, Hf⟩
    subst hw
    simp only [ofVal, vToEList, List.map, List.cons_append, List.nil_append]
    take_drop_app_rewrite 3
    iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV []⌝ ∗
      isStack k [Wasm.Int.intOfZ 6, Wasm.Int.intOfZ 4] ∗ ↪[frame] F))
    isplitr
    · iintro ⟨%h, -⟩; cases h
    isplitl [Hf H4 Hs]
    · rw [show ([.basic (.const (valueOfUint k)), .basic (.const (.int32 (Wasm.Int.intOfZ 6))),
        .basic (.call 4)] : Expr) = vToEList [valueOfUint k, .int32 (Wasm.Int.intOfZ 6)] ++
        [.basic (.call 4)] from rfl]
      iapply wp_call_vals _ _ _ _ 4 idf4 _ (hFi ▸ hf4) $$ Hf
      inext; iintro Hf
      rw [show (vToEList [valueOfUint k, .int32 (Wasm.Int.intOfZ 6)] ++ [.invoke idf4] : Expr) =
        [.basic (u32const k), .basic (.const (.int32 (Wasm.Int.intOfZ 6))), .invoke idf4] from rfl]
      iapply Hs4 $$ %(Wasm.Int.intOfZ 6) %k %([Wasm.Int.intOfZ 4] : List I32) %F [Hf H4 Hs]
      · iframe; ipureintro; decide
      iintro %w ⟨%hw, Hs, -, Hf⟩
      iframe; ipureintro; exact hw
    iintro %w ⟨%hw, Hs, Hf⟩
    subst hw
    simp only [ofVal, vToEList, List.map, List.nil_append]
    -- map square
    take_drop_app_rewrite 1
    iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV [valueOfUint k]⌝ ∗ ↪[frame] F))
    isplitr
    · iintro ⟨%h, -⟩; cases h
    isplitl [Hf]
    · iapply wp_get_local _ _ _ _ (fun w => iprop(⌜w = .immV [valueOfUint k]⌝)) F hF0 $$ [] Hf
      inext; ipureintro; rfl
    iintro %w ⟨%hw, Hf⟩
    subst hw
    simp only [ofVal, vToEList, List.map, List.cons_append, List.nil_append]
    take_drop_app_rewrite 3
    iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV []⌝ ∗
      isStack k [Wasm.Int.imul (Wasm.Int.intOfZ 6) (Wasm.Int.intOfZ 6),
        Wasm.Int.imul (Wasm.Int.intOfZ 4) (Wasm.Int.intOfZ 4)] ∗ ↪[frame] F))
    isplitr
    · iintro ⟨%h, -⟩; cases h
    isplitl [Hf H5 Hs Ht Hsq]
    · rw [show ([.basic (.const (valueOfUint k)), .basic (.const (.int32 (Wasm.Int.intOfZ 0))),
        .basic (.call 5)] : Expr) = vToEList [valueOfUint k, .int32 (Wasm.Int.intOfZ 0)] ++
        [.basic (.call 5)] from rfl]
      iapply wp_call_vals _ _ _ _ 5 idf5 _ (hFi ▸ hf5) $$ Hf
      inext; iintro Hf
      rw [show (vToEList [valueOfUint k, .int32 (Wasm.Int.intOfZ 0)] ++ [.invoke idf5] : Expr) =
        [.basic (u32const k), .basic (.const (.int32 (Wasm.Int.intOfZ 0))), .invoke idf5] from rfl]
      iapply Hs5 $$ %F %(Wasm.Int.intOfZ 0) %k %([Wasm.Int.intOfZ 6, Wasm.Int.intOfZ 4] : List I32) %fsq
        %(.funcNative inst (.tf [.i32] [.i32]) [] square) %(fun _ => iprop(True))
        %(fun u v => iprop(⌜v = Wasm.Int.imul u u⌝)) [Hf H5 Hs Ht Hsq]
      · rw [show Wasm.Int.natOfUint (Wasm.Int.intOfZ 0 : I32) = 0 from rfl]
        iframe
        isplitr
        · simp only [stackAll]; iintro; isplitr <;> itrivial
        isplitr
        · ipureintro; rfl
        dsimp only
        iapply square_spec
      iintro %w ⟨%hw, ⟨%s', Hs, Hs2⟩, -, Hf, -, -⟩
      ihave %hs' := stackAll2_square _ _ $$ Hs2
      subst hs'
      simp only [List.map_cons, List.map_nil]
      iframe; ipureintro; exact hw
    iintro %w ⟨%hw, Hs, Hf⟩
    subst hw
    simp only [ofVal, vToEList, List.map, List.nil_append]
    -- pop
    take_drop_app_rewrite 1
    iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV [valueOfUint k]⌝ ∗ ↪[frame] F))
    isplitr
    · iintro ⟨%h, -⟩; cases h
    isplitl [Hf]
    · iapply wp_get_local _ _ _ _ (fun w => iprop(⌜w = .immV [valueOfUint k]⌝)) F hF0 $$ [] Hf
      inext; ipureintro; rfl
    iintro %w ⟨%hw, Hf⟩
    subst hw
    simp only [ofVal, vToEList, List.map, List.cons_append, List.nil_append]
    take_drop_app_rewrite 2
    iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV [.int32 (Wasm.Int.imul (Wasm.Int.intOfZ 6) (Wasm.Int.intOfZ 6))]⌝ ∗ isStack k [(Wasm.Int.imul (Wasm.Int.intOfZ 4) (Wasm.Int.intOfZ 4))] ∗
      idf3 ↦[wf] (.funcNative i0 (.tf [.i32] [.i32]) l3 b3) ∗ ↪[frame] F))
    isplitr
    · iintro ⟨%h, -⟩; cases h
    isplitl [Hf H3 Hs]
    · rw [show ([.basic (.const (valueOfUint k)), .basic (.call 3)] : Expr) =
        vToEList [valueOfUint k] ++ [.basic (.call 3)] from rfl]
      iapply wp_call_vals _ _ _ _ 3 idf3 _ (hFi ▸ hf3) $$ Hf
      inext; iintro Hf
      rw [show (vToEList [valueOfUint k] ++ [.invoke idf3] : Expr) =
        [.basic (u32const k), .invoke idf3] from rfl]
      iapply Hs3 $$ %(Wasm.Int.imul (Wasm.Int.intOfZ 6) (Wasm.Int.intOfZ 6)) %k %([(Wasm.Int.imul (Wasm.Int.intOfZ 4) (Wasm.Int.intOfZ 4))] : List I32) %F [Hf H3 Hs]
      · iframe
      iintro %w ⟨%hw, Hs, H3, Hf⟩
      iframe; ipureintro; exact hw
    iintro %w ⟨%hw, Hs, H3, Hf⟩
    subst hw
    simp only [ofVal, vToEList, List.map, List.cons_append, List.nil_append]
    -- pop
    take_drop_app_rewrite 3
    iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV [.int32 (Wasm.Int.imul (Wasm.Int.intOfZ 6) (Wasm.Int.intOfZ 6)), .int32 (Wasm.Int.imul (Wasm.Int.intOfZ 4) (Wasm.Int.intOfZ 4))]⌝ ∗ ↪[frame] F))
    isplitr
    · iintro ⟨%h, -⟩; cases h
    isplitl [Hf H3 Hs]
    · take_drop_app_rewrite 1
      iapply wp_val_app1
      isplitr
      · iintro !> ⟨%h, -⟩; cases h
      take_drop_app_rewrite 1
      iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV [valueOfUint k]⌝ ∗ ↪[frame] F))
      isplitr
      · iintro ⟨%h, -⟩; cases h
      isplitl [Hf]
      · iapply wp_get_local _ _ _ _ (fun w => iprop(⌜w = .immV [valueOfUint k]⌝)) F hF0 $$ [] Hf
        inext; ipureintro; rfl
      iintro %w ⟨%hw, Hf⟩
      subst hw
      rw [show (ofVal (.immV [valueOfUint k]) ++ [.basic (.call 3)] : Expr) =
        vToEList [valueOfUint k] ++ [.basic (.call 3)] from rfl]
      iapply wp_call_vals _ _ _ _ 3 idf3 _ (hFi ▸ hf3) $$ Hf
      inext; iintro Hf
      rw [show (vToEList [valueOfUint k] ++ [.invoke idf3] : Expr) =
        [.basic (u32const k), .invoke idf3] from rfl]
      iapply Hs3 $$ %(Wasm.Int.imul (Wasm.Int.intOfZ 4) (Wasm.Int.intOfZ 4)) %k %([] : List I32) %F [Hf H3 Hs]
      · iframe
      iintro %w ⟨%hw, -, -, Hf⟩
      subst hw
      iframe; ipureintro; rfl
    iintro %w ⟨%hw, Hf⟩
    subst hw
    simp only [ofVal, vToEList, List.map, List.cons_append, List.nil_append]
    -- sub
    take_drop_app_rewrite 3
    iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV [.int32 (Wasm.Int.intOfZ 20)]⌝ ∗ ↪[frame] F))
    isplitr
    · iintro ⟨%h, -⟩; cases h
    isplitl [Hf]
    · iapply wp_binop (Φ := fun w => iprop(⌜w = .immV [.int32 (Wasm.Int.intOfZ 20)]⌝))
        rfl rfl .i32Agree sub_squares $$ Hf
      inext; ipureintro; rfl
    iintro %w ⟨%hw, Hf⟩
    subst hw
    simp only [ofVal, vToEList, List.map, List.cons_append, List.nil_append]
    -- set_global
    iapply wp_wand_s $$ [Hf Hg]
    · iapply wp_set_global _ _ (.int32 (Wasm.Int.intOfZ 20)) _ 0
        (fun w => iprop(⌜w = .immV []⌝)) _ g (hFi ▸ hg) $$ [] Hf Hg
      inext; ipureintro; rfl
    iintro %w ⟨%hw, Hg, Hf⟩
    isplitr
    · ileft; ipureintro; exact hw
    isplitl [Hg]
    · ileft; iexact Hg
    iexists _; iexact Hf

end Helpers

end StackClient

open StackClient

section Client
variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF] [HvisG GF] [HmsG GF] [HasG GF]
  [LogrelNaInvs GF]

attribute [local instance] WasmG.invGS

omit [WasmG hlc GF] [LogrelNaInvs GF] [HvisG GF] [HmsG GF] [HasG GF] in
private theorem StackClient.nodupKeys_zip (ks : List Nat) (l : List FunctionClosure) (h : ks.Nodup) :
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
resource `R`. -/
private theorem StackClient.wp_seq_host_nostart_imm (E : CoPset) (Φ : HostVal → IProp GF) (R : IProp GF)
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

@[rocq_alias iriswasm.stack_client.instantiate_stack_client_spec]
theorem StackClient.instantiate_stack_client_spec (E : CoPset) (vis_addrs : List Nat)
    (stack_mod_addr client_mod_addr : Nat) :
    vis_addrs.length = 9 →
    ⊢ (↪[frame] emptyFrame -∗
      stack_mod_addr ↪[mods] stackModule -∗
      client_mod_addr ↪[mods] clientModule -∗
      ownVisPointers vis_addrs -∗
      WP ((stackInstantiate vis_addrs stack_mod_addr client_mod_addr, []) : HostExpr)
        @ Stuckness.NotStuck ; E
        {{ v, ⌜v = .immHV []⌝ ∗
          ↪[frame] emptyFrame ∗
          stack_mod_addr ↪[mods] stackModule ∗
          client_mod_addr ↪[mods] clientModule ∗
          ∃ (idg : Nat) (name : Name),
            vis_addrs.getD 8 0 ↪[vis] ({ name := name, desc := .global (.globalidx idg) } :
              ModuleExport) ∗
            (idg ↦[wg] ({ mut_ := .mut, val := valueOfInt 20 } : Global) ∨
              idg ↦[wg] ({ mut_ := .mut, val := valueOfInt (-1) } : Global)) }} : IProp GF) := by
  intro hlen
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, rfl⟩ :
      ∃ e0 e1 e2 e3 e4 e5 e6 e7 e8, vis_addrs = [e0, e1, e2, e3, e4, e5, e6, e7, e8] := by
    match vis_addrs, hlen with
    | [e0, e1, e2, e3, e4, e5, e6, e7, e8], _ => exact ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, rfl⟩
  iintro Hemptyframe Hmod0 Hmod1 Hvis
  unfold ownVisPointers
  rw [show [e0, e1, e2, e3, e4, e5, e6, e7, e8] = [e0, e1, e2, e3, e4, e5, e6, e7] ++ [e8] from rfl]
  icases BI.BigSepL.bigSepL_append.1 $$ Hvis with ⟨Hvis, Hvis8⟩
  simp only [stackInstantiate]
  rw [show List.take 8 ([e0, e1, e2, e3, e4, e5, e6, e7] ++ [e8]) = [e0, e1, e2, e3, e4, e5, e6, e7]
    from rfl, show List.drop 8 ([e0, e1, e2, e3, e4, e5, e6, e7] ++ [e8]) = [e8] from rfl]
  have Hstack := instantiate_stack_spec (GF := GF) .NotStuck E [e0, e1, e2, e3, e4, e5, e6, e7]
    stack_mod_addr rfl
  simp only [stackInstantiatePara, ownVisPointers] at Hstack
  iapply wp_seq_host_nostart_imm E _ _ _ stack_mod_addr [] stackModule _ rfl $$ Hmod0 [Hvis]
  · iintro Hmod0
    iapply Hstack $$ Hmod0 Hvis
  iintro ⟨%idf0, %idf1, %idf2, %idf3, %idf4, %idf5, %idf6, %idt, %nm0, %nm1, %nm2, %nm3, %nm4, %nm5,
    %nm6, %nm7, %f0, %f1, %f2, %f3, %f4, %f5, %f6, %i0, %l0, %l1, %l2, %l3, %l4, %l5, %l6,
    %tab, %isStack, %nextStackAddrIs, Himport, Himp_type, %Hnodup, %Hfnodup, %Htab, Hnextaddr,
    Hspec0, -, -, Hspec3, Hspec4, Hspec5, -, -⟩ Hmod0
  iapply instantiation_spec_operational_start .NotStuck E client_mod_addr
    [e0, e1, e2, e3, e4, e5, e6, e7]
    (stackInstVis idf0 idf1 idf2 idf3 idf4 idf5 idf6 idt nm0 nm1 nm2 nm3 nm4 nm5 nm6 nm7) [e8]
    clientModule expts [.glob { mut_ := .mut, t := .i32 }]
    (stackInstMap idf0 idf1 idf2 idf3 idf4 idf5 idf6 i0 l0 l1 l2 l3 l4 l5 l6 f0 f1 f2 f3 f4 f5 f6)
    (insert (∅ : NatMap Tableinst) idt tab) ∅ ∅ 7 _ rfl module_typing_client
    module_restrictions_client
    $$ Hemptyframe [Hmod1 Himport Himp_type Hvis8] [Hmod0 Hnextaddr Hspec0 Hspec3 Hspec4 Hspec5]
  · simp only [instantiationResourcesPre, instantiationResourcesPreWasm, exportOwnershipHost]
    iframe Hmod1 Himport
    isplitl [Himp_type]
    · isplitl
      · iapply (irwt_nodup_equiv _ _ _ _ _ _ Hnodup).2; iexact Himp_type
      isplit
      · ipureintro
        intro e he
        simp only [clientModule, List.mem_singleton] at he
        subst he
        rw [Tableinst.length_data] at Htab
        simp [assertConst1I32, extTabs, stackInstVis, i32const, LawfulPartialMap.get?_insert,
          natOfInt]
        omega
      · ipureintro
        intro d hd
        simp [clientModule] at hd
    isplitl
    · iexact Hvis8
    · ipureintro; rfl
  iintro %idnstart Hf Hpost
  simp only [instantiationResourcesPost, instantiationResourcesPostWasm]
  icases Hpost with ⟨Hmod1, -, %inst, ⟨%g_inits, %tabA, %memA, %globA, %wts', %wms', Himpres, %Hinst,
    %-, %Hwts', %-, %-, %-, %-, %-, %Hglob, Hres⟩, Hexphost⟩
  obtain ⟨Htypes, ⟨rest, Hfuncs⟩, ⟨rtab, Htabs⟩, -, -, Hstart⟩ := Hinst
  simp only [extFuncAddrs, extFuncs, extTabAddrs, extTabs, stackInstVis, Function.comp,
    List.map_cons, List.map_nil, List.filterMap_cons, List.filterMap_nil, List.cons_append,
    List.nil_append] at Hfuncs Htabs
  obtain ⟨itypes, ifuncs, itab, imem, iglobs⟩ := inst
  simp only at Htypes Hfuncs Htabs
  subst Htypes Hfuncs Htabs
  simp only [moduleInstResourcesWasm, moduleInstResourcesFunc, moduleInstResourcesGlob,
    show getImportFuncCount clientModule = 7 from rfl,
    show getImportGlobalCount clientModule = 0 from rfl, List.drop_zero, List.drop_succ_cons]
  icases Hres with ⟨Hresf, -, -, Hresg⟩
  ihave %Hlen := BI.BigSepL2.bigSepL2_length $$ Hresf
  obtain ⟨fm, fs, rfl⟩ : ∃ fm fs, rest = [fm, fs] := by
    match rest, Hlen with
    | [fm, fs], _ => exact ⟨fm, fs, rfl⟩
  obtain ⟨vg, rfl⟩ : ∃ vg, globA = [{ mut_ := .mut, val := vg }] := by
    subst Hglob
    cases g_inits <;>
      simp [moduleInstGlobalInit, moduleInstBuildGlobals, clientModule, globalInitReplaceSingle]
  ihave %Hlen' := BI.BigSepL2.bigSepL2_length $$ Hresg
  obtain ⟨g, rfl⟩ : ∃ g, iglobs = [g] := by
    match iglobs, Hlen' with
    | [g], _ => exact ⟨g, rfl⟩
  have hfm : fm = idnstart := by
    simpa [checkStart, clientModule, optionBind] using Hstart
  subst hfm
  rw [show clientModule.funcs = [{ type := .typeidx 0, locals := [.i32], body := main },
    { type := .typeidx 2, locals := [], body := square }] from rfl]
  icases Hresf with ⟨Hmaincl, Hsqcl, -⟩
  rw [show clientModule.types.getD 0 (.tf [] []) = .tf [] [] from rfl,
    show clientModule.types.getD 2 (.tf [] []) = .tf [.i32] [.i32] from rfl]
  icases Hresg with ⟨Hg, -⟩
  ihave Himpres := (irwt_nodup_equiv _ _ _ _ _ _ Hnodup).1 $$ Himpres
  simp only [importResourcesWasmTypecheckSepL2, stackInstVis, expts, funcTypes,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  icases Himpres with ⟨-, ⟨%cl0, Hcl0, %Hcl0⟩, -, -, ⟨%cl3, Hcl3, %Hcl3⟩,
    ⟨%cl4, Hcl4, %Hcl4⟩, ⟨%cl5, Hcl5, %Hcl5⟩, -, ⟨%tab', %tt, Htabb, %Htab'⟩, -⟩
  have hk := nodupKeys_zip _ [FunctionClosure.funcNative i0 (.tf [] [.i32]) l0 f0,
     .funcNative i0 (.tf [.i32] [.i32]) l1 f1,
     .funcNative i0 (.tf [.i32] [.i32]) l2 f2,
     .funcNative i0 (.tf [.i32] [.i32]) l3 f3,
     .funcNative i0 (.tf [.i32, .i32] []) l4 f4,
     .funcNative i0 (.tf [.i32, .i32] []) l5 f5,
     .funcNative i0 (.tf [.i32] [.i32]) l6 f6] Hfnodup
  obtain rfl := Option.some.inj ((LawfulPartialMap.get?_ofList_some (k := idf0)
    (v := .funcNative i0 (.tf [] [.i32]) l0 f0) (by simp) hk).symm.trans Hcl0.1)
  obtain rfl := Option.some.inj ((LawfulPartialMap.get?_ofList_some (k := idf3)
    (v := .funcNative i0 (.tf [.i32] [.i32]) l3 f3) (by simp) hk).symm.trans Hcl3.1)
  obtain rfl := Option.some.inj ((LawfulPartialMap.get?_ofList_some (k := idf4)
    (v := .funcNative i0 (.tf [.i32, .i32] []) l4 f4) (by simp) hk).symm.trans Hcl4.1)
  obtain rfl := Option.some.inj ((LawfulPartialMap.get?_ofList_some (k := idf5)
    (v := .funcNative i0 (.tf [.i32, .i32] []) l5 f5) (by simp) hk).symm.trans Hcl5.1)
  subst Hwts'
  have htab' := Htab'.1
  simp [moduleImportInitTabs, clientModule, getImportTableCount, lookupFuncaddr,
    LawfulPartialMap.get?_insert] at htab'
  have h0 : tab'.data[0]? = some (some fs) := by
    subst htab'
    rw [data_tableInitReplaceSingle]
    cases h : tab.data with
    | nil => simp [h] at Htab
    | cons x xs => rfl
  simp only [tabBlock]
  icases Htabb with ⟨Hbig, -, -⟩
  ihave Ht := BI.BigSepL.bigSepL_lookup h0 $$ Hbig
  iapply wp_lift_wasm .NotStuck E [] [.invoke fm] _
  iapply wp_wand_s $$ [Hf Hmaincl Hsqcl Hg Ht Hcl0 Hcl3 Hcl4 Hcl5 Hnextaddr Hspec0 Hspec3 Hspec4
    Hspec5]
  · iapply wp_invoke_native_unit .NotStuck E fm
      ⟨clientModule.types, [idf0, idf1, idf2, idf3, idf4, idf5, idf6, fm, fs], idt :: rtab, imem, [g]⟩
      [.i32] main emptyFrame
      iprop(g ↦[wg] ({ mut_ := .mut, val := valueOfInt 20 } : Global) ∨
        g ↦[wg] ({ mut_ := .mut, val := valueOfInt (-1) } : Global)) $$ Hf Hmaincl
    iintro Hf
    iapply main_spec E _ i0 idf0 idf3 idf4 idf5 fs g idt l0 l3 l4 l5 f0 f3 f4 f5 isStack
      nextStackAddrIs vg rfl rfl rfl rfl rfl $$ Hf Hg Ht Hsqcl Hcl0 Hcl3 Hcl4 Hcl5 Hnextaddr Hspec0
      Hspec3 Hspec4 Hspec5
  iintro %v ⟨⟨%hv, HR, -⟩, Hf⟩
  subst hv
  iapply IrisHost.wp_value .NotStuck E _ (.immHV []) _
    (show hostToVal (([], ofVal (Val.immV [])) : HostExpr) = some (.immHV []) from
      IrisHost.to_of_val (.immHV []))
  rw [show clientModule.exports = [⟨nameOfString "answer", .global (.globalidx 0)⟩] from rfl]
  simp only [moduleExportResourcesHost]
  icases Hexphost with ⟨⟨%nm, Hvis⟩, -⟩
  isplitr
  · ipureintro; trivial
  iframe
  iexists nm
  simp only [List.getD_cons_succ, List.getD_cons_zero]
  iexact Hvis

end Client

end IrisWasm.Examples.Stack
