/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Examples.Stack.StackInstantiation
import IrisWasm.Logrel.IrisInterpInstanceAlloc
import IrisWasm.Rules.IrisExampleHelper
import Wasm.ModuleValidation

/-! Port of `theories/iris/examples/stack/stack_robust.v`.

`main`, `client_module` and `wp_wand_host` are also defined in other Coq files, so they live in the
sub-namespace `IrisWasm.Examples.Stack.StackRobust` (aliases `iriswasm.stack_robust.<name>`).
The file-local Coq host notation `{{{{ P }}}} es {{{{ v, Q }}}}` (mask `⊤`) is written out as
`□ ∀ Φ, P -∗ (∀ v, Q -∗ Φ v) -∗ WP es @ NotStuck ; ⊤ {{ v, Φ v }}`. -/

namespace IrisWasm.Examples.Stack

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm
open scoped Iris.Std.PartialMap

namespace StackRobust

@[rocq_alias iriswasm.stack_robust.main]
def main : List BasicInstruction :=
  [ .call 0,
    .teeLocal 0,
    i32const (-1),
    .relop .i32 (.i .eq),
    -- If new_stack failed, trap
    .if_ (.result none) [.unreachable] [],
    .getLocal 0,
    i32const 4,
    .call 4,
    .getLocal 0,
    i32const 2,
    .call 4,
    .getLocal 0,
    i32const 0,
    .call 5,
    .getLocal 0,
    .call 6,
    .setGlobal 0 ]

@[rocq_alias iriswasm.stack_robust.client_module]
def clientModule : Module where
  types := [.tf [] [], .tf [] [.i32], .tf [.i32] [.i32], .tf [.i32, .i32] []]
  funcs := [{ type := .typeidx 0, locals := [.i32], body := main }]
  tables := []
  mems := []
  globals := []
  elem := [{ table := .tableidx 0, offset := [i32const 0], init := [.funcidx 7] }]
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
    { module := nameOfString "Adv", name := nameOfString "adv_call", desc := .func 2 },
    { module := nameOfString "Ret", name := nameOfString "ret_glob",
      desc := .global { mut_ := .mut, t := .i32 } } ]
  exports := []

end StackRobust

open StackRobust

@[rocq_alias iriswasm.client_func_impts]
def clientFuncImpts : List ExternT := expts ++ [.func (.tf [.i32] [.i32])]

@[rocq_alias iriswasm.client_glob_impts]
def clientGlobImpts : List ExternT := [.glob { mut_ := .mut, t := .i32 }]

@[rocq_alias iriswasm.client_module_typing]
theorem client_module_typing :
    ModuleTyping clientModule (clientFuncImpts ++ clientGlobImpts) [] := by
  apply (validateModule_iff _ ⟨_, _⟩).mp
  kernel_rfl

section Client_main
variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF] [LogrelNaInvs GF]

attribute [local instance] WasmG.invGS

private instance (idf0 : Nat) (i : Instance) (l : List ValueType) (fn : List BasicInstruction)
    (isStack : Nat → List I32 → IProp GF) (P : Nat → IProp GF) (E : CoPset) :
    Persistent (spec0NewStack idf0 i l fn isStack P E) := by
  unfold spec0NewStack; infer_instance

private instance (idf : Nat) (i : Instance) (l : List ValueType) (fn : List BasicInstruction)
    (isStack : Nat → List I32 → IProp GF) (E : CoPset) :
    Persistent (spec4Push idf i l fn isStack E) := by
  unfold spec4Push; infer_instance

private instance (idf : Nat) (i : Instance) (l : List ValueType) (fn : List BasicInstruction)
    (isStack : Nat → List I32 → IProp GF) (j0 : Nat) (E : CoPset) :
    Persistent (spec5StackMapTrap idf i l fn isStack j0 E) := by
  unfold spec5StackMapTrap; infer_instance

private instance (idf : Nat) (i : Instance) (l : List ValueType) (fn : List BasicInstruction)
    (isStack : Nat → List I32 → IProp GF) (E : CoPset) :
    Persistent (spec6StackLength idf i l fn isStack E) := by
  unfold spec6StackLength; infer_instance

omit [LogrelNaInvs GF] in
private theorem wp_wand_s {s : Stuckness} {E : CoPset} {e : Expr} {Φ Ψ : Val → IProp GF} :
    iprop(WP e @ s ; E {{ Φ }}) ⊢ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s ; E {{ Ψ }} :=
  IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)

omit [LogrelNaInvs GF] in
private theorem fupd_wp_s {s : Stuckness} {E : CoPset} {e : Expr} {Φ : Val → IProp GF} :
    iprop(|={E}=> WP e @ s ; E {{ Φ }}) ⊢ WP e @ s ; E {{ Φ }} :=
  IrisWp.fupd_wp (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)

omit [LogrelNaInvs GF] in
/-- Calling a function after pushing constant arguments (Coq: the `wp_base_push`/`wp_call_ctx`/
`wp_base_pull` dance). -/
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

omit [WasmG hlc GF] [LogrelNaInvs GF] in
private theorem stackAll2_length {A : Type} (s s' : List A) (Ψ : A → A → IProp GF) :
    stackAll2 s s' Ψ ⊢ ⌜s.length = s'.length⌝ := by
  induction s generalizing s' with
  | nil =>
    cases s' with
    | nil => iintro -; ipureintro; rfl
    | cons _ _ => unfold stackAll2; iintro H; iexfalso; iexact H
  | cons x s ih =>
    cases s' with
    | nil => unfold stackAll2; iintro H; iexfalso; iexact H
    | cons y s' =>
      unfold stackAll2
      iintro ⟨-, H⟩
      ihave %h := ih s' $$ H
      ipureintro; simp [h]

local notation "logrelNais" => LogrelNaInvs.logrelNais (GF := GF)

@[rocq_alias iriswasm.main_spec]
theorem main_spec (C : TContext) (k idt : Nat) (locs : List ValueType) (es : List BasicInstruction)
    (f : Frame) (a : Nat) (i : Instance) (idf0 : Nat) (l0 : List ValueType)
    (f0 : List BasicInstruction) (idf4 : Nat) (l4 : List ValueType) (f4 : List BasicInstruction)
    (idf5 : Nat) (l5 : List ValueType) (f5 : List BasicInstruction) (idf6 : Nat)
    (l6 : List ValueType) (f6 : List BasicInstruction) (istack : Instance)
    (isStack : Nat → List I32 → IProp GF) (newStackAddrIs : Nat → IProp GF)
    (stacktab : Tableinst) :
    C.label = [] ∧ C.return_ = none →
    f.inst.globs[0]? = some k →
    f.inst.tab[0]? = some idt →
    f.inst.funcs[0]? = some idf0 →
    f.inst.funcs[4]? = some idf4 →
    f.inst.funcs[5]? = some idf5 →
    f.inst.funcs[6]? = some idf6 →
    f.locs = nZeros [.i32] →
    stacktab.data.length ≥ 1 →
    BeTyping (updLocalLabelReturn C (.i32 :: locs) [[.i32]] (some [.i32])) es (.tf [] [.i32]) →
    ⊢ ({{{{ ↪[frame] f ∗
          NonAtomicInvariant.own (LogrelNaInvs.logrelNais (GF := GF)) ⊤ ∗
          NonAtomicInvariant.inv (LogrelNaInvs.logrelNais (GF := GF)) (wfN a)
            (a ↦[wf] (.funcNative i (.tf [.i32] [.i32]) locs es)) ∗
          interpInstance C [] i ∗
          (∃ gv, k ↦[wg] (⟨.mut, gv⟩ : Global)) ∗
          -- new stack
          idf0 ↦[wf] (.funcNative istack (.tf [] [.i32]) l0 f0) ∗
          spec0NewStack idf0 istack l0 f0 isStack newStackAddrIs ⊤ ∗
          -- push
          idf4 ↦[wf] (.funcNative istack (.tf [.i32, .i32] []) l4 f4) ∗
          spec4Push idf4 istack l4 f4 isStack ⊤ ∗
          -- map
          idf5 ↦[wf] (.funcNative istack (.tf [.i32, .i32] []) l5 f5) ∗
          spec5StackMapTrap idf5 istack l5 f5 isStack idt ⊤ ∗
          -- length
          idf6 ↦[wf] (.funcNative istack (.tf [.i32] [.i32]) l6 f6) ∗
          spec6StackLength idf6 istack l6 f6 isStack ⊤ ∗
          -- table
          idt ↦[wtblock] (tableInitReplaceSingle stacktab
            (natOfInt (Wasm.Int.repr (w := 32) 0)) [some a]) ∗
          -- new stack predicate
          newStackAddrIs 0 }}}}
        (toEList main)
      {{{{ w, (⌜w = .trapV⌝ ∨ (⌜w = .immV []⌝ ∗ k ↦[wg] (⟨.mut, xx 2⟩ : Global) ∗
            NonAtomicInvariant.own (LogrelNaInvs.logrelNais (GF := GF)) ⊤)) ∗
          ∃ f', ↪[frame] f' ∗ ∃ r, ⌜f' = ⟨f.locs.set 0 r, f.inst⟩⌝ }}}} : IProp GF) := by
  intro hC hglob htab hidf0 hidf4 hidf5 hidf6 hflocs htablen htyp
  imodintro
  iintro %Φ ⟨Hf, Hown, #Hadv, #Hi, Hg, Hidf0, #Hnewstack, Hidf4, #Hpush, Hidf5, #Hmap, Hidf6,
    #Hstacklen, Hidt, Hnsa⟩ HΦ
  rw [show toEList main = ([.basic (.call 0)] : Expr) ++ toEList (main.drop 1) from rfl]
  iapply wp_seq _ _ _ (fun v => iprop((((⌜v = .immV [valueOfInt (-1)]⌝ ∗ newStackAddrIs 0) ∨
      (∃ k, ⌜v = .immV [valueOfUint k]⌝ ∗ ⌜0 ≤ k ∧ k ≤ ffff0000⌝ ∗ isStack k [] ∗
        newStackAddrIs (0 + pageSize))) ∗
      idf0 ↦[wf] (.funcNative istack (.tf [] [.i32]) l0 f0)) ∗ ↪[frame] f))
  isplitr
  · iintro ⟨⟨(⟨%H, -⟩ | ⟨%k, %H, -⟩), -⟩, -⟩ <;> cases H
  isplitl [Hf Hidf0 Hnsa]
  · iapply wp_call _ _ _ f 0 idf0 hidf0 $$ Hf
    inext; iintro Hf
    iunfold spec0NewStack at Hnewstack
    iapply Hnewstack $$ %f %0 [Hf Hidf0 Hnsa]
    · iframe
      ipureintro
      refine ⟨by decide, by decide, Nat.dvd_zero _⟩
    iintro %v ⟨Hres, Hidf, Hf⟩
    iframe
  iintro %w ⟨⟨Hres, Hidf⟩, Hf⟩
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
    ([.basic (.const (.int32 k')), .basic (.const (.int32 (Wasm.Int.intOfZ (-1)))), .basic (.relop .i32 (.i .eq))] : Expr) ++
      toEList (main.drop 4) from rfl]
  iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV [.int32 (wasmBool
      (appRelop (.i .eq) (.int32 k') (.int32 (Wasm.Int.intOfZ (-1)))))]⌝ ∗
    ↪[frame] (⟨f.locs.set 0 (.int32 k'), f.inst⟩ : Frame)))
  isplitr
  · iintro ⟨%H, -⟩; cases H
  isplitl [Hf]
  · iapply wp_relop rfl rfl .i32Agree rfl $$ Hf
    inext; ipureintro; rfl
  iintro %w ⟨%Hw, Hf⟩
  subst Hw
  rw [show ∀ c : I32, ofVal (.immV [.int32 c]) ++ toEList (main.drop 4) =
    ([.basic (.const (.int32 c)), .basic (.if_ (.result none) [.unreachable] [])] : Expr) ++
      toEList (main.drop 5) from fun _ => rfl]
  icases Hres with (⟨%Heq, Hnsa⟩ | ⟨%r, %Heq, %Hle, Hst, Hnsa⟩)
  · -- new stack failed: trap
    simp only [valueOfInt, Val.immV.injEq, List.cons.injEq, Value.int32.injEq, _root_.and_true] at Heq
    subst Heq
    iapply wp_wand_s $$ [Hf]
    · iapply wp_if_unreachable_trap _ (by decide) _ (toEList (main.drop 5)) $$ Hf
    iintro %w ⟨%Hw, Hf⟩
    subst Hw
    iapply HΦ
    isplitr
    · ileft; ipureintro; rfl
    iexists _; iframe
    iexists _; ipureintro; rfl
  -- new stack succeeded
  simp only [valueOfUint, Val.immV.injEq, List.cons.injEq, Value.int32.injEq, _root_.and_true] at Heq
  subst Heq
  have hne : Wasm.Int.intOfZ (w := 32) (r : _root_.Int) ≠ Wasm.Int.intOfZ (-1) := by
    intro h
    have := congrArg BitVec.toNat h
    simp [Wasm.Int.intOfZ, BitVec.toNat_ofInt] at this
    simp only [ffff0000] at Hle
    omega
  generalize hf1 : (⟨f.locs.set 0 (.int32 (Wasm.Int.intOfZ (r : _root_.Int))), f.inst⟩ : Frame) = f1
  have hloc : f1.locs[0]? = some (.int32 (Wasm.Int.intOfZ (r : _root_.Int))) := by
    subst hf1; simp [hflocs, nZeros]
  have hinst : f1.inst = f.inst := by subst hf1; rfl
  rw [← hinst] at hidf4 hidf5 hidf6 hglob htab
  -- if
  iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV []⌝ ∗ ↪[frame] f1))
  isplitr
  · iintro ⟨%H, -⟩; cases H
  isplitl [Hf]
  · iapply wp_if_false (by simp only [wasmBool, appRelop, appRelopI, Wasm.Int.ieq, beq_eq_false_iff_ne.2 hne,
      Bool.false_eq_true, ite_false]) $$ Hf
    inext; iintro Hf
    rw [show ([.basic (.block (.result none) [])] : Expr) = [] ++ [.basic (.block (.result none) [])]
      from rfl]
    iapply wp_block (bt := .result none) (vs := []) rfl rfl rfl rfl rfl $$ Hf
    inext; iintro Hf
    iapply wp_label_value rfl $$ Hf
    inext; ipureintro; rfl
  iintro %w ⟨%Hw, Hf⟩
  subst Hw
  rw [show ofVal (.immV []) ++ toEList (main.drop 5) =
    ([.basic (.getLocal 0)] : Expr) ++ toEList (main.drop 6) from rfl]
  iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV [.int32 (Wasm.Int.intOfZ (r : _root_.Int))]⌝ ∗
    ↪[frame] f1))
  isplitr
  · iintro ⟨%H, -⟩; cases H
  isplitl [Hf]
  · iapply wp_get_local _ _ _ 0 (fun w => iprop(⌜w = .immV [.int32 (Wasm.Int.intOfZ (r : _root_.Int))]⌝))
      f1 hloc $$ [] Hf
    inext; ipureintro; rfl
  iintro %w ⟨%Hw, Hf⟩
  subst Hw
  rw [show ofVal (.immV [.int32 (Wasm.Int.intOfZ (r : _root_.Int))]) ++ toEList (main.drop 6) =
    ([.basic (u32const r), .basic (.const (.int32 (Wasm.Int.intOfZ 4)))] ++
      [.basic (.call 4)] : Expr) ++ toEList (main.drop 8) from rfl]
  iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV []⌝ ∗ isStack r ([Wasm.Int.intOfZ 4]) ∗
    idf4 ↦[wf] (.funcNative istack (.tf [.i32, .i32] []) l4 f4) ∗ ↪[frame] f1))
  isplitr
  · iintro ⟨%H, -⟩; cases H
  isplitl [Hf Hidf4 Hst]
  · iapply wp_call_consts f1 _ rfl 4 idf4 hidf4 $$ Hf
    inext; iintro Hf
    simp only [List.cons_append, List.nil_append]
    iunfold spec4Push at Hpush
    iapply Hpush $$ %(Wasm.Int.intOfZ 4) %r %([]) %f1 [Hf Hidf4 Hst]
    · iframe; ipureintro; decide
    iintro %w H; iexact H
  iintro %w ⟨%Hw, Hst, Hidf4, Hf⟩
  subst Hw
  rw [show ofVal (.immV []) ++ toEList (main.drop 8) =
    ([.basic (.getLocal 0)] : Expr) ++ toEList (main.drop 9) from rfl]
  iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV [.int32 (Wasm.Int.intOfZ (r : _root_.Int))]⌝ ∗
    ↪[frame] f1))
  isplitr
  · iintro ⟨%H, -⟩; cases H
  isplitl [Hf]
  · iapply wp_get_local _ _ _ 0 (fun w => iprop(⌜w = .immV [.int32 (Wasm.Int.intOfZ (r : _root_.Int))]⌝))
      f1 hloc $$ [] Hf
    inext; ipureintro; rfl
  iintro %w ⟨%Hw, Hf⟩
  subst Hw
  rw [show ofVal (.immV [.int32 (Wasm.Int.intOfZ (r : _root_.Int))]) ++ toEList (main.drop 9) =
    ([.basic (u32const r), .basic (.const (.int32 (Wasm.Int.intOfZ 2)))] ++
      [.basic (.call 4)] : Expr) ++ toEList (main.drop 11) from rfl]
  iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV []⌝ ∗ isStack r ([Wasm.Int.intOfZ 2, Wasm.Int.intOfZ 4]) ∗
    idf4 ↦[wf] (.funcNative istack (.tf [.i32, .i32] []) l4 f4) ∗ ↪[frame] f1))
  isplitr
  · iintro ⟨%H, -⟩; cases H
  isplitl [Hf Hidf4 Hst]
  · iapply wp_call_consts f1 _ rfl 4 idf4 hidf4 $$ Hf
    inext; iintro Hf
    simp only [List.cons_append, List.nil_append]
    iunfold spec4Push at Hpush
    iapply Hpush $$ %(Wasm.Int.intOfZ 2) %r %([Wasm.Int.intOfZ 4]) %f1 [Hf Hidf4 Hst]
    · iframe; ipureintro; decide
    iintro %w H; iexact H
  iintro %w ⟨%Hw, Hst, Hidf4, Hf⟩
  subst Hw
  rw [show ofVal (.immV []) ++ toEList (main.drop 11) =
    ([.basic (.getLocal 0)] : Expr) ++ toEList (main.drop 12) from rfl]
  iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV [.int32 (Wasm.Int.intOfZ (r : _root_.Int))]⌝ ∗
    ↪[frame] f1))
  isplitr
  · iintro ⟨%H, -⟩; cases H
  isplitl [Hf]
  · iapply wp_get_local _ _ _ 0 (fun w => iprop(⌜w = .immV [.int32 (Wasm.Int.intOfZ (r : _root_.Int))]⌝))
      f1 hloc $$ [] Hf
    inext; ipureintro; rfl
  iintro %w ⟨%Hw, Hf⟩
  subst Hw
  -- map (may trap)
  have hdata : ∃ rest, (tableInitReplaceSingle stacktab (natOfInt (Wasm.Int.repr 0)) [some a]).data =
      some a :: rest := by
    obtain ⟨n, hn⟩ : ∃ n, stacktab.data.length = n + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos htablen).symm⟩
    exact ⟨stacktab.data.tail, by simp [data_tableInitReplaceSingle, hn, natOfInt, Wasm.Int.repr]⟩
  obtain ⟨rest, hrest⟩ := hdata
  iunfold tabBlock at Hidt
  icases Hidt with ⟨Ht, -, -⟩
  rw [hrest]
  ihave ⟨Ht, -⟩ := BI.BigSepL.bigSepL_cons.1 $$ Ht
  rw [show ofVal (.immV [.int32 (Wasm.Int.intOfZ (r : _root_.Int))]) ++ toEList (main.drop 12) =
    ([.basic (u32const r), .basic (.const (.int32 (Wasm.Int.intOfZ 0)))] ++
      [.basic (.call 5)] : Expr) ++ toEList (main.drop 14) from rfl]
  iapply wp_wand_s (Φ := fun v => iprop((⌜v = .trapV⌝ ∨ (⌜v = .immV []⌝ ∗
      k ↦[wg] (⟨.mut, xx 2⟩ : Global) ∗ NonAtomicInvariant.own logrelNais ⊤)) ∗ ↪[frame] f1))
    $$ [-HΦ]
  · iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).2
    iapply wp_seq_can_trap_same_ctx _ (fun w => iprop(⌜w = .immV []⌝ ∗
      (∃ s', isStack r s' ∗ stackAll2 [Wasm.Int.intOfZ 2, Wasm.Int.intOfZ 4] s'
        (fun _ _ => iprop(True))) ∗
      idf5 ↦[wf] (.funcNative istack (.tf [.i32, .i32] []) l5 f5) ∗
      NonAtomicInvariant.own logrelNais ⊤))
    isplitr
    · iintro ⟨%H, -⟩; cases H
    isplitr
    · ileft; ipureintro; rfl
    iframe Hf
    isplitl [Hst Hidf5 Ht Hown]
    · iintro Hf
      iapply wp_call_consts f1 _ rfl 5 idf5 hidf5 $$ Hf
      inext; iintro Hf
      simp only [List.cons_append, List.nil_append]
      iapply fupd_wp_s
      imod NonAtomicInvariant.inv_alloc (p := logrelNais) (N := wtN idt 0) $$ [Ht] with #Ht
      · inext; iexact Ht
      imodintro
      iunfold spec5StackMapTrap at Hmap
      iapply Hmap $$ %f1 %(Wasm.Int.intOfZ 0) %r %([Wasm.Int.intOfZ 2, Wasm.Int.intOfZ 4] : List I32) %(some a)
        %(.funcNative i (.tf [.i32] [.i32]) locs es) %(wtN idt 0) %(fun _ => iprop(True))
        %(fun _ _ => iprop(True)) %(CoPset.subseteq_top) [Hst Hidf5 Hown Hf]
      · iframe
        isplitr
        · simp only [stackAll]
          isplitr
          · ipureintro; trivial
          isplitr <;> ipureintro <;> trivial
        isplitr
        · rw [show Wasm.Int.natOfUint (Wasm.Int.intOfZ (w := 32) 0) = 0 from rfl]
          iexact Ht
        -- the imported function gets its spec from the fundamental theorem
        simp only [mapClosureSpec]
        iexists wfN a
        isplitr
        · ipureintro; exact ⟨CoPset.subseteq_top, FundAux.wfN_sub_wtN a idt 0⟩
        isplitr
        · iexact Hadv
        isplitr
        · ipureintro; rfl
        iintro %u %fc
        imodintro
        iintro %Ψ' ⟨-, %Histack, Hf, Hown⟩ HΨ
        iapply fupd_wp_s
        imod NonAtomicInvariant.inv_acc CoPset.subseteq_top CoPset.subseteq_top $$ Hadv Hown with
          ⟨>Haf, Hown, Hcls⟩
        imodintro
        iapply wp_wand_s (Φ := fun v => iprop((⌜v = .trapV⌝ ∨ ∃ v', ⌜v = .immV [.int32 v']⌝ ∗
            iprop(True)) ∗ NonAtomicInvariant.own logrelNais ⊤ ∗ ↪[frame] fc)) $$ [-HΨ] HΨ
        rw [show ([.basic (.const (.int32 u)), .invoke a] : Expr) =
          [.basic (.const (.int32 u))] ++ [.invoke a] from rfl]
        iapply wp_invoke_native .NotStuck ⊤ _ [.basic (.const (.int32 u))] [.int32 u] [.i32] [.i32] locs a es i 1 fc
          (to_of_val (.immV [.int32 u])) rfl rfl
          $$ Hf Haf
        inext
        iintro ⟨Hf, Haf⟩
        iapply fupd_wp_s
        imod Hcls $$ [Haf Hown] with Hown
        · iframe
        imodintro
        ihave Hl := be_fundamental_local (GF := GF) C es [.i32] [.i32] locs hC htyp
        iunfold semanticTypingLocalNoHost at Hl
        icases Hl with ⟨-, Hl⟩
        iunfold interpExpressionClosureNoHost at Hl
        ihave H := Hl $$ %i Hi %fc %([.int32 u] ++ nZeros locs) Hf Hown []
        · iunfold interpVal
          iright
          iunfold interpValues
          iexists [.int32 u] ++ nZeros locs
          isplitr
          · ipureintro; rfl
          simp only [List.singleton_append]
          iapply BI.BigSepL2.bigSepL2_cons.2
          isplitr
          · simp only [interpValue, interpValueI32]; ipureintro; exact ⟨u, rfl⟩
          iapply n_zeros_interp_values
        iapply wp_wand_s $$ H
        iintro %v ⟨⟨Hv, Hown⟩, Hf⟩
        iframe
        iunfold interpVal at Hv
        icases Hv with (%Hv | Hv)
        · ileft; ipureintro; exact Hv
        iright
        iunfold interpValues at Hv
        icases Hv with ⟨%ws, %Hws, Hws⟩
        subst Hws
        ihave %Hlen := BI.BigSepL2.bigSepL2_length $$ Hws
        match ws, Hlen with
        | [w], _ =>
          ihave ⟨Hw, -⟩ := BI.BigSepL2.bigSepL2_cons.1 $$ Hws
          simp only [interpValue, interpValueI32]
          icases Hw with %Hw
          obtain ⟨z, rfl⟩ := Hw
          iexists z
          isplitr
          · ipureintro; rfl
          itrivial
      iintro %w ⟨Hw, Hown, Hf⟩
      iframe Hf
      icases Hw with (%Hw | ⟨%Hw, Hst, Hidf5⟩)
      · ileft; ipureintro; exact Hw
      · iright; iframe; ipureintro; exact Hw
    iintro %w ⟨⟨%Hw, ⟨%s', Hst, Hall⟩, Hidf5, Hown⟩, Hf⟩
    subst Hw
    iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).1
    ihave %hlen := stackAll2_length _ _ _ $$ Hall
    -- get_local
    rw [show ofVal (.immV []) ++ toEList (main.drop 14) =
      ([.basic (.getLocal 0)] : Expr) ++ toEList (main.drop 15) from rfl]
    iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV [.int32 (Wasm.Int.intOfZ (r : _root_.Int))]⌝ ∗
      ↪[frame] f1))
    isplitr
    · iintro ⟨%H, -⟩; cases H
    isplitl [Hf]
    · iapply wp_get_local _ _ _ 0
        (fun w => iprop(⌜w = .immV [.int32 (Wasm.Int.intOfZ (r : _root_.Int))]⌝)) f1 hloc $$ [] Hf
      inext; ipureintro; rfl
    iintro %w ⟨%Hw, Hf⟩
    subst Hw
    -- stack length
    rw [show ofVal (.immV [.int32 (Wasm.Int.intOfZ (r : _root_.Int))]) ++ toEList (main.drop 15) =
      ([.basic (u32const r)] ++ [.basic (.call 6)] : Expr) ++ toEList (main.drop 16) from rfl]
    iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV [valueOfUint 2]⌝ ∗ isStack r s' ∗
      idf6 ↦[wf] (.funcNative istack (.tf [.i32] [.i32]) l6 f6) ∗ ↪[frame] f1))
    isplitr
    · iintro ⟨%H, -⟩; cases H
    isplitl [Hf Hidf6 Hst]
    · iapply wp_call_consts f1 _ rfl 6 idf6 hidf6 $$ Hf
      inext; iintro Hf
      simp only [List.cons_append, List.nil_append]
      iunfold spec6StackLength at Hstacklen
      iapply Hstacklen $$ %r %s' %f1 %2 [Hf Hidf6 Hst]
      · iframe; ipureintro; simpa using hlen.symm
      iintro %w H; iexact H
    iintro %w ⟨%Hw, -, -, Hf⟩
    subst Hw
    -- set_global
    icases Hg with ⟨%gv, Hg⟩
    rw [show ofVal (.immV [valueOfUint 2]) ++ toEList (main.drop 16) =
      ([.basic (.const (valueOfUint 2)), .basic (.setGlobal 0)] : Expr) from rfl]
    iapply wp_wand_s $$ [Hf Hg]
    · iapply wp_set_global _ _ _ f1 0 (fun w => iprop(⌜w = .immV []⌝)) _ k hglob $$ [] Hf Hg
      inext; ipureintro; rfl
    iintro %w ⟨%Hw, Hg, Hf⟩
    subst Hw
    rw [show valueOfUint 2 = xx 2 from rfl]
    iframe
    iright
    iframe
    ipureintro; rfl
  iintro %v ⟨Hv, Hf⟩
  iapply HΦ
  iframe Hv
  iexists f1
  iframe Hf
  iexists _; ipureintro; exact hf1.symm

end Client_main

section Client_instantiation_helpers
variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF]

attribute [local instance] WasmG.invGS

/-- Running the client's start function `main` from the empty frame, given a spec for its
body (Lean helper factored out of Coq's `instantiate_client`). -/
private theorem client_start_spec (inst : Instance) (idnstart : Nat) (P R : IProp GF)
    (Q : Frame → IProp GF)
    (hspec : ⊢ iprop(□ ∀ Φ : Val → IProp GF, (↪[frame] (⟨nZeros [.i32], inst⟩ : Frame) ∗ P) -∗
        (∀ w : Val, ((⌜w = .trapV⌝ ∨ (⌜w = .immV []⌝ ∗ R)) ∗ ∃ f', ↪[frame] f' ∗ Q f') -∗ Φ w) -∗
        WP (toEList main : Expr) @ Stuckness.NotStuck ; ⊤ {{ Φ }})) :
    ⊢ iprop(↪[frame] emptyFrame -∗
      idnstart ↦[wf] (.funcNative inst (.tf [] []) [.i32] main) -∗ P -∗
      WP ([.invoke idnstart] : Expr) @ Stuckness.NotStuck ; ⊤
        {{ w, (⌜w = Val.trapV⌝ ∨ (⌜w = Val.immV []⌝ ∗ R)) ∗ ↪[frame] emptyFrame }}) := by
  iintro Hf Hcl HP
  ihave #Hspec := hspec
  rw [show ([.invoke idnstart] : Expr) = [] ++ [.invoke idnstart] from rfl]
  iapply wp_invoke_native .NotStuck ⊤ _ [] [] [] [] [.i32] idnstart main inst 0 emptyFrame
    rfl rfl rfl $$ Hf Hcl
  inext
  iintro ⟨Hf, -⟩
  have hfb := wp_frame_bind (GF := GF) .NotStuck ⊤
    (fun w => iprop((⌜w = .trapV⌝ ∨ (⌜w = .immV []⌝ ∗ R)) ∗ ↪[frame] emptyFrame)) 0
    ⟨[] ++ nZeros [.i32], inst⟩ emptyFrame
    [.label 0 [] (toEList main)] (toVal_native_frame_none _ _ _)
  unfold wpWasmFrame at hfb
  iapply hfb $$ Hf
  iintro Hf
  iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).2
  iapply wp_label_push_nil
  iapply wp_ctx_bind _ _ _ _ 1 (pushBase (.base [] []) 0 [] [] []) (by simp [BaseIsEmpty, pushBase])
  simp only [List.nil_append]
  iapply Hspec $$ %_ [Hf HP]
  · iframe Hf HP
  iintro %w ⟨Hw, %f', Hf, -⟩
  icases Hw with (%Hw | ⟨%Hw, HR⟩)
  · subst Hw
    iapply wp_wand_ctx $$ [Hf]
    · rw [show ofVal Val.trapV = ([] ++ [AdministrativeInstruction.trap] ++ [] : Expr) from rfl]
      iapply wp_trap_ctx _ _ _ _ _ [] [] rfl $$ Hf
    iintro %v ⟨%Hv, Hf⟩
    subst Hv
    iexists _
    iframe Hf
    iintro Hf0
    have ht := wp_frame_trap (GF := GF) .NotStuck ⊤
      (fun w => iprop(⌜w = Val.trapV⌝ ∨ (⌜w = Val.immV []⌝ ∗ R))) 0 f' emptyFrame
    unfold wpWasmFrame at ht
    rw [show ofVal Val.trapV = [AdministrativeInstruction.trap] from rfl]
    iapply ht $$ Hf0
    inext; ileft; ipureintro; rfl
  · subst Hw
    rw [show ofVal (Val.immV []) = ([] : Expr) from rfl,
      show pushBase (.base [] []) 0 [] [] [] = .rec_ [] 0 [] (.base [] []) [] from rfl]
    iapply wp_val_return (vs := []) (vs' := []) (es'' := []) rfl $$ Hf
    iintro Hf
    rw [show ([] ++ [] ++ [] : Expr) = ofVal (Val.immV []) from rfl]
    iapply IrisWp.wp_value (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) ⟨rfl⟩
    iexists _
    iframe Hf
    iintro Hf0
    have hv := wp_frame_value (GF := GF) .NotStuck ⊤
      (fun w => iprop(⌜w = Val.trapV⌝ ∨ (⌜w = Val.immV []⌝ ∗ R))) [] 0 f' emptyFrame [] rfl rfl
    unfold wpWasmFrame at hv
    rw [show ofVal (Val.immV []) = ([] : Expr) from rfl]
    iapply hv $$ Hf0
    inext; iright; iframe; ipureintro; rfl


private theorem forall2_lookup_r'' {A B : Type} {R : A → B → Prop} {l1 : List A} {l2 : List B}
    (h : Wasm.List.Forall₂ R l1 l2) {i : Nat} {b : B} (hb : l2[i]? = some b) :
    ∃ a, l1[i]? = some a ∧ R a b := by
  induction h generalizing i with
  | nil => simp at hb
  | cons hab _ ih =>
    cases i with
    | zero => simp at hb; subst hb; exact ⟨_, rfl, hab⟩
    | succ i => simpa using ih (by simpa using hb)

/-- What `ModuleTyping adv [] [.func (.tf [.i32] [.i32])]` says about the adversary module (Lean
helper: the Coq proof of `instantiate_client` derives these facts inline). -/
private theorem adv_typing_facts (adv : Module)
    (htyp : ModuleTyping adv [] [.func (.tf [.i32] [.i32])]) :
    ∃ fts gts, ModuleTypingBody adv [] [.func (.tf [.i32] [.i32])] fts gts ∧ adv.imports = [] ∧
      ∃ nm nidx mf k, adv.exports = [⟨nm, .func (.funcidx nidx)⟩] ∧ adv.funcs[nidx]? = some mf ∧
        mf.type = .typeidx k ∧ adv.types.getD k (.tf [] []) = .tf [.i32] [.i32] ∧
        BeTyping (updLocalLabelReturn
          { typesT := adv.types, funcT := extTFuncs [] ++ fts, global := extTGlobs [] ++ gts
            table := extTTabs [] ++ adv.tables.map (·.type), memory := extTMems [] ++ adv.mems
            local_ := [], label := [], return_ := none } (.i32 :: mf.locals) [[.i32]] (some [.i32]))
          mf.body (.tf [] [.i32]) := by
  obtain ⟨fts, gts, h⟩ := htyp
  refine ⟨fts, gts, h, ?_⟩
  obtain ⟨tfs, fs, ts, ms, gs, els, ds, iOpt, imps, exps⟩ := adv
  obtain ⟨hfs, -, -, -, -, -, -, himps, -, hexps⟩ := h
  cases himps
  cases hexps with
  | cons he hnil =>
  cases hnil
  rename_i e
  obtain ⟨nm, desc⟩ := e
  refine ⟨rfl, ?_⟩
  cases desc with
  | func fi =>
    obtain ⟨nidx⟩ := fi
    have hft : fts[nidx]? = some (.tf [.i32] [.i32]) := by
      simp [moduleExportTyping, moduleContext, extTFuncs] at he
      split at he <;> simp_all
    obtain ⟨⟨⟨k⟩, locs, body⟩, hmf, hty⟩ := forall2_lookup_r'' hfs hft
    obtain ⟨hk, hbe⟩ := hty
    change tfs[k]? = _ at hk
    refine ⟨nm, nidx, _, k, rfl, hmf, rfl, by simp [List.getD_eq_getElem?_getD, hk], ?_⟩
    simpa [moduleContext, updLocalLabelReturn] using hbe
  | table t => obtain ⟨_⟩ := t; simp [moduleExportTyping] at he
  | mem m => obtain ⟨_⟩ := m; simp [moduleExportTyping] at he
  | global g => obtain ⟨_⟩ := g; simp [moduleExportTyping] at he

/-- An empty resource map together with a true side condition. -/
private theorem empty_map_check' {V : Type} (Φ : Nat → V → IProp GF) {φ : Prop} (hφ : φ) :
    ⊢ iprop(([∗map] k ↦ x ∈ (∅ : NatMap V), Φ k x) ∗ ⌜φ⌝) :=
  BI.emp_sep.2.trans (BI.sep_mono BI.BigSepM.bigSepM_empty_intro (BI.pure_intro hφ))

omit [WasmG hlc GF] in
private theorem empty_dom' {V : Type} (k : Nat) :
    PartialMap.dom (∅ : NatMap V) k ↔ k ∈ ([] : List Nat) := by
  simp [PartialMap.dom, get?_empty]

omit [WasmG hlc GF] in
private theorem nodupKeys_zip' (ks : List Nat) (l : List FunctionClosure) (h : ks.Nodup) :
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

variable [HvisG GF] [HmsG GF] [HasG GF]

private theorem wp_seq_host_nostart_imm' (E : CoPset) (Φ : HostVal → IProp GF) (R : IProp GF)
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

end Client_instantiation_helpers

section Client_instantiation
variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF] [HvisG GF] [HmsG GF]
  [LogrelNaInvs GF] [HasG GF]

attribute [local instance] WasmG.invGS

@[rocq_alias iriswasm.stack_adv_client_instantiate]
def stackAdvClientInstantiate (exp_addrs : List Nat)
    (stack_mod_addr adv_mod_addr client_mod_addr : Nat) : List HostE :=
  [.instantiate (exp_addrs.take 8) stack_mod_addr [],
   .instantiate [exp_addrs.getD 8 0] adv_mod_addr [],
   .instantiate [] client_mod_addr exp_addrs]

omit [LogrelNaInvs GF] in
@[rocq_alias iriswasm.stack_robust.wp_wand_host]
theorem StackRobust.wp_wand_host (s : Stuckness) (E : CoPset) (e : HostExpr)
    (Φ Ψ : HostVal → IProp GF) :
    ⊢ WP e @ s ; E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s ; E {{ Ψ }} := by
  iintro H1 H2
  iapply Iris.wp_wand $$ H1 H2

@[rocq_alias iriswasm.instantiate_client]
theorem instantiate_client (adv_module : Module) (g_ret : Nat) (wret : Value)
    (exp_addrs : List Nat) (stack_mod_addr adv_mod_addr client_mod_addr : Nat) :
    exp_addrs.length = 10 →
    -- we assume the adversary module has an export of type [i32] → [i32]
    ModuleTyping adv_module [] [.func (.tf [.i32] [.i32])] →
    -- that it does not have a start function
    adv_module.start = none →
    -- that it adheres to the module restrictions (i.e. only constant initializers for globals)
    ModuleRestrictions adv_module →
    -- if the adversary module declares a table, there cannot be more initializers than its size
    ModuleElemBoundCheckGmap ∅ [] adv_module →
    -- if the adversary module declares a memory, there cannot be more initializers than its size
    ModuleDataBoundCheckGmap ∅ [] adv_module →
    -- the imported return global has type i32
    typeof wret = .i32 →
    ⊢ iprop(□ ∀ Φ : HostVal → IProp GF,
        (g_ret ↦[wg] (⟨.mut, wret⟩ : Global) ∗
          stack_mod_addr ↪[mods] stackModule ∗
          adv_mod_addr ↪[mods] adv_module ∗
          client_mod_addr ↪[mods] clientModule ∗
          NonAtomicInvariant.own (LogrelNaInvs.logrelNais (GF := GF)) ⊤ ∗
          (∃ name, exp_addrs.getD 9 0 ↪[vis]
            (⟨name, .global (.globalidx g_ret)⟩ : ModuleExport)) ∗
          ownVisPointers (exp_addrs.take 8) ∗
          (∃ vs, exp_addrs.getD 8 0 ↪[vis] vs) ∗
          ↪[frame] emptyFrame) -∗
        (∀ v, (⌜v = HostVal.trapHV⌝ ∨ g_ret ↦[wg] (⟨.mut, xx 2⟩ : Global)) -∗ Φ v) -∗
        WP ((stackAdvClientInstantiate exp_addrs stack_mod_addr adv_mod_addr client_mod_addr,
            []) : HostExpr) @ Stuckness.NotStuck ; ⊤ {{ v, Φ v }}) := by
  intro hlen htyp hnostart hrestrict hboundst hboundsm hgrettyp
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, rfl⟩ :
      ∃ e0 e1 e2 e3 e4 e5 e6 e7 e8 e9, exp_addrs = [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9] := by
    match exp_addrs, hlen with
    | [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9], _ =>
      exact ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, rfl⟩
  obtain ⟨fts, gts, Hbody, Himps, nm, nidx, mf, k, Hexps, Hmf, Hmft, Hk, Hbe⟩ :=
    adv_typing_facts adv_module htyp
  imodintro
  iintro %Φ ⟨Hgret, Hmod_stack, Hmod_adv, Hmod_client, Hown, ⟨%gname, Hvisglob⟩, Hvisvst,
    ⟨%vs, Hvisadv⟩, Hemptyframe⟩ HΦ
  simp only [stackAdvClientInstantiate, List.take, List.getD_cons_succ, List.getD_cons_zero]
  -- the stack module
  have Hvalid := instantiate_stack_spec (GF := GF) .NotStuck ⊤ [e0, e1, e2, e3, e4, e5, e6, e7]
    stack_mod_addr rfl
  simp only [stackInstantiatePara] at Hvalid
  iapply wp_seq_host_nostart_imm' ⊤ Φ _ _ stack_mod_addr [] stackModule _ rfl $$ Hmod_stack
    [Hvisvst]
  · iintro Hmod_stack
    iapply Hvalid $$ Hmod_stack Hvisvst
  iintro ⟨%idf0, %idf1, %idf2, %idf3, %idf4, %idf5, %idf6, %idt, %nm0, %nm1, %nm2, %nm3, %nm4,
    %nm5, %nm6, %nm7, %f0, %f1, %f2, %f3, %f4, %f5, %f6, %istack, %l0, %l1, %l2, %l3, %l4, %l5,
    %l6, %stacktab, %isStack, %newStackAddrIs, HimpsH, HimpsW, %Hnodup, %Hfnodup, %Htablen,
    Hnsa, #Hnewstack, -, -, -, #Hpush, -, #Hmaptrap, #Hstacklen⟩ Hmod_stack
  -- the adversary module
  iapply wp_seq_host_nostart_imm' ⊤ Φ
    iprop(importResourcesHost [] [] ∗
      ∃ inst, instantiationResourcesPostWasm adv_module [] [] ∅ ∅ ∅ ∅ none inst ∗
        moduleExportResourcesHost [e8] adv_module.exports inst)
    _ adv_mod_addr [] adv_module _ hnostart $$ Hmod_adv [Hvisadv]
  · iintro Hmod_adv
    iapply Iris.wp_wand $$ [Hmod_adv Hvisadv]
    · iapply instantiation_spec_operational_no_start .NotStuck ⊤ adv_mod_addr [] [] [e8] adv_module []
        [.func (.tf [.i32] [.i32])] ∅ ∅ ∅ ∅ hnostart htyp hrestrict
      unfold instantiationResourcesPre importResourcesHost exportOwnershipHost
        instantiationResourcesPreWasm importResourcesWasmTypecheck
      unfold_irwt_all
      iframe Hmod_adv
      isplitr
      · iapply BI.BigSepL2.bigSepL2_nil.2; iempintro
      isplitr
      · isplitr
        · isplitr
          · iapply empty_map_check' _ ⟨.nil, empty_dom'⟩
          isplitr
          · iapply empty_map_check' _ ⟨.nil, empty_dom'⟩
          isplitr
          · iapply empty_map_check' _ ⟨.nil, empty_dom'⟩
          iapply empty_map_check' _ ⟨.nil, empty_dom'⟩
        isplitr
        · ipureintro; exact hboundst
        ipureintro; exact hboundsm
      isplitl [Hvisadv]
      · iapply BI.BigSepL.bigSepL_singleton.2
        iexists vs; iexact Hvisadv
      ipureintro; simp [Hexps]
    · iintro %v ⟨%Hv, Hpost⟩
      iunfold instantiationResourcesPost at Hpost
      icases Hpost with ⟨Hmod, Himps, Hpost⟩
      iframe Hmod Himps Hpost
      ipureintro; exact Hv
  iintro ⟨-, ⟨%inst_adv, Hpost, Hexp⟩⟩ Hmod_adv
  have hfc : getImportFuncCount adv_module = 0 := by simp [getImportFuncCount, Himps]
  unfold instantiationResourcesPostWasm moduleInstResourcesWasm moduleExportResourcesHost
  rw [Hexps, hfc, List.drop_zero]
  icases Hexp with ⟨⟨%nm', Hn⟩, -⟩
  icases Hpost with ⟨%g_inits, %tabA, %memA, %globA, %wts', %wms', Himpstyp, %HH, %Htabeq, %Hwts',
    %-, %Hmemeq, %Hwms', %-, %Hgv, %Hgleq, Hresf, Hrest, Hresm, Hresg⟩
  unfold moduleInstResourcesFunc
  ihave ⟨%Hflen, Hresf⟩ := BI.persistent_entails_right BI.BigSepL2.bigSepL2_length $$ Hresf
  obtain ⟨advf, Hadv⟩ : ∃ advf, inst_adv.funcs[nidx]? = some advf := by
    have := (List.getElem?_eq_some_iff.1 Hmf).1
    exact ⟨_, List.getElem?_eq_getElem (Hflen ▸ this)⟩
  ihave ⟨Hadvf, Hcls⟩ := BI.BigSepL2.bigSepL2_lookup_acc Hmf Hadv $$ Hresf
  have hgd : inst_adv.funcs.getD nidx 0 = advf := by simp [List.getD_eq_getElem?_getD, Hadv]
  have htyk : inst_adv.types.getD (match mf.type with | .typeidx k => k) (.tf [] []) =
      .tf [.i32] [.i32] := by
    rw [HH.1, Hmft]; exact Hk
  dsimp only
  rw [hgd, htyk]
  simp only [importResourcesWasmTypecheckSepL2, stackInstVis, expts, funcTypes,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  icases HimpsW with ⟨-, ⟨%cl0, Hcl0, %Hcl0⟩, ⟨%cl1, Hcl1, %Hcl1⟩, ⟨%cl2, Hcl2, %Hcl2⟩,
    ⟨%cl3, Hcl3, %Hcl3⟩, ⟨%cl4, Hcl4, %Hcl4⟩, ⟨%cl5, Hcl5, %Hcl5⟩, ⟨%cl6, Hcl6, %Hcl6⟩,
    ⟨%tab0, %tt0, Htab, %Htab0⟩, -⟩
  have hk7 := nodupKeys_zip' _ [FunctionClosure.funcNative istack (.tf [] [.i32]) l0 f0,
     .funcNative istack (.tf [.i32] [.i32]) l1 f1,
     .funcNative istack (.tf [.i32] [.i32]) l2 f2,
     .funcNative istack (.tf [.i32] [.i32]) l3 f3,
     .funcNative istack (.tf [.i32, .i32] []) l4 f4,
     .funcNative istack (.tf [.i32, .i32] []) l5 f5,
     .funcNative istack (.tf [.i32] [.i32]) l6 f6] Hfnodup
  obtain rfl := Option.some.inj ((LawfulPartialMap.get?_ofList_some (k := idf0)
    (v := (.funcNative istack (.tf [] [.i32]) l0 f0 : FunctionClosure)) (by simp) hk7).symm.trans Hcl0.1)
  obtain rfl := Option.some.inj ((LawfulPartialMap.get?_ofList_some (k := idf1)
    (v := (.funcNative istack (.tf [.i32] [.i32]) l1 f1 : FunctionClosure)) (by simp) hk7).symm.trans Hcl1.1)
  obtain rfl := Option.some.inj ((LawfulPartialMap.get?_ofList_some (k := idf2)
    (v := (.funcNative istack (.tf [.i32] [.i32]) l2 f2 : FunctionClosure)) (by simp) hk7).symm.trans Hcl2.1)
  obtain rfl := Option.some.inj ((LawfulPartialMap.get?_ofList_some (k := idf3)
    (v := (.funcNative istack (.tf [.i32] [.i32]) l3 f3 : FunctionClosure)) (by simp) hk7).symm.trans Hcl3.1)
  obtain rfl := Option.some.inj ((LawfulPartialMap.get?_ofList_some (k := idf4)
    (v := (.funcNative istack (.tf [.i32, .i32] []) l4 f4 : FunctionClosure)) (by simp) hk7).symm.trans Hcl4.1)
  obtain rfl := Option.some.inj ((LawfulPartialMap.get?_ofList_some (k := idf5)
    (v := (.funcNative istack (.tf [.i32, .i32] []) l5 f5 : FunctionClosure)) (by simp) hk7).symm.trans Hcl5.1)
  obtain rfl := Option.some.inj ((LawfulPartialMap.get?_ofList_some (k := idf6)
    (v := (.funcNative istack (.tf [.i32] [.i32]) l6 f6 : FunctionClosure)) (by simp) hk7).symm.trans Hcl6.1)
  obtain ⟨Htab0, ⟨⟩, Htabty⟩ := Htab0
  obtain rfl : tab0 = stacktab := (Option.some.inj ((get?_insert_eq rfl).symm.trans Htab0)).symm
  ihave %Hne0 := @pointsTo_ne GF Nat FunctionClosure NatMap _ WasmG.funcHs _ _ _ _ _ $$ Hadvf Hcl0
  ihave %Hne1 := @pointsTo_ne GF Nat FunctionClosure NatMap _ WasmG.funcHs _ _ _ _ _ $$ Hadvf Hcl1
  ihave %Hne2 := @pointsTo_ne GF Nat FunctionClosure NatMap _ WasmG.funcHs _ _ _ _ _ $$ Hadvf Hcl2
  ihave %Hne3 := @pointsTo_ne GF Nat FunctionClosure NatMap _ WasmG.funcHs _ _ _ _ _ $$ Hadvf Hcl3
  ihave %Hne4 := @pointsTo_ne GF Nat FunctionClosure NatMap _ WasmG.funcHs _ _ _ _ _ $$ Hadvf Hcl4
  ihave %Hne5 := @pointsTo_ne GF Nat FunctionClosure NatMap _ WasmG.funcHs _ _ _ _ _ $$ Hadvf Hcl5
  ihave %Hne6 := @pointsTo_ne GF Nat FunctionClosure NatMap _ WasmG.funcHs _ _ _ _ _ $$ Hadvf Hcl6
  have hnd8 : [idf0, idf1, idf2, idf3, idf4, idf5, idf6, advf].Nodup := by
    simp at Hfnodup ⊢; grind
  have hk8 := nodupKeys_zip' _ [FunctionClosure.funcNative istack (.tf [] [.i32]) l0 f0,
       .funcNative istack (.tf [.i32] [.i32]) l1 f1,
       .funcNative istack (.tf [.i32] [.i32]) l2 f2,
       .funcNative istack (.tf [.i32] [.i32]) l3 f3,
       .funcNative istack (.tf [.i32, .i32] []) l4 f4,
       .funcNative istack (.tf [.i32, .i32] []) l5 f5,
       .funcNative istack (.tf [.i32] [.i32]) l6 f6,
       .funcNative inst_adv (.tf [.i32] [.i32]) mf.locals mf.body] hnd8
  have hnd10 : (List.map (·.desc) ([⟨nm0, .func ⟨idf0⟩⟩, ⟨nm1, .func ⟨idf1⟩⟩, ⟨nm2, .func ⟨idf2⟩⟩, ⟨nm3, .func ⟨idf3⟩⟩,
      ⟨nm4, .func ⟨idf4⟩⟩, ⟨nm5, .func ⟨idf5⟩⟩, ⟨nm6, .func ⟨idf6⟩⟩, ⟨nm7, .table ⟨idt⟩⟩,
      ⟨nm', .func ⟨advf⟩⟩, ⟨gname, .global ⟨g_ret⟩⟩] : List ModuleExport)).Nodup := by
    simp at Hnodup Hfnodup ⊢; grind
  iapply instantiation_spec_operational_start .NotStuck ⊤ client_mod_addr
    [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9] [⟨nm0, .func ⟨idf0⟩⟩, ⟨nm1, .func ⟨idf1⟩⟩, ⟨nm2, .func ⟨idf2⟩⟩, ⟨nm3, .func ⟨idf3⟩⟩,
      ⟨nm4, .func ⟨idf4⟩⟩, ⟨nm5, .func ⟨idf5⟩⟩, ⟨nm6, .func ⟨idf6⟩⟩, ⟨nm7, .table ⟨idt⟩⟩,
      ⟨nm', .func ⟨advf⟩⟩, ⟨gname, .global ⟨g_ret⟩⟩]
    [] clientModule (clientFuncImpts ++ clientGlobImpts) [] (PartialMap.ofList ([idf0, idf1, idf2, idf3, idf4, idf5, idf6, advf].zip
      [.funcNative istack (.tf [] [.i32]) l0 f0,
       .funcNative istack (.tf [.i32] [.i32]) l1 f1,
       .funcNative istack (.tf [.i32] [.i32]) l2 f2,
       .funcNative istack (.tf [.i32] [.i32]) l3 f3,
       .funcNative istack (.tf [.i32, .i32] []) l4 f4,
       .funcNative istack (.tf [.i32, .i32] []) l5 f5,
       .funcNative istack (.tf [.i32] [.i32]) l6 f6,
       .funcNative inst_adv (.tf [.i32] [.i32]) mf.locals mf.body]))
    (insert (∅ : NatMap Tableinst) idt tab0) ∅ (PartialMap.singleton g_ret ⟨.mut, wret⟩) 8 Φ rfl
    client_module_typing ⟨⟨[], rfl⟩, ⟨[Wasm.Int.intOfZ 0], rfl⟩, ⟨[], rfl⟩⟩ $$ Hemptyframe
    [Hmod_client HimpsH Hn Hvisglob Hcl0 Hcl1 Hcl2 Hcl3 Hcl4 Hcl5 Hcl6 Htab Hadvf Hgret]
  · unfold instantiationResourcesPre instantiationResourcesPreWasm exportOwnershipHost
    iframe Hmod_client
    isplitl [HimpsH Hn Hvisglob]
    · unfold importResourcesHost
      rw [show [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9] = [e0, e1, e2, e3, e4, e5, e6, e7] ++ [e8, e9]
        from rfl, show ([⟨nm0, .func ⟨idf0⟩⟩, ⟨nm1, .func ⟨idf1⟩⟩, ⟨nm2, .func ⟨idf2⟩⟩,
          ⟨nm3, .func ⟨idf3⟩⟩, ⟨nm4, .func ⟨idf4⟩⟩, ⟨nm5, .func ⟨idf5⟩⟩, ⟨nm6, .func ⟨idf6⟩⟩,
          ⟨nm7, .table ⟨idt⟩⟩, ⟨nm', .func ⟨advf⟩⟩, ⟨gname, .global ⟨g_ret⟩⟩] : List ModuleExport) =
        [⟨nm0, .func ⟨idf0⟩⟩, ⟨nm1, .func ⟨idf1⟩⟩, ⟨nm2, .func ⟨idf2⟩⟩, ⟨nm3, .func ⟨idf3⟩⟩,
          ⟨nm4, .func ⟨idf4⟩⟩, ⟨nm5, .func ⟨idf5⟩⟩, ⟨nm6, .func ⟨idf6⟩⟩, ⟨nm7, .table ⟨idt⟩⟩] ++ [⟨nm', .func ⟨advf⟩⟩, ⟨gname, .global ⟨g_ret⟩⟩] from rfl]
      iapply (BI.BigSepL2.bigSepL2_append (l1a := [e0, e1, e2, e3, e4, e5, e6, e7])
        (l2a := ([⟨nm0, .func ⟨idf0⟩⟩, ⟨nm1, .func ⟨idf1⟩⟩, ⟨nm2, .func ⟨idf2⟩⟩, ⟨nm3, .func ⟨idf3⟩⟩,
          ⟨nm4, .func ⟨idf4⟩⟩, ⟨nm5, .func ⟨idf5⟩⟩, ⟨nm6, .func ⟨idf6⟩⟩, ⟨nm7, .table ⟨idt⟩⟩] : List ModuleExport)) (Or.inl rfl)).2
      isplitl [HimpsH]
      · iexact HimpsH
      iapply BI.BigSepL2.bigSepL2_cons.2
      isplitl [Hn]
      · iexact Hn
      iapply BI.BigSepL2.bigSepL2_singleton.2
      iexact Hvisglob
    isplitl
    · isplitl
      · iapply (irwt_nodup_equiv _ _ _ _ _ _ hnd10).2
        simp only [importResourcesWasmTypecheckSepL2, importResourcesWasmDomcheck, clientFuncImpts,
          clientGlobImpts, expts, funcTypes, List.map_cons, List.map_nil, List.cons_append,
          List.nil_append]
        isplitr
        · ipureintro
          refine ⟨fun k => ?_, fun k => ?_, fun k => ?_, fun k => ?_⟩
          · simp only [List.zip_cons_cons, List.zip_nil_left, LawfulPartialMap.ofList_cons,
              LawfulPartialMap.dom_insert_iff]
            simp [PartialMap.ofList, PartialMap.dom, get?_empty, extFuncAddrs, extFuncs, @eq_comm _ k]
          · simp only [PartialMap.dom]
            by_cases h : idt = k <;>
              simp [h, get?_insert_eq, get?_insert_ne, get?_empty, extTabAddrs, extTabs, @eq_comm _ k]
          · simp [PartialMap.dom, get?_empty, extMemAddrs, extMems]
          · simp only [PartialMap.dom, PartialMap.singleton]
            by_cases h : g_ret = k <;>
              simp [h, get?_insert_eq, get?_insert_ne, get?_empty, extGlobAddrs, extGlobs, @eq_comm _ k]
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
        · iexists _, _; iframe Htab
          ipureintro; exact ⟨get?_insert_eq rfl, rfl, Htabty⟩
        iapply BI.BigSepL2.bigSepL2_cons.2
        isplitl [Hadvf]
        · iexists _; iframe Hadvf
          ipureintro; exact ⟨LawfulPartialMap.get?_ofList_some (by simp) hk8, rfl⟩
        iapply BI.BigSepL2.bigSepL2_cons.2
        isplitl [Hgret]
        · iexists _, _; iframe Hgret
          ipureintro; exact ⟨get?_insert_eq rfl, rfl, by simp [globalAgree, hgrettyp]⟩
        iapply BI.BigSepL2.bigSepL2_nil.2
        iempintro
      isplit
      · ipureintro
        intro e he
        simp [clientModule] at he
        subst he
        simp [assertConst1I32, i32const, extTabs, get?_insert_eq]
        exact (show 1 ≤ tab0.entries.size by simpa only [Tableinst.length_data] using Htablen)
      · ipureintro
        intro d hd
        simp [clientModule] at hd
    isplitr
    · iapply BI.BigSepL.bigSepL_nil.2; iempintro
    · ipureintro; rfl
  iintro %idnstart Hf Hpost
  unfold instantiationResourcesPost instantiationResourcesPostWasm moduleInstResourcesWasm
  icases Hpost with ⟨-, -, %inst, ⟨%g_inits', %tabA', %memA', %globA', %wts'', %wms'', Hirwt,
    %HH', %-, %Hwts'', %-, %-, %-, %-, %-, %-, Hrf, -⟩, -⟩
  ihave Hirwt := (irwt_nodup_equiv _ _ _ _ _ _ hnd10).1 $$ Hirwt
  simp only [importResourcesWasmTypecheckSepL2, clientFuncImpts, clientGlobImpts, expts, funcTypes,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  icases Hirwt with ⟨-, ⟨%c0, Hc0, %Hc0⟩, ⟨%c1, Hc1, %Hc1⟩, ⟨%c2, Hc2, %Hc2⟩,
    ⟨%c3, Hc3, %Hc3⟩, ⟨%c4, Hc4, %Hc4⟩, ⟨%c5, Hc5, %Hc5⟩, ⟨%c6, Hc6, %Hc6⟩,
    ⟨%tab, %tt, Htabr, %Htabr⟩, ⟨%cadv, Hca, %Hca⟩, ⟨%g, %gt, Hg, %Hgl⟩, -⟩
  obtain rfl : c0 = FunctionClosure.funcNative istack (.tf [] [.i32]) l0 f0 := Option.some.inj (Hc0.1.symm.trans
    (LawfulPartialMap.get?_ofList_some (by simp) hk8))
  obtain rfl : c1 = FunctionClosure.funcNative istack (.tf [.i32] [.i32]) l1 f1 := Option.some.inj (Hc1.1.symm.trans
    (LawfulPartialMap.get?_ofList_some (by simp) hk8))
  obtain rfl : c2 = FunctionClosure.funcNative istack (.tf [.i32] [.i32]) l2 f2 := Option.some.inj (Hc2.1.symm.trans
    (LawfulPartialMap.get?_ofList_some (by simp) hk8))
  obtain rfl : c3 = FunctionClosure.funcNative istack (.tf [.i32] [.i32]) l3 f3 := Option.some.inj (Hc3.1.symm.trans
    (LawfulPartialMap.get?_ofList_some (by simp) hk8))
  obtain rfl : c4 = FunctionClosure.funcNative istack (.tf [.i32, .i32] []) l4 f4 := Option.some.inj (Hc4.1.symm.trans
    (LawfulPartialMap.get?_ofList_some (by simp) hk8))
  obtain rfl : c5 = FunctionClosure.funcNative istack (.tf [.i32, .i32] []) l5 f5 := Option.some.inj (Hc5.1.symm.trans
    (LawfulPartialMap.get?_ofList_some (by simp) hk8))
  obtain rfl : c6 = FunctionClosure.funcNative istack (.tf [.i32] [.i32]) l6 f6 := Option.some.inj (Hc6.1.symm.trans
    (LawfulPartialMap.get?_ofList_some (by simp) hk8))
  obtain rfl : cadv = FunctionClosure.funcNative inst_adv (.tf [.i32] [.i32]) mf.locals mf.body := Option.some.inj (Hca.1.symm.trans
    (LawfulPartialMap.get?_ofList_some (by simp) hk8))
  obtain rfl : g = ⟨.mut, wret⟩ := Option.some.inj (Hgl.1.symm.trans (get?_insert_eq rfl))
  obtain ⟨Hity, ⟨tf, Htf⟩, ⟨tt', Htt⟩, -, ⟨tg, Htg⟩, Hcs⟩ := HH'
  have hf0 : inst.funcs[0]? = some idf0 := by rw [← Htf]; rfl
  have hf4 : inst.funcs[4]? = some idf4 := by rw [← Htf]; rfl
  have hf5 : inst.funcs[5]? = some idf5 := by rw [← Htf]; rfl
  have hf6 : inst.funcs[6]? = some idf6 := by rw [← Htf]; rfl
  have hf7 : inst.funcs[7]? = some advf := by rw [← Htf]; rfl
  have ht0 : inst.tab[0]? = some idt := by rw [← Htt]; rfl
  have hg0 : inst.globs[0]? = some g_ret := by rw [← Htg]; rfl
  have hs : inst.funcs[8]? = some idnstart := of_decide_eq_true Hcs
  obtain rfl : tab = tableInitReplaceSingle tab0 (natOfInt (Wasm.Int.repr (w := 32) 0))
      [some advf] := by
    have h := Htabr.1
    subst Hwts''
    simp [moduleImportInitTabs, clientModule, getImportTableCount, ht0, get?_insert_eq,
      lookupFuncaddr, hf7] at h
    exact h.symm
  rw [show clientModule.funcs = [⟨.typeidx 0, [.i32], main⟩] from rfl]
  unfold moduleInstResourcesFunc
  ihave ⟨%a', %xs', %hfd, Hidn, -⟩ := BI.BigSepL2.bigSepL2_cons_inv_left.1 $$ Hrf
  have ha' : a' = idnstart := by
    rw [show getImportFuncCount clientModule = 8 from rfl] at hfd
    have := congrArg (·[0]?) hfd; simp at this; rw [hs] at this; exact (Option.some.inj this).symm
  subst ha'
  rw [Hity]
  ihave Hresf := Hcls $$ Hca
  subst Hwts' Hwms' Htabeq Hmemeq Hgleq
  ihave HR : moduleInstResourcesWasm adv_module inst_adv (moduleInstBuildTables adv_module inst_adv)
      (moduleInstBuildMems adv_module inst_adv)
      (moduleInstGlobalInit (moduleInstBuildGlobals adv_module.globals) g_inits)
      $$ [Hresf Hrest Hresm Hresg]
  · unfold moduleInstResourcesWasm moduleInstResourcesFunc
    rw [hfc, List.drop_zero]; iframe
  iapply Iris.fupd_wp
  imod interp_instance_alloc [] ⊤ adv_module [] [.func (.tf [.i32] [.i32])] [] ∅ ∅ ∅ ∅ inst_adv
    fts gts g_inits Hbody ⟨HH.1, by simp [extFuncAddrs, extTabAddrs, extMemAddrs, extGlobAddrs,
      extFuncs, extTabs, extMems, extGlobs]⟩ Hgv.1
    $$ [] [] [] [Himpstyp] HR with ⟨#Hi, Hinvs, -⟩
  · iapply BI.BigSepM.bigSepM_empty.2; iempintro
  · iapply BI.BigSepM.bigSepM_empty.2; iempintro
  · iapply BI.BigSepM.bigSepM_empty.2; iempintro
  · unfold importResourcesWasmTypecheck; unfold_irwt_all; iexact Himpstyp
  unfold moduleInstResourcesWasmInvs moduleInstResourcesFuncInvs
  icases Hinvs with ⟨Hires, -⟩
  rw [hfc, List.drop_zero]
  ihave #Ha := BI.BigSepL2.bigSepL2_lookup Hmf Hadv $$ Hires
  rw [htyk]
  imodintro
  dsimp only
  rw [show clientModule.types.getD 0 (FunctionType.tf [] []) = .tf [] [] from rfl]
  iapply wp_lift_wasm .NotStuck ⊤ [] [.invoke a'] Φ
  have hms := main_spec (GF := GF) _ g_ret idt mf.locals mf.body ⟨nZeros [.i32], inst⟩ advf inst_adv
    idf0 l0 f0 idf4 l4 f4 idf5 l5 f5 idf6 l6 f6 istack isStack newStackAddrIs tab0 ⟨rfl, rfl⟩ hg0 ht0
    hf0 hf4 hf5 hf6 rfl Htablen Hbe
  iapply wp_wand_s $$ [Hf Hidn Hown Hg Hc0 Hc4 Hc5 Hc6 Htabr Hnsa]
  · iapply client_start_spec inst a' _ _ _ hms $$ Hf [Hidn] [Hown Hg Hc0 Hc4 Hc5 Hc6 Htabr Hnsa]
    · iexact Hidn
    iframe
    iframe Ha Hi Hnewstack Hpush Hmaptrap Hstacklen
  iintro %w ⟨Hw, -⟩
  icases Hw with (%Hw | ⟨%Hw, Hg, -⟩)
  · subst Hw
    iapply IrisHost.wp_value .NotStuck ⊤ _ .trapHV Φ
      (show hostToVal (([], ofVal Val.trapV) : HostExpr) = some .trapHV from
        IrisHost.to_of_val .trapHV)
    iapply HΦ; ileft; ipureintro; rfl
  · subst Hw
    iapply IrisHost.wp_value .NotStuck ⊤ _ (.immHV []) Φ
      (show hostToVal (([], ofVal (Val.immV [])) : HostExpr) = some (.immHV []) from
        IrisHost.to_of_val (.immHV []))
    iapply HΦ; iright; iexact Hg

end Client_instantiation

end IrisWasm.Examples.Stack
