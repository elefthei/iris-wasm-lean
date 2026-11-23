/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Host.IrisHost
import IrisWasm.Logrel.IrisInterpInstanceAlloc
import IrisWasm.Rules.IrisExampleHelper
import Wasm.ModuleValidation

/-! Port of `theories/iris/examples/iris_robust_example.v`.

The Coq section notation `{{{{ P }}}} es {{{{ v, Q }}}}` (persistent Hoare quadruple,
`□ ∀ Φ, P -∗ (∀ v, Q -∗ Φ v) -∗ WP es @ NotStuck ; ⊤ {{ v, Φ v }}`) is written out in the
statements below. -/

namespace IrisWasm.Examples

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm IrisWasm
open scoped Iris.Std.PartialMap

/-- Coq `String.list_byte_of_string` (ASCII strings only). -/
def nameOfString (s : String) : Name := s.toList.map fun c => BitVec.ofNat 8 c.toNat

section Examples
variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF] [LogrelNaInvs GF]

attribute [local instance] WasmG.invGS

local notation "logrelNais" => LogrelNaInvs.logrelNais (GF := GF)

omit [LogrelNaInvs GF] in
private theorem wp_wand_s {s : Stuckness} {E : CoPset} {e : Expr} {Φ Ψ : Val → IProp GF} :
    iprop(WP e @ s ; E {{ Φ }}) ⊢ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s ; E {{ Ψ }} :=
  IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)

omit [LogrelNaInvs GF] in
private theorem fupd_wp_s {s : Stuckness} {E : CoPset} {e : Expr} {Φ : Val → IProp GF} :
    iprop(|={E}=> WP e @ s ; E {{ Φ }}) ⊢ WP e @ s ; E {{ Φ }} :=
  IrisWp.fupd_wp (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)

/-- Store 42 to the memory, invoke an external function, and load the memory entry again.
This program is called 'return' because the value is returned instead of being set to a
global. -/
@[rocq_alias iriswasm.lse_expr_return]
def lseExprReturn (a : Nat) : List BasicInstruction :=
  [.const (xx 0), .const (xx 42), .store .i32 none ⟨0, 0, 0⟩, .call a, .const (xx 0),
   .load .i32 none ⟨0, 0, 0⟩]

@[rocq_alias iriswasm.lse_return]
def lseReturn (a : Nat) : Expr := toEList (lseExprReturn a)

@[rocq_alias iriswasm.lse_return_spec]
theorem lse_return_spec (f : Frame) (n j a : Nat) (C : TContext) (i : Instance)
    (es : List BasicInstruction) (locs : List ValueType)
    (hC : C.label = [] ∧ C.return_ = none)
    (hn : f.inst.memory[0]? = some n) (ha : f.inst.funcs[j]? = some a)
    (hes : BeTyping (updLocalLabelReturn C locs [[]] (some [])) es (.tf [] [])) :
    ⊢ iprop(□ ∀ Φ : Val → IProp GF,
        (↪[frame] f ∗
          NonAtomicInvariant.own logrelNais ⊤ ∗
          NonAtomicInvariant.inv logrelNais (wfN a)
            iprop(a ↦[wf] (.funcNative i (.tf [] []) locs es)) ∗
          interpInstance C [] i ∗
          ∃ c, n ↦[wms][ 0 ] (bits (.int32 c))) -∗
        (∀ w, ((⌜w = .trapV⌝ ∨ (⌜w = .immV [xx 42]⌝ ∗
              n ↦[wms][ 0 ] (bits (xx 42)) ∗
              NonAtomicInvariant.own logrelNais ⊤)) ∗ ↪[frame] f) -∗ Φ w) -∗
        WP (lseReturn j) @ Stuckness.NotStuck ; ⊤ {{ v, Φ v }}) := by
  imodintro
  iintro %Φ ⟨Hf, Hown, #Ha, #Hi, ⟨%c, Hn⟩⟩ HΦ
  iapply wp_wand_s $$ [-HΦ] HΦ
  rw [show lseReturn j = ([.basic (.const (xx 0)), .basic (.const (xx 42)),
      .basic (.store .i32 none ⟨0, 0, 0⟩)] : Expr) ++
      [.basic (.call j), .basic (.const (xx 0)), .basic (.load .i32 none ⟨0, 0, 0⟩)] from rfl]
  iapply wp_seq _ _ _ (fun w => iprop((⌜w = .immV []⌝ ∗ n ↦[wms][ 0 ] (bits (xx 42))) ∗
    ↪[frame] f))
  isplitr
  · iintro ⟨⟨%H, -⟩, -⟩; cases H
  isplitl [Hf Hn]
  · have H := wp_store (GF := GF) (x := 0) (fun w => iprop(⌜w = Val.immV []⌝))
      .NotStuck ⊤ .i32 (xx 42)
      (bits (.int32 c)) 0 0 (.i32 (Wasm.Int.intOfZ 0)) n f rfl
      (by simp [bits, lengthT, serialiseI32, length_encodeInt]) hn
    rw [show (AddressOperand.i32 (Wasm.Int.intOfZ 0)).unsigned + 0 = 0 from rfl] at H
    simp only [xx] at H ⊢
    iapply H
    iframe
    inext; ipureintro; trivial
  iintro %w ⟨⟨%hw, Hn⟩, Hf⟩
  subst hw
  simp only [ofVal, vToEList, List.map_nil, List.nil_append]
  rw [show ([.basic (.call j), .basic (.const (xx 0)),
      .basic (.load .i32 none ⟨0, 0, 0⟩)] : Expr) =
    [] ++ [.basic (.call j)] ++
      [.basic (.const (xx 0)), .basic (.load .i32 none ⟨0, 0, 0⟩)] from rfl]
  iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).2
  iapply wp_base_push rfl
  iapply wp_call_ctx .NotStuck ⊤ _ f j a 0 _ ha $$ Hf
  inext; iintro Hf
  simp only [frameBase, List.append_nil]
  rw [show ([.invoke a] : Expr) = [.invoke a] ++ [] from rfl]
  iapply wp_seq_can_trap_same_ctx
    (fun w => iprop(⌜w = .trapV⌝ ∨ (⌜w = .immV [xx 42]⌝ ∗
      n ↦[wms][ 0 ] (bits (xx 42)) ∗ NonAtomicInvariant.own logrelNais ⊤)))
    (fun w => iprop(interpValues [] w ∗ NonAtomicInvariant.own logrelNais ⊤))
  isplitr
  · iintro ⟨H, -⟩
    iunfold interpValues at H
    icases H with ⟨%ws, %H, -⟩; cases H
  isplitr
  · ileft; ipureintro; rfl
  iframe Hf
  isplitl [Hown]
  · iintro Hf
    iapply fupd_wp_s
    imod NonAtomicInvariant.inv_acc CoPset.subseteq_top CoPset.subseteq_top $$ Ha Hown with
      ⟨>Haf, Hown, Hcls⟩
    imodintro
    rw [show ([.invoke a] : Expr) = [] ++ [.invoke a] from rfl]
    iapply wp_invoke_native .NotStuck ⊤ _ [] [] [] [] locs a es i 0 f rfl rfl rfl $$ Hf Haf
    inext
    iintro ⟨Hf, Haf⟩
    iapply fupd_wp_s
    imod Hcls $$ [Haf Hown] with Hown
    · iframe
    imodintro
    ihave Hl := be_fundamental_local (GF := GF) C es [] [] locs hC hes
    iunfold semanticTypingLocalNoHost at Hl
    icases Hl with ⟨-, Hl⟩
    iunfold interpExpressionClosureNoHost at Hl
    ihave H := Hl $$ %i Hi %f %(nZeros locs) Hf Hown []
    · iunfold interpVal
      iright
      iunfold interpValues
      iexists nZeros locs
      isplitr; · ipureintro; rfl
      simp only [List.nil_append]
      iapply n_zeros_interp_values
    simp only [List.nil_append]
    iapply wp_wand_s $$ H
    iintro %v ⟨⟨Hv, Hown⟩, Hf⟩
    iframe Hf
    iunfold interpVal at Hv
    icases Hv with (%Hv | Hv)
    · ileft; ipureintro; exact Hv
    · iright; iframe
  iintro %w ⟨⟨Hw, Hown⟩, Hf⟩
  iunfold interpValues at Hw
  icases Hw with ⟨%ws, %Hw, Hws⟩
  subst Hw
  ihave %Hlen := BI.BigSepL2.bigSepL2_length $$ Hws
  cases ws with
  | cons _ _ => simp at Hlen
  | nil =>
  iapply wp_base_pull
  simp only [pullBase, ofVal, vToEList, List.map_nil, List.nil_append, List.append_nil]
  iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).1
  have H := wp_load (GF := GF) (x := 0) (fun w => iprop(⌜w = Val.immV [xx 42]⌝))
    .NotStuck ⊤ .i32 (xx 42)
    0 0 (.i32 (Wasm.Int.intOfZ 0)) n f rfl hn
  rw [show (AddressOperand.i32 (Wasm.Int.intOfZ 0)).unsigned + 0 = 0 from rfl] at H
  simp only [xx] at H ⊢
  iapply wp_wand_s $$ [Hn Hf]
  · iapply H
    iframe
    inext; ipureintro; trivial
  iintro %v ⟨⟨%Hv, Hn⟩, Hf⟩
  iframe Hf
  iright
  iframe
  ipureintro; exact Hv

/-- Setting the memory value to a global instead of returning it. -/
@[rocq_alias iriswasm.lse_expr]
def lseExpr (a n : Nat) : List BasicInstruction :=
  [.const (xx 0), .const (xx 42), .store .i32 none ⟨0, 0, 0⟩, .call a, .const (xx 0),
   .load .i32 none ⟨0, 0, 0⟩, .setGlobal n]

@[rocq_alias iriswasm.lse]
def lse (a n : Nat) : Expr := toEList (lseExpr a n)

@[rocq_alias iriswasm.lse_spec]
theorem lse_spec (f : Frame) (n j a : Nat) (C : TContext) (i : Instance)
    (es : List BasicInstruction) (g k : Nat) (locs : List ValueType)
    (hC : C.label = [] ∧ C.return_ = none)
    (hn : f.inst.memory[0]? = some n) (ha : f.inst.funcs[j]? = some a)
    (hg : f.inst.globs[g]? = some k)
    (hes : BeTyping (updLocalLabelReturn C locs [[]] (some [])) es (.tf [] [])) :
    ⊢ iprop(□ ∀ Φ : Val → IProp GF,
        (↪[frame] f ∗
          NonAtomicInvariant.own logrelNais ⊤ ∗
          NonAtomicInvariant.inv logrelNais (wfN a)
            iprop(a ↦[wf] (.funcNative i (.tf [] []) locs es)) ∗
          interpInstance C [] i ∗
          (∃ gv, k ↦[wg] (⟨.mut, gv⟩ : Global)) ∗
          ∃ c, n ↦[wms][ 0 ] (bits (.int32 c))) -∗
        (∀ w, ((⌜w = .trapV⌝ ∨ (⌜w = .immV []⌝ ∗
              k ↦[wg] (⟨.mut, xx 42⟩ : Global) ∗
              n ↦[wms][ 0 ] (bits (xx 42)) ∗
              NonAtomicInvariant.own logrelNais ⊤)) ∗ ↪[frame] f) -∗ Φ w) -∗
        WP (lse j g) @ Stuckness.NotStuck ; ⊤ {{ v, Φ v }}) := by
  imodintro
  iintro %Φ ⟨Hf, Hown, #Ha, #Hi, ⟨%gv, Hg⟩, ⟨%c, Hn⟩⟩ HΦ
  iapply wp_wand_s $$ [-HΦ] HΦ
  rw [show lse j g = lseReturn j ++ [.basic (.setGlobal g)] from rfl]
  iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).2
  iapply wp_seq_can_trap_same_ctx
    (fun w => iprop(⌜w = .trapV⌝ ∨ (⌜w = .immV []⌝ ∗ k ↦[wg] (⟨.mut, xx 42⟩ : Global) ∗
      n ↦[wms][ 0 ] (bits (xx 42)) ∗ NonAtomicInvariant.own logrelNais ⊤)))
    (fun w => iprop((⌜w = .immV [xx 42]⌝ ∗ n ↦[wms][ 0 ] (bits (xx 42)) ∗
      NonAtomicInvariant.own logrelNais ⊤) ∗ k ↦[wg] (⟨.mut, gv⟩ : Global)))
  isplitr
  · iintro ⟨⟨%H, -, -⟩, -⟩; cases H
  isplitr
  · ileft; ipureintro; rfl
  iframe Hf
  isplitl [Hown Hn Hg]
  · iintro Hf
    iapply (lse_return_spec f n j a C i es locs hC hn ha hes) $$ [Hf Hown Hn] [Hg]
    · iframe Hf Hown Ha Hi
      iexists c; iexact Hn
    · iintro %w ⟨Hw, Hf⟩
      iframe Hf
      icases Hw with (%Hw | ⟨%Hw, Hn, Hown⟩)
      · ileft; ipureintro; exact Hw
      · iright; iframe; ipureintro; exact Hw
  iintro %w ⟨⟨⟨%Hw, Hn, Hown⟩, Hg⟩, Hf⟩
  subst Hw
  simp only [ofVal, vToEList, List.map_cons, List.map_nil]
  iapply wp_base_pull
  simp only [pullBase, List.nil_append, List.append_nil, List.cons_append]
  iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).1
  have H := wp_set_global (GF := GF) .NotStuck ⊤ (xx 42) f g (fun w => iprop(⌜w = Val.immV []⌝))
    ⟨.mut, gv⟩ k hg
  iapply wp_wand_s $$ [Hf Hg]
  · iapply H $$ [] Hf Hg
    inext; ipureintro; rfl
  iintro %v ⟨%Hv, Hg, Hf⟩
  iframe Hf
  iright
  iframe
  ipureintro; exact Hv

/-- Running the start function of `lseModule` from the empty frame (Lean helper factored out of
Coq's `instantiate_lse`; `n`, `a`, `k` are the instance's memory, imported function and imported
global). -/
theorem RobustAux.lse_start_spec (inst : Instance) (idnstart n a k : Nat) (C : TContext)
    (i : Instance) (es : List BasicInstruction) (locs : List ValueType)
    (hC : C.label = [] ∧ C.return_ = none)
    (hn : inst.memory[0]? = some n) (ha : inst.funcs[0]? = some a)
    (hk : inst.globs[0]? = some k)
    (hes : BeTyping (updLocalLabelReturn C locs [[]] (some [])) es (.tf [] [])) :
    ⊢ iprop((↪[frame] emptyFrame : IProp GF) -∗
      idnstart ↦[wf] (.funcNative inst (.tf [] []) [] (lseExpr 0 0)) -∗
      NonAtomicInvariant.own logrelNais ⊤ -∗
      NonAtomicInvariant.inv logrelNais (wfN a)
        iprop(a ↦[wf] (.funcNative i (.tf [] []) locs es)) -∗
      interpInstance C [] i -∗
      (∃ gv, k ↦[wg] (⟨.mut, gv⟩ : Global)) -∗
      (∃ c, n ↦[wms][ 0 ] (bits (.int32 c))) -∗
      WP ([.invoke idnstart] : Expr) @ Stuckness.NotStuck ; ⊤
        {{ w, (⌜w = Val.trapV⌝ ∨ (⌜w = Val.immV []⌝ ∗ k ↦[wg] (⟨.mut, xx 42⟩ : Global))) ∗
          ↪[frame] emptyFrame }}) := by
  iintro Hf Hcl Hown #Ha #Hi Hg Hn
  rw [show ([.invoke idnstart] : Expr) = [] ++ [.invoke idnstart] from rfl]
  iapply wp_invoke_native .NotStuck ⊤ _ [] [] [] [] [] idnstart (lseExpr 0 0) inst 0 emptyFrame
    rfl rfl rfl $$ Hf Hcl
  inext
  iintro ⟨Hf, -⟩
  have hfb := wp_frame_bind (GF := GF) .NotStuck ⊤
    (fun w => iprop((⌜w = .trapV⌝ ∨ (⌜w = .immV []⌝ ∗ k ↦[wg] (⟨.mut, xx 42⟩ : Global))) ∗
      ↪[frame] emptyFrame)) 0 ⟨[] ++ nZeros [], inst⟩ emptyFrame
    [.label 0 [] (toEList (lseExpr 0 0))] (toVal_native_frame_none _ _ _)
  unfold wpWasmFrame at hfb
  iapply hfb $$ Hf
  iintro Hf
  iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).2
  iapply wp_label_push_nil
  iapply wp_ctx_bind _ _ _ _ 1 (pushBase (.base [] []) 0 [] [] []) (by simp [BaseIsEmpty, pushBase])
  simp only [List.nil_append]
  rw [show toEList (lseExpr 0 0) = lse 0 0 from rfl]
  iapply wp_wand_s $$ [Hf Hown Hg Hn]
  · iapply (lse_spec ⟨nZeros [], inst⟩ n 0 a C i es 0 k locs hC hn ha hk hes) $$
      [Hf Hown Hg Hn] []
    · iframe Hf Hown Ha Hi Hg Hn
    · iintro %w Hw; iexact Hw
  iintro %w ⟨Hw, Hf⟩
  icases Hw with (%Hw | ⟨%Hw, Hg, -, -⟩)
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
      (fun w => iprop(⌜w = Val.trapV⌝ ∨ (⌜w = Val.immV []⌝ ∗ k ↦[wg] (⟨.mut, xx 42⟩ : Global))))
      0 ⟨nZeros [], inst⟩ emptyFrame
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
      (fun w => iprop(⌜w = Val.trapV⌝ ∨ (⌜w = Val.immV []⌝ ∗ k ↦[wg] (⟨.mut, xx 42⟩ : Global))))
      [] 0 ⟨nZeros [], inst⟩ emptyFrame [] rfl rfl
    unfold wpWasmFrame at hv
    rw [show ofVal (Val.immV []) = ([] : Expr) from rfl]
    iapply hv $$ Hf0
    inext; iright; iframe; ipureintro; rfl

end Examples

section Examples_host
variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF] [HvisG GF] [HmsG GF] [HasG GF]
  [LogrelNaInvs GF]

attribute [local instance] WasmG.invGS

local notation "logrelNais" => LogrelNaInvs.logrelNais (GF := GF)

@[rocq_alias iriswasm.iris_robust_example.wp_wand_host]
theorem wp_wand_host (s : Stuckness) (E : CoPset) (e : HostExpr) (Φ Ψ : HostVal → IProp GF) :
    ⊢ WP e @ s ; E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s ; E {{ Ψ }} := by
  iintro Hwp H
  iapply Iris.wp_wand $$ Hwp H

@[rocq_alias iriswasm.lse_module]
def lseModule : Module where
  types := [.tf [] [], .tf [] []]
  funcs := [{ type := .typeidx 0, locals := [], body := lseExpr 0 0 }]
  tables := []
  mems := [{ address := .i32, limits := ⟨1, none⟩ }]
  globals := []
  elem := []
  data := []
  start := some { func := .funcidx 1 }
  imports := [
    { module := nameOfString "Adv", name := nameOfString "adv_call", desc := .func 0 },
    { module := nameOfString "Ret", name := nameOfString "ret_glob",
      desc := .global { mut_ := .mut, t := .i32 } }]
  exports := []

@[rocq_alias iriswasm.iris_robust_example.lse_func_impts]
def lseFuncImpts : List ExternT := [.func (.tf [] [])]

@[rocq_alias iriswasm.lse_glob_impts]
def lseGlobImpts : List ExternT := [.glob { mut_ := .mut, t := .i32 }]

@[rocq_alias iriswasm.iris_robust_example.lse_module_typing]
theorem lse_module_typing : ModuleTyping lseModule (lseFuncImpts ++ lseGlobImpts) [] := by
  apply (validateModule_iff _ ⟨_, _⟩).mp
  rfl

@[rocq_alias iriswasm.iris_robust_example.module_restrictions_lse]
theorem module_restrictions_lse : ModuleRestrictions lseModule :=
  ⟨⟨[], rfl⟩, ⟨[], rfl⟩, ⟨[], rfl⟩⟩

@[rocq_alias iriswasm.iris_robust_example.adv_lse_instantiate]
def advLseInstantiate (g : Nat) : List HostE :=
  [.instantiate [0] 0 [], .instantiate [] 1 [0, 1], .getGlobal g]

omit [WasmG hlc GF] [HvisG GF] [HmsG GF] [HasG GF] [LogrelNaInvs GF] in
private theorem forall2_lookup_r' {A B : Type} {R : A → B → Prop} {l1 : List A} {l2 : List B}
    (h : Wasm.List.Forall₂ R l1 l2) {i : Nat} {b : B} (hb : l2[i]? = some b) :
    ∃ a, l1[i]? = some a ∧ R a b := by
  induction h generalizing i with
  | nil => simp at hb
  | cons hab _ ih =>
    cases i with
    | zero => simp at hb; subst hb; exact ⟨_, rfl, hab⟩
    | succ i => simpa using ih (by simpa using hb)

omit [HvisG GF] [HmsG GF] [HasG GF] [LogrelNaInvs GF] in
/-- An empty resource map together with a true side condition (Lean helper). -/
theorem RobustAux.empty_map_check {V : Type} (Φ : Nat → V → IProp GF) {φ : Prop} (hφ : φ) :
    ⊢ iprop(([∗map] k ↦ x ∈ (∅ : NatMap V), Φ k x) ∗ ⌜φ⌝) :=
  BI.emp_sep.2.trans (BI.sep_mono BI.BigSepM.bigSepM_empty_intro (BI.pure_intro hφ))

omit [HvisG GF] [HmsG GF] [HasG GF] [LogrelNaInvs GF] in
theorem RobustAux.empty_dom {V : Type} (k : Nat) : PartialMap.dom (∅ : NatMap V) k ↔ k ∈ ([] : List Nat) := by
  simp [PartialMap.dom, get?_empty]

omit [HvisG GF] [HmsG GF] [HasG GF] [LogrelNaInvs GF] in
theorem RobustAux.singleton_get {V : Type} (a : Nat) (v : V) :
    get? (PartialMap.singleton a v : NatMap V) a = some v :=
  get?_insert_eq rfl

omit [HvisG GF] [HmsG GF] [HasG GF] [LogrelNaInvs GF] in
theorem RobustAux.singleton_dom {V : Type} (a : Nat) (v : V) (k : Nat) :
    PartialMap.dom (PartialMap.singleton a v : NatMap V) k ↔ k ∈ [a] := by
  by_cases h : a = k
  · subst h; simp [PartialMap.dom, RobustAux.singleton_get]
  · simp [PartialMap.dom, PartialMap.singleton, get?_insert_ne h, get?_empty, Ne.symm h]

omit [HvisG GF] [HmsG GF] [HasG GF] [LogrelNaInvs GF] in
/-- The first four bytes of a zero-initialised memory hold an i32 (Lean helper for the Coq
`repeat_app` step of `instantiate_lse`). -/
theorem RobustAux.zero_mem_i32 (n r : Nat) (mem : Memory)
    (h : mem.data.data = List.replicate (4 + r) (0 : Byte)) :
    n ↦[wmblock] mem ⊢ iprop(∃ c, n ↦[wms][ 0 ] (bits (.int32 c)) : IProp GF) := by
  unfold memBlock memBlockAtPos
  rw [h, ← List.replicate_append_replicate]
  iintro ⟨-, Hb, -, -⟩
  ihave ⟨Hb, -⟩ := BI.BigSepL.bigSepL_append.1 $$ Hb
  iexists 0#32
  have hb : bits (.int32 0#32) = List.replicate 4 (0 : Byte) := by decide
  rw [hb]
  iapply BI.BigSepL.bigSepL_mono_of_forall (fun {k x} => by rw [Nat.zero_add]) $$ Hb

omit [WasmG hlc GF] [HvisG GF] [HmsG GF] [HasG GF] [LogrelNaInvs GF] in
/-- What `ModuleTyping adv [] lseFuncImpts` says about the adversary module (Lean helper: the
Coq proof of `instantiate_lse` derives these facts inline). -/
theorem RobustAux.adv_typing_facts (adv : Module) (htyp : ModuleTyping adv [] lseFuncImpts) :
    ∃ fts gts, ModuleTypingBody adv [] lseFuncImpts fts gts ∧ adv.imports = [] ∧
      ∃ nm nidx mf k, adv.exports = [⟨nm, .func (.funcidx nidx)⟩] ∧ adv.funcs[nidx]? = some mf ∧
        mf.type = .typeidx k ∧ adv.types.getD k (.tf [] []) = .tf [] [] ∧
        BeTyping (updLocalLabelReturn
          { typesT := adv.types, funcT := extTFuncs [] ++ fts, global := extTGlobs [] ++ gts
            table := extTTabs [] ++ adv.tables.map (·.type), memory := extTMems [] ++ adv.mems
            local_ := [], label := [], return_ := none } mf.locals [[]] (some []))
          mf.body (.tf [] []) := by
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
    have hft : fts[nidx]? = some (.tf [] []) := by
      simp [moduleExportTyping, moduleContext, extTFuncs] at he
      split at he <;> simp_all
    obtain ⟨⟨⟨k⟩, locs, body⟩, hmf, hty⟩ := forall2_lookup_r' hfs hft
    obtain ⟨hk, hbe⟩ := hty
    change tfs[k]? = _ at hk
    refine ⟨nm, nidx, _, k, rfl, hmf, rfl, by simp [List.getD_eq_getElem?_getD, hk], ?_⟩
    simpa [moduleContext, updLocalLabelReturn] using hbe
  | table t => obtain ⟨_⟩ := t; simp [moduleExportTyping] at he
  | mem m => obtain ⟨_⟩ := m; simp [moduleExportTyping] at he
  | global g => obtain ⟨_⟩ := g; simp [moduleExportTyping] at he

@[rocq_alias iriswasm.iris_robust_example.instantiate_lse]
theorem instantiate_lse (advModule : Module) (gRet : Nat) (wret : Value)
    -- we assume the adversary module has an export of the () → ()
    (htyp : ModuleTyping advModule [] lseFuncImpts)
    -- that it does not have a start function
    (hnostart : advModule.start = none)
    -- that it adheres to the module restrictions (i.e. only constant initializers for globals)
    (hrestrict : ModuleRestrictions advModule)
    -- if the adversary module declares a table, there cannot be more initializers than its size
    (hboundst : ModuleElemBoundCheckGmap ∅ [] advModule)
    -- if the adversary module declares a memory, there cannot be more initializers than its size
    (hboundsm : ModuleDataBoundCheckGmap ∅ [] advModule)
    -- the imported return global has type i32
    (hgrettyp : typeof wret = .i32) :
    ⊢ iprop(□ ∀ Φ : HostVal → IProp GF,
        (↪[frame] emptyFrame ∗
          gRet ↦[wg] (⟨.mut, wret⟩ : Global) ∗
          0 ↪[mods] advModule ∗
          1 ↪[mods] lseModule ∗
          NonAtomicInvariant.own logrelNais ⊤ ∗
          (∃ name, 1 ↪[vis] (⟨name, .global (.globalidx gRet)⟩ : ModuleExport)) ∗
          (∃ vs, 0 ↪[vis] vs)) -∗
        (∀ v, (⌜v = HostVal.trapHV⌝ ∨ ⌜v = HostVal.immHV [xx 42]⌝) -∗ Φ v) -∗
        WP ((advLseInstantiate gRet, []) : HostExpr) @ Stuckness.NotStuck ; ⊤ {{ v, Φ v }}) := by
  obtain ⟨fts, gts, Hbody, Himps, nm, nidx, mf, k, Hexps, Hmf, Hmft, Hk, Hbe⟩ :=
    RobustAux.adv_typing_facts advModule htyp
  imodintro
  iintro %Φ ⟨Hemptyframe, Hgret, Hmod_adv, Hmod_lse, Hown, ⟨%name1, Hvis1⟩, ⟨%vs, Hvis⟩⟩ HΦ
  unfold advLseInstantiate
  iapply wp_seq_host_nostart .NotStuck ⊤ Φ
    (fun w => iprop(⌜w = HostVal.immHV []⌝ ∗ importResourcesHost [] [] ∗
      ∃ inst, instantiationResourcesPostWasm advModule [] [] ∅ ∅ ∅ ∅ none inst ∗
        moduleExportResourcesHost [0] advModule.exports inst))
    [0] 0 [] advModule _ [] hnostart rfl $$ [] Hmod_adv [Hvis]
  · iintro ⟨%H, -⟩; cases H
  · iintro Hmod_adv
    iapply Iris.wp_wand $$ [Hmod_adv Hvis]
    · iapply instantiation_spec_operational_no_start .NotStuck ⊤ 0 [] [] [0] advModule []
        lseFuncImpts ∅ ∅ ∅ ∅ hnostart htyp hrestrict
      unfold instantiationResourcesPre importResourcesHost exportOwnershipHost
        instantiationResourcesPreWasm importResourcesWasmTypecheck
      unfold_irwt_all
      iframe Hmod_adv
      isplitr
      · iapply BI.BigSepL2.bigSepL2_nil.2; iempintro
      isplitr
      · isplitr
        · isplitr
          · iapply RobustAux.empty_map_check _ ⟨.nil, RobustAux.empty_dom⟩
          isplitr
          · iapply RobustAux.empty_map_check _ ⟨.nil, RobustAux.empty_dom⟩
          isplitr
          · iapply RobustAux.empty_map_check _ ⟨.nil, RobustAux.empty_dom⟩
          iapply RobustAux.empty_map_check _ ⟨.nil, RobustAux.empty_dom⟩
        isplitr
        · ipureintro; exact hboundst
        ipureintro; exact hboundsm
      isplitl [Hvis]
      · iapply BI.BigSepL.bigSepL_singleton.2
        iexists vs; iexact Hvis
      ipureintro; simp [Hexps]
    · iintro %v ⟨%Hv, Hpost⟩
      iunfold instantiationResourcesPost at Hpost
      icases Hpost with ⟨Hmod, Himps, Hpost⟩
      iframe Hmod Himps Hpost
      ipureintro; exact Hv
  iintro %w ⟨%Hw, -, ⟨%inst_adv, Hpost, Hexp⟩⟩ Hmod_adv
  have hfc : getImportFuncCount advModule = 0 := by simp [getImportFuncCount, Himps]
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
  subst hgd
  have htyk : inst_adv.types.getD (match mf.type with | .typeidx k => k) (.tf [] []) = .tf [] [] := by
    rw [HH.1, Hmft]; exact Hk
  rw [htyk]
  iapply instantiation_spec_operational_start_seq .NotStuck ⊤ 1 [0, 1]
    [⟨nm', .func ⟨inst_adv.funcs.getD nidx 0⟩⟩, ⟨name1, .global ⟨gRet⟩⟩] [] lseModule
    (lseFuncImpts ++ lseGlobImpts) []
    (PartialMap.singleton (inst_adv.funcs.getD nidx 0) (.funcNative inst_adv (.tf [] []) mf.locals mf.body))
    ∅ ∅ (PartialMap.singleton gRet ⟨.mut, wret⟩) 1 Φ [.getGlobal gRet] rfl lse_module_typing
    module_restrictions_lse $$ Hemptyframe [Hmod_lse Hn Hvis1 Hadvf Hgret]
  · unfold instantiationResourcesPre importResourcesHost exportOwnershipHost
      instantiationResourcesPreWasm importResourcesWasmTypecheck
    unfold_irwt_all
    iframe Hmod_lse
    isplitl [Hn Hvis1]
    · iapply BI.BigSepL2.bigSepL2_cons.2
      isplitl [Hn]
      · iexact Hn
      iapply BI.BigSepL2.bigSepL2_singleton.2
      iexact Hvis1
    isplitl [Hadvf Hgret]
    · isplitl
      · isplitl [Hadvf]
        · isplitl
          · iapply BI.BigSepM.bigSepM_singleton.2; iexact Hadvf
          ipureintro
          refine ⟨.cons ⟨_, RobustAux.singleton_get _ _, rfl⟩ (.cons trivial .nil), fun k => ?_⟩
          rw [RobustAux.singleton_dom]; simp [extFuncAddrs, extFuncs]
        isplitr
        · iapply RobustAux.empty_map_check _ ⟨.cons trivial (.cons trivial .nil),
            fun k => by simp [PartialMap.dom, get?_empty, extTabAddrs, extTabs]⟩
        isplitr
        · iapply RobustAux.empty_map_check _ ⟨.cons trivial (.cons trivial .nil),
            fun k => by simp [PartialMap.dom, get?_empty, extMemAddrs, extMems]⟩
        isplitl
        · iapply BI.BigSepM.bigSepM_singleton.2; iexact Hgret
        ipureintro
        refine ⟨.cons trivial (.cons ⟨_, _, RobustAux.singleton_get _ _, rfl, ?_⟩ .nil), fun k => ?_⟩
        · simp [globalAgree, hgrettyp]
        · rw [RobustAux.singleton_dom]; simp [extGlobAddrs, extGlobs]
      isplitr
      · ipureintro; intro e he; simp [lseModule] at he
      ipureintro; intro e he; simp [lseModule] at he
    isplitr
    · iapply BI.BigSepL.bigSepL_nil.2; iempintro
    ipureintro; rfl
  iintro %idnstart Hf Hpost
  unfold instantiationResourcesPost instantiationResourcesPostWasm moduleInstResourcesWasm
    importResourcesWasmTypecheck
  unfold_irwt_all
  icases Hpost with ⟨Hmod_lse, Himph, %inst, ⟨%g_inits', %tabA', %memA', %globA', %wts'', %wms'',
    ⟨⟨Hwf, -⟩, -, -, ⟨Hwg, -⟩⟩, %HH', %-, %-, %-, %Hmemeq', %-, %-, %-, %-, Hrf, -, Hrm, -⟩, -⟩
  ihave Hwf := BI.BigSepM.bigSepM_singleton.1 $$ Hwf
  ihave Hwg := BI.BigSepM.bigSepM_singleton.1 $$ Hwg
  ihave Hresf := Hcls $$ Hwf
  obtain ⟨Hity, ⟨tf, Htf⟩, -, -, ⟨tg, Htg⟩, Hcs⟩ := HH'
  have ha : inst.funcs[0]? = some (inst_adv.funcs.getD nidx 0) := by rw [← Htf]; rfl
  have hk : inst.globs[0]? = some gRet := by rw [← Htg]; rfl
  have hs : inst.funcs[1]? = some idnstart := by
    exact of_decide_eq_true Hcs
  subst Hmemeq'
  rw [show moduleInstBuildMems lseModule inst = [moduleInstMemBaseFunc ⟨.i32, ⟨1, none⟩⟩] from rfl,
    show lseModule.funcs = [⟨.typeidx 0, [], lseExpr 0 0⟩] from rfl]
  unfold moduleInstResourcesMem moduleInstResourcesFunc
  ihave ⟨%n, %xs, %hmem, Hm, -⟩ := BI.BigSepL2.bigSepL2_cons_inv_left.1 $$ Hrm
  have hn : inst.memory[0]? = some n := by
    rw [show getImportMemCount lseModule = 0 from rfl, List.drop_zero] at hmem; simp [hmem]
  ihave Hm := RobustAux.zero_mem_i32 n 65532 (moduleInstMemBaseFunc ⟨.i32, ⟨1, none⟩⟩)
    (by rw [moduleInstMemBaseFunc, memMk, MemoryList.data_make]; rfl) $$ Hm
  ihave ⟨%a', %xs', %hfd, Hidn, -⟩ := BI.BigSepL2.bigSepL2_cons_inv_left.1 $$ Hrf
  have ha' : a' = idnstart := by
    rw [show getImportFuncCount lseModule = 1 from rfl] at hfd
    have := congrArg (·[0]?) hfd; simp at this; rw [hs] at this; exact (Option.some.inj this).symm
  subst ha'
  rw [Hity]
  subst Hwts' Hwms' Htabeq Hmemeq Hgleq
  ihave HR : moduleInstResourcesWasm advModule inst_adv (moduleInstBuildTables advModule inst_adv)
      (moduleInstBuildMems advModule inst_adv)
      (moduleInstGlobalInit (moduleInstBuildGlobals advModule.globals) g_inits)
      $$ [Hresf Hrest Hresm Hresg]
  · unfold moduleInstResourcesWasm moduleInstResourcesFunc moduleInstResourcesTab
      moduleInstResourcesMem moduleInstResourcesGlob
    rw [hfc, List.drop_zero]; iframe
  iapply Iris.fupd_wp
  imod interp_instance_alloc [] ⊤ advModule [] lseFuncImpts [] ∅ ∅ ∅ ∅ inst_adv fts gts g_inits
    Hbody ⟨HH.1, by simp [extFuncAddrs, extTabAddrs, extMemAddrs, extGlobAddrs, extFuncs, extTabs,
      extMems, extGlobs]⟩ Hgv.1
    $$ [] [] [] [Himpstyp] HR with ⟨Hi, Hinvs, -⟩
  · iapply BI.BigSepM.bigSepM_empty.2; iempintro
  · iapply BI.BigSepM.bigSepM_empty.2; iempintro
  · iapply BI.BigSepM.bigSepM_empty.2; iempintro
  · unfold importResourcesWasmTypecheck; unfold_irwt_all; iexact Himpstyp
  unfold moduleInstResourcesWasmInvs moduleInstResourcesFuncInvs
  icases Hinvs with ⟨Hires, -⟩
  rw [hfc, List.drop_zero]
  ihave Ha := BI.BigSepL2.bigSepL2_lookup Hmf Hadv $$ Hires
  rw [htyk, show lseModule.types.getD _ (FunctionType.tf [] []) = .tf [] [] from rfl]
  ihave Hidn : a' ↦[wf] (.funcNative inst (.tf [] []) [] (lseExpr 0 0)) $$ [Hidn]
  · iexact Hidn
  imodintro
  iapply wp_lift_wasm
  iapply wp_wand_s $$ [Hf Hidn Hown Ha Hi Hwg Hm]
  · iapply RobustAux.lse_start_spec inst a' n (inst_adv.funcs.getD nidx 0) gRet _ inst_adv mf.body
      mf.locals ⟨rfl, rfl⟩ hn ha hk Hbe $$ Hf Hidn Hown Ha Hi [Hwg] Hm
    iexists _; iexact Hwg
  iintro %w ⟨Hw, -⟩
  icases Hw with (%Hw | ⟨%Hw, Hg⟩)
  · subst Hw
    rw [show ofVal Val.trapV = [AdministrativeInstruction.trap] from rfl]
    iapply wp_get_global_trap_host
    inext; iapply HΦ; ileft; ipureintro; rfl
  · subst Hw
    rw [show ofVal (Val.immV []) = vToEList [] from rfl]
    iapply wp_get_global_host .NotStuck ⊤ gRet _ [] $$ Hg
    inext; iintro Hg; iapply HΦ; iright; ipureintro; rfl

end Examples_host

end IrisWasm.Examples
