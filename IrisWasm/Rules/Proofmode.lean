/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Rules.IrisExampleHelper

/-! Port of `theories/iris/rules/proofmode.v`.

Coq's typeclass-driven list decomposition becomes Lean classes whose computed arguments are
`outParam`s (Coq `Hint Mode`: `!` = input, `-` = output). The tactics are `macro`s/`elab`s with the
Coq names. `take_drop_app_rewrite(_twice)` is redefined verbatim in `proofmode.v`; the Lean tactics
live in `IrisExampleHelper.lean` (imported here). -/

namespace IrisWasm

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm

@[rocq_alias iriswasm.build_llfill_local]
theorem build_llfill_local (n : Nat) (f : Frame) (llh : Llholed) (es e : List AdministrativeInstruction)
    (l1 : List Value) (l2 : List AdministrativeInstruction) :
    llfill llh e = es →
    llfill (.local l1 n f llh l2) e = vToEList l1 ++ [.local n f es] ++ l2 := by
  intro h; subst h; simp [llfill]

@[rocq_alias iriswasm.build_llfill_label]
theorem build_llfill_label (n : Nat) (es' : List AdministrativeInstruction) (llh : Llholed)
    (es e : List AdministrativeInstruction) (l1 : List Value) (l2 : List AdministrativeInstruction) :
    llfill llh e = es →
    llfill (.label l1 n es' llh l2) e = vToEList l1 ++ [.label n es' es] ++ l2 := by
  intro h; subst h; simp [llfill]

@[rocq_alias iriswasm.build_llfill_base]
theorem build_llfill_base (l1 : List Value) (l2 e : List AdministrativeInstruction) :
    llfill (.base l1 l2) e = vToEList l1 ++ e ++ l2 := by
  simp [llfill]

/-! ### Decomposing a list around a frame -/

@[rocq_alias iriswasm.DecomposeLocal]
class DecomposeLocal (l : List AdministrativeInstruction) (l1 : outParam (List Value))
    (n : outParam Nat) (f : outParam Frame) (es : outParam (List AdministrativeInstruction))
    (l2 : outParam (List AdministrativeInstruction)) : Prop where
  mkDecomposeLocal : l = vToEList l1 ++ [.local n f es] ++ l2

@[rocq_alias iriswasm.DecomposeLocalConsHere]
instance (priority := high) decomposeLocalConsHere (n : Nat) (f : Frame)
    (es l2 : List AdministrativeInstruction) :
    DecomposeLocal (.local n f es :: l2) [] n f es l2 := ⟨rfl⟩

@[rocq_alias iriswasm.DecomposeLocalCons]
instance decomposeLocalCons (n : Nat) (f : Frame) (es l2 : List AdministrativeInstruction)
    (l : List Value) (l' : List AdministrativeInstruction) (e : Value)
    [h : DecomposeLocal l2 l n f es l'] :
    DecomposeLocal (.basic (.const e) :: l2) (e :: l) n f es l' :=
  ⟨by rw [h.mkDecomposeLocal]; rfl⟩

@[rocq_alias iriswasm.decompose_local_list]
theorem decompose_local_list (l : List AdministrativeInstruction) (l1 : List Value)
    (l2 es : List AdministrativeInstruction) (n : Nat) (f : Frame) :
    DecomposeLocal l l1 n f es l2 → l = vToEList l1 ++ [.local n f es] ++ l2
  | ⟨h⟩ => h

/-- Coq Ltac `build_llfill_local`: on a goal `llfill ?llh e = l`, finds the first `.local` frame of
`l` after constants and refines `?llh` to a `Llholed.local` layer. -/
macro "build_llfill_local" : tactic =>
  `(tactic| (refine Eq.trans ?_ (decompose_local_list _ _ _ _ _ _ inferInstance).symm;
             apply build_llfill_local))

/-! ### Decomposing a list around a label -/

@[rocq_alias iriswasm.DecomposeLabel]
class DecomposeLabel (l : List AdministrativeInstruction) (l1 : outParam (List Value))
    (n : outParam Nat) (f : outParam (List AdministrativeInstruction))
    (es : outParam (List AdministrativeInstruction))
    (l2 : outParam (List AdministrativeInstruction)) : Prop where
  mkDecomposeLabel : l = vToEList l1 ++ [.label n f es] ++ l2

@[rocq_alias iriswasm.DecomposeLabelConsHere]
instance (priority := high) decomposeLabelConsHere (n : Nat)
    (f es l2 : List AdministrativeInstruction) :
    DecomposeLabel (.label n f es :: l2) [] n f es l2 := ⟨rfl⟩

@[rocq_alias iriswasm.DecomposeLabelCons]
instance decomposeLabelCons (n : Nat) (f es l2 : List AdministrativeInstruction) (l : List Value)
    (l' : List AdministrativeInstruction) (e : Value) [h : DecomposeLabel l2 l n f es l'] :
    DecomposeLabel (.basic (.const e) :: l2) (e :: l) n f es l' :=
  ⟨by rw [h.mkDecomposeLabel]; rfl⟩

@[rocq_alias iriswasm.decompose_label_list]
theorem decompose_label_list (l : List AdministrativeInstruction) (l1 : List Value)
    (l2 es : List AdministrativeInstruction) (n : Nat) (f : List AdministrativeInstruction) :
    DecomposeLabel l l1 n f es l2 → l = vToEList l1 ++ [.label n f es] ++ l2
  | ⟨h⟩ => h

/-- Coq Ltac `build_llfill_label`. -/
macro "build_llfill_label" : tactic =>
  `(tactic| (refine Eq.trans ?_ (decompose_label_list _ _ _ _ _ _ inferInstance).symm;
             apply build_llfill_label))

/-! ### Decomposing a list around a given sub-list -/

@[rocq_alias iriswasm.DecomposeBase]
class DecomposeBase (l e : List AdministrativeInstruction) (l1 : outParam (List Value))
    (l2 : outParam (List AdministrativeInstruction)) : Prop where
  mkDecomposeBase : l = vToEList l1 ++ e ++ l2

-- Priorities follow Coq's default (premise-free instances are tried first).
@[rocq_alias iriswasm.DecomposeBaseConsAppNil]
instance (priority := high) decomposeBaseConsAppNil (e : List AdministrativeInstruction) :
    DecomposeBase e e [] [] := ⟨by simp [vToEList]⟩

@[rocq_alias iriswasm.DecomposeBaseConsSingletonHere]
instance (priority := high) decomposeBaseConsSingletonHere (e : AdministrativeInstruction)
    (l2 : List AdministrativeInstruction) : DecomposeBase (e :: l2) [e] [] l2 := ⟨rfl⟩

@[rocq_alias iriswasm.DecomposeBaseConsHere]
instance decomposeBaseConsHere (l : List AdministrativeInstruction) (e : AdministrativeInstruction)
    (es l2 : List AdministrativeInstruction) [h : DecomposeBase l es [] l2] :
    DecomposeBase (e :: l) (e :: es) [] l2 :=
  ⟨by rw [h.mkDecomposeBase]; rfl⟩

@[rocq_alias iriswasm.DecomposeBaseCons]
instance decomposeBaseCons (l : List AdministrativeInstruction) (l1 : List Value)
    (e l2 : List AdministrativeInstruction) (e' : Value) [h : DecomposeBase l e l1 l2] :
    DecomposeBase (.basic (.const e') :: l) e (e' :: l1) l2 :=
  ⟨by rw [h.mkDecomposeBase]; rfl⟩

@[rocq_alias iriswasm.decompose_base_list]
theorem decompose_base_list (l e : List AdministrativeInstruction) (l1 : List Value)
    (l2 : List AdministrativeInstruction) :
    DecomposeBase l e l1 l2 → l = vToEList l1 ++ e ++ l2
  | ⟨h⟩ => h

/-- Coq Ltac `build_llfill_base`: closes `llfill ?llh [.callHost _ _ _] = l`. -/
macro "build_llfill_base" : tactic =>
  `(tactic| (show llfill _ [AdministrativeInstruction.callHost _ _ _] = _
             exact (build_llfill_base _ _ _).trans
               (decompose_base_list _ _ _ _ inferInstance).symm))

/-- Coq Ltac `build_llfill`: builds the `Llholed` of a goal `llfill ?llh [.callHost _ _ _] = l`. -/
macro "build_llfill" : tactic =>
  `(tactic| repeat (first | build_llfill_local | build_llfill_label | build_llfill_base))

/-! ### Building and deconstructing evaluation contexts -/

@[rocq_alias iriswasm.BuildCtx]
class BuildCtx (i : outParam Nat) (lh : outParam Lholed) (es LI : List AdministrativeInstruction) :
    Prop where
  mkBuildCtx : lfilled i lh es LI = true

@[rocq_alias iriswasm.DeconstructCtx]
class DeconstructCtx (i : Nat) (lh : Lholed) (es : List AdministrativeInstruction)
    (LI : outParam (List AdministrativeInstruction)) : Prop where
  mkDeconstruct : lfilled i lh es LI = true

@[rocq_alias iriswasm.DeconstructCtxBaseApp]
instance deconstructCtxBaseApp (es : List AdministrativeInstruction) (l1 : List Value)
    (l2 : List AdministrativeInstruction) :
    DeconstructCtx 0 (.base (vToEList l1) l2) es (vToEList l1 ++ es ++ l2) :=
  ⟨(lfilled_Ind_Equivalent _ _ _ _).2 (.lfilledBase _ _ _ (v_to_e_is_const_list l1))⟩

@[rocq_alias iriswasm.BuildCtxBase]
instance buildCtxBase (LI es : List AdministrativeInstruction) (l1 : List Value)
    (l2 : List AdministrativeInstruction) [h : DecomposeBase LI es l1 l2] :
    BuildCtx 0 (.base (vToEList l1) l2) es LI :=
  ⟨by rw [h.mkDecomposeBase]
      exact (lfilled_Ind_Equivalent _ _ _ _).2 (.lfilledBase _ _ _ (v_to_e_is_const_list l1))⟩

@[rocq_alias iriswasm.DeconstructCtxLabelApp]
instance deconstructCtxLabelApp (l1 : List Value) (n : Nat) (es es' e l2 : List AdministrativeInstruction)
    (i : Nat) (lh : Lholed) [h : DeconstructCtx i lh e es] :
    DeconstructCtx (i + 1) (.rec_ (vToEList l1) n es' lh l2) e (vToEList l1 ++ [.label n es' es] ++ l2) :=
  ⟨(lfilled_Ind_Equivalent _ _ _ _).2 (.lfilledRec _ _ _ _ _ _ _ _ (v_to_e_is_const_list l1)
    ((lfilled_Ind_Equivalent _ _ _ _).1 h.mkDeconstruct))⟩

-- Coq tries the one-premise `BuildCtxBase` before the two-premise `BuildCtxLabel`.
@[rocq_alias iriswasm.BuildCtxLabel]
instance (priority := low) buildCtxLabel (LI : List AdministrativeInstruction) (l1 : List Value)
    (n : Nat) (es es' e l2 : List AdministrativeInstruction) (i : Nat) (lh : Lholed)
    [hd : DecomposeLabel LI l1 n es' es l2] [hb : BuildCtx i lh e es] :
    BuildCtx (i + 1) (.rec_ (vToEList l1) n es' lh l2) e LI :=
  ⟨by rw [hd.mkDecomposeLabel]
      exact (lfilled_Ind_Equivalent _ _ _ _).2 (.lfilledRec _ _ _ _ _ _ _ _ (v_to_e_is_const_list l1)
        ((lfilled_Ind_Equivalent _ _ _ _).1 hb.mkBuildCtx))⟩

/-- Lean helper for `deconstruct_ctx`: a computed fill (Coq: `constructor; cbn; …; eauto`). -/
theorem lfilled_of_lfill {i : Nat} {lh : Lholed} {es LI : List AdministrativeInstruction}
    (h : lfill i lh es = some LI) : lfilled i lh es LI = true := by
  simp [lfilled, h]

section wp
variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF]

@[rocq_alias iriswasm.wp_build_ctx]
theorem wp_build_ctx (es : Expr) (i : Nat) (lh : Lholed) (LI : Expr) (s : Stuckness) (E : CoPset)
    (P : Val → IProp GF) :
    BuildCtx i lh es LI →
    ⊢ iprop(WP es @ s ; E CTX i ; lh {{ P }} -∗ WP LI @ s ; E {{ P }}) := by
  intro ⟨fill⟩
  unfold wpWasmCtx
  iintro W
  iapply W $$ %LI %fill

@[rocq_alias iriswasm.wp_deconstruct_ctx]
theorem wp_deconstruct_ctx (es : Expr) (i : Nat) (lh : Lholed) (LI : Expr) (s : Stuckness)
    (E : CoPset) (P : Val → IProp GF) :
    DeconstructCtx i lh es LI →
    ⊢ iprop(WP LI @ s ; E {{ P }} -∗ WP es @ s ; E CTX i ; lh {{ P }}) := by
  intro ⟨fill⟩
  unfold wpWasmCtx
  iintro W %LI' %fill'
  rw [lfilled_inj fill fill'] at *
  iexact W

end wp

namespace ProofmodeTac
open Lean Meta Elab Tactic

/-- The proof-mode conclusion of the main goal (the whole target outside the proof mode). -/
def conclusion : TacticM Lean.Expr := do
  let t ← instantiateMVars (← getMainTarget)
  return match Iris.ProofMode.parseIrisGoal? t with
    | some g => g.goal
    | none => t

/-- Expression `e` of the first plain `WP e @ s ; E {{ Φ }}` in the conclusion. -/
def wpExprOfGoal : TacticM Lean.Expr := do
  let some t := (← conclusion).find? (·.isAppOfArity ``Iris.Wp.wp 9)
    | throwError "no WP in the goal"
  return t.getArg! 7

/-- `(s, E, e, Φ, i, lh)` of the first `WP e @ s ; E CTX i ; lh {{ Φ }}` in the conclusion. -/
def ctxOfGoal : TacticM (Array Lean.Expr) := do
  let some t := (← conclusion).find? (·.isAppOfArity ``wpWasmCtx 9)
    | throwError "no WP … CTX in the goal"
  return t.getAppArgs[3:9].toArray

end ProofmodeTac

open Lean Elab Tactic in
/-- Coq Ltac `build_ctx e`: rewrites the goal `WP LI {{ P }}` into `WP e CTX i ; lh {{ P }}`, the
context `lh` being found by `BuildCtx`. -/
elab "build_ctx " e:term:max : tactic => withMainContext do
  let li ← Term.exprToSyntax (← ProofmodeTac.wpExprOfGoal)
  evalTactic (← `(tactic| iapply wp_build_ctx $e _ _ $li _ _ _ inferInstance))

open Lean Elab Tactic in
/-- Coq Ltac `deconstruct_ctx`: turns `WP es CTX i ; lh {{ P }}` into `WP LI {{ P }}` for the
filled `LI`, then simplifies it (Coq `iSimpl`). -/
elab "deconstruct_ctx" : tactic => withMainContext do
  let args ← ProofmodeTac.ctxOfGoal
  let es ← Term.exprToSyntax args[2]!
  let i ← Term.exprToSyntax args[4]!
  let lh ← Term.exprToSyntax args[5]!
  evalTactic (← `(tactic|
    iapply wp_deconstruct_ctx $es $i $lh _ _ _ _
      (by first | exact inferInstance | exact ⟨lfilled_of_lfill rfl⟩)))
  evalTactic (← `(tactic|
    try isimp only [vToEList, List.map_cons, List.map_nil, List.cons_append, List.nil_append]))

section wp
variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF]

@[rocq_alias iriswasm.bind_seq_base_imm]
theorem bind_seq_base_imm (es : Expr) (P : Val → IProp GF) (LI : Expr) (l1 : List Value) (l2 : Expr)
    (s : Stuckness) (E : CoPset) (Q : Val → IProp GF) (w : List Value) :
    DecomposeBase LI es l1 l2 →
    ⊢ iprop(WP es @ E {{ v, ⌜v = .immV w⌝ ∗ P v }} -∗
      (∀ v, ⌜v = .immV w⌝ ∗ P v -∗ WP (vToEList l1 ++ ofVal v ++ l2) @ s ; E {{ Q }}) -∗
      WP LI @ s ; E {{ Q }}) := by
  intro _
  iintro H1 H2
  build_ctx es
  rw [← List.append_nil es]
  iapply wp_seq_ctx s E Q (fun v => iprop(⌜v = .immV w⌝ ∗ P v)) es [] 0
  isplitr
  · iintro ⟨%Hcontr, -⟩; cases Hcontr
  rw [List.append_nil]
  iframe
  iintro %v' H
  rw [List.append_nil]
  iapply wp_base_pull
  dsimp only [pullBase]
  iapply (wandIff_equiv (wp_wasm_empty_ctx s E _ _)).1
  iapply H2 $$ H

@[rocq_alias iriswasm.bind_seq_base_callhost]
theorem bind_seq_base_callhost (es : Expr) (P : Val → IProp GF) (LI : Expr) (l1 : List Value)
    (l2 : Expr) (s : Stuckness) (E : CoPset) (Q : Val → IProp GF) (a1 : FunctionType)
    (a2 : Hostfuncidx) (a3 : List Value) (a4 : Llholed) :
    DecomposeBase LI es l1 l2 →
    ⊢ iprop(WP es @ E {{ v, ⌜v = .callHostV a1 a2 a3 a4⌝ ∗ P v }} -∗
      (∀ v, ⌜v = .callHostV a1 a2 a3 a4⌝ ∗ P v -∗
        WP (vToEList l1 ++ ofVal v ++ l2) @ s ; E {{ Q }}) -∗
      WP LI @ s ; E {{ Q }}) := by
  intro _
  iintro H1 H2
  build_ctx es
  rw [← List.append_nil es]
  iapply wp_seq_ctx s E Q (fun v => iprop(⌜v = .callHostV a1 a2 a3 a4⌝ ∗ P v)) es [] 0
  isplitr
  · iintro ⟨%Hcontr, -⟩; cases Hcontr
  rw [List.append_nil]
  iframe
  iintro %v' H
  rw [List.append_nil]
  iapply wp_base_pull
  dsimp only [pullBase]
  iapply (wandIff_equiv (wp_wasm_empty_ctx s E _ _)).1
  iapply H2 $$ H

end wp

/-- Coq `bind_seq_base_imm e with "pat"`: `iApply (bind_seq_base_imm e with "pat")`, the
decomposition of the goal's `WP LI` around `e` being found by `DecomposeBase`. -/
syntax "bind_seq_base_imm " term:max " with " (ppSpace colGt specPat)+ : tactic

/-- Coq `bind_seq_base_callhost e with "pat"`. -/
syntax "bind_seq_base_callhost " term:max " with " (ppSpace colGt specPat)+ : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| bind_seq_base_imm $e with $pats*) => withMainContext do
    let li ← Term.exprToSyntax (← ProofmodeTac.wpExprOfGoal)
    evalTactic (← `(tactic|
      iapply bind_seq_base_imm $e _ $li _ _ _ _ _ _ inferInstance $$ $pats*))
  | `(tactic| bind_seq_base_callhost $e with $pats*) => withMainContext do
    let li ← Term.exprToSyntax (← ProofmodeTac.wpExprOfGoal)
    evalTactic (← `(tactic|
      iapply bind_seq_base_callhost $e _ $li _ _ _ _ _ _ _ _ _ inferInstance $$ $pats*))

/-! ### Tactic checks (Lean only) -/

example (tf : FunctionType) (h : Hostfuncidx) (vs : List Value) (v : Value) (f : Frame) :
    ∃ llh, llfill llh [.callHost tf h vs] =
      [.basic (.const v), .label 1 [] [.local 0 f [.callHost tf h vs]]] := by
  constructor
  build_llfill

section checks
variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF]

example (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF) (v : Value)
    (x y : AdministrativeInstruction) :
    iprop(WP ([.basic (.const v), x, y] : Expr) @ s ; E {{ Φ }}) ⊢
      iprop(WP ([.basic (.const v), x, y] : Expr) @ s ; E {{ Φ }}) := by
  iintro H
  build_ctx [x]
  deconstruct_ctx
  iexact H

example (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF) (v : Value)
    (x y : AdministrativeInstruction) (P : IProp GF) (w : List Value) :
    iprop(P ∗ (P -∗ WP ([x] : Expr) @ E {{ v, ⌜v = .immV w⌝ ∗ True }}) ∗
      (∀ v', ⌜v' = .immV w⌝ ∗ True -∗ WP (vToEList [v] ++ ofVal v' ++ [y]) @ s ; E {{ Φ }})) ⊢
      iprop(WP ([.basic (.const v), x, y] : Expr) @ s ; E {{ Φ }}) := by
  iintro ⟨HP, Hx, Hk⟩
  bind_seq_base_imm [x] with [HP Hx]
  · iapply Hx $$ HP
  · iexact Hk

example (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF) (x y : AdministrativeInstruction)
    (tf : FunctionType) (h : Hostfuncidx) (vs : List Value) (llh : Llholed) :
    iprop(WP ([x] : Expr) @ E {{ v, ⌜v = .callHostV tf h vs llh⌝ ∗ True }} ∗
      (∀ v', ⌜v' = .callHostV tf h vs llh⌝ ∗ True -∗
        WP (vToEList [] ++ ofVal v' ++ [y]) @ s ; E {{ Φ }})) ⊢
      iprop(WP ([x, y] : Expr) @ s ; E {{ Φ }}) := by
  iintro ⟨Hx, Hk⟩
  bind_seq_base_callhost [x] with [Hx]
  · iexact Hx
  · iexact Hk

example (a b c d : AdministrativeInstruction) (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF) :
    iprop(WP ([a] ++ [b, c] ++ [d] : Expr) @ s ; E {{ Φ }}) ⊢
      iprop(WP ([a, b, c, d] : Expr) @ s ; E {{ Φ }}) := by
  iintro H
  take_drop_app_rewrite_twice 1 1
  iexact H

end checks

end IrisWasm
