/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Rules.IrisRulesPure
import IrisWasm.Rules.IrisRulesStructural
import IrisWasm.Rules.IrisRulesControl
import IrisWasm.Rules.IrisRulesCalls
import IrisWasm.Rules.IrisRulesResources

/-! Port of `theories/iris/rules/iris_example_helper.v`. -/

namespace IrisWasm

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm

/-! Shorthands for common constructors. -/

@[rocq_alias iriswasm.xx]
def xx (i : _root_.Int) : Value := .int32 (Wasm.Int.intOfZ i)

@[rocq_alias iriswasm.xb]
def xb (b : Bool) : Value := .int32 (wasmBool b)

@[rocq_alias iriswasm.yy]
def yy (i : _root_.Int) : Nat := Wasm.Int.natOfUint (Wasm.Int.intOfZ (w := 32) i)

section Examples
variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF]

/-! Helper lemmas for the list manipulations of expressions. `iris_examples.v` restates the same
four lemmas; those copies are `IrisWasm.Examples.iRewrite_nil_*`. -/

@[rocq_alias iriswasm.iris_example_helper.iRewrite_nil_l]
theorem iRewrite_nil_l (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF) (e : Expr) :
    iprop(WP ([] ++ e) @ s ; E {{ Φ }}) ⊢ iprop(WP e @ s ; E {{ Φ }}) := .rfl

@[rocq_alias iriswasm.iris_example_helper.iRewrite_nil_r]
theorem iRewrite_nil_r (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF) (e : Expr) :
    iprop(WP (e ++ []) @ s ; E {{ Φ }}) ⊢ iprop(WP e @ s ; E {{ Φ }}) := by
  rw [List.append_nil]

@[rocq_alias iriswasm.iris_example_helper.iRewrite_nil_l_ctx]
theorem iRewrite_nil_l_ctx (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF) (e : Expr) (i : Nat)
    (lh : Lholed) :
    iprop(WP ([] ++ e) @ s ; E CTX i ; lh {{ Φ }}) ⊢ iprop(WP e @ s ; E CTX i ; lh {{ Φ }}) :=
  .rfl

@[rocq_alias iriswasm.iris_example_helper.iRewrite_nil_r_ctx]
theorem iRewrite_nil_r_ctx (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF) (e : Expr) (i : Nat)
    (lh : Lholed) :
    iprop(WP (e ++ []) @ s ; E CTX i ; lh {{ Φ }}) ⊢ iprop(WP e @ s ; E CTX i ; lh {{ Φ }}) := by
  rw [List.append_nil]

end Examples

/-! ### Tactics

`take_drop_app_rewrite n` (Coq Ltac, also redefined verbatim in `proofmode.v`; defined once here):
splits the expression `e` of the first `WP e … CTX`, `WP e …`, `WP e … FRAME … CTX`, `WP e … FRAME`
(searched in that order, in the proof-mode conclusion first) into `take n e ++ drop n e`, both
computed (Coq: `rewrite -(take_drop n e); simpl take; simpl drop`). All occurrences of `e` in the
goal are rewritten, as with Coq's `rewrite`. `take_drop_app_rewrite_twice n m` additionally splits
the right part `e'` of the resulting `WP _ ++ e'` (`CTX` form first) at `length e' - m`. -/

end IrisWasm

namespace IrisWasmTactic.TakeDrop
open Lean Meta Elab Tactic

/-- Splits `e : List α` after `k` elements by weak-head reduction (Coq `simpl take/drop`); if the
list gets stuck after `j < k` elements, the remainder is `take (k-j) r ++ drop (k-j) r`. -/
partial def split (k : Nat) (e : Expr) : MetaM (Expr × Expr) := do
  let α := (← whnf (← inferType e)).appArg!
  let rec go (k : Nat) (e : Expr) (acc : Array Expr) : MetaM (Expr × Expr) := do
    if k = 0 then return (← mkListLit α acc.toList, e)
    let e' ← whnf e
    match e'.getAppFnArgs with
    | (``List.cons, #[_, a, tl]) => go (k - 1) tl (acc.push a.headBeta)
    | (``List.nil, _) => return (← mkListLit α acc.toList, e')
    | _ =>
      let kE := mkNatLit k
      let tk ← mkAppM ``List.take #[kE, e]
      let dk ← mkAppM ``List.drop #[kE, e]
      let pre ← acc.foldrM (fun a l => mkAppM ``List.cons #[a, l]) tk
      return (pre, dk)
  go k e #[]

/-- Number of elements of `e` reachable by weak-head reduction. -/
partial def length (e : Expr) : MetaM Nat := do
  match (← whnf e).getAppFnArgs with
  | (``List.cons, #[_, _, tl]) => return (← length tl) + 1
  | (``List.nil, _) => return 0
  | _ => throwError "take_drop_app_rewrite_twice: cannot compute the length of{indentExpr e}"

/-- The expression argument of a WP of kind `kind` (`ctx`, `wp`, `ctxFrame`, `frame`). -/
def wpExpr? (kind : Name) (t : Expr) : Option Expr :=
  if kind == ``Iris.Wp.wp then
    if t.isAppOfArity ``Iris.Wp.wp 9 then some (t.getArg! 7) else none
  else if t.isAppOf kind && t.getAppNumArgs ≥ 6 then
    -- `wpWasmCtx`/`wpWasmFrame`/`wpWasmCtxFrame` take `hlc GF _ s E e …`
    some (t.getArg! 5)
  else none

def kinds : List Name :=
  [``IrisWasm.wpWasmCtx, ``Iris.Wp.wp, ``IrisWasm.wpWasmCtxFrame, ``IrisWasm.wpWasmFrame]

/-- First WP expression of one of `ks` (in order of `ks`), searching the proof-mode conclusion
first and then the whole target. -/
def findWp (ks : List Name) (target : Expr) : MetaM Expr := do
  let concl := match Iris.ProofMode.parseIrisGoal? target with
    | some g => g.goal
    | none => target
  for scope in [concl, target] do
    for k in ks do
      if let some t := scope.find? (fun t => (wpExpr? k t).isSome) then
        return (wpExpr? k t).get!
  throwError "take_drop_app_rewrite: no WP found in the goal"

/-- Replaces every occurrence of `e` in the main goal by the definitionally equal `e'`. -/
def replaceIn (e e' : Expr) : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let abst ← kabstract t e
  unless ← isDefEq e e' do throwError "take_drop_app_rewrite: split is not definitional"
  replaceMainGoal [← g.replaceTargetDefEq (abst.instantiate1 e')]

def run (n : Expr) : TacticM Unit := withMainContext do
  let n ← instantiateMVars n
  let some k ← (evalNat (← reduce n)).run | throwError "take_drop_app_rewrite: {n} is not a numeral"
  let e ← findWp kinds (← instantiateMVars (← getMainTarget))
  let (l1, l2) ← split k e
  replaceIn e (← mkAppM ``HAppend.hAppend #[l1, l2])

def runTwice (n : Expr) (m : Nat) : TacticM Unit := withMainContext do
  run n
  let w ← findWp [``IrisWasm.wpWasmCtx, ``Iris.Wp.wp] (← instantiateMVars (← getMainTarget))
  let some (l0, e) := (if w.isAppOfArity ``HAppend.hAppend 6 then some (w.appFn!.appArg!, w.appArg!)
    else none) | throwError "take_drop_app_rewrite_twice: WP expression is not an append"
  let (l1, l2) ← split ((← length e) - m) e
  -- Lean's `++` is left-associative: produce `l0 ++ l1 ++ l2` (Coq's right-nested form if the
  -- prefix `l0` is not a literal list)
  let left ← mkAppM ``HAppend.hAppend #[← mkAppM ``HAppend.hAppend #[l0, l1], l2]
  if ← isDefEq w left then replaceIn w left
  else replaceIn e (← mkAppM ``HAppend.hAppend #[l1, l2])

end IrisWasmTactic.TakeDrop

open Lean Elab Tactic in
/-- Coq Ltac `take_drop_app_rewrite n`. -/
elab "take_drop_app_rewrite " n:term:max : tactic => do
  let n ← withMainContext <| Term.elabTermEnsuringType n (mkConst ``Nat)
  IrisWasmTactic.TakeDrop.run n

open Lean Elab Tactic in
/-- Coq Ltac `take_drop_app_rewrite_twice n m`. -/
elab "take_drop_app_rewrite_twice " n:term:max m:num : tactic => do
  let n ← withMainContext <| Term.elabTermEnsuringType n (mkConst ``Nat)
  IrisWasmTactic.TakeDrop.runTwice n m.getNat
