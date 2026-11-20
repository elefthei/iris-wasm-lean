/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Language.Iris.Iris
import IrisWasm.Language.Iris.IrisLocations
import IrisWasm.Language.IrisWp
import IrisWasm.Helpers.IrisWasmDeterm
import Iris.BI.Lib.GenHeap
import Iris.Instances.Lib.GhostMap
import Iris.Instances.Lib.NaInvariants
import Iris.Instances.Lib.FUpd

/-! Port of `theories/iris/language/iris_wp_def.v`.

The heaps of `WasmG` are deliberately *not* instances: two pairs of them share the same
`(L, V)` (`tabsize`/`memsize`, `tablimit`/`memlimit`), so every use selects its heap explicitly
via `(G := WasmG.<heap>)`. The points-to notations below do this for you. -/

namespace IrisWasm

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm

#rocq_ignore iriswasm.iris_wp_def.expr "same as `IrisWasm.Expr`"
#rocq_ignore iriswasm.iris_wp_def.val "same as `IrisWasm.Val`"
#rocq_ignore iriswasm.iris_wp_def.to_val "same as `IrisWasm.toVal`"
#rocq_ignore iriswasm.wasm_lang "the `Language` instance of `Iris.lean`"
#rocq_ignore iriswasm.iris_wp_def.reducible "use `Language.Reducible`"
#rocq_ignore iriswasm.proph_id "unused"
#rocq_ignore iriswasm.eqdecision_frame "`Frame` derives `DecidableEq`"

/-- The single-key map holding the current frame (`gmap unit frame`). -/
abbrev UnitMapF := fun V => Std.ExtTreeMap Unit V compare

@[rocq_alias iriswasm.wasmG]
class WasmG (hlc : outParam HasLC) (GF : BundledGFunctors) where
  [invGS : InvGS_gen hlc GF]
  funcHs : genHeapGS Nat FunctionClosure GF NatMap
  tabHs : genHeapGS (Nat × Nat) Funcelem GF NatPairMap
  tabsizeHs : genHeapGS Nat Nat GF NatMap
  tablimitHs : genHeapGS Nat (Option Nat) GF NatMap
  memHs : genHeapGS (Nat × Nat) Byte GF NatPairMap
  memsizeHs : genHeapGS Nat Nat GF NatMap
  memlimitHs : genHeapGS Nat (Option Nat) GF NatMap
  globHs : genHeapGS Nat Global GF NatMap
  locsHs : GhostMapG GF Unit Frame UnitMapF
  frameGName : GName

attribute [reducible, instance] WasmG.locsHs
-- `WasmG.invGS` is brought in as a `local instance` by example files; keep it unfoldable there.
attribute [instance_reducible] WasmG.invGS

@[rocq_alias iriswasm.logrel_na_invs]
class LogrelNaInvs (GF : BundledGFunctors) where
  [naInvG : NaInvG GF]
  logrelNais : NaInvPoolName

attribute [reducible, instance] LogrelNaInvs.naInvG

variable {hlc : HasLC} {GF : BundledGFunctors}

section wp_def
variable [WasmG hlc GF]

/-- Body of the `↪[frame]{ q } f` notation: ownership of the current frame. -/
def frameOwn (q : DFrac) (f : Frame) : IProp GF :=
  ghost_map_elem (H := UnitMapF) (WasmG.frameGName GF) q () f

@[rocq_alias iriswasm.gen_heap_wasm_store]
def genHeapWasmStore (s : StoreRecord) : IProp GF := iprop(
  genHeapInterp (G := WasmG.funcHs) (gmapOfList s.funcs) ∗
  genHeapInterp (G := WasmG.tabHs) (gmapOfTable s.tables) ∗
  genHeapInterp (G := WasmG.memHs) (gmapOfMemory s.mems) ∗
  genHeapInterp (G := WasmG.globHs) (gmapOfList s.globals) ∗
  genHeapInterp (G := WasmG.memsizeHs) (gmapOfList (s.mems.map lengthMem)) ∗
  genHeapInterp (G := WasmG.tabsizeHs) (gmapOfList (s.tables.map tabSize)) ∗
  genHeapInterp (G := WasmG.memlimitHs) (gmapOfList (s.mems.map (·.maxOpt))) ∗
  genHeapInterp (G := WasmG.tablimitHs) (gmapOfList (s.tables.map (·.maxOpt))))

@[rocq_alias iriswasm.state_interp]
def stateInterp : State → IProp GF
  | (s, locs, inst) => iprop(
    genHeapInterp (G := WasmG.funcHs) (gmapOfList s.funcs) ∗
    genHeapInterp (G := WasmG.tabHs) (gmapOfTable s.tables) ∗
    genHeapInterp (G := WasmG.memHs) (gmapOfMemory s.mems) ∗
    genHeapInterp (G := WasmG.globHs) (gmapOfList s.globals) ∗
    ghost_map_auth (WasmG.frameGName GF) (DFrac.own 1)
      (insert (PartialMap.empty : UnitMapF Frame) () ⟨locs, inst⟩) ∗
    genHeapInterp (G := WasmG.memsizeHs) (gmapOfList (s.mems.map lengthMem)) ∗
    genHeapInterp (G := WasmG.tabsizeHs) (gmapOfList (s.tables.map tabSize)) ∗
    genHeapInterp (G := WasmG.memlimitHs) (gmapOfList (s.mems.map (·.maxOpt))) ∗
    genHeapInterp (G := WasmG.tablimitHs) (gmapOfList (s.tables.map (·.maxOpt))))

/-- Coq `heapG_irisG`. A `def`, not an instance, so that iris-lean's generic
`Wp` instance for `IrisGS_gen` never fires on Wasm expressions; `wpWasm` is used instead. -/
@[reducible, rocq_alias iriswasm.heapG_irisG]
def wasmIrisGS : IrisGS_gen hlc Expr GF where
  stateInterp σ _ _ _ := stateInterp σ
  invGS := WasmG.invGS
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono _ _ _ _ := by
    let := @WasmG.invGS hlc GF _
    exact fupd_intro

#rocq_ignore iriswasm.state_interp_mono "inlined into `wasmIrisGS`"

end wp_def

/-! ### Resource ownership -/

section notations
open Lean

/-- `n ↦[wf]{ q } v`: function closure `v` at function address `n`. -/
syntax:50 term:51 " ↦[wf]{ " term " } " term:51 : term
syntax:50 term:51 " ↦[wf] " term:51 : term
syntax:50 term:51 " ↦[wt]{ " term " }[ " term " ] " term:51 : term
syntax:50 term:51 " ↦[wt][ " term " ] " term:51 : term
syntax:50 term:51 " ↪[wtsize] " term:51 : term
syntax:50 term:51 " ↪[wtlimit] " term:51 : term
syntax:50 term:51 " ↦[wm]{ " term " }[ " term " ] " term:51 : term
syntax:50 term:51 " ↦[wm][ " term " ] " term:51 : term
syntax:50 term:51 " ↦[wmlength] " term:51 : term
syntax:50 term:51 " ↪[wmlimit] " term:51 : term
syntax:50 term:51 " ↦[wg]{ " term " } " term:51 : term
syntax:50 term:51 " ↦[wg] " term:51 : term
syntax:50 "↪[frame]{ " term " } " term:51 : term
syntax:50 "↪[frame] " term:51 : term

macro_rules
  | `($n ↦[wf]{ $q } $v) => `(pointsTo (G := WasmG.funcHs) ($n : Nat) $q ($v : FunctionClosure))
  | `($n ↦[wf] $v) => `(pointsTo (G := WasmG.funcHs) ($n : Nat) (DFrac.own 1) ($v : FunctionClosure))
  | `($n ↦[wt]{ $q }[ $i ] $v) =>
    `(pointsTo (G := WasmG.tabHs) (($n : Nat), ($i : Nat)) $q ($v : Funcelem))
  | `($n ↦[wt][ $i ] $v) =>
    `(pointsTo (G := WasmG.tabHs) (($n : Nat), ($i : Nat)) (DFrac.own 1) ($v : Funcelem))
  | `($n ↪[wtsize] $m) => `(pointsTo (G := WasmG.tabsizeHs) ($n : Nat) DFrac.discard ($m : Nat))
  | `($n ↪[wtlimit] $m) =>
    `(pointsTo (G := WasmG.tablimitHs) ($n : Nat) DFrac.discard ($m : Option Nat))
  | `($n ↦[wm]{ $q }[ $i ] $v) =>
    `(pointsTo (G := WasmG.memHs) (($n : Nat), ($i : Nat)) $q ($v : Byte))
  | `($n ↦[wm][ $i ] $v) =>
    `(pointsTo (G := WasmG.memHs) (($n : Nat), ($i : Nat)) (DFrac.own 1) ($v : Byte))
  | `($n ↦[wmlength] $v) =>
    `(pointsTo (G := WasmG.memsizeHs) ($n : Nat) (DFrac.own 1) ($v : Nat))
  | `($n ↪[wmlimit] $v) =>
    `(pointsTo (G := WasmG.memlimitHs) ($n : Nat) DFrac.discard ($v : Option Nat))
  | `($n ↦[wg]{ $q } $v) => `(pointsTo (G := WasmG.globHs) ($n : Nat) $q ($v : Global))
  | `($n ↦[wg] $v) => `(pointsTo (G := WasmG.globHs) ($n : Nat) (DFrac.own 1) ($v : Global))
  | `(↪[frame]{ $q } $f) => `(frameOwn $q $f)
  | `(↪[frame] $f) => `(frameOwn (DFrac.own 1) $f)

end notations

section blocks
variable [WasmG hlc GF]

/-! ### Memory blocks and whole tables -/

@[rocq_alias iriswasm.mem_block]
def memBlock (n : Nat) (m : Memory) : IProp GF := iprop(
  ([∗list] i ↦ b ∈ m.data.data, n ↦[wm][ i ] b) ∗
    n ↦[wmlength] lengthMem m ∗ n ↪[wmlimit] m.maxOpt)

@[rocq_alias iriswasm.mem_block_at_pos]
def memBlockAtPos (n : Nat) (l : Bytes) (k : Nat) : IProp GF := iprop(
  [∗list] i ↦ b ∈ l, n ↦[wm][ k + i ] b)

@[rocq_alias iriswasm.tab_block]
def tabBlock (n : Nat) (tab : Tableinst) : IProp GF := iprop(
  ([∗list] i ↦ tabelem ∈ tab.data, n ↦[wt][ i ] tabelem) ∗
    n ↪[wtsize] tabSize tab ∗ n ↪[wtlimit] tab.maxOpt)

end blocks

/-- `n ↦[wmblock] m`: the whole memory `m` at memory address `n`. -/
notation:50 n:51 " ↦[wmblock] " m:51 => memBlock n m
/-- `n ↦[wms][ i ] bs`: the bytes `bs` at offset `i` of memory `n`. -/
notation:50 n:51 " ↦[wms][ " i " ] " l:51 => memBlockAtPos n l i
/-- `n ↦[wtblock] t`: the whole table `t` at table address `n`. -/
notation:50 n:51 " ↦[wtblock] " t:51 => tabBlock n t

@[rocq_alias iriswasm.mem_equiv]
def MemEquiv (m1 m2 : Memory) : Prop :=
  m1.maxOpt = m2.maxOpt ∧ m1.data.data = m2.data.data

@[rocq_alias iriswasm.mem_equiv_wmblock_rewrite]
theorem mem_equiv_wmblock_rewrite [WasmG hlc GF] {m1 m2 : Memory} {n : Nat}
    (h : MemEquiv m1 m2) : (n ↦[wmblock] m1 : IProp GF) ⊣⊢ n ↦[wmblock] m2 := by
  obtain ⟨⟨d1⟩, o1⟩ := m1
  obtain ⟨⟨d2⟩, o2⟩ := m2
  obtain ⟨h1, h2⟩ := h
  simp only at h1 h2
  subst h1 h2
  exact .rfl

/-! ### The Wasm weakest precondition -/

section wasm_wp
variable [WasmG hlc GF]

@[rocq_alias iriswasm.wp_wasm]
instance wpWasm : Wp (IProp GF) Expr Val Stuckness :=
  ⟨fun s E e Φ =>
    @IrisWp.wp hlc Expr State Observation Val _ GF wasmIrisGS Frame
      (fun f => iprop(↪[frame] f)) s E e Φ⟩

@[rocq_alias iriswasm.wp_wasm_ctx]
def wpWasmCtx (s : Stuckness) (E : CoPset) (e : Expr) (Φ : Val → IProp GF) (i : Nat)
    (lh : Lholed) : IProp GF :=
  iprop(∀ LI, ⌜lfilled i lh e LI = true⌝ -∗ WP LI @ s ; E {{ Φ }})

@[rocq_alias iriswasm.wp_wasm_frame]
def wpWasmFrame (s : Stuckness) (E : CoPset) (es : Expr) (Φ : Val → IProp GF) (n : Nat)
    (f : Frame) : IProp GF :=
  iprop(WP [AdministrativeInstruction.local n f es] @ s ; E {{ Φ }})

@[rocq_alias iriswasm.wp_wasm_ctx_frame]
def wpWasmCtxFrame (s : Stuckness) (E : CoPset) (es : Expr) (Φ : Val → IProp GF) (n : Nat)
    (f : Frame) (i : Nat) (lh : Lholed) : IProp GF :=
  iprop(∀ LI, ⌜lfilled i lh es LI = true⌝ -∗
    WP [AdministrativeInstruction.local n f LI] @ s ; E {{ Φ }})

end wasm_wp

/-! ### Context and frame WP notations

`WP e @ s ; E CTX i ; lh {{ v, Q }}`, `WP e @ s ; E CTX_EMPTY {{ v, Q }}`,
`WP e @ s ; E FRAME n ; f {{ v, Q }}`, `WP e @ s ; E FRAME n ; f CTX i ; lh {{ v, Q }}`,
`WP e @ s ; E FRAME n ; f CTX_EMPTY {{ v, Q }}`. The `@ s ; E` part accepts every form of
iris-lean's `wpExpr` (`@ E`, `@ E ?`, bare, `?`); as in Coq, a `?` may also follow `lh`. -/

section ctxNotations
open Lean

syntax "WP " wpExpr " CTX " term:max " ; " term:max (" ?")? ppSpace wpPostcond : term
syntax "WP " wpExpr " CTX_EMPTY " wpPostcond : term
syntax "WP " wpExpr " FRAME " term:max " ; " term:max ppSpace wpPostcond : term
syntax "WP " wpExpr " FRAME " term:max " ; " term:max " CTX " term:max " ; " term:max (" ?")?
  ppSpace wpPostcond : term
syntax "WP " wpExpr " FRAME " term:max " ; " term:max " CTX_EMPTY " wpPostcond : term

/-- Parses the shared `wpExpr`/postcondition parts; total (`[{ }]`) postconditions are rejected. -/
private meta def parseCtxWp (expr : TSyntax ``wpExpr) (post : TSyntax `wpPostcond)
    (maybe : Bool) : MacroM (Term × Term × Term × Term) := do
  let (e, s, E) ← parseWpExpr expr
  let (Φ, total) ← parseWpPostcond post
  if total then Macro.throwUnsupported
  let s ← if maybe then `(Stuckness.MaybeStuck) else pure s
  return (e, s, E, Φ)

macro_rules
  | `(WP $x CTX $i ; $lh $[?%$q]? $p) => do
    let (e, s, E, Φ) ← parseCtxWp x p q.isSome
    `(wpWasmCtx $s $E $e $Φ $i $lh)
  | `(WP $x CTX_EMPTY $p) => do
    let (e, s, E, Φ) ← parseCtxWp x p false
    `(wpWasmCtx $s $E $e $Φ 0 (Lholed.base [] []))
  | `(WP $x FRAME $n ; $f $p) => do
    let (e, s, E, Φ) ← parseCtxWp x p false
    `(wpWasmFrame $s $E $e $Φ $n $f)
  | `(WP $x FRAME $n ; $f CTX $i ; $lh $[?%$q]? $p) => do
    let (e, s, E, Φ) ← parseCtxWp x p q.isSome
    `(wpWasmCtxFrame $s $E $e $Φ $n $f $i $lh)
  | `(WP $x FRAME $n ; $f CTX_EMPTY $p) => do
    let (e, s, E, Φ) ← parseCtxWp x p false
    `(wpWasmCtxFrame $s $E $e $Φ $n $f 0 (Lholed.base [] []))

end ctxNotations

/-- Port of Coq's `only_one_reduction H` (`iris_wp_def.v`). `H : Reduce ws f es ws' f' es'` is the
unknown reduction of a lifting lemma; `using hred` proves the expected reduction of the same `es`
(Coq builds it with `repeat econstructor`; when omitted, it is searched with `constructor`/`assumption`).
Applies `reduce_det`: in the deterministic case `H` becomes the componentwise equalities and they are
substituted when possible; the `growMemory`/`trap` cases (hypothesis `Hstart`) are closed by computing
`firstInstr` when `es` is concrete. Unlike Coq, the frame-reintroduction `iExists f; iFrame` of the
deterministic case is left to the caller. -/
syntax (name := onlyOneReduction) "only_one_reduction " ident (" using " term)? : tactic

macro_rules
  | `(tactic| only_one_reduction $h) =>
    `(tactic| only_one_reduction $h using (by repeat' (first | constructor! | assumption)))
  | `(tactic| only_one_reduction $h using $hred) => do
    let hs := Lean.mkIdent `Hstart
    let r := Lean.mkIdent `rfl
    `(tactic| (obtain $h:ident | ⟨_, $hs:ident⟩ | ⟨_, _, _, $hs:ident, _, _, _⟩ := reduce_det $h $hred
               all_goals first
                 | (simp [firstInstr_cons, firstInstrInstr] at $hs:ident; done)
                 | (simp only [Prod.mk.injEq] at $h:ident; try obtain ⟨$r:ident, $r:ident, $r:ident⟩ := $h)
                 | skip))

example {s s' : StoreRecord} {f f' : Frame} {es' : List AdministrativeInstruction} {v1 v2 v : Value}
    {op : Binop} {t : ValueType} (hv : appBinop op v1 v2 = some v)
    (H : Reduce s f [.basic (.const v1), .basic (.const v2), .basic (.binop t op)] s' f' es') :
    s' = s ∧ f' = f ∧ es' = [.basic (.const v)] := by
  only_one_reduction H
  exact ⟨rfl, rfl, rfl⟩

-- Notation smoke test (plan, Verification 3).
example [WasmG hlc GF] (f : Frame) : Prop :=
  ⊢ (iprop(↪[frame] f -∗ WP [AdministrativeInstruction.trap] {{ v, ⌜v = .trapV⌝ ∗ ↪[frame] f }})
    : IProp GF)

example [WasmG hlc GF] (f : Frame) (lh : Lholed) (Φ : Val → IProp GF) : Prop :=
  ⊢ (iprop(WP [] @ .NotStuck ; ⊤ CTX 1 ; lh {{ v, Φ v }} ∗ WP [] CTX_EMPTY {{ Φ }} ∗
    WP [] @ ⊤ FRAME 0 ; f {{ Φ }} ∗ WP [] @ ⊤ FRAME 0 ; f CTX 1 ; lh ? {{ Φ }} ∗
    0 ↦[wmblock] default ∗ 0 ↦[wms][ 3 ] [] ∗ 0 ↦[wg] default ∗ 0 ↦[wt][ 1 ] none) : IProp GF)

end IrisWasm
