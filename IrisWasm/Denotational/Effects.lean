import CTree.Misc.Pure
import IrisWasm.Language.Iris.Iris

/-! Effects used by a single Wasm reduction layer and by its host-facing resumption. -/

namespace IrisWasm.Denotational
open Wasm

abbrev Cfg := Expr × State

abbrev HostCallE : ITree.Effect :=
  ⟨FunctionType × Hostfuncidx × List Value, fun _ ↦ StoreRecord × Expr⟩

inductive ChoiceOp where
  | grow
  | trim (a b : Nat)

abbrev ChoiceE : ITree.Effect := ⟨ChoiceOp, fun
  | .grow => Bool
  | .trim a b => {p : Nat × Nat // p.1 ≤ a ∧ p.2 ≤ b ∧ p.1 + p.2 < a + b}⟩

abbrev Tree := CTree.CTree HostCallE ChoiceE

/-- One reduction layer: even a continuation with infinitely many possible answers has only
finite paths. Steps and host interactions belong to the resumption, not to this program. -/
inductive Prog (E : ITree.Effect.{0}) (α : Type) where
  | ret (x : α)
  | stuck
  | vis (o : E.I) (k : E.O o → Prog E α)
  | br (b : ChoiceE.I) (k : ChoiceE.O b → Prog E α)

namespace Prog

variable {E : ITree.Effect.{0}} {α β γ : Type}

def bind (p : Prog E α) (f : α → Prog E β) : Prog E β :=
  match p with
  | .ret x => f x
  | .stuck => .stuck
  | .vis o k => .vis o fun x ↦ (k x).bind f
  | .br b k => .br b fun x ↦ (k x).bind f

instance : Monad (Prog E) where
  pure := .ret
  bind := bind

theorem bind_assoc (p : Prog E α) (f : α → Prog E β) (g : β → Prog E γ) :
    (p.bind f).bind g = p.bind (fun x ↦ (f x).bind g) := by
  induction p <;> simp [bind, *]

end Prog

/-- No visible request survives the state handler. -/
abbrev ClosedProg := Prog ⟨Empty, Empty.elim⟩

namespace ClosedProg

variable {α β : Type}

noncomputable def toTree : ClosedProg α → Tree α
  | .ret x => pure x
  | .stuck => .stuck
  | .vis o _ => nomatch o
  | .br b k => .br b fun x ↦ toTree (k x)

@[simp] theorem toTree_ret (x : α) : toTree (pure x) = (pure x : Tree α) := rfl
@[simp] theorem toTree_stuck : toTree (.stuck : ClosedProg α) = .stuck := rfl
@[simp] theorem toTree_br (b : ChoiceE.I) (k : ChoiceE.O b → ClosedProg α) :
    toTree (.br b k) = .br b (fun x ↦ toTree (k x)) := rfl

theorem toTree_bind (p : ClosedProg α) (f : α → ClosedProg β) :
    toTree (p.bind f) = toTree p >>= (fun x ↦ toTree (f x)) := by
  induction p with
  | ret => simp [Prog.bind, toTree]
  | stuck => simp [Prog.bind, toTree]
  | vis o => exact nomatch o
  | br _ _ ih => simp [Prog.bind, toTree, ih]

theorem finite (p : ClosedProg α) : CTree.PureFinite (toTree p) := by
  induction p with
  | ret x => exact .ret x
  | stuck => exact .stuck
  | vis o => exact nomatch o
  | br b _ ih => exact .br b _ ih

/-- Choose successful growth where it is offered; retain no prefix or suffix on strict trim. -/
def choose (b : ChoiceE.I) : Option (ChoiceE.O b) :=
  match b with
  | .grow => some true
  | .trim a b =>
    if h : 0 < a + b then some ⟨(0, 0), Nat.zero_le _, Nat.zero_le _, h⟩ else none

theorem choose_none_iff (b : ChoiceE.I) : choose b = none ↔ ¬ Nonempty (ChoiceE.O b) := by
  cases b with
  | grow => simp [choose, ChoiceE, show Nonempty Bool from ⟨true⟩]
  | trim a b =>
    simp only [choose]
    split
    · rename_i h
      simp only [Option.some_ne_none, false_iff, Classical.not_not]
      exact ⟨⟨(0, 0), Nat.zero_le _, Nat.zero_le _, h⟩⟩
    · rename_i h
      simp only [true_iff]
      rintro ⟨⟨⟨x, y⟩, _, _, hxy⟩⟩
      omega

def run : ClosedProg α → Option α
  | .ret x => some x
  | .stuck => none
  | .vis o _ => nomatch o
  | .br b k => (choose b).bind fun x ↦ run (k x)

/-- Answers for one path. Two occurrences of the same choice need not agree. -/
inductive Path : ClosedProg α → Type where
  | ret (x : α) : Path (.ret x)
  | br {b : ChoiceE.I} {k : ChoiceE.O b → ClosedProg α} (x : ChoiceE.O b) :
    Path (k x) → Path (.br b k)

def Path.result {p : ClosedProg α} : Path p → α
  | .ret x => x
  | .br _ rest => rest.result

end ClosedProg

inductive Front where
  | next (es : Expr)
  | done (v : Val)

inductive WasmOp where
  | getLocal (j : Nat)
  | setLocal (j : Nat) (v : Value)
  | getGlobal (j : Nat)
  | setGlobal (j : Nat) (v : Value)
  | callAddr (j : Nat)
  | tableAddr (j : Nat)
  | closureAt (a : Funcaddr)
  | typeAt (j : Nat)
  | readMem (x : Nat) (t : ValueType) (pack : Option (PackedType × Sx)) (addr off : Nat)
  | writeMem (x : Nat) (t : ValueType) (pack : Option PackedType) (addr off : Nat) (v : Value)
  | currentPages (x : Nat)
  | growPages (x : Nat) (delta : AddressOperand)
  | swapFrame (f : Frame)

abbrev WasmE : ITree.Effect := ⟨WasmOp, fun
  | .getLocal _ | .getGlobal _ => Value
  | .setLocal .. | .setGlobal .. => Unit
  | .callAddr _ => Funcaddr
  | .tableAddr _ => Option Funcaddr
  | .closureAt _ => FunctionClosure
  | .typeAt _ => Option FunctionType
  | .readMem .. => Option Value
  | .writeMem .. => Bool
  | .currentPages _ | .growPages .. => Value
  | .swapFrame _ => Frame⟩

abbrev WasmProg := Prog WasmE

def withMemory {α : Type} (s : StoreRecord) (inst : Instance) (x : Nat)
    (k : Nat → Memory → ClosedProg α) (missing : ClosedProg α := .stuck) : ClosedProg α :=
  match inst.memory[x]? with
  | none => missing
  | some i => match s.mems[i]? with
    | none => missing
    | some m => k i m

/-- Interpret a state request. Failed growth is permitted even without a memory lookup. -/
def handle (o : WasmE.I) : StateT State ClosedProg (WasmE.O o) := fun σ ↦
  let (s, locs, inst) := σ
  match o with
  | .getLocal j => match locs[j]? with
    | some v => pure (v, σ)
    | none => .stuck
  | .setLocal j v =>
    if j < locs.length then pure ((), s, locs.set j v, inst) else .stuck
  | .getGlobal j => match sglobVal s inst j with
    | some v => pure (v, σ)
    | none => .stuck
  | .setGlobal j v => match supdateGlob s inst j v with
    | some s' => pure ((), s', locs, inst)
    | none => .stuck
  | .callAddr j => match inst.funcs[j]? with
    | some a => pure (a, σ)
    | none => .stuck
  | .tableAddr j => pure (stabAddr s ⟨locs, inst⟩ j, σ)
  | .closureAt a => match s.funcs[a]? with
    | some cl => pure (cl, σ)
    | none => .stuck
  | .typeAt j => pure (stypes s inst j, σ)
  | .readMem x t pack addr off => withMemory s inst x fun _ m ↦
    let bytes := match pack with
      | none => load m addr off (lengthT t)
      | some (tp, sx) => loadPacked sx m addr off (lengthTp tp) (lengthT t)
    pure (bytes.map (fun bs ↦ wasmDeserialise bs t), σ)
  | .writeMem x t pack addr off v => withMemory s inst x fun i m ↦
    let m' := match pack with
      | none => store m addr off (bits v) (lengthT t)
      | some tp => storePacked m addr off (bits v) (lengthTp tp)
    match m' with
    | none => pure (false, σ)
    | some mem => pure (true, updSMem s (updateListAt s.mems i mem), locs, inst)
  | .currentPages x => withMemory s inst x fun _ m ↦
    let n := memSize m
    if lengthMem m = n * pageSize ∧ n < 2^m.type.address.width then pure (m.type.address.natValue n, σ)
    else .stuck
  | .growPages x delta => withMemory s inst x (missing := pure (delta.failure, σ)) fun i m ↦
    if memSize m < 2^delta.address.width then
      match memGrow m delta.unsigned with
      | none => pure (delta.failure, σ)
      | some mem => .br .grow fun ok ↦
        if ok then pure (delta.result (memSize m), updSMem s (updateListAt s.mems i mem), locs, inst)
        else pure (delta.failure, σ)
    else pure (delta.failure, σ)
  | .swapFrame f => pure (Frame.mk locs inst, s, f.locs, f.inst)

/-- Interpret a request and continue in its resulting state, leaving only choices. -/
def close {α : Type} (p : WasmProg α) (σ : State) : ClosedProg (α × State) :=
  match p with
  | .ret x => .ret (x, σ)
  | .stuck => .stuck
  | .vis o k => (handle o σ).bind fun (x, σ') ↦ close (k x) σ'
  | .br b k => .br b fun x ↦ close (k x) σ

theorem close_bind {α β : Type} (p : WasmProg α) (k : α → WasmProg β) (σ : State) :
    close (p >>= k) σ = (close p σ).bind fun (x, σ') ↦ close (k x) σ' := by
  change close (p.bind k) σ = _
  induction p generalizing σ with
  | ret => rfl
  | stuck => rfl
  | vis _ _ ih => simp [Prog.bind, close, Prog.bind_assoc, ih]
  | br _ _ ih => simp [Prog.bind, close, ih]

theorem handle_finite (o : WasmE.I) (σ : State) :
    CTree.PureFinite (ClosedProg.toTree (handle o σ)) := ClosedProg.finite _

end IrisWasm.Denotational
