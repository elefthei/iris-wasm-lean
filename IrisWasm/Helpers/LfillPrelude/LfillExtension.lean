/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import Wasm.Operations
import Wasm.Opsem
import Wasm.ListExtra

/-! Port of `theories/iris/helpers/lfill_prelude/lfill_extension.v`: total evaluation contexts. -/

namespace IrisWasm

open Wasm

#rocq_ignore iriswasm.ai_list_eq_dec "List AdministrativeInstruction has DecidableEq by instance resolution"
#rocq_ignore iriswasm.ai_eq_dec "AdministrativeInstruction has a DecidableEq instance in Wasm.Datatypes"
#rocq_ignore iriswasm.value_list_eq_dec "List Value has DecidableEq by instance resolution"
#rocq_ignore iriswasm.lholed_eq_dec "Lholed derives DecidableEq in Wasm.Datatypes"

@[rocq_alias iriswasm.size_of_instruction]
def sizeOfInstruction : AdministrativeInstruction → Nat
  | .label _ _ LI => (LI.map sizeOfInstruction).sum + 1
  | .local _ _ LI => (LI.map sizeOfInstruction).sum + 1
  | _ => 1

@[rocq_alias iriswasm.length_rec]
def lengthRec (es : List AdministrativeInstruction) : Nat := (es.map sizeOfInstruction).sum

/-- An object of `ValidHoled n` is an `Lholed` shallow enough for a `br n` to be placed inside and
be stuck. The left-hand sides are constant. -/
@[rocq_alias iriswasm.valid_holed]
inductive ValidHoled : Nat → Type where
  | base {n : Nat} : List Value → List AdministrativeInstruction → ValidHoled n
  | rec_ {n : Nat} : List Value → Nat → List AdministrativeInstruction → ValidHoled n →
      List AdministrativeInstruction → ValidHoled (n + 1)
  deriving DecidableEq

#rocq_ignore iriswasm.valid_holed_eq_dec "ValidHoled derives DecidableEq"

/-- Contexts with constant left-hand sides and no depth constraint. -/
@[rocq_alias iriswasm.simple_valid_holed]
inductive SimpleValidHoled where
  | base : List Value → List AdministrativeInstruction → SimpleValidHoled
  | rec_ : List Value → Nat → List AdministrativeInstruction → SimpleValidHoled →
      List AdministrativeInstruction → SimpleValidHoled
  deriving DecidableEq

#rocq_ignore iriswasm.simple_valid_holed_eq_dec "SimpleValidHoled derives DecidableEq"

/-- Contexts that may also go through `local` frames. -/
@[rocq_alias iriswasm.llholed]
inductive Llholed where
  | base : List Value → List AdministrativeInstruction → Llholed
  | label : List Value → Nat → List AdministrativeInstruction → Llholed →
      List AdministrativeInstruction → Llholed
  | local : List Value → Nat → Frame → Llholed → List AdministrativeInstruction → Llholed
  deriving DecidableEq

#rocq_ignore iriswasm.llholed_eq_dec "Llholed derives DecidableEq"

@[rocq_alias iriswasm.vfill]
def vfill : {n : Nat} → ValidHoled n → List AdministrativeInstruction → List AdministrativeInstruction
  | _, .base bef aft, es => vToEList bef ++ es ++ aft
  | _, .rec_ bef n es0 vh aft, es => vToEList bef ++ .label n es0 (vfill vh es) :: aft

@[rocq_alias iriswasm.sfill]
def sfill : SimpleValidHoled → List AdministrativeInstruction → List AdministrativeInstruction
  | .base bef aft, es => vToEList bef ++ es ++ aft
  | .rec_ bef n es0 sh aft, es => vToEList bef ++ .label n es0 (sfill sh es) :: aft

@[rocq_alias iriswasm.llfill]
def llfill : Llholed → List AdministrativeInstruction → List AdministrativeInstruction
  | .base bef aft, es => vToEList bef ++ es ++ aft
  | .label bef n es0 lh aft, es => vToEList bef ++ .label n es0 (llfill lh es) :: aft
  | .local bef n f lh aft, es => vToEList bef ++ .local n f (llfill lh es) :: aft

@[rocq_alias iriswasm.sh_push_const]
def shPushConst : SimpleValidHoled → List Value → SimpleValidHoled
  | .base bef aft, vs => .base (vs ++ bef) aft
  | .rec_ bef n es sh aft, vs => .rec_ (vs ++ bef) n es sh aft

@[rocq_alias iriswasm.sh_append]
def shAppend : SimpleValidHoled → List AdministrativeInstruction → SimpleValidHoled
  | .base bef aft, e => .base bef (aft ++ e)
  | .rec_ bef n es lh aft, e => .rec_ bef n es lh (aft ++ e)

@[rocq_alias iriswasm.vh_push_const]
def vhPushConst : {n : Nat} → ValidHoled n → List Value → ValidHoled n
  | _, .base bef aft, vs => .base (vs ++ bef) aft
  | _, .rec_ bef m es vh aft, vs => .rec_ (vs ++ bef) m es vh aft

@[rocq_alias iriswasm.vh_append]
def vhAppend : {n : Nat} → ValidHoled n → List AdministrativeInstruction → ValidHoled n
  | _, .base bef aft, e => .base bef (aft ++ e)
  | _, .rec_ bef m es vh aft, e => .rec_ bef m es vh (aft ++ e)

@[rocq_alias iriswasm.llh_push_const]
def llhPushConst : Llholed → List Value → Llholed
  | .base bef aft, vs => .base (vs ++ bef) aft
  | .label bef m es lh aft, vs => .label (vs ++ bef) m es lh aft
  | .local bef n f lh aft, vs => .local (vs ++ bef) n f lh aft

@[rocq_alias iriswasm.llh_append]
def llhAppend : Llholed → List AdministrativeInstruction → Llholed
  | .base bef aft, e => .base bef (aft ++ e)
  | .label bef m es lh aft, e => .label bef m es lh (aft ++ e)
  | .local bef n f lh aft, e => .local bef n f lh (aft ++ e)

/-- Given a `ValidHoled (m + 1)`, attempts to give back an "equal" `ValidHoled m`. -/
@[rocq_alias iriswasm.vh_decrease]
def vhDecrease : {m : Nat} → ValidHoled (m + 1) → Option (ValidHoled m)
  | _, .base bef aft => some (.base bef aft)
  | 0, .rec_ _ _ _ _ _ => none
  | _ + 1, .rec_ bef m es vh aft => (vhDecrease vh).map fun vh' => .rec_ bef m es vh' aft

@[rocq_alias iriswasm.vh_increase]
def vhIncrease : {m : Nat} → ValidHoled m → ValidHoled (m + 1)
  | _, .base bef aft => .base bef aft
  | _, .rec_ bef n es vh aft => .rec_ bef n es (vhIncrease vh) aft

/-- Coq indexes the result by `n + m`; Lean uses `m + n` so that the recursion is definitional. -/
@[rocq_alias iriswasm.vh_increase_repeat]
def vhIncreaseRepeat {m : Nat} (vh : ValidHoled m) : (n : Nat) → ValidHoled (m + n)
  | 0 => vh
  | n + 1 => vhIncrease (vhIncreaseRepeat vh n)

/-- The constant prefix of a context, as values. -/
private def constsOf (bef : List AdministrativeInstruction) : Option (List Value) :=
  those (bef.map fun
    | .basic (.const v) => some v
    | _ => none)

@[rocq_alias iriswasm.vh_of_lh]
def vhOfLh : Lholed → (i : Nat) → Option (ValidHoled i)
  | .base bef aft, _ => (constsOf bef).map fun bef => .base bef aft
  | .rec_ _ _ _ _ _, 0 => none
  | .rec_ bef n es lh aft, i + 1 =>
    match constsOf bef with
    | some bef => (vhOfLh lh i).map fun vh => .rec_ bef n es vh aft
    | none => none

@[rocq_alias iriswasm.lh_of_vh]
def lhOfVh : {i : Nat} → ValidHoled i → Lholed
  | _, .base bef aft => .base (bef.map fun x => .basic (.const x)) aft
  | _, .rec_ bef n es vh aft => .rec_ (bef.map fun x => .basic (.const x)) n es (lhOfVh vh) aft

@[rocq_alias iriswasm.lh_of_sh]
def lhOfSh : SimpleValidHoled → Lholed
  | .base bef aft => .base (bef.map fun x => .basic (.const x)) aft
  | .rec_ bef n es sh aft => .rec_ (bef.map fun x => .basic (.const x)) n es (lhOfSh sh) aft

@[rocq_alias iriswasm.llh_of_lh]
def llhOfLh : Lholed → Option Llholed
  | .base bef aft => (constsOf bef).map fun bef => .base bef aft
  | .rec_ bef n es lh aft =>
    match constsOf bef with
    | some bef => (llhOfLh lh).map fun lh' => .label bef n es lh' aft
    | none => none

#rocq_ignore iriswasm.rewrite_cats1_list "ssreflect list-shape rewriting; Lean list literals need no rewriting"

end IrisWasm
