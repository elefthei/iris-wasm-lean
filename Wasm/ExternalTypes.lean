import Wasm.CoreTypes
import Wasm.Datatypes

namespace Wasm

#rocq_ignore iriswasm.limit_typing "Core limits bound the minimum and order both endpoints"
def limitTyping (lim : Limits) (k : Nat) : Bool :=
  decide (lim.min ≤ k) &&
    match lim.max with
    | none => true
    | some n => decide (lim.min ≤ n ∧ n ≤ k)

def Limits.Within (l : Limits) (k : Nat) : Prop :=
  l.min ≤ k ∧ ∀ n, l.max = some n → l.min ≤ n ∧ n ≤ k

theorem limitTyping_iff (l : Limits) (k : Nat) : limitTyping l k = true ↔ l.Within k := by
  rcases l with ⟨n, m⟩; cases m <;> simp [limitTyping, Limits.Within]

def Limits.maxMatches : Option Nat → Option Nat → Bool
  | _, none => true
  | some a, some b => decide (a ≤ b)
  | none, some _ => false

@[simp] theorem Limits.maxMatches_self (m : Option Nat) : Limits.maxMatches m m = true := by
  cases m <;> simp [Limits.maxMatches]

def Limits.matches (actual required : Limits) : Bool :=
  decide (required.min ≤ actual.min) && Limits.maxMatches actual.max required.max

def Limits.Sub (a b : Limits) : Prop :=
  b.min ≤ a.min ∧ ∀ n, b.max = some n → ∃ k, a.max = some k ∧ k ≤ n

/-- A required maximum cannot be satisfied by an unbounded import. -/
theorem Limits.matches_iff (a b : Limits) : a.matches b = true ↔ a.Sub b := by
  rcases a with ⟨a, m⟩; rcases b with ⟨b, n⟩
  cases m <;> cases n <;> simp [Limits.matches, Limits.maxMatches, Limits.Sub]

abbrev MemoryType.matches (a b : MemoryType) : Bool :=
  a.address == b.address && a.limits.matches b.limits

theorem MemoryType.matches_iff (a b : MemoryType) :
    a.matches b = true ↔ a.address = b.address ∧ a.limits.Sub b.limits := by
  simp [MemoryType.matches, Limits.matches_iff]

namespace CoreTypes

/-- Source uses are type indices. Closed import/export interfaces use group projections. -/
inductive External (U : Type) where
  | func (type : U)
  | tag (type : U)
  | global_ (isMutable : Bool) (type : Val U)
  | mem (type : MemoryType)
  | table (address : AddrType) (limits : Limits) (element : Ref U)
  deriving DecidableEq, Repr

def External.close (types : Array Defined) : External Nat → Option (External Defined)
  | .func i => do
    let d ← types[i]?
    guard (d.kind == some .func)
    return .func d
  | .tag i => do
    let d ← types[i]?
    let some (.func _ []) := d.expand | none
    return .tag d
  | .global_ m t => .global_ m <$> closeVal types t
  | .mem mt => do
    guard (limitTyping mt.limits mt.address.pageLimit)
    return .mem mt
  | .table at_ l e => do
    guard (limitTyping l (2 ^ at_.width - 1))
    return .table at_ l (← closeRef types e)

def External.matches : External Defined → External Defined → Bool
  | .func a, .func b => a.matches b
  | .tag a, .tag b => a.matches b && b.matches a
  | .global_ m a, .global_ n b => m == n && a.matches b && (!n || b.matches a)
  | .mem a, .mem b => a.matches b
  | .table a l e, .table b k f => a == b && l.matches k && e.matches f && f.matches e
  | _, _ => false

end CoreTypes
end Wasm
