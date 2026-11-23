/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import Init

/-! Binary32 and binary64 arithmetic for Core's scalar and vector operators.
Finite intermediates are signed dyadics; division rounds an exact ratio, and square root compares
squares at the rounding midpoint. No machine float enters these calculations. -/

namespace Wasm.IEEE

inductive Format where | f32 | f64
  deriving DecidableEq, Repr

namespace Format

def width : Format → Nat | .f32 => 32 | .f64 => 64
def frac : Format → Nat | .f32 => 23 | .f64 => 52
private def bias : Format → Nat | .f32 => 127 | .f64 => 1023
abbrev Bits (f : Format) := BitVec f.width

private def unit (f : Format) := 1 <<< f.frac
private def infMag (f : Format) := (2 * f.bias + 1) <<< f.frac
private def signMask (f : Format) : f.Bits := BitVec.ofNat _ (1 <<< (f.width - 1))

def abs (f : Format) (x : f.Bits) := x &&& ~~~f.signMask
def neg (f : Format) (x : f.Bits) := x ^^^ f.signMask
def copySign (f : Format) (x y : f.Bits) := f.abs x ||| (y &&& f.signMask)

private def signedBits (f : Format) (negative : Bool) (mag : Nat) : f.Bits :=
  let x := BitVec.ofNat f.width mag
  if negative then x ||| f.signMask else x

def canonicalNaN (f : Format) : f.Bits := BitVec.ofNat _ (f.infMag + f.unit / 2)
def isNaN (f : Format) (x : f.Bits) : Bool := f.infMag < (f.abs x).toNat
def isCanonicalNaN (f : Format) (x : f.Bits) : Bool := f.abs x == f.canonicalNaN
def isArithmeticNaN (f : Format) (x : f.Bits) : Bool := f.canonicalNaN ≤ f.abs x

end Format

/-- A generated NaN may have either sign. A noncanonical NaN input also permits every quiet payload. -/
inductive Outcome (f : Format) where
  | exact (bits : f.Bits)
  | nan (allowNoncanonical : Bool)

namespace Outcome

def allows {f : Format} (o : Outcome f) (x : f.Bits) : Bool :=
  match o with
  | .exact y => x == y
  | .nan true => f.isArithmeticNaN x
  | .nan false => f.isCanonicalNaN x

def choose {f : Format} : Outcome f → f.Bits
  | .exact x => x
  | .nan _ => f.canonicalNaN

@[simp] theorem allows_choose {f : Format} (o : Outcome f) : o.allows o.choose = true := by
  cases o with
  | exact x => simp [allows, choose]
  | nan b => cases f <;> cases b <;> decide

end Outcome

/-- Internal exact quantities. A finite value is `(-1)^s * n * 2^e`; zero retains its sign.
For arithmetic, the only information needed about a NaN is whether its payload is noncanonical. -/
inductive Number where
  | finite (negative : Bool) (n : Nat) (e : Int)
  | inf (negative : Bool)
  | nan (noncanonical : Bool)

namespace Format

def decode (f : Format) (x : f.Bits) : Number :=
  let mag := (f.abs x).toNat
  let field := mag >>> f.frac
  let fraction := mag &&& (f.unit - 1)
  if mag > f.infMag then .nan (fraction != f.unit / 2)
  else if mag == f.infMag then .inf x.msb
  else if field == 0 then .finite x.msb fraction (1 - (f.bias : Int) - f.frac)
  else .finite x.msb (f.unit + fraction) ((field : Int) - f.bias - f.frac)

/-- Given the truncated magnitude `q` and a comparison to the midpoint, resolve a tie to even. -/
private def roundAt (q : Nat) (midpoint : Ordering) : Nat :=
  if midpoint == .gt || (midpoint == .eq && q.testBit 0) then q + 1 else q

private def roundQuotient (n d : Nat) : Nat :=
  if d == 1 then n else
  let q := n / d
  roundAt q (compare (2 * (n - q * d)) d)

private def scale (n d : Nat) (e : Int) : Nat × Nat :=
  if e < 0 then (n, d <<< e.natAbs) else (n <<< e.toNat, d)

private def floorLogRatio (n d : Nat) : Int :=
  let k : Int := (n.log2 : Int) - d.log2
  if d == 1 then k else
  let (a, b) := scale n d (-k)
  if a < b then k - 1 else k

private def quantum (f : Format) (binade : Int) : Int := max (1 - (f.bias : Int)) binade - f.frac

/-- `m` is measured in units of `2^q`. Adding the hidden bit carries into the exponent field:
this also handles subnormal-to-normal, carry on rounding, and overflow to infinity. -/
private def pack (f : Format) (s : Bool) (m : Nat) (q : Int) : f.Bits :=
  let base := (q + f.frac + f.bias - 1).toNat <<< f.frac
  f.signedBits s (min f.infMag (base + m))

private def roundRatio (f : Format) (s : Bool) (n d : Nat) (e : Int) : f.Bits :=
  if n == 0 then f.signedBits s 0 else
  let q := f.quantum (e + floorLogRatio n d)
  let (a, b) := scale n d (e - q)
  f.pack s (roundQuotient a b) q

def encode (f : Format) : Number → Outcome f
  | .finite s n e => .exact (f.roundRatio s n 1 e)
  | .inf s => .exact (f.signedBits s f.infMag)
  | .nan b => .nan b

private def signedInt (s : Bool) (m : Nat) : Int := if s then -(m : Int) else m

private def addExact : Number → Number → Number
  | .nan a, .nan b => .nan (a || b)
  | .nan b, _ | _, .nan b => .nan b
  | .inf a, .inf b => if a == b then .inf a else .nan false
  | .inf s, _ | _, .inf s => .inf s
  | .finite a m e, .finite b n k =>
    if m == 0 then .finite (if n == 0 then a && b else b) n k
    else if n == 0 then .finite a m e
    else
      let q := min e k
      let v := signedInt a (m <<< (e-q).toNat) + signedInt b (n <<< (k-q).toNat)
      .finite (v < 0) v.natAbs q

private def mulExact : Number → Number → Number
  | .nan a, .nan b => .nan (a || b)
  | .nan b, _ | _, .nan b => .nan b
  | .inf a, .inf b => .inf (a.xor b)
  | .inf a, .finite b n _ | .finite b n _, .inf a => if n == 0 then .nan false else .inf (a.xor b)
  | .finite a m e, .finite b n k => .finite (a.xor b) (m * n) (e + k)

def add (f : Format) (x y : f.Bits) := f.encode (addExact (f.decode x) (f.decode y))
def sub (f : Format) (x y : f.Bits) := f.add x (f.neg y)
def mul (f : Format) (x y : f.Bits) := f.encode (mulExact (f.decode x) (f.decode y))

def fma (f : Format) (x y z : f.Bits) : Outcome f :=
  f.encode (addExact (mulExact (f.decode x) (f.decode y)) (f.decode z))

def div (f : Format) (x y : f.Bits) : Outcome f :=
  match f.decode x, f.decode y with
  | .nan a, .nan b => .nan (a || b)
  | .nan b, _ | _, .nan b => .nan b
  | .inf _, .inf _ => .nan false
  | .inf a, .finite b _ _ => .exact (f.signedBits (a.xor b) f.infMag)
  | .finite a _ _, .inf b => .exact (f.signedBits (a.xor b) 0)
  | .finite a m e, .finite b n k =>
    if n == 0 then
      if m == 0 then .nan false else .exact (f.signedBits (a.xor b) f.infMag)
    else .exact (f.roundRatio (a.xor b) m n (e - k))

def sqrt (f : Format) (x : f.Bits) : Outcome f :=
  match f.decode x with
  | .nan b => .nan b
  | .inf true => .nan false
  | .inf false => .exact x
  | .finite s m e =>
    if m == 0 then .exact x else if s then .nan false else
    let q := f.quantum (((m.log2 : Int) + e) / 2)
    let (a, b) := scale m 1 (e - 2*q)
    let r := (a / b).sqrt
    -- Compare sqrt(a/b) with r + 1/2 without approximating the root.
    .exact (f.pack false (roundAt r (compare (4*a) (b * (2*r+1)^2))) q)

inductive IntegralMode where | ceil | floor | trunc | nearest

def integral (f : Format) (mode : IntegralMode) (x : f.Bits) : Outcome f :=
  match f.decode x with
  | .nan b => .nan b
  | .inf _ => .exact x
  | .finite s m e =>
    if e ≥ 0 || m == 0 then .exact x else
    let k := e.natAbs
    let n := m >>> k
    let rounded := match mode with
      | .nearest => roundQuotient m (1 <<< k)
      | .trunc => n
      | .ceil => if !s && m != n <<< k then n+1 else n
      | .floor => if s && m != n <<< k then n+1 else n
    .exact (f.roundRatio s rounded 1 0)

/-- IEEE ordered comparison. Unlike bit-pattern equality, the two zeros compare equal. -/
def cmp (f : Format) (x y : f.Bits) : Option Ordering :=
  let a := f.abs x
  let b := f.abs y
  if a.toNat > f.infMag || b.toNat > f.infMag then none
  else if x.msb == y.msb then some (if x.msb then compare b a else compare a b)
  else if a == 0 && b == 0 then some .eq else some (if x.msb then .lt else .gt)

def minMax (f : Format) (maximum : Bool) (x y : f.Bits) : Outcome f :=
  match f.cmp x y with
  | none => .nan ((f.isNaN x && !f.isCanonicalNaN x) || (f.isNaN y && !f.isCanonicalNaN y))
  | some .eq => .exact (if maximum == x.msb then y else x)
  | some .lt => .exact (if maximum then y else x)
  | some .gt => .exact (if maximum then x else y)

private def intBounds (signed : Bool) (width : Nat) : Int × Int :=
  let limit : Int := 1 <<< (if signed then width-1 else width)
  (if signed then -limit else 0, limit-1)

private def truncInt (s : Bool) (m : Nat) (e : Int) : Int :=
  signedInt s (if e < 0 then m >>> e.natAbs else m <<< e.toNat)

def truncToInt (f : Format) (signed : Bool) (width : Nat) (x : f.Bits) : Option (BitVec width) := do
  let .finite s m e := f.decode x | none
  let i := truncInt s m e
  let (lo, hi) := intBounds signed width
  guard (lo ≤ i && i ≤ hi)
  return BitVec.ofInt width i

def truncSat (f : Format) (signed : Bool) (width : Nat) (x : f.Bits) : BitVec width :=
  let (lo, hi) := intBounds signed width
  let i := match f.decode x with
    | .nan _ => 0
    | .inf s => if s then lo else hi
    | .finite s m e => max lo (min hi (truncInt s m e))
  BitVec.ofInt width i

def fromInt (f : Format) (i : Int) : f.Bits := f.roundRatio (i < 0) i.natAbs 1 0

def convert (src dst : Format) (x : src.Bits) : Outcome dst := dst.encode (src.decode x)

end Format
end Wasm.IEEE
