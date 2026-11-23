import Std.Data.ByteSlice
import Wasm.ExternalTypes

/-! Bounded readers for the Core binary grammar. Section and body windows share the input bytes. -/

namespace Wasm

structure DecodeError where
  offset : Nat
  message : String
  deriving Repr, DecidableEq

namespace Binary

abbrev Reader := StateT ByteSlice (Except DecodeError)

private def failAt {α : Type} (offset : Nat) (message : String) : Reader α :=
  throw { offset, message }

def byte : Reader UInt8 := fun s ↦
  if h : 0 < s.size then .ok (s.get ⟨0, h⟩, s.slice 1)
  else .error ⟨s.start, "unexpected end of input"⟩

def take (n : Nat) : Reader ByteSlice := fun s ↦
  if n ≤ s.size then .ok (s.slice 0 n, s.slice n)
  else .error ⟨s.start, "length exceeds enclosing input"⟩

/-- Execute a reader inside a section or function body and reject a trailing suffix. -/
def complete {α : Type} (p : Reader α) (s : ByteSlice) : Except DecodeError α := do
  let (x, rest) ← p.run s
  if rest.size != 0 then throw ⟨rest.start, "trailing bytes"⟩
  return x

theorem byte_iff {s rest : ByteSlice} {b : UInt8} :
    byte.run s = .ok (b, rest) ↔
      ∃ h : 0 < s.size, s.get ⟨0, h⟩ = b ∧ rest = s.slice 1 := by
  by_cases h : 0 < s.size <;> simp [StateT.run, byte, h, eq_comm]

theorem complete_iff {α : Type} {p : Reader α} {s : ByteSlice} {x : α} :
    complete p s = .ok x ↔ ∃ rest, p.run s = .ok (x, rest) ∧ rest.size = 0 := by
  cases hr : p.run s with
  | error e => simp [complete, hr, Bind.bind, Except.bind]
  | ok pair =>
    rcases pair with ⟨y, rest⟩
    by_cases he : rest.size = 0 <;>
      simp [complete, hr, Bind.bind, Except.bind, Pure.pure, Except.pure, he, and_assoc]

private def lastDigit (signed : Bool) (b : UInt8) : Int :=
  if signed && b.toNat ≥ 64 then (b.toNat : Int) - 128 else b.toNat

private def Fits (signed : Bool) (width : Nat) (x : Int) : Prop :=
  let bound : Int := 2 ^ (if signed then width - 1 else width)
  0 < width ∧ (7 ≤ width ∨ (x < bound ∧ (signed = false ∨ -bound ≤ x)))

private instance (sg : Bool) (w : Nat) (x : Int) : Decidable (Fits sg w x) := by
  unfold Fits; infer_instance

/-- The bounded signed/unsigned LEB productions, relating the input to its unconsumed suffix. -/
inductive Leb (sg : Bool) : Nat → ByteSlice → Int → ByteSlice → Prop where
  | last {w s b tail} : byte s = .ok (b, tail) → b.toNat < 128 →
      Fits sg w (lastDigit sg b) → Leb sg w s (lastDigit sg b) tail
  | more {w s b rest hi tail} : byte s = .ok (b, rest) → 128 ≤ b.toNat → 7 < w →
      Leb sg (w - 7) rest hi tail → Leb sg w s (hi * 128 + (b.toNat - 128 : Nat)) tail

def leb (signed : Bool) (width : Nat) (s : ByteSlice) : Except DecodeError (Int × ByteSlice) :=
  match byte s with
  | .error e => .error e
  | .ok (b, rest) =>
    if b.toNat ≥ 128 then
      if h : width > 7 then
        (leb signed (width - 7) rest).map fun (hi, tail) ↦ (hi * 128 + (b.toNat - 128 : Nat), tail)
      else .error ⟨s.start, "integer representation too long"⟩
    else if Fits signed width (lastDigit signed b) then .ok (lastDigit signed b, rest)
    else .error ⟨s.start, "integer too large"⟩
termination_by width

theorem Leb.decode {sg w s x tail} (h : Leb sg w s x tail) : leb sg w s = .ok (x, tail) := by
  induction h with
  | last hr hb hf => rw [leb, hr]; simp [Nat.not_le_of_lt hb, hf]
  | more hr hb hw _ ih => rw [leb, hr]; simp [hb, hw, ih, Except.map]

theorem leb_sound {sg w s x tail} (h : leb sg w s = .ok (x, tail)) : Leb sg w s x tail := by
  rw [leb] at h
  cases hr : byte s with
  | error e => simp [hr] at h
  | ok p =>
    obtain ⟨b, rest⟩ := p
    simp only [hr] at h
    split at h
    · rename_i hb
      split at h
      · rename_i hw
        cases hh : leb sg (w - 7) rest with
        | error e => simp [hh, Except.map] at h
        | ok pair =>
          rcases pair with ⟨hi, tail'⟩
          rw [hh] at h
          cases h
          exact .more hr hb hw (leb_sound hh)
      · contradiction
    · rename_i hb
      split at h
      · rename_i hf
        cases h
        exact .last hr (by omega) hf
      · contradiction
termination_by w

theorem leb_iff {sg w s x tail} : leb sg w s = .ok (x, tail) ↔ Leb sg w s x tail :=
  ⟨leb_sound, Leb.decode⟩

/-- Bounded LEB encodings need not be minimal. Their unused high bits must still be valid. -/
def u32 : Reader Nat := Int.toNat <$> leb false 32
def u64 : Reader Nat := Int.toNat <$> leb false 64
def s33 : Reader Int := leb true 33
def i32 : Reader (BitVec 32) := BitVec.ofInt 32 <$> leb true 32
def i64 : Reader (BitVec 64) := BitVec.ofInt 64 <$> leb true 64

/-- Direct little-endian decoding, including signaling NaN payloads and vector bits. -/
def fixedBits (bytes : Nat) : Reader (BitVec (8 * bytes)) := do
  let s ← take bytes
  return BitVec.ofNat _ (s.foldr (fun b hi ↦ hi * 256 + b.toNat) 0)

def name : Reader String := do
  let s ← take (← u32)
  match String.fromUTF8? s.toByteArray with
  | some text => return text
  | none => failAt s.start "invalid UTF-8 in name"

/-- Each element of a binary vector must consume at least one byte in its enclosing window. -/
def vector {α : Type} (p : Reader α) : Reader (Array α) := do
  let n ← u32
  let s ← get
  if n > s.size then failAt s.start "vector length exceeds enclosing input"
  let mut xs := #[]
  for _ in [:n] do xs := xs.push (← p)
  return xs

open CoreTypes

private def peekByte : Reader UInt8 := fun s ↦
  if h : 0 < s.size then .ok (s.get ⟨0, h⟩, s) else .error ⟨s.start, "unexpected end of input"⟩

private def absHeap? : UInt8 → Option AbsHeap
  | 0x69 => some .exn | 0x6a => some .array | 0x6b => some .struct_ | 0x6c => some .i31
  | 0x6d => some .eq | 0x6e => some .any | 0x6f => some .extern_ | 0x70 => some .func
  | 0x71 => some .none | 0x72 => some .noextern | 0x73 => some .nofunc | 0x74 => some .noexn
  | _ => none

private def nonnegativeIndex : Reader Nat := do
  let pos := (← get).start
  let i ← s33
  if i < 0 then failAt pos "negative type index"
  return i.toNat

def heapType : Reader (Heap Nat) := do
  if let some h := absHeap? (← peekByte) then
    let _ ← byte
    return .abs h
  return .use (← nonnegativeIndex)

private def refFrom (pos : Nat) (tag : UInt8) : Reader (Ref Nat) := do
  if tag == 0x63 || tag == 0x64 then return ⟨tag == 0x63, ← heapType⟩
  if let some h := absHeap? tag then return ⟨true, .abs h⟩
  failAt pos "expected reference type"

def refType : Reader (Ref Nat) := do
  let pos := (← get).start
  refFrom pos (← byte)

private def numVecTag : UInt8 → Option ValueType
  | 0x7f => some .i32 | 0x7e => some .i64 | 0x7d => some .f32
  | 0x7c => some .f64 | 0x7b => some .v128 | _ => none

/-- The number/vector subgrammar, not a decoder for reference types. -/
def numVecType : Reader ValueType := do
  let pos := (← get).start
  let some t := numVecTag (← byte) | failAt pos "expected a numeric or vector type"
  return t

def valType : Reader (Val Nat) := do
  let pos := (← get).start
  let tag ← byte
  match numVecTag tag with
  | some .i32 => return .i32 | some .i64 => return .i64 | some .f32 => return .f32
  | some .f64 => return .f64 | some .v128 => return .v128
  | none => return .ref (← refFrom pos tag)

def mutability : Reader Bool := do
  let pos := (← get).start
  match ← byte with
  | 0 => return false
  | 1 => return true
  | _ => failAt pos "invalid mutability"

def fieldType : Reader (Field Nat) := do
  let st ← match ← peekByte with
    | 0x77 => byte *> pure Storage.i16
    | 0x78 => byte *> pure Storage.i8
    | _ => Storage.val <$> valType
  return ⟨← mutability, st⟩

def compositeType : Reader (Composite Nat) := do
  let pos := (← get).start
  match ← byte with
  | 0x5e => return .array (← fieldType)
  | 0x5f => return .struct_ (← vector fieldType).toList
  | 0x60 => return .func (← vector valType).toList (← vector valType).toList
  | _ => failAt pos "expected composite type"

def subType : Reader (CoreTypes.Sub Nat) := do
  let tag ← peekByte
  if tag == 0x4f || tag == 0x50 then
    let _ ← byte
    return ⟨tag == 0x4f, (← vector u32).toList, ← compositeType⟩
  return ⟨true, [], ← compositeType⟩

def recType : Reader (RecGroup Nat) := do
  if (← peekByte) == 0x4e then
    let _ ← byte
    return (← vector subType).toList
  return [← subType]

/-- A type section preserves the grouping and every declared supertype, including invalid ones. -/
def typeSection : Reader (Array (RecGroup Nat)) := vector recType

def blockTypeWith {V : Type} (inline : Reader V) : Reader (CoreTypes.BlockType V) := do
  let tag ← peekByte
  if tag == 0x40 then return ← byte *> pure (.result none)
  if (0x7b ≤ tag && tag ≤ 0x7f) || tag == 0x63 || tag == 0x64 || (absHeap? tag).isSome then
    return .result (some (← inline))
  return .index (← nonnegativeIndex)

def blockType : Reader (CoreTypes.BlockType (Val Nat)) := blockTypeWith valType

/-- Decode the payload after a direct branch or return opcode. Label depths belong to validation. -/
def branchPayload : UInt8 → Reader BasicInstruction
  | 0x0c => return .br (← u32)
  | 0x0d => return .brIf (← u32)
  | 0x0e => return .brTable (← vector u32).toList (← u32)
  | 0x0f => return .return_
  | _ => fun s ↦ .error ⟨s.start - 1, "expected a branch opcode"⟩

private inductive Enclosure where
  | block (bt : Wasm.BlockType) (before : Wasm.Expr)
  | loop (bt : Wasm.BlockType) (before : Wasm.Expr)
  | thenArm (bt : Wasm.BlockType) (before : Wasm.Expr)
  | elseArm (bt : Wasm.BlockType) (before yes : Wasm.Expr)

/-- Read through the matching `end`. The caller supplies inline value types and the payload reader
    for other opcodes (already consumed). A section or function body retains its own byte window. -/
def structuredExpr (inline : Reader ValueType) (leaf : UInt8 → Reader BasicInstruction) :
    Reader Wasm.Expr := do
  let mut frames := []
  let mut rev := []
  -- Each iteration consumes at least its opcode, even when a region has an empty body.
  for _ in [:(← get).size] do
    let pos := (← get).start
    let tag ← byte
    match tag with
    | 0x02 | 0x03 | 0x04 =>
      let bt ← blockTypeWith inline
      let frame := if tag == 0x02 then Enclosure.block bt rev
        else if tag == 0x03 then .loop bt rev else .thenArm bt rev
      frames := frame :: frames
      rev := []
    | 0x05 =>
      let .thenArm bt before :: rest := frames | failAt pos "unexpected else"
      frames := .elseArm bt before rev.reverse :: rest
      rev := []
    | 0x0b =>
      let code := rev.reverse
      let frame :: rest := frames | return code
      rev := match frame with
        | .block bt before => .block bt code :: before
        | .loop bt before => .loop bt code :: before
        | .thenArm bt before => .if_ bt code [] :: before
        | .elseArm bt before yes => .if_ bt yes code :: before
      frames := rest
    | 0x0c | 0x0d | 0x0e | 0x0f => rev := (← branchPayload tag) :: rev
    | _ => rev := (← leaf tag) :: rev
  failAt (← get).start "unterminated expression"

/-- A length-delimited function body. Keep local groups compressed: a valid six-byte group can
    declare 2^32-1 locals. The local-count bound is on their sum, not on the number of groups. -/
def codeBody {V E : Type} (localType : Reader V) (expression : Reader E) :
    Reader (Array (Nat × V) × E) := do
  let payload ← take (← u32)
  liftM (m := Except DecodeError) <| complete (do
    let count ← u32
    let s ← get
    if count > s.size / 2 then failAt s.start "local groups exceed function body"
    let mut total := 0
    let mut groups := #[]
    for _ in [:count] do
      let pos := (← get).start
      let n ← u32
      total := total + n
      if total ≥ 2^32 then failAt pos "too many locals"
      groups := groups.push (n, ← localType)
    return (groups, ← expression)) payload

def limits : Reader (AddrType × Limits) := do
  let pos := (← get).start
  let tag ← byte
  let (width, hasMax) ← match tag with
    | 0 => pure (AddrType.i32, false) | 1 => pure (.i32, true)
    | 4 => pure (.i64, false) | 5 => pure (.i64, true)
    | _ => failAt pos "invalid limits flags"
  let min ← u64
  let max ← if hasMax then some <$> u64 else pure none
  return (width, ⟨min, max⟩)

def memoryType : Reader MemoryType := do
  let (address, l) ← limits
  return ⟨address, l⟩

def externType : Reader (External Nat) := do
  let pos := (← get).start
  match ← byte with
  | 0 => return .func (← u32)
  | 1 =>
    let e ← refType
    let (a, l) ← limits
    return .table a l e
  | 2 => return .mem (← memoryType)
  | 3 =>
    let t ← valType
    return .global_ (← mutability) t
  | 4 =>
    let attr := (← get).start
    if (← byte) != 0 then failAt attr "invalid tag attribute"
    return .tag (← u32)
  | _ => failAt pos "invalid external type"

def memArg : Reader MemArg := fun s ↦ do
  let (n, p) ← u32 s
  if n ≥ 128 then throw ⟨s.start, "reserved memory alignment flags"⟩
  let (i, q) ← if n ≥ 64 then u32 p else pure (0, p)
  let (offset, r) ← u64 q
  return (⟨i, n % 64, offset⟩, r)

/-- Exactly the two `Bmemarg` productions over their bounded integer fields. -/
inductive MemArgBytes (s : ByteSlice) : MemArg → ByteSlice → Prop where
  | implicitIndex {a offset p r} : a < 64 → u32 s = .ok (a, p) → u64 p = .ok (offset, r) →
      MemArgBytes s ⟨0, a, offset⟩ r
  | explicitIndex {a i offset p q r} : a < 64 → u32 s = .ok (a+64, p) → u32 p = .ok (i, q) →
      u64 q = .ok (offset, r) → MemArgBytes s ⟨i, a, offset⟩ r

theorem memArg_iff {s r : ByteSlice} {ma : MemArg} : memArg s = .ok (ma, r) ↔ MemArgBytes s ma r := by
  constructor
  · intro h
    cases hf : u32 s with
    | error e => simp [memArg, hf, Bind.bind, Except.bind] at h
    | ok pair =>
      obtain ⟨n, p⟩ := pair
      by_cases bad : n ≥ 128
      · simp [memArg, hf, bad, Bind.bind, Except.bind] at h
      by_cases hasIndex : n ≥ 64
      · cases hi : u32 p with
        | error e => simp [memArg, hf, bad, hasIndex, hi, Bind.bind, Except.bind] at h
        | ok pair =>
          obtain ⟨i, q⟩ := pair
          cases ho : u64 q with
          | error e => simp [memArg, hf, bad, hasIndex, hi, ho, Bind.bind, Except.bind] at h
          | ok pair =>
            obtain ⟨off, rest⟩ := pair
            simp [memArg, hf, bad, hasIndex, hi, ho, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
            obtain ⟨rfl, rfl⟩ := h
            exact .explicitIndex (by omega) (by simpa [show n % 64 + 64 = n by omega] using hf) hi ho
      · cases ho : u64 p with
        | error e => simp [memArg, hf, bad, hasIndex, ho, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
        | ok pair =>
          obtain ⟨off, rest⟩ := pair
          simp [memArg, hf, bad, hasIndex, ho, Bind.bind, Except.bind, Pure.pure, Except.pure,
            Nat.mod_eq_of_lt (by omega : n < 64)] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .implicitIndex (by omega) hf ho
  · intro h
    cases h with
    | @implicitIndex a off p r ha hf ho =>
      simp [memArg, hf, ho, show ¬a ≥ 64 by omega, show ¬a ≥ 128 by omega,
        Bind.bind, Except.bind, Pure.pure, Except.pure, Nat.mod_eq_of_lt ha]
    | @explicitIndex a i off p q r ha hf hi ho =>
      simp [memArg, hf, hi, ho, show ¬a+64 ≥ 128 by omega, Bind.bind, Except.bind,
        Pure.pure, Except.pure, Nat.mod_eq_of_lt ha]

/-- Decode the memory index, alignment and offset without checking the module's memory types. -/
def memoryPayload : UInt8 → Reader BasicInstruction
  | 0x28 => .load .i32 none <$> memArg
  | 0x29 => .load .i64 none <$> memArg
  | 0x2a => .load .f32 none <$> memArg
  | 0x2b => .load .f64 none <$> memArg
  | 0x2c => .load .i32 (some (.i8, .s)) <$> memArg
  | 0x2d => .load .i32 (some (.i8, .u)) <$> memArg
  | 0x2e => .load .i32 (some (.i16, .s)) <$> memArg
  | 0x2f => .load .i32 (some (.i16, .u)) <$> memArg
  | 0x30 => .load .i64 (some (.i8, .s)) <$> memArg
  | 0x31 => .load .i64 (some (.i8, .u)) <$> memArg
  | 0x32 => .load .i64 (some (.i16, .s)) <$> memArg
  | 0x33 => .load .i64 (some (.i16, .u)) <$> memArg
  | 0x34 => .load .i64 (some (.i32, .s)) <$> memArg
  | 0x35 => .load .i64 (some (.i32, .u)) <$> memArg
  | 0x36 => .store .i32 none <$> memArg
  | 0x37 => .store .i64 none <$> memArg
  | 0x38 => .store .f32 none <$> memArg
  | 0x39 => .store .f64 none <$> memArg
  | 0x3a => .store .i32 (some .i8) <$> memArg
  | 0x3b => .store .i32 (some .i16) <$> memArg
  | 0x3c => .store .i64 (some .i8) <$> memArg
  | 0x3d => .store .i64 (some .i16) <$> memArg
  | 0x3e => .store .i64 (some .i32) <$> memArg
  | 0x3f => .currentMemory <$> u32
  | 0x40 => .growMemory <$> u32
  | 0xfd => do
    let pos := (← get).start
    match ← u32 with
    | 0 => return .load .v128 none (← memArg)
    | 11 => return .store .v128 none (← memArg)
    | _ => failAt pos "expected a full-width vector memory instruction"
  | _ => fun s ↦ .error ⟨s.start - 1, "expected a memory instruction"⟩

-- The two widths of each scalar family share the same relative opcode ordering.
private def integerTests (t : ValueType) : Array BasicInstruction :=
  #[.testop t .eqz] ++
    (#[.eq, .ne, .lt .s, .lt .u, .gt .s, .gt .u, .le .s, .le .u, .ge .s, .ge .u] :
      Array RelopI).map (fun op ↦ .relop t (.i op))

private def floatTests (t : ValueType) : Array BasicInstruction :=
  (#[.eq, .ne, .lt, .gt, .le, .ge] : Array RelopF).map (fun op ↦ .relop t (.f op))

private def integerOps (t : ValueType) : Array BasicInstruction :=
  (#[.clz, .ctz, .popcnt] : Array UnopI).map (fun op ↦ .unop t (.i op)) ++
    (#[.add, .sub, .mul, .div .s, .div .u, .rem .s, .rem .u, .and, .or, .xor, .shl,
        .shr .s, .shr .u, .rotl, .rotr] : Array BinopI).map (fun op ↦ .binop t (.i op))

private def floatOps (t : ValueType) : Array BasicInstruction :=
  (#[.abs, .neg, .ceil, .floor, .trunc, .nearest, .sqrt] : Array UnopF).map
    (fun op ↦ .unop t (.f op)) ++
  (#[.add, .sub, .mul, .div, .min, .max, .copysign] : Array BinopF).map
    (fun op ↦ .binop t (.f op))

private def conversions (dst src : ValueType) : Array BasicInstruction :=
  #[.cvtop dst .convert src (some .s), .cvtop dst .convert src (some .u)]

private def numericOpcodes : Array BasicInstruction :=
  integerTests .i32 ++ integerTests .i64 ++ floatTests .f32 ++ floatTests .f64 ++
  integerOps .i32 ++ integerOps .i64 ++ floatOps .f32 ++ floatOps .f64 ++
  #[.cvtop .i32 .convert .i64 none] ++ conversions .i32 .f32 ++ conversions .i32 .f64 ++
  conversions .i64 .i32 ++ conversions .i64 .f32 ++ conversions .i64 .f64 ++
  conversions .f32 .i32 ++ conversions .f32 .i64 ++ #[.cvtop .f32 .convert .f64 none] ++
  conversions .f64 .i32 ++ conversions .f64 .i64 ++ #[.cvtop .f64 .convert .f32 none,
    .cvtop .i32 .reinterpret .f32 none, .cvtop .i64 .reinterpret .f64 none,
    .cvtop .f32 .reinterpret .i32 none, .cvtop .f64 .reinterpret .i64 none,
    .unop .i32 (.extendS .i8), .unop .i32 (.extendS .i16), .unop .i64 (.extendS .i8),
    .unop .i64 (.extendS .i16), .unop .i64 (.extendS .i32)]

/-- Scalar instruction payload after dispatch. `0xfc` subopcodes are bounded LEBs, not bytes. -/
def numericPayload (opcode : UInt8) : Reader BasicInstruction := do
  let pos := (← get).start - 1
  match opcode with
  | 0x41 => return .const (.int32 (← i32))
  | 0x42 => return .const (.int64 (← i64))
  | 0x43 => return .const (.float32 ⟨← fixedBits 4⟩)
  | 0x44 => return .const (.float64 ⟨← fixedBits 8⟩)
  | 0xfc =>
    let sub ← u32
    if sub ≥ 8 then failAt pos "expected a saturating conversion"
    let dst := if sub < 4 then ValueType.i32 else .i64
    let src := if sub % 4 < 2 then ValueType.f32 else .f64
    return .cvtop dst .truncSat src (some (if sub % 2 == 0 then .s else .u))
  | _ =>
    if opcode ≥ 0x45 then
      if let some instr := numericOpcodes[opcode.toNat - 0x45]? then return instr
    failAt pos "expected a scalar numeric instruction"

def numericInstr : Reader BasicInstruction := do numericPayload (← byte)

/-- A variable index is syntax; lookup in the module or frame is not a decoder check. -/
def variablePayload : UInt8 → Reader BasicInstruction
  | 0x20 => return .getLocal (← u32)
  | 0x21 => return .setLocal (← u32)
  | 0x22 => return .teeLocal (← u32)
  | 0x23 => return .getGlobal (← u32)
  | 0x24 => return .setGlobal (← u32)
  | _ => fun s ↦ .error ⟨s.start - 1, "expected a local or global instruction"⟩

def variableInstr : Reader BasicInstruction := do variablePayload (← byte)

/-- Decode a vector constant or a full-width `v128` logical operation. -/
def vectorBitsInstr : Reader BasicInstruction := do
  let pos := (← get).start
  if (← byte) != 0xfd then failAt pos "expected SIMD prefix"
  match ← u32 with
  | 12 => return .const (.vec128 (← fixedBits 16))
  | 77 => return .unop .v128 .vnot
  | 78 => return .binop .v128 (.v .and)
  | 79 => return .binop .v128 (.v .andNot)
  | 80 => return .binop .v128 (.v .or)
  | 81 => return .binop .v128 (.v .xor)
  | 82 => return .vbitselect
  | 83 => return .testop .v128 .anyTrue
  | _ => failAt pos "expected vector constant or full-width logical opcode"

/-- Includes legal non-minimal subopcodes: the cursor after the literal is the `fixedBits` suffix. -/
theorem vectorBitsInstr_const {s p q r : ByteSlice} {v : BitVec 128}
    (hp : byte s = .ok (0xfd, p)) (hu : u32 p = .ok (12, q))
    (hv : fixedBits 16 q = .ok (v, r)) : vectorBitsInstr s = .ok (.const (.vec128 v), r) := by
  simp [vectorBitsInstr, Bind.bind, StateT.bind, MonadState.get, getThe, MonadStateOf.get,
    StateT.get, Pure.pure, StateT.pure, Except.bind, Except.pure, hp, hu, hv]

inductive Section where
  | types | imports | functions | tables | memories | tags | globals | exports | start
  | elements | dataCount | code | data
  deriving Repr, DecidableEq

private def sectionOfId : UInt8 → Option Section
  | 1 => some .types | 2 => some .imports | 3 => some .functions
  | 4 => some .tables | 5 => some .memories | 13 => some .tags
  | 6 => some .globals | 7 => some .exports | 8 => some .start
  | 9 => some .elements | 12 => some .dataCount | 10 => some .code
  | 11 => some .data | _ => none

/-- The section envelope. Only the supplied payload reader interprets standard sections. -/
def foldSections {α : Type} (bytes : ByteArray) (init : α)
    (readSection : α → Section → Reader α) : Except DecodeError α := complete (do
  for expected in [0, 0x61, 0x73, 0x6d, 1, 0, 0, 0] do
    let pos := (← get).start
    if (← byte) != expected then failAt pos "bad module header"
  let mut acc := init
  let mut rank := 0
  -- Even a zero-length section consumes its id and at least one length byte.
  for _ in [:((← get).size / 2)] do
    let input ← get
    if input.size == 0 then break
    let id ← byte
    let payload ← take (← u32)
    if id == 0 then
      let _ ← liftM (m := Except DecodeError) (name.run payload)
      pure ()
    else
      let some kind := sectionOfId id | failAt input.start "unknown section id"
      let next := kind.ctorIdx + 1
      if next ≤ rank then failAt input.start "duplicate or out-of-order section"
      rank := next
      acc ← liftM (m := Except DecodeError) (complete (readSection acc kind) payload)
  return acc) bytes.toByteSlice

end Binary
end Wasm
