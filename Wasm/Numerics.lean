/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import Iris.Std.RocqPorting
import Wasm.IEEE

/-! Port of `theories/numerics.v`.

Integers are `BitVec w`; the CompCert-based `Wasm_int.Make` functor and its mixin record are
replaced by width-polymorphic functions in `Wasm.Int`. Floating arithmetic uses `Wasm.IEEE`'s
exact bit-level operators, choosing the positive canonical payload when an operation generates NaN. -/

namespace Wasm

@[rocq_alias iriswasm.i32]
abbrev I32 := BitVec 32

@[rocq_alias iriswasm.i64]
abbrev I64 := BitVec 64

/-- A 32-bit IEEE float, represented by its bit pattern. -/
@[rocq_alias iriswasm.f32]
structure F32 where
  bits : BitVec 32
  deriving DecidableEq, Inhabited, Repr

/-- A 64-bit IEEE float, represented by its bit pattern. -/
@[rocq_alias iriswasm.f64]
structure F64 where
  bits : BitVec 64
  deriving DecidableEq, Inhabited, Repr

-- Bit casts for clients exchanging host floats; none of the semantic operations uses them.
def F32.ofFloat32 (x : Float32) : F32 := ⟨x.toBits.toBitVec⟩
def F32.toFloat32 (x : F32) : Float32 := Float32.ofBits (UInt32.ofBitVec x.bits)
def F64.ofFloat (x : Float) : F64 := ⟨x.toBits.toBitVec⟩
def F64.toFloat (x : F64) : Float := Float.ofBits (UInt64.ofBitVec x.bits)


#rocq_ignore iriswasm.i32r "class record of the eqType packaging; BitVec has DecidableEq"
#rocq_ignore iriswasm.i32t "Wasm_int.type packaging; replaced by width-polymorphic functions"
#rocq_ignore iriswasm.i32m "mixin record; use the Wasm.Int functions at width 32"
#rocq_ignore iriswasm.i64r "class record of the eqType packaging; BitVec has DecidableEq"
#rocq_ignore iriswasm.i64t "Wasm_int.type packaging; replaced by width-polymorphic functions"
#rocq_ignore iriswasm.i64m "mixin record; use the Wasm.Int functions at width 64"
#rocq_ignore iriswasm.f32r "class record of the eqType packaging; F32 has DecidableEq"
#rocq_ignore iriswasm.f32t "Wasm_float.type packaging; replaced by the MixinOf class"
#rocq_ignore iriswasm.f64r "class record of the eqType packaging; F64 has DecidableEq"
#rocq_ignore iriswasm.f64t "Wasm_float.type packaging; replaced by the MixinOf class"

/-! ## Integers -/

namespace Int

#rocq_ignore iriswasm.Wasm_int.mixin_of "width-polymorphic BitVec functions replace the mixin"
#rocq_ignore iriswasm.Wasm_int.type "width-polymorphic BitVec functions replace the mixin"
#rocq_ignore iriswasm.Wasm_int.class_of "width-polymorphic BitVec functions replace the mixin"
#rocq_ignore iriswasm.Wasm_int.Pack "width-polymorphic BitVec functions replace the mixin"
#rocq_ignore iriswasm.Wasm_int.sort "width-polymorphic BitVec functions replace the mixin"
#rocq_ignore iriswasm.Wasm_int.Make.T "the carrier is BitVec w"

variable {w : Nat}

/-! ### Constants (CompCert `Integers.Make`, included in `Wasm_int.Make`) -/

@[rocq_alias iriswasm.Wasm_int.Make.wordsize]
abbrev wordsize (w : Nat) : Nat := w

@[rocq_alias iriswasm.Wasm_int.Make.modulus]
abbrev modulus (w : Nat) : _root_.Int := 2 ^ w

@[rocq_alias iriswasm.Wasm_int.Make.half_modulus]
abbrev halfModulus (w : Nat) : _root_.Int := modulus w / 2

@[rocq_alias iriswasm.Wasm_int.Make.max_unsigned]
abbrev maxUnsigned (w : Nat) : _root_.Int := modulus w - 1

@[rocq_alias iriswasm.Wasm_int.Make.max_signed]
abbrev maxSigned (w : Nat) : _root_.Int := halfModulus w - 1

@[rocq_alias iriswasm.Wasm_int.Make.min_signed]
abbrev minSigned (w : Nat) : _root_.Int := - halfModulus w

/-- CompCert `Z_mod_modulus`: reduction into `[0, modulus)`. -/
@[rocq_alias iriswasm.Wasm_int.Make.Z_mod_modulus]
abbrev zModModulus (w : Nat) (z : _root_.Int) : _root_.Int := z % modulus w

@[rocq_alias iriswasm.Wasm_int.int_zero]
abbrev zero : BitVec w := 0#w

@[rocq_alias iriswasm.Wasm_int.Make.one]
abbrev one : BitVec w := 1#w

@[rocq_alias iriswasm.Wasm_int.Make.mone]
abbrev mone : BitVec w := -1#w

/-! ### Conversions -/

/-- CompCert `unsigned` (also `intval`). -/
@[rocq_alias iriswasm.Wasm_int.Make.unsigned]
abbrev unsigned (x : BitVec w) : _root_.Int := x.toNat

@[rocq_alias iriswasm.Wasm_int.Make.signed]
abbrev signed (x : BitVec w) : _root_.Int := x.toInt

@[rocq_alias iriswasm.Wasm_int.Make.repr]
abbrev repr (z : _root_.Int) : BitVec w := BitVec.ofInt w z

@[rocq_alias iriswasm.Wasm_int.int_of_Z]
abbrev intOfZ (z : _root_.Int) : BitVec w := repr z

@[rocq_alias iriswasm.Wasm_int.nat_of_uint]
abbrev natOfUint (x : BitVec w) : Nat := x.toNat

@[rocq_alias iriswasm.Wasm_int.N_of_uint]
abbrev nOfUint (x : BitVec w) : Nat := x.toNat

@[rocq_alias iriswasm.Wasm_int.Z_of_uint]
abbrev zOfUint (x : BitVec w) : _root_.Int := unsigned x

@[rocq_alias iriswasm.Wasm_int.Z_of_sint]
abbrev zOfSint (x : BitVec w) : _root_.Int := signed x

/-! ### Operations (`numerics.v` `Wasm_int.Make` and its `Tmixin`) -/

@[rocq_alias iriswasm.Wasm_int.int_clz]
def iclz (x : BitVec w) : BitVec w := x.clz

@[rocq_alias iriswasm.Wasm_int.int_ctz]
def ictz (x : BitVec w) : BitVec w := x.ctz

@[rocq_alias iriswasm.Wasm_int.int_popcnt]
def ipopcnt (x : BitVec w) : BitVec w := x.cpop

@[rocq_alias iriswasm.Wasm_int.int_add]
def iadd (x y : BitVec w) : BitVec w := x + y

@[rocq_alias iriswasm.Wasm_int.int_sub]
def isub (x y : BitVec w) : BitVec w := x - y

@[rocq_alias iriswasm.Wasm_int.int_mul]
def imul (x y : BitVec w) : BitVec w := x * y

@[rocq_alias iriswasm.Wasm_int.int_div_u]
def idivU (x y : BitVec w) : Option (BitVec w) :=
  if y = zero then none else some (x / y)

@[rocq_alias iriswasm.Wasm_int.int_div_s]
def idivS (x y : BitVec w) : Option (BitVec w) :=
  let j1 := signed x
  let j2 := signed y
  if j2 = 0 then none
  else
    let d := j1.tdiv j2
    if d = halfModulus w then none else some (repr d)

@[rocq_alias iriswasm.Wasm_int.int_rem_u]
def iremU (x y : BitVec w) : Option (BitVec w) :=
  if y = zero then none else some (x % y)

/-- Remainder with the sign of the dividend; Coq's `Z.modulo` is `Int.fmod`. -/
@[rocq_alias iriswasm.Wasm_int.int_rem_s]
def iremS (x y : BitVec w) : Option (BitVec w) :=
  let j1 := signed x
  let j2 := signed y
  if j2 = 0 then none
  else
    let r := j1.fmod j2
    let r := if r = 0 then r else if decide (r ≥ 0) = decide (j1 ≥ 0) then r else r - j2
    some (repr r)

@[rocq_alias iriswasm.Wasm_int.int_and]
def iand (x y : BitVec w) : BitVec w := x &&& y

@[rocq_alias iriswasm.Wasm_int.int_or]
def ior (x y : BitVec w) : BitVec w := x ||| y

@[rocq_alias iriswasm.Wasm_int.int_xor]
def ixor (x y : BitVec w) : BitVec w := x ^^^ y

-- Shift counts are taken modulo `w` as in the Wasm spec; numerics.v uses CompCert's
-- `shl`/`shru`/`shr` (no reduction, an upstream TODO).
@[rocq_alias iriswasm.Wasm_int.int_shl]
def ishl (x k : BitVec w) : BitVec w := x <<< (k.toNat % w)

@[rocq_alias iriswasm.Wasm_int.int_shr_u]
def ishrU (x k : BitVec w) : BitVec w := x >>> (k.toNat % w)

@[rocq_alias iriswasm.Wasm_int.int_shr_s]
def ishrS (x k : BitVec w) : BitVec w := x.sshiftRight (k.toNat % w)

@[rocq_alias iriswasm.Wasm_int.int_rotl]
def irotl (x k : BitVec w) : BitVec w := x.rotateLeft (k.toNat % w)

@[rocq_alias iriswasm.Wasm_int.int_rotr]
def irotr (x k : BitVec w) : BitVec w := x.rotateRight (k.toNat % w)

@[rocq_alias iriswasm.Wasm_int.int_eq]
def ieq (x y : BitVec w) : Bool := x == y

@[rocq_alias iriswasm.Wasm_int.int_ne]
def ine (x y : BitVec w) : Bool := !ieq x y

@[rocq_alias iriswasm.Wasm_int.int_eqz]
def ieqz (x : BitVec w) : Bool := ieq zero x

@[rocq_alias iriswasm.Wasm_int.int_lt_u]
def iltU (x y : BitVec w) : Bool := x.ult y

@[rocq_alias iriswasm.Wasm_int.int_lt_s]
def iltS (x y : BitVec w) : Bool := x.slt y

@[rocq_alias iriswasm.Wasm_int.int_gt_u]
def igtU (x y : BitVec w) : Bool := y.ult x

@[rocq_alias iriswasm.Wasm_int.int_gt_s]
def igtS (x y : BitVec w) : Bool := y.slt x

@[rocq_alias iriswasm.Wasm_int.int_le_u]
def ileU (x y : BitVec w) : Bool := !(y.ult x)

@[rocq_alias iriswasm.Wasm_int.int_le_s]
def ileS (x y : BitVec w) : Bool := !(y.slt x)

@[rocq_alias iriswasm.Wasm_int.int_ge_u]
def igeU (x y : BitVec w) : Bool := !(x.ult y)

@[rocq_alias iriswasm.Wasm_int.int_ge_s]
def igeS (x y : BitVec w) : Bool := !(x.slt y)

#rocq_ignore iriswasm.Wasm_int.Make.iadd "same function as Wasm.Int.iadd (aliased as int_add)"
#rocq_ignore iriswasm.Wasm_int.Make.isub "same function as Wasm.Int.isub (aliased as int_sub)"
#rocq_ignore iriswasm.Wasm_int.Make.imul "same function as Wasm.Int.imul (aliased as int_mul)"
#rocq_ignore iriswasm.Wasm_int.Make.idiv_u "same function as Wasm.Int.idivU (aliased as int_div_u)"
#rocq_ignore iriswasm.Wasm_int.Make.idiv_s "same function as Wasm.Int.idivS (aliased as int_div_s)"
#rocq_ignore iriswasm.Wasm_int.Make.irem_u "same function as Wasm.Int.iremU (aliased as int_rem_u)"
#rocq_ignore iriswasm.Wasm_int.Make.irem_s "same function as Wasm.Int.iremS (aliased as int_rem_s)"
#rocq_ignore iriswasm.Wasm_int.Make.iand "same function as Wasm.Int.iand (aliased as int_and)"
#rocq_ignore iriswasm.Wasm_int.Make.ior "same function as Wasm.Int.ior (aliased as int_or)"
#rocq_ignore iriswasm.Wasm_int.Make.ixor "same function as Wasm.Int.ixor (aliased as int_xor)"
#rocq_ignore iriswasm.Wasm_int.Make.ishl "same function as Wasm.Int.ishl (aliased as int_shl)"
#rocq_ignore iriswasm.Wasm_int.Make.ishr_u "same function as Wasm.Int.ishrU (aliased as int_shr_u)"
#rocq_ignore iriswasm.Wasm_int.Make.clz "same function as Wasm.Int.iclz (aliased as int_clz)"
#rocq_ignore iriswasm.Wasm_int.Make.ctz "same function as Wasm.Int.ictz (aliased as int_ctz)"
#rocq_ignore iriswasm.Wasm_int.Make.popcnt
  "same function as Wasm.Int.ipopcnt (aliased as int_popcnt)"
#rocq_ignore iriswasm.Wasm_int.Make.Tmixin
  "mixin instance; the Wasm.Int functions are used directly"
#rocq_ignore iriswasm.Wasm_int.Make.cT "eqType packaging; BitVec has DecidableEq"
#rocq_ignore iriswasm.Wasm_int.Make.class "eqType packaging; BitVec has DecidableEq"
#rocq_ignore iriswasm.Wasm_int.Make.clone "eqType packaging; BitVec has DecidableEq"
#rocq_ignore iriswasm.Wasm_int.Make.xT "eqType packaging; BitVec has DecidableEq"
#rocq_ignore iriswasm.Wasm_int.Make.pack "eqType packaging; BitVec has DecidableEq"
#rocq_ignore iriswasm.Wasm_int.Make.eqType "eqType packaging; BitVec has DecidableEq"
#rocq_ignore iriswasm.Wasm_int.Make.Z_lt_irrelevant "proof irrelevance for CompCert's int record"
#rocq_ignore iriswasm.Wasm_int.Make.eq_T_intval "BitVec.eq_of_toNat_eq"
#rocq_ignore iriswasm.Wasm_int.Make.Z_mod_modulus_intval "unused"
#rocq_ignore iriswasm.Wasm_int.Make.Z_mod_modulus_add_modulus "unused"
#rocq_ignore iriswasm.Wasm_int.Make.modulus_mod_2 "unused"
#rocq_ignore iriswasm.Wasm_int.Make.modulus_ge_2 "unused"
#rocq_ignore iriswasm.Wasm_int.Make.wordsize_modulus "unused"
#rocq_ignore iriswasm.Wasm_int.Make.modulus_minus_half_modulus "unused"
#rocq_ignore iriswasm.Wasm_int.Make.modulus_twice_half_modulus "unused"
#rocq_ignore iriswasm.Wasm_int.Make.repr_add_modulus_rev "unused"
#rocq_ignore iriswasm.Wasm_int.Make.unsigned_repr_unsigned "unused; see repr_unsigned"
#rocq_ignore iriswasm.Wasm_int.Make.signed_repr_signed "unused"
#rocq_ignore iriswasm.Wasm_int.Make.signed_repr_unsigned "unused"
#rocq_ignore iriswasm.Wasm_int.Make.unsigned_repr_signed "unused"
#rocq_ignore iriswasm.Wasm_int.Make.power_index_to_bits
  "bit lists are replaced by BitVec.clz/ctz/cpop"
#rocq_ignore iriswasm.Wasm_int.Make.power_index_to_bits_size "bit lists are replaced by BitVec"
#rocq_ignore iriswasm.Wasm_int.Make.power_index_to_bits_none "bit lists are replaced by BitVec"
#rocq_ignore iriswasm.Wasm_int.Make.power_index_to_bits_in "bit lists are replaced by BitVec"
#rocq_ignore iriswasm.Wasm_int.Make.power_index_to_bits_nth "bit lists are replaced by BitVec"
#rocq_ignore iriswasm.Wasm_int.Make.convert_to_bits "bit lists are replaced by BitVec"
#rocq_ignore iriswasm.Wasm_int.Make.convert_to_bits_size "bit lists are replaced by BitVec"
#rocq_ignore iriswasm.Wasm_int.Make.convert_to_bits_zero "bit lists are replaced by BitVec"
#rocq_ignore iriswasm.Wasm_int.Make.convert_to_bits_nth "bit lists are replaced by BitVec"
#rocq_ignore iriswasm.Wasm_int.Make.convert_to_bits_one "bit lists are replaced by BitVec"
#rocq_ignore iriswasm.Wasm_int.Make.convert_to_bits_two_p "bit lists are replaced by BitVec"
#rocq_ignore iriswasm.Wasm_int.Make.convert_to_bits_inj "bit lists are replaced by BitVec"
#rocq_ignore iriswasm.Wasm_int.Make.convert_from_bits_to_Z_one_bits
  "bit lists are replaced by BitVec"
#rocq_ignore iriswasm.Wasm_int.Make.convert_from_bits_to_Z_one_bits_power_index_to_bits
  "bit lists are replaced by BitVec"
#rocq_ignore iriswasm.Wasm_int.Make.convert_from_bits "bit lists are replaced by BitVec"
#rocq_ignore iriswasm.Wasm_int.Make.convert_to_from_bits "bit lists are replaced by BitVec"
#rocq_ignore iriswasm.Wasm_int.Make.Zbits_Z_one_bits_range "bit lists are replaced by BitVec"
#rocq_ignore iriswasm.Wasm_int.Make.Zbits_Z_one_bits_uniq "bit lists are replaced by BitVec"
#rocq_ignore iriswasm.Wasm_int.Make.Zbits_powerserie_uniq_in "bit lists are replaced by BitVec"
#rocq_ignore iriswasm.Wasm_int.Make.power_index_to_bits_Zbits_powerserie
  "bit lists are replaced by BitVec"
#rocq_ignore iriswasm.Wasm_int.Make.clz_wordsize "unused"
#rocq_ignore iriswasm.Wasm_int.Make.repr_0 "rfl over BitVec; unused"
#rocq_ignore iriswasm.Wasm_int.Make.repr_1 "rfl over BitVec; unused"
#rocq_ignore iriswasm.Wasm_int.Make.repr_m1 "rfl over BitVec; unused"
#rocq_ignore iriswasm.Wasm_int.Make.nat_Z_lt_neq "omega"
#rocq_ignore iriswasm.Wasm_int.Make.nat_Z_gt_neq "omega"
#rocq_ignore iriswasm.Wasm_int.Make.idiv_s_2_wordsize_m1_m1
  "unused; checked by #guard in WasmTest.Numerics"
#rocq_ignore iriswasm.Wasm_int.Make.idiv_u_irem_u "unused"
#rocq_ignore iriswasm.Wasm_int.Make.idiv_s_irem_s "unused"

/-! ### Lemmas (CompCert/`numerics.v` lemmas used by later files, restated over `BitVec`) -/

@[rocq_alias iriswasm.Wasm_int.Make.unsigned_range]
theorem unsigned_range (x : BitVec w) : 0 ≤ unsigned x ∧ unsigned x < modulus w := by
  have := x.isLt
  have e : ((2 ^ w : Nat) : _root_.Int) = 2 ^ w := by push_cast; rfl
  simp only [unsigned, modulus]; omega

@[simp, rocq_alias iriswasm.Wasm_int.Make.repr_unsigned]
theorem repr_unsigned (x : BitVec w) : repr (unsigned x) = x := by simp

@[rocq_alias iriswasm.Wasm_int.Make.Z_mod_modulus_eq]
theorem Z_mod_modulus_eq (z : _root_.Int) : zModModulus w z = z % modulus w := rfl

@[rocq_alias iriswasm.Wasm_int.Make.Z_mod_modulus_range]
theorem Z_mod_modulus_range (z : _root_.Int) :
    0 ≤ zModModulus w z ∧ zModModulus w z < modulus w := by
  have h : (0 : _root_.Int) < 2 ^ w := _root_.Int.pow_pos (by decide)
  exact ⟨_root_.Int.emod_nonneg _ (by unfold modulus; omega), _root_.Int.emod_lt_of_pos _ h⟩

@[rocq_alias iriswasm.Wasm_int.Make.Z_mod_modulus_id]
theorem Z_mod_modulus_id {z : _root_.Int} (h : -1 < z ∧ z < modulus w) : zModModulus w z = z := by
  obtain ⟨h1, h2⟩ := h
  exact _root_.Int.emod_eq_of_lt (by omega) h2

@[rocq_alias iriswasm.Wasm_int.Make.unsigned_repr_eq]
theorem unsigned_repr_eq (z : _root_.Int) : unsigned (repr (w := w) z) = zModModulus w z := by
  have := (Z_mod_modulus_range (w := w) z).1
  simp only [unsigned, repr, zModModulus, modulus, BitVec.toNat_ofInt] at *
  push_cast; omega

@[rocq_alias iriswasm.Wasm_int.Make.unsigned_repr]
theorem unsigned_repr {z : _root_.Int} (h : 0 ≤ z ∧ z ≤ maxUnsigned w) :
    unsigned (repr (w := w) z) = z := by
  rw [unsigned_repr_eq]; exact Z_mod_modulus_id ⟨by omega, by simp only [maxUnsigned] at h; omega⟩

@[rocq_alias iriswasm.Wasm_int.Make.signed_repr]
theorem signed_repr {z : _root_.Int} (h : minSigned w ≤ z ∧ z ≤ maxSigned w) :
    signed (repr (w := w) z) = z := by
  simp only [minSigned, maxSigned, halfModulus, modulus] at h
  have e : ((2 ^ w : Nat) : _root_.Int) = 2 ^ w := by push_cast; rfl
  simp only [signed, repr, BitVec.toInt_ofInt]
  apply _root_.Int.bmod_eq_of_le <;> omega

@[rocq_alias iriswasm.Wasm_int.Make.repr_inv]
theorem repr_inv {i j : _root_.Int} (hi : -1 < i ∧ i < modulus w) (hj : -1 < j ∧ j < modulus w)
    (h : repr (w := w) i = repr j) : i = j := by
  have := congrArg unsigned h
  rwa [unsigned_repr_eq, unsigned_repr_eq, Z_mod_modulus_id hi, Z_mod_modulus_id hj] at this

@[rocq_alias iriswasm.Wasm_int.Make.repr_add_modulus]
theorem repr_add_modulus (i : _root_.Int) : repr (w := w) i = repr (i + modulus w) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofInt, modulus]

@[simp, rocq_alias iriswasm.Wasm_int.Make.eq_true]
theorem eq_true (x : BitVec w) : ieq x x = true := by simp [ieq]

@[rocq_alias iriswasm.Wasm_int.Make.eq_false]
theorem eq_false {x y : BitVec w} (h : x ≠ y) : ieq x y = false := by simp [ieq, h]

@[rocq_alias iriswasm.Wasm_int.Make.eq_eqP]
theorem eq_eqP {x y : BitVec w} : ieq x y = true ↔ x = y := by simp [ieq]

@[rocq_alias iriswasm.Wasm_int.Make.same_if_eq]
theorem same_if_eq {x y : BitVec w} (h : ieq x y = true) : x = y := eq_eqP.1 h

@[rocq_alias iriswasm.Wasm_int.Make.mul_signed]
theorem mul_signed (x y : BitVec w) : imul x y = repr (signed x * signed y) := by
  apply BitVec.eq_of_toInt_eq; simp [imul, BitVec.toInt_mul]

@[rocq_alias iriswasm.Wasm_int.Make.int_of_Z_nat_of_uint]
theorem int_of_Z_nat_of_uint (x : BitVec w) : intOfZ (natOfUint x : _root_.Int) = x := by simp

@[rocq_alias iriswasm.Wasm_int.Make.int_of_Z_Z_of_uint]
theorem int_of_Z_Z_of_uint (x : BitVec w) : intOfZ (zOfUint x) = x := by simp

@[rocq_alias iriswasm.Wasm_int.Make.int_of_Z_Z_of_sint]
theorem int_of_Z_Z_of_sint (x : BitVec w) : intOfZ (zOfSint x) = x := by simp

@[rocq_alias iriswasm.Wasm_int.Make.nat_of_uint_Z_of_uint]
theorem nat_of_uint_Z_of_uint (x : BitVec w) : (natOfUint x : _root_.Int) = zOfUint x := rfl

end Int

@[rocq_alias iriswasm.wasm_wrap]
def wasmWrap (i : I64) : I32 := i.setWidth 32

@[rocq_alias iriswasm.wasm_extend_u]
def wasmExtendU (i : I32) : I64 := i.setWidth 64

@[rocq_alias iriswasm.wasm_extend_s]
def wasmExtendS (i : I32) : I64 := i.signExtend 64

@[rocq_alias iriswasm.wasm_bool]
def wasmBool (b : Bool) : I32 := if b then Int.one else Int.zero

@[rocq_alias iriswasm.int32_minus_one]
def int32MinusOne : I32 := Int.mone

/-! ## Floats -/

namespace Float

#rocq_ignore iriswasm.Wasm_float.class_of "eqType packaging; F32/F64 have DecidableEq"
#rocq_ignore iriswasm.Wasm_float.type "eqType packaging; replaced by the MixinOf class"
#rocq_ignore iriswasm.Wasm_float.Pack "eqType packaging; replaced by the MixinOf class"
#rocq_ignore iriswasm.Wasm_float.sort "eqType packaging; replaced by the MixinOf class"
#rocq_ignore iriswasm.Wasm_float.FloatSize
  "Flocq parameters; see IEEE.Format"
#rocq_ignore iriswasm.Wasm_float.FloatSize32 "binary32 parameters; see IEEE.Format.f32"
#rocq_ignore iriswasm.Wasm_float.FloatSize64 "binary64 parameters; see IEEE.Format.f64"
#rocq_ignore iriswasm.Wasm_float.Make
  "Flocq-based operations; see IEEE.Format"
#rocq_ignore iriswasm.Wasm_float.Float32 "instantiation of Make; see instMixinOfF32"
#rocq_ignore iriswasm.Wasm_float.Float64 "instantiation of Make; see instMixinOfF64"

/-- The Wasm float operations (`Wasm_float.mixin_of`). `eq` is IEEE equality, not Leibniz. -/
@[rocq_alias iriswasm.Wasm_float.mixin_of]
class MixinOf (α : Type) where
  zero : α
  neg : α → α
  abs : α → α
  sqrt : α → α
  ceil : α → α
  floor : α → α
  trunc : α → α
  nearest : α → α
  add : α → α → α
  sub : α → α → α
  mul : α → α → α
  div : α → α → α
  min : α → α → α
  max : α → α → α
  copysign : α → α → α
  eq : α → α → Bool
  lt : α → α → Bool
  gt : α → α → Bool
  le : α → α → Bool
  ge : α → α → Bool
  ui32Trunc : α → Option I32
  si32Trunc : α → Option I32
  ui64Trunc : α → Option I64
  si64Trunc : α → Option I64
  convertUi32 : I32 → α
  convertSi32 : I32 → α
  convertUi64 : I64 → α
  convertSi64 : I64 → α

@[rocq_alias iriswasm.Wasm_float.float_ne]
def ne {α : Type} [MixinOf α] (x y : α) : Bool := !MixinOf.eq x y

private abbrev bitMixin {α : Type} (f : IEEE.Format) (bits : α → f.Bits) (mk : f.Bits → α) :
    MixinOf α where
  zero := mk 0
  neg x := mk (f.neg (bits x))
  abs x := mk (f.abs (bits x))
  sqrt x := mk (f.sqrt (bits x)).choose
  ceil x := mk (f.integral .ceil (bits x)).choose
  floor x := mk (f.integral .floor (bits x)).choose
  trunc x := mk (f.integral .trunc (bits x)).choose
  nearest x := mk (f.integral .nearest (bits x)).choose
  add x y := mk (f.add (bits x) (bits y)).choose
  sub x y := mk (f.sub (bits x) (bits y)).choose
  mul x y := mk (f.mul (bits x) (bits y)).choose
  div x y := mk (f.div (bits x) (bits y)).choose
  min x y := mk (f.minMax false (bits x) (bits y)).choose
  max x y := mk (f.minMax true (bits x) (bits y)).choose
  copysign x y := mk (f.copySign (bits x) (bits y))
  eq x y := f.cmp (bits x) (bits y) == some .eq
  lt x y := f.cmp (bits x) (bits y) == some .lt
  gt x y := f.cmp (bits x) (bits y) == some .gt
  le x y := (f.cmp (bits x) (bits y)).any Ordering.isLE
  ge x y := (f.cmp (bits y) (bits x)).any Ordering.isLE
  ui32Trunc x := f.truncToInt false 32 (bits x)
  si32Trunc x := f.truncToInt true 32 (bits x)
  ui64Trunc x := f.truncToInt false 64 (bits x)
  si64Trunc x := f.truncToInt true 64 (bits x)
  convertUi32 i := mk (f.fromInt i.toNat)
  convertSi32 i := mk (f.fromInt i.toInt)
  convertUi64 i := mk (f.fromInt i.toNat)
  convertSi64 i := mk (f.fromInt i.toInt)

end Float

@[rocq_alias iriswasm.f32m]
instance instMixinOfF32 : Float.MixinOf F32 := Float.bitMixin .f32 F32.bits F32.mk

@[rocq_alias iriswasm.f64m]
instance instMixinOfF64 : Float.MixinOf F64 := Float.bitMixin .f64 F64.bits F64.mk

@[rocq_alias iriswasm.wasm_demote]
def wasmDemote (z : F64) : F32 := ⟨(IEEE.Format.f64.convert .f32 z.bits).choose⟩

@[rocq_alias iriswasm.wasm_promote]
def wasmPromote (z : F32) : F64 := ⟨(IEEE.Format.f32.convert .f64 z.bits).choose⟩

end Wasm
