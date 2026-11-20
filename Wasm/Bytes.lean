/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import Iris.Std.RocqPorting

/-! Port of `theories/bytes.v` and of the parts of CompCert's `Memdata` it relies on. -/

namespace Wasm

@[rocq_alias iriswasm.byte]
abbrev Byte := BitVec 8

@[rocq_alias iriswasm.bytes]
abbrev Bytes := List Byte

#rocq_ignore iriswasm.encode "bytes are BitVec 8; numerals replace the successor encoding"
#rocq_ignore iriswasm.byte_eq_dec "BitVec has DecidableEq"
#rocq_ignore iriswasm.byte_eqb "BitVec has DecidableEq"
#rocq_ignore iriswasm.eqbyteP "BitVec has DecidableEq"
#rocq_ignore iriswasm.bytes_eq_dec "List has DecidableEq"
#rocq_ignore iriswasm.bytes_eqb "List has DecidableEq"
#rocq_ignore iriswasm.eqbytesP "List has DecidableEq"
#rocq_ignore iriswasm.compcert_byte_of_byte "single byte type in Lean"
#rocq_ignore iriswasm.byte_of_compcert_byte "single byte type in Lean"

@[rocq_alias iriswasm.bytes_takefill]
def bytesTakefill (a : Byte) : Nat → Bytes → Bytes
  | 0, _ => []
  | n + 1, [] => a :: bytesTakefill a n []
  | n + 1, a' :: aas => a' :: bytesTakefill a n aas

@[rocq_alias iriswasm.bytes_replicate]
def bytesReplicate : Nat → Byte → Bytes
  | 0, _ => []
  | n + 1, b => b :: bytesReplicate n b

@[rocq_alias iriswasm.msbyte]
def msbyte (bs : Bytes) : Option Byte := bs.getLast?

theorem length_bytesTakefill (a : Byte) (n : Nat) (bs : Bytes) :
    (bytesTakefill a n bs).length = n := by
  induction n generalizing bs with
  | zero => rfl
  | succ n ih => cases bs <;> simp [bytesTakefill, ih]

theorem bytesTakefill_of_length (a : Byte) (bs : Bytes) : bytesTakefill a bs.length bs = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [bytesTakefill, ih]

/-- CompCert `Memdata.encode_int n z`: the `n` low bytes of `z`, little-endian. -/
def encodeInt : Nat → Int → Bytes
  | 0, _ => []
  | n + 1, z => BitVec.ofInt 8 z :: encodeInt n (z / 256)

/-- CompCert `Memdata.decode_int bs`: little-endian unsigned value of `bs`. -/
def decodeInt : Bytes → Int
  | [] => 0
  | b :: bs => (b.toNat : Int) + decodeInt bs * 256

theorem length_encodeInt (n : Nat) (z : Int) : (encodeInt n z).length = n := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih => simp [encodeInt, ih]

theorem decodeInt_nonneg (bs : Bytes) : 0 ≤ decodeInt bs := by
  induction bs with
  | nil => simp [decodeInt]
  | cons b bs ih => simp only [decodeInt]; omega

theorem decodeInt_lt (bs : Bytes) : decodeInt bs < 2 ^ (8 * bs.length) := by
  induction bs with
  | nil => simp [decodeInt]
  | cons b bs ih =>
    have hb := b.isLt
    simp only [decodeInt, List.length_cons, Nat.mul_succ, Int.pow_add]
    have : (2 : Int) ^ 8 = 256 := by decide
    rw [this]
    have := decodeInt_nonneg bs
    simp only [Nat.reducePow] at hb
    omega

private theorem emod_mul_256 (z M : Int) (hM : 0 < M) :
    z % (M * 256) = z % 256 + z / 256 % M * 256 := by
  have h1 := Int.emod_add_ediv_mul z 256
  have h2 := Int.emod_add_ediv_mul (z / 256) M
  have hr0 := Int.emod_nonneg z (by decide : (256 : Int) ≠ 0)
  have hr1 := Int.emod_lt_of_pos z (by decide : (0 : Int) < 256)
  have hq0 := Int.emod_nonneg (z / 256) (Int.ne_of_gt hM)
  have hq1 := Int.emod_lt_of_pos (z / 256) hM
  generalize z % 256 = r at *
  generalize z / 256 / M = q' at *
  generalize z / 256 % M = r' at *
  generalize z / 256 = q at *
  subst h1
  subst h2
  have : (r + (r' + q' * M) * 256) = (r + r' * 256) + (M * 256) * q' := by
    rw [Int.add_mul, Int.mul_assoc, Int.mul_comm q' (M * 256)]; omega
  rw [this, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega)]
  have : r' * 256 ≤ (M - 1) * 256 := Int.mul_le_mul_of_nonneg_right (by omega) (by decide)
  rw [Int.sub_mul] at this
  omega

/-- `decode_int (encode_int n z) = z mod 2^(8n)`. -/
theorem decode_encode_int (n : Nat) (z : Int) : decodeInt (encodeInt n z) = z % 2 ^ (8 * n) := by
  induction n generalizing z with
  | zero => simp [encodeInt, decodeInt, Int.emod_one]
  | succ n ih =>
    simp only [encodeInt, decodeInt, ih, BitVec.toNat_ofInt]
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide)), Nat.mul_succ, Int.pow_add]
    have h256 : (2 : Int) ^ 8 = 256 := by decide
    rw [h256, emod_mul_256 _ _ (Int.pow_pos (by decide))]
    simp

theorem decode_encode_int_of_lt {n : Nat} {z : Int} (h0 : 0 ≤ z) (h : z < 2 ^ (8 * n)) :
    decodeInt (encodeInt n z) = z := by
  rw [decode_encode_int, Int.emod_eq_of_lt h0 h]

end Wasm
