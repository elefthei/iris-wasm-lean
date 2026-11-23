/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import Wasm.Numerics

/-! Behaviour checks for `Wasm.Numerics`. -/

namespace WasmTest.Numerics

open Wasm Wasm.Int Wasm.Float

/-! Integers -/

#guard idivS (BitVec.ofInt 32 (-2147483648)) (BitVec.ofInt 32 (-1)) = none
#guard idivS (BitVec.ofInt 32 (-7)) 2#32 = some (BitVec.ofInt 32 (-3))
#guard idivU 7#32 0#32 = none
#guard iremS (BitVec.ofInt 32 (-2147483648)) (BitVec.ofInt 32 (-1)) = some 0#32
#guard iremS (BitVec.ofInt 32 (-7)) 2#32 = some (BitVec.ofInt 32 (-1))
#guard iremS 7#32 (BitVec.ofInt 32 (-2)) = some 1#32
#guard iremU 7#32 0#32 = none
#guard irotl 0x80000001#32 1#32 = 0x00000003#32
#guard irotr 0x00000003#32 1#32 = 0x80000001#32
#guard ishl 1#32 33#32 = 2#32
#guard ishrS 0x80000000#32 31#32 = 0xffffffff#32
#guard ishrU 0x80000000#32 31#32 = 1#32
#guard iclz 0#32 = 32#32 ∧ iclz 1#32 = 31#32
#guard ictz 0#64 = 64#64 ∧ ictz 8#64 = 3#64
#guard ipopcnt 0xff00ff00#32 = 16#32
#guard iltS (BitVec.ofInt 32 (-1)) 0#32 ∧ !iltU (BitVec.ofInt 32 (-1)) 0#32
#guard ieqz (0#32) ∧ ine 1#32 2#32
#guard wasmExtendS (BitVec.ofInt 32 (-1)) = BitVec.ofInt 64 (-1)
#guard wasmWrap 0x100000005#64 = 5#32

/-! Floats -/

private abbrev f32 := F32.mk
private abbrev f64 := F64.mk
private abbrev b32 := IEEE.Format.f32
private abbrev b64 := IEEE.Format.f64

-- Integer range checks are on the truncated value, including the interval (-1, 0).
#guard MixinOf.ui32Trunc (f32 0xbf800000) = none
#guard MixinOf.ui32Trunc (f32 0xbf000000) = some 0#32
#guard MixinOf.si32Trunc (f32 0xbfc00000) = some 0xffffffff#32
#guard MixinOf.si32Trunc (f32 0x4f000000) = none
#guard MixinOf.si64Trunc (f64 0xc3e0000000000000) = some 0x8000000000000000#64
#guard MixinOf.si64Trunc (f64 0x43e0000000000000) = none
#guard MixinOf.si64Trunc (f64 0x41f0000000000000) = some 4294967296#64
#guard MixinOf.ui64Trunc (f64 0x7ff8000000000000) = none
#guard MixinOf.ui64Trunc (f64 0x43efffffffffffff) = some 0xfffffffffffff800#64
#guard b32.truncSat true 32 0xff800000 = 0x80000000#32
#guard b32.truncSat true 32 0x4f000000 = 0x7fffffff#32
#guard b32.truncSat false 64 0x7f800000 = 0xffffffffffffffff#64
#guard b32.truncSat false 64 0x7f800001 = 0#64
#guard b32.truncSat false 32 0xbf800000 = 0#32
#guard MixinOf.convertSi32 (BitVec.ofInt 32 (-3)) = f64 0xc008000000000000
#guard MixinOf.convertUi32 0xffffffff#32 = f64 0x41efffffffe00000
#guard MixinOf.convertUi64 0xffffffffffffffff#64 = f32 0x5f800000
-- Just above the binary32 midpoint. Converting via binary64 would double-round down.
#guard MixinOf.convertUi64 0x8000008000000001#64 = f32 0x5f000001

#guard MixinOf.nearest (f64 0x4004000000000000) = f64 0x4000000000000000
#guard MixinOf.nearest (f64 0x400c000000000000) = f64 0x4010000000000000
#guard MixinOf.nearest (f64 0xc004000000000000) = f64 0xc000000000000000
#guard MixinOf.nearest (f32 0x40200000) = f32 0x40000000
#guard MixinOf.nearest (f64 0xbfe0000000000000) = f64 0x8000000000000000
#guard MixinOf.trunc (f64 0xbffb333333333333) = f64 0xbff0000000000000
#guard MixinOf.ceil (f32 0x80000001) = f32 0x80000000
#guard MixinOf.floor (f32 0x80000001) = f32 0xbf800000
#guard MixinOf.copysign (f64 0x4008000000000000) (f64 0x8000000000000000) =
  f64 0xc008000000000000
#guard MixinOf.copysign (f32 0xc0400000) (f32 0x3f800000) = f32 0x40400000
#guard MixinOf.min (f64 0) (f64 0x8000000000000000) = f64 0x8000000000000000
#guard MixinOf.max (f64 0x8000000000000000) (f64 0) = f64 0
#guard MixinOf.min (f32 0x80000000) (f32 0) = f32 0x80000000
#guard MixinOf.min (f64 0x3ff0000000000000) (f64 0xfff8000000000010) =
  f64 0x7ff8000000000000
#guard MixinOf.max (f32 0xff800001) (f32 0x3f800000) = f32 0x7fc00000
#guard MixinOf.eq (f64 0) (f64 0x8000000000000000) ∧ ne (f32 0x7fc00000) (f32 0x7fc00000)
#guard !MixinOf.le (f32 0x7f800001) (f32 0xff800000)
#guard MixinOf.lt (f32 0x80000001) (f32 0)

#guard MixinOf.add (f32 0x3fc00000) (f32 0x40000000) = f32 0x40600000
#guard MixinOf.add (f32 0x80000000) (f32 0x80000000) = f32 0x80000000
#guard MixinOf.sub (f32 0xbf800000) (f32 0xbf800000) = f32 0
#guard MixinOf.add (f32 0x007fffff) (f32 1) = f32 0x00800000
#guard MixinOf.add (f32 0x7f7fffff) (f32 0x73000000) = f32 0x7f800000
#guard MixinOf.mul (f32 0x80000001) (f32 0x3f000000) = f32 0x80000000
#guard MixinOf.mul (f32 3) (f32 0x3f000000) = f32 2
#guard MixinOf.div (f32 0x3f800000) (f32 0x40400000) = f32 0x3eaaaaab
#guard MixinOf.div (f32 0xbf800000) (f32 0) = f32 0xff800000
#guard MixinOf.div (f32 0xff800000) (f32 0x7f800000) = f32 0x7fc00000
#guard MixinOf.sqrt (f32 0x80000000) = f32 0x80000000
#guard MixinOf.sqrt (f32 0xbf800000) = f32 0x7fc00000
#guard MixinOf.sqrt (f32 1) = f32 0x1a3504f3
#guard MixinOf.sqrt (f64 1) = f64 0x1e60000000000000
#guard MixinOf.sqrt (f64 0x4000000000000000) = f64 0x3ff6a09e667f3bcd
#guard wasmPromote (f32 1) = f64 0x36a0000000000000
#guard wasmDemote (f64 0x3ff0000010000000) = f32 0x3f800000
#guard wasmDemote (f64 0x3ff0000010000001) = f32 0x3f800001

-- Fusing preserves the low product bits and permits cancellation of an unrounded overflow.
#guard (b32.fma 0x3f800001 0x3f7ffffe 0xbf800000).choose == 0xa8800000#32
#guard (b32.fma 0x7f7fffff 0x40000000 0xff7fffff).choose == 0x7f7fffff#32
#guard (b32.fma 0x80000000 0x3f800000 0x80000000).choose == 0x80000000#32
#guard (b32.fma 0x7f800000 0 0x7f800001).allows 0xffc0000a

-- Invalid operations generate canonical payloads of either sign; noncanonical operands
-- also permit noncanonical quiet payloads, never signaling payloads.
#guard (b32.div 0 0).allows 0xffc00000 && !(b32.div 0 0).allows 0xffc00001
#guard !(b32.add 0xffc00000 0x7fc00000).allows 0x7fc00001
#guard (b32.add 0x7fc00000 0xff800001).allows 0xffc00001
#guard !(b32.add 0x7fc00000 0xff800001).allows 0x7f800001
#guard (b64.convert .f32 0x7ff0000000000001).allows 0x7fc00001
#guard !(b32.convert .f64 0xffc00000).allows 0x7ff8000000000001
#guard MixinOf.neg (f32 0x7f800001) = f32 0xff800001
#guard MixinOf.abs (f32 0xff800001) = f32 0x7f800001

end WasmTest.Numerics
