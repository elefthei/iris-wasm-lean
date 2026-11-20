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

def f32 (x : Float32) : F32 := F32.ofFloat32 x
def f64 (x : Float) : F64 := F64.ofFloat x

#guard MixinOf.ui32Trunc (f32 (-1.0)) = none
#guard MixinOf.ui32Trunc (f32 (-0.5)) = some 0#32
#guard MixinOf.si32Trunc (f32 (-1.5)) = some (BitVec.ofInt 32 (-1))
#guard MixinOf.si32Trunc (f32 2147483648.0) = none
#guard MixinOf.si64Trunc (f64 (-9223372036854775808.0)) =
  some (BitVec.ofInt 64 (-9223372036854775808))
#guard MixinOf.si64Trunc (f64 9223372036854775808.0) = none
#guard MixinOf.si64Trunc (f64 4294967296.0) = some 4294967296#64
#guard MixinOf.ui64Trunc (f64 (0.0 / 0.0)) = none
#guard MixinOf.nearest (f64 2.5) = f64 2.0
#guard MixinOf.nearest (f64 3.5) = f64 4.0
#guard MixinOf.nearest (f64 (-2.5)) = f64 (-2.0)
#guard MixinOf.nearest (f32 2.5) = f32 2.0
#guard MixinOf.nearest (f64 (-0.5)) = f64 (-0.0)
#guard MixinOf.trunc (f64 (-1.7)) = f64 (-1.0)
#guard MixinOf.copysign (f64 3.0) (f64 (-0.0)) = f64 (-3.0)
#guard MixinOf.copysign (f32 (-3.0)) (f32 1.0) = f32 3.0
#guard MixinOf.min (f64 0.0) (f64 (-0.0)) = f64 (-0.0)
#guard MixinOf.max (f64 (-0.0)) (f64 0.0) = f64 0.0
#guard MixinOf.min (f32 (-0.0)) (f32 0.0) = f32 (-0.0)
#guard (MixinOf.min (f64 1.0) (f64 (0.0 / 0.0))).toFloat.isNaN
#guard (MixinOf.max (f32 (0.0 / 0.0)) (f32 1.0)).toFloat32.isNaN
#guard MixinOf.eq (f64 0.0) (f64 (-0.0)) ∧ ne (f64 (0.0 / 0.0)) (f64 (0.0 / 0.0))
#guard MixinOf.add (f32 1.5) (f32 2.0) = f32 3.5
#guard MixinOf.convertSi32 (BitVec.ofInt 32 (-3)) = f64 (-3.0)
#guard MixinOf.convertUi32 (BitVec.ofInt 32 (-1)) = f64 4294967295.0

end WasmTest.Numerics
