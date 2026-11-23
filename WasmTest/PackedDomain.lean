import IrisWasm.Denotational.Run

namespace WasmTest.PackedDomain

open Wasm IrisWasm IrisWasm.Denotational

private def loadCode (t : ValueType) (tp : PackedType) (sx : Sx) (a off : Nat) (addr : I32) :
    IrisWasm.Expr := [.basic (.const (.int32 addr)), .basic (.load t (some (tp, sx)) ⟨0, a, off⟩)]

private def storeCode (t : ValueType) (tp : PackedType) (a off : Nat) (addr : I32) (v : Value) :
    IrisWasm.Expr := [.basic (.const (.int32 addr)), .basic (.const v), .basic (.store t (some tp) ⟨0, a, off⟩)]

/-- The opcode domain excludes a packed load before any memory lookup or bounds check. -/
theorem packed_load_stuck {s f s' f' out t tp sx a off addr} (h : packedTypeOK tp t = false) :
    ¬ Reduce s f (loadCode t tp sx a off addr) s' f' out := by
  intro hs
  have hr := (round_next_iff (es := loadCode t tp sx a off addr) (es' := out)
    (σ := stateOf s f) (σ' := stateOf s' f')).2 ⟨hs, rfl, rfl⟩
  change Runs (layer (loadCode t tp sx a off addr)) _ (.next out) _ at hr
  simp [loadCode, layer, frag, basicLayer, AddressOperand.ofValue?, Option.all, h] at hr

/-- Even a correctly typed store operand cannot make a malformed packed store trap or write. -/
theorem packed_store_stuck {s f s' f' out t tp a off addr v} (h : packedTypeOK tp t = false) :
    ¬ Reduce s f (storeCode t tp a off addr v) s' f' out := by
  intro hs
  have hr := (round_next_iff (es := storeCode t tp a off addr v) (es' := out)
    (σ := stateOf s f) (σ' := stateOf s' f')).2 ⟨hs, rfl, rfl⟩
  change Runs (layer (storeCode t tp a off addr v)) _ (.next out) _ at hr
  simp [storeCode, layer, frag, basicLayer, AddressOperand.ofValue?, Option.all, h] at hr

private def memoryState : State :=
  (⟨[], [], [⟨MemoryList.ofBytes [0x80, 0, 0, 0], ⟨.i32, ⟨0, none⟩⟩⟩], []⟩,
    [], ⟨[], [], [], [0], []⟩)

private def cut (es : IrisWasm.Expr) (steps := 1) := (runCut steps (es, memoryState)).map Prod.fst

-- Same four-byte memory: bad opcode shapes are stuck both in bounds and out of bounds.
#guard cut (loadCode .f32 .i8 .s 0 0 0) == none
#guard cut (storeCode .f64 .i8 0 4 0 (.float64 ⟨0⟩)) == none
#guard cut (loadCode .i32 .i32 .u 0 0 0) == none
#guard cut (storeCode .i32 .i32 0 0 0 (.int32 7)) == none
#guard cut (loadCode .v128 .i16 .u 0 4 0) == none
#guard cut (storeCode .v128 .i16 0 0 0 (.vec128 3)) == none

-- The largest packed i64 load fits exactly; one byte farther, both load and store trap.
theorem packed_access_end :
    cut (loadCode .i64 .i32 .u 0 0 0) = some [.basic (.const (.int64 0x80))] ∧
    cut (loadCode .i64 .i32 .u 0 1 0) = some [.trap] ∧
    cut (storeCode .i64 .i32 0 1 0 (.int64 7)) = some [.trap] := by decide +kernel

-- A large alignment is invalid for validation but is not a raw execution premise.
#guard !loadStoreTBounds 31 (some .i8) .i32
#guard cut (loadCode .i32 .i8 .s 31 0 0) == some [.basic (.const (.int32 0xffffff80))]
#guard cut (storeCode .i64 .i8 31 0 0 (.int64 0x1234) ++ loadCode .i32 .i8 .u 31 0 0) 2 ==
  some [.basic (.const (.int32 0x34))]

end WasmTest.PackedDomain
