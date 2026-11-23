import Wasm.Binary
import IrisWasm.Denotational.Run
import Lean.Data.Json

namespace WasmTest.SignExtension
open Wasm IrisWasm IrisWasm.Denotational

private def decodeBody (bytes : ByteArray) : Except String IrisWasm.Expr := do
  let expr := Binary.structuredExpr Binary.numVecType fun tag ↦
    if tag == 0x20 then Binary.variablePayload tag else Binary.numericPayload tag
  let (groups, code) ← (Binary.complete (Binary.codeBody Binary.numVecType expr)
    bytes.toByteSlice).mapError fun e ↦ s!"body offset {e.offset}: {e.message}"
  unless groups.isEmpty do throw "expected no local groups"
  return toEList code

private def observe (code : IrisWasm.Expr) (arg : Value) : Except String Value := do
  let σ : State := (⟨[], [], [], []⟩, [arg], emptyInstance)
  let some (residual, after) := runCut 2 (code, σ) | throw "no two-step cut"
  unless after == σ do throw "cut changed state"
  let [.basic (.const v)] := residual | throw "expected a single constant after two steps"
  return v

/-- Emit actual typed integer results for one sized body; the caller supplies no expected bits. -/
def printCases (body : ByteArray) (trials : Array (Nat × Value)) : IO Unit := do
  let code ← IO.ofExcept (decodeBody body)
  for (ordinal, arg) in trials do
    let v ← IO.ofExcept <| (observe code arg).mapError fun e ↦ s!"case {ordinal}: {e}"
    let (t, n) : String × Nat ← match v with
      | .int32 x => pure ("i32", x.toNat)
      | .int64 x => pure ("i64", x.toNat)
      | _ => throw <| IO.userError s!"case {ordinal}: expected an integer result"
    let row := Lean.Json.arr #[Lean.toJson ordinal,
      Lean.Json.mkObj [("type", .str t), ("value", .str (toString n))]]
    IO.println row.compress

/-- The sized body itself selects the extension width; high input bits must be discarded. -/
theorem extend16_from_body :
    ((decodeBody ⟨#[5, 0, 0x20, 0, 0xc1, 0x0b]⟩).bind
      (observe · (.int32 0xfedc8000))).toOption = some (.int32 0xffff8000) := by decide +kernel

#guard (decodeBody ⟨#[5, 0, 0x20, 0, 0xc1, 0x0b, 0]⟩).toOption.isNone
#guard ((decodeBody ⟨#[5, 0, 0x20, 1, 0xc1, 0x0b]⟩).toOption.map fun code ↦
  (observe code (.int32 0xfedc8000)).toOption) == some none

end WasmTest.SignExtension
