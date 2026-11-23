import Wasm.Binary
import Wasm.TypeChecker
import IrisWasm.Denotational.Run
import Lean.Data.Json

namespace WasmTest.FuzzRuntime
open Wasm IrisWasm IrisWasm.Denotational
open Lean (Json toJson)

private def leaf (tag : UInt8) : Binary.Reader BasicInstruction := do
  match tag with
  | 0x00 => return .unreachable
  | 0x01 => return .nop
  | 0x10 => return .call (← Binary.u32)
  | 0x11 =>
    let ty ← Binary.u32
    let pos := (← get).start
    unless (← Binary.u32) == 0 do throw ⟨pos, "expected table 0"⟩
    return .callIndirect ty
  | 0x1a => return .drop
  | 0x1b => return .select
  | _ =>
    if 0x20 ≤ tag && tag ≤ 0x24 then return ← Binary.variablePayload tag
    if 0x28 ≤ tag && tag ≤ 0x40 then return ← Binary.memoryPayload tag
    return ← Binary.numericPayload tag

private def abiType : String → Except String ValueType
  | "i32" => .ok .i32
  | "i64" => .ok .i64
  | t => .error s!"unsupported ABI type {t}"

private def argument (t : ValueType) (bits : String) : Except String Value := do
  let some n := bits.toNat? | throw "expected unsigned decimal argument"
  match t with
  | .i32 =>
    unless n < 2^32 do throw "i32 argument out of range"
    return .int32 (BitVec.ofNat 32 n)
  | .i64 =>
    unless n < 2^64 do throw "i64 argument out of range"
    return .int64 (BitVec.ofNat 64 n)
  | _ => throw "expected integer ABI"

#guard (argument .i32 "4294967296").toOption.isNone

private def prepare (msg : Json) : Except String (State × List ValueType) := do
  let bytes ← msg.getObjValAs? (Array Nat) "body"
  unless bytes.all (· < 256) do throw "body byte out of range"
  let body := ByteArray.mk (bytes.map Nat.toUInt8)
  let parser := Binary.codeBody Binary.numVecType (Binary.structuredExpr Binary.numVecType leaf)
  let (locals, code) ← (Binary.complete parser body.toByteSlice).mapError fun e ↦
    s!"body offset {e.offset}: {e.message}"
  unless locals.isEmpty do throw "expected zero local groups"
  let params ← (← msg.getObjValAs? (List String) "params").mapM abiType
  let result ← abiType (← msg.getObjValAs? String "result")
  let wide ← msg.getObjValAs? Bool "memory64"
  let helperTy := FunctionType.tf [.i32] [.i32]
  let runTy := FunctionType.tf params [result]
  let types := [helperTy, runTy]
  let inst : Instance := ⟨types, [0, 1], [0], [0, 1], [0]⟩
  let limits : Limits := ⟨1, some 1⟩
  let memTy : MemoryType := ⟨if wide then .i64 else .i32, limits⟩
  let ctx : TContext := ⟨types, types, [⟨.mut, .i32⟩], [⟨limits, .funcref⟩],
    [memTy, memTy], params, [[result]], some [result]⟩
  unless bETypeChecker ctx code (.tf [] [result]) do throw "body failed type checking"
  let mem : Memory := ⟨MemoryList.memMake 0 pageSize, memTy⟩
  let helper : FunctionClosure := .funcNative inst helperTy []
    [.getLocal 0, .const (.int32 1), .binop .i32 (.i .add)]
  let store : StoreRecord := ⟨[helper, .funcNative inst runTy [] code],
    [⟨RunTable.ofList [some 0], some 1⟩], [mem, mem], [⟨.mut, .int32 0⟩]⟩
  return ((store, [], inst), params)

private def observe (σ : State) (params : List ValueType) (trial : Json) :
    Except String Json := do
  let args : List String ← Lean.fromJson? trial
  unless args.length == params.length do throw "argument count mismatch"
  let vs ← (params.zip args).mapM fun (t, n) ↦ argument t n
  match (runUntil 512 (vToEList vs ++ [.invoke 1], σ)).2 with
  | .boundary .trapV => return Json.mkObj [("kind", .str "trap")]
  | .boundary (.immV [v]) =>
    let (ty, bits) : String × Nat ← match v with
      | .int32 x => pure ("i32", x.toNat)
      | .int64 x => pure ("i64", x.toNat)
      | _ => throw "unexpected noninteger runtime result"
    let value := Json.mkObj [("type", .str ty), ("value", .str (toString bits))]
    return Json.mkObj [("kind", .str "return"), ("values", .arr #[value])]
  | .boundary _ => throw "unexpected runtime boundary"
  | .budget => throw "step budget exhausted"
  | .frameLimit => throw "frame limit reached"
  | .noLeaf => throw "no executable leaf"

private def outcome : Except String Json → Json
  | .ok j => j
  | .error e => Json.mkObj [("kind", .str "error"), ("diagnostic", .str e)]

private def rows (line : String) : Except String Json := do
  let msg ← Json.parse line
  let trials ← msg.getObjValAs? (Array Json) "trials"
  if trials.isEmpty then throw "empty trial batch"
  let setup := prepare msg
  let mut out : Array Json := Array.emptyWithCapacity trials.size
  for h : i in [:trials.size] do
    let actual := setup.bind fun (σ, params) ↦ observe σ params trials[i]
    out := out.push (.arr #[toJson (i + 1), outcome actual])
  return .arr out

/-- Consume one generated module batch per line; importing this file runs no requests. -/
def serve : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let reply := match rows line with
      | .ok batch => batch
      | .error e => Json.arr #[.arr #[toJson (1 : Nat), outcome (.error e)]]
    stdout.putStrLn reply.compress
    stdout.flush

end WasmTest.FuzzRuntime

def main : IO Unit := WasmTest.FuzzRuntime.serve
