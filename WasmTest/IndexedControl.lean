import Wasm.Binary
import IrisWasm.Denotational.Run
import Wasm.ModuleValidation

namespace WasmTest.IndexedControl
open Wasm IrisWasm IrisWasm.Denotational

private def sig : FunctionType := .tf [.i32] [.v128, .i64]
private def types : List FunctionType := [.tf [] [], sig]
private def inst := { emptyInstance with types }
private def caller : State := (⟨[], [], [], []⟩, [.int32 99], inst)
private def i32 (x : I32) := AdministrativeInstruction.basic (.const (.int32 x))
private def body : List BasicInstruction := [.drop, .const (.vec128 7), .const (.int64 9)]
private def blockOp := BasicInstruction.block (.index 1) body
private def loopOp := BasicInstruction.loop (.index 1) [.br 0]
private def start (op : BasicInstruction) : Cfg := ([i32 3, i32 23, .basic op], caller)

/-- The signature uses slot 1, retains the lower operand and sets the label arity to two. -/
theorem block_step : runCut 1 (start blockOp) =
    some ([i32 3, .label 2 [] (i32 23 :: toEList body)], caller) := by decide +kernel

/-- Loop continuation carries the original index; its label arity counts parameters, not results. -/
theorem loop_step : runCut 1 (start loopOp) =
    some ([i32 3, .label 1 [.basic loopOp] [i32 23, .basic (.br 0)]], caller) := by decide +kernel

#guard runCut 2 (start loopOp) == some (start loopOp)
#guard runCut 3 (start blockOp) == some ([i32 3, .basic (.const (.vec128 7)), .basic (.const (.int64 9))], caller)
#guard runCut 1 ([.basic blockOp], caller) == none -- valid index, missing parameter

theorem missing_block_index_stuck {s f s' f' out i} (args : List Value) (es : List BasicInstruction)
    (missing : f.inst.types[i]? = none) :
    ¬ Reduce s f (vToEList args ++ [.basic (.block (.index i) es)]) s' f' out := by
  intro step
  have h := (round_next_iff (σ := stateOf s f) (σ' := stateOf s' f')).2 ⟨step, rfl, rfl⟩
  change Runs (layer _) (stateOf s f) (.next out) (stateOf s' f') at h
  rw [layer, frag_consts, frag, basicLayer, runs_withBlockType] at h
  obtain ⟨tf, ht, _⟩ := h
  change f.inst.types[i]? = some tf at ht
  simp [missing] at ht

private def unknown := BasicInstruction.if_ (.index 12) [.nop] [.unreachable]

theorem if_defers_lookup :
    runCut 1 ([i32 1, .basic unknown], caller) = some ([.basic (.block (.index 12) [.nop])], caller) ∧
    runCut 1 ([i32 0, .basic unknown], caller) = some ([.basic (.block (.index 12) [.unreachable])], caller) ∧
    runCut 2 ([i32 0, .basic unknown], caller) = none := by decide +kernel

-- The caller has slot 1, but the active frame does not.
#guard runCut 1 ([.local 0 ⟨[], emptyInstance⟩ [i32 23, .basic blockOp]], caller) == none
-- Conversely a callee's type must work even if the caller lacks it.
private def outside : State := (caller.1, [], emptyInstance)
#guard runCut 1 ([.local 2 ⟨[], inst⟩ [i32 23, .basic blockOp]], outside) ==
  some ([.local 2 ⟨[], inst⟩ [.label 2 [] (i32 23 :: toEList body)]], outside)

private def ctx : TContext := ⟨types, [], [], [], [], [], [], none⟩

theorem block_typed : BeTyping ctx [blockOp] sig := by decide
theorem loop_typed : BeTyping ctx [loopOp] sig := by decide
#guard !bETypeChecker ctx [unknown] (.tf [.i32] [])
#guard !bETypeChecker ctx [.loop (.index 1) [.const (.int32 1), .br 0]] (.tf [] [])
theorem if_typed : BeTyping ctx [.if_ (.index 1) body body] (.tf [.i32, .i32] [.v128, .i64]) := by
  decide
#guard !bETypeChecker ctx [.if_ (.index 1) body []] (.tf [.i32, .i32] [.v128, .i64])

private def readExpr := Binary.structuredExpr Binary.numVecType Binary.numericPayload

private def parse (bs : Array UInt8) := (Binary.complete readExpr (ByteArray.mk bs).toByteSlice).toOption

/-- The unmodified expression bytes of `block.wast`'s `params-break` export, after the locals. -/
theorem params_break_bytes :
    parse #[0x41, 1, 0x41, 2, 2, 0, 0x6a, 0x0c, 0, 0x0b, 0x0b] =
      some [.const (.int32 1), .const (.int32 2),
        .block (.index 0) [.binop .i32 (.i .add), .br 0]] := by decide +kernel

private def paramsBreakCut : Option IrisWasm.Expr := do
  let es ← parse #[0x41, 1, 0x41, 2, 2, 0, 0x6a, 0x0c, 0, 0x0b, 0x0b]
  let i := { emptyInstance with types := [.tf [.i32, .i32] [.i32]] }
  return (← runCut 3 (toEList es, caller.1, [], i)).1

#guard paramsBreakCut == some [i32 3]

theorem nested_else_bytes :
    parse #[4, 0x40, 2, 0x7f, 0x0f, 0x0b, 5, 3, 0x80, 1, 0x0d, 0, 0x0b, 0x0b, 0x0b] =
      some [.if_ (.result none) [.block (.result (some .i32)) [.return_]]
        [.loop (.index 128) [.brIf 0]]] := by decide +kernel

#guard parse #[4, 0x40, 0x0b, 0x0b] == some [.if_ (.result none) [] []]
#guard parse #[0x0e, 2, 0x80, 1, 0, 3, 0x0b] == some [.brTable [128, 0] 3]
#guard (parse #[0x0e, 0]).isNone -- missing mandatory default
#guard (parse #[5, 0x0b]).isNone -- unmatched else
#guard (parse #[4, 0x40, 5, 5, 0x0b, 0x0b]).isNone -- second else
#guard (parse #[4, 0x40, 2, 0x40, 5, 0x0b, 0x0b]).isNone -- else cannot cross an open block
#guard (parse #[2, 0, 0x0b]).isNone -- end closed the block, not the outer expression
#guard (parse #[0x0b, 0x0b]).isNone -- trailing byte in a complete window

end WasmTest.IndexedControl
