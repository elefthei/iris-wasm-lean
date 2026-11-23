import IrisWasm.Denotational.Effects

namespace IrisWasm.Denotational
open Wasm

/-- Emit one boundary, restoring the unconsumed top-first stack to source order. -/
def emit (vs : List Value) (replacement tail : Expr) : WasmProg Front :=
  pure (.next (vToEList vs.reverse ++ (replacement ++ tail)))

/-- Split off the top `n` arguments and present them in source order. -/
def withArgs (n : Nat) (vs : List Value) (k : List Value → List Value → WasmProg Front) :
    WasmProg Front :=
  if n ≤ vs.length then k (vs.drop n) (vs.take n).reverse else .stuck

/-- Numeric operations and loads turn failure into a trap, not a stuck computation. -/
def resultCode : Option Value → Expr
  | some v => [.basic (.const v)]
  | none => [.trap]

/-- Inline results need no store read. An unknown type index has no enabled continuation. -/
def withBlockType {α : Type} (bt : Wasm.BlockType) (k : FunctionType → WasmProg α) : WasmProg α :=
  match bt with
  | .result t => k (.tf [] t.toList)
  | .index i => .vis (.typeAt i) fun
    | some tf => k tf
    | none => .stuck

/-- The continuation is called only by a constant: every other instruction is a boundary. -/
def basicLayer (b : BasicInstruction) (vs : List Value) (tail : Expr)
    (push : List Value → WasmProg Front) : WasmProg Front :=
  match b with
  | .const v => push (v :: vs)
  | .unreachable => emit vs [.trap] tail
  | .nop => emit vs [] tail
  | .drop => match vs with
    | _ :: ws => emit ws [] tail
    | _ => .stuck
  | .select => match vs with
    | .int32 n :: v2 :: v1 :: ws =>
      emit ws [.basic (.const (if n = Wasm.Int.zero then v2 else v1))] tail
    | _ => .stuck
  | .vbitselect => match vs with
    | .vec128 mask :: .vec128 y :: .vec128 x :: ws =>
      emit ws [.basic (.const (.vec128 (vbitselect x y mask)))] tail
    | _ => .stuck
  | .unop t op => match vs with
    | v :: ws => if typesAgree t v && unopTypeOK t op then emit ws [.basic (.const (appUnop op v))] tail
      else .stuck
    | _ => .stuck
  | .binop t op => match vs with
    | v2 :: v1 :: ws =>
      if typesAgree t v1 && typesAgree t v2 && binopTypeOK t op then
        emit ws (resultCode (appBinop op v1 v2)) tail
      else .stuck
    | _ => .stuck
  | .testop t op => match t, op, vs with
    | .i32, .eqz, .int32 n :: ws => emit ws [.basic (.const (.int32 (wasmBool (Wasm.Int.ieqz n))))] tail
    | .i64, .eqz, .int64 n :: ws => emit ws [.basic (.const (.int32 (wasmBool (Wasm.Int.ieqz n))))] tail
    | .v128, .anyTrue, .vec128 n :: ws => emit ws [.basic (.const (.int32 (wasmBool (n != 0))))] tail
    | _, _, _ => .stuck
  | .relop t op => match vs with
    | v2 :: v1 :: ws =>
      if typesAgree t v1 && typesAgree t v2 && relopTypeOK t op then
        emit ws [.basic (.const (.int32 (wasmBool (appRelop op v1 v2))))] tail
      else .stuck
    | _ => .stuck
  | .cvtop t2 op t1 sx => match vs with
    | v :: ws => if typesAgree t1 v then
        match op, sx with
        | .convert, _ => if convertCond t2 t1 sx then emit ws (resultCode (cvt t2 sx v)) tail else .stuck
        | .reinterpret, none => if reinterpretCond t2 t1 then
            emit ws [.basic (.const (wasmDeserialise (bits v) t2))] tail else .stuck
        | .reinterpret, some _ => .stuck
        | .truncSat, some s => match truncSat t2 s v with
          | some w => emit ws [.basic (.const w)] tail
          | none => .stuck
        | .truncSat, none => .stuck
      else .stuck
    | _ => .stuck
  | .block bt body => withBlockType bt fun (.tf ins outs) ↦
    withArgs ins.length vs fun ws args ↦ emit ws [.label outs.length [] (vToEList args ++ toEList body)] tail
  | .loop bt body => withBlockType bt fun (.tf ins _) ↦
    withArgs ins.length vs fun ws args ↦
      emit ws [.label ins.length [.basic (.loop bt body)] (vToEList args ++ toEList body)] tail
  | .if_ tf yes no => match vs with
    | .int32 n :: ws => emit ws [.basic (.block tf (if n = Wasm.Int.zero then no else yes))] tail
    | _ => .stuck
  | .br i => pure (.done (.brV (ValidHoled.base (n := i) vs.reverse tail)))
  | .return_ => pure (.done (.retV (.base vs.reverse tail)))
  | .brIf i => match vs with
    | .int32 n :: ws => emit ws (if n = Wasm.Int.zero then [] else [.basic (.br i)]) tail
    | _ => .stuck
  | .brTable targets fallback => match vs with
    | .int32 n :: ws =>
      emit ws [.basic (.br (targets[Wasm.Int.natOfUint n]?.getD fallback))] tail
    | _ => .stuck
  | .call i => .vis (.callAddr i) fun a => emit vs [.invoke a] tail
  | .callIndirect i => match vs with
    | .int32 n :: ws => .vis (.tableAddr (Wasm.Int.natOfUint n)) fun
      | none => emit ws [.trap] tail
      | some a => .vis (.closureAt a) fun cl => .vis (.typeAt i) fun tf =>
        emit ws (if tf = some (clType cl) then [.invoke a] else [.trap]) tail
    | _ => .stuck
  | .getLocal i => .vis (.getLocal i) fun v => emit vs [.basic (.const v)] tail
  | .setLocal i => match vs with
    | v :: ws => .vis (.setLocal i v) fun _ => emit ws [] tail
    | _ => .stuck
  | .teeLocal i => match vs with
    | v :: ws => emit ws [.basic (.const v), .basic (.const v), .basic (.setLocal i)] tail
    | _ => .stuck
  | .getGlobal i => .vis (.getGlobal i) fun v => emit vs [.basic (.const v)] tail
  | .setGlobal i => match vs with
    | v :: ws => .vis (.setGlobal i v) fun _ => emit ws [] tail
    | _ => .stuck
  | .load t pack ma => match vs with
    | v :: ws => match AddressOperand.ofValue? v with
      | some addr => if pack.all (fun p ↦ packedTypeOK p.1 t) then
          .vis (.readMem ma.memory t pack addr.unsigned ma.offset) fun r => emit ws (resultCode r) tail
        else .stuck
      | none => .stuck
    | _ => .stuck
  | .store t pack ma => match vs with
    | v :: p :: ws => match AddressOperand.ofValue? p with
      | some addr => if typesAgree t v && pack.all (packedTypeOK · t) then
          .vis (.writeMem ma.memory t pack addr.unsigned ma.offset v) fun ok =>
            emit ws (if ok then [] else [.trap]) tail
        else .stuck
      | none => .stuck
    | _ => .stuck
  | .currentMemory x => .vis (.currentPages x) fun v => emit vs [.basic (.const v)] tail
  | .growMemory x => match vs with
    | v :: ws => match AddressOperand.ofValue? v with
      | some d => .vis (.growPages x d) fun r => emit ws [.basic (.const r)] tail
      | none => .stuck
    | _ => .stuck

end IrisWasm.Denotational
