/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import Wasm.Operations
import Iris.Std.Relation

/-! Port of `theories/opsem.v`: the small-step operational semantics.
Constructor variables occurring in the conclusion are implicit; the others are explicit (Coq order). -/

namespace Wasm

open AdministrativeInstruction (basic trap)

@[rocq_alias iriswasm.reduce_simple]
inductive ReduceSimple : List AdministrativeInstruction → List AdministrativeInstruction → Prop where
  | unop {v : Value} {op : Unop} {t : ValueType} :
    typesAgree t v = true → unopTypeOK t op = true →
    ReduceSimple [basic (.const v), basic (.unop t op)] [basic (.const (appUnop op v))]
  | binopSuccess {v1 v2 v : Value} {op : Binop} {t : ValueType} :
    typesAgree t v1 = true → typesAgree t v2 = true → binopTypeOK t op = true →
    appBinop op v1 v2 = some v →
    ReduceSimple [basic (.const v1), basic (.const v2), basic (.binop t op)] [basic (.const v)]
  | binopFailure {v1 v2 : Value} {op : Binop} {t : ValueType} :
    typesAgree t v1 = true → typesAgree t v2 = true → binopTypeOK t op = true →
    appBinop op v1 v2 = none →
    ReduceSimple [basic (.const v1), basic (.const v2), basic (.binop t op)] [trap]
  | testopI32 {c : I32} :
    ReduceSimple [basic (.const (.int32 c)), basic (.testop .i32 .eqz)]
      [basic (.const (.int32 (wasmBool (Int.ieqz c))))]
  | testopI64 {c : I64} :
    ReduceSimple [basic (.const (.int64 c)), basic (.testop .i64 .eqz)]
      [basic (.const (.int32 (wasmBool (Int.ieqz c))))]
  | testopV128 {c : BitVec 128} :
    ReduceSimple [basic (.const (.vec128 c)), basic (.testop .v128 .anyTrue)]
      [basic (.const (.int32 (wasmBool (c != 0))))]
  | relop {v1 v2 : Value} {t : ValueType} {op : Relop} :
    typesAgree t v1 = true → typesAgree t v2 = true → relopTypeOK t op = true →
    ReduceSimple [basic (.const v1), basic (.const v2), basic (.relop t op)]
      [basic (.const (.int32 (wasmBool (appRelop op v1 v2))))]
  | convertSuccess {t1 t2 : ValueType} {v v' : Value} {sx : Option Sx} :
    typesAgree t1 v = true → convertCond t2 t1 sx = true → cvt t2 sx v = some v' →
    ReduceSimple [basic (.const v), basic (.cvtop t2 .convert t1 sx)] [basic (.const v')]
  | convertFailure {t1 t2 : ValueType} {v : Value} {sx : Option Sx} :
    typesAgree t1 v = true → convertCond t2 t1 sx = true → cvt t2 sx v = none →
    ReduceSimple [basic (.const v), basic (.cvtop t2 .convert t1 sx)] [trap]
  | reinterpret {t1 t2 : ValueType} {v : Value} :
    typesAgree t1 v = true → reinterpretCond t2 t1 = true →
    ReduceSimple [basic (.const v), basic (.cvtop t2 .reinterpret t1 none)]
      [basic (.const (wasmDeserialise (bits v) t2))]
  | truncSat {src dst : ValueType} {sx : Sx} {v w : Value} :
    typesAgree src v = true → Wasm.truncSat dst sx v = some w →
    ReduceSimple [basic (.const v), basic (.cvtop dst .truncSat src (some sx))] [basic (.const w)]
  | unreachable : ReduceSimple [basic .unreachable] [trap]
  | nop : ReduceSimple [basic .nop] []
  | drop {v : Value} : ReduceSimple [basic (.const v), basic .drop] []
  | vbitselect {x y mask : BitVec 128} :
    ReduceSimple [basic (.const (.vec128 x)), basic (.const (.vec128 y)), basic (.const (.vec128 mask)),
      basic .vbitselect] [basic (.const (.vec128 (Wasm.vbitselect x y mask)))]
  | selectFalse {n : I32} {v1 v2 : Value} :
    n = Int.zero →
    ReduceSimple [basic (.const v1), basic (.const v2), basic (.const (.int32 n)), basic .select]
      [basic (.const v2)]
  | selectTrue {n : I32} {v1 v2 : Value} :
    n ≠ Int.zero →
    ReduceSimple [basic (.const v1), basic (.const v2), basic (.const (.int32 n)), basic .select]
      [basic (.const v1)]
  | ifFalse {n : I32} {tf : BlockType} {e1s e2s : List BasicInstruction} :
    n = Int.zero →
    ReduceSimple [basic (.const (.int32 n)), basic (.if_ tf e1s e2s)] [basic (.block tf e2s)]
  | ifTrue {n : I32} {tf : BlockType} {e1s e2s : List BasicInstruction} :
    n ≠ Int.zero →
    ReduceSimple [basic (.const (.int32 n)), basic (.if_ tf e1s e2s)] [basic (.block tf e1s)]
  | labelConst {n : Nat} {es vs : List AdministrativeInstruction} :
    constList vs = true → ReduceSimple [.label n es vs] vs
  | labelTrap {n : Nat} {es : List AdministrativeInstruction} :
    ReduceSimple [.label n es [trap]] [trap]
  | br {n : Nat} {vs es : List AdministrativeInstruction} (i : Nat) {LI : List AdministrativeInstruction}
      (lh : Lholed) :
    constList vs = true → vs.length = n → lfilled i lh (vs ++ [basic (.br i)]) LI = true →
    ReduceSimple [.label n es LI] (vs ++ es)
  | brIfFalse {n : I32} {i : Nat} :
    n = Int.zero → ReduceSimple [basic (.const (.int32 n)), basic (.brIf i)] []
  | brIfTrue {n : I32} {i : Nat} :
    n ≠ Int.zero → ReduceSimple [basic (.const (.int32 n)), basic (.brIf i)] [basic (.br i)]
  | brTable {iss : List Nat} {c : I32} {i j : Nat} :
    iss.length > Int.natOfUint c → iss[Int.natOfUint c]? = some j →
    ReduceSimple [basic (.const (.int32 c)), basic (.brTable iss i)] [basic (.br j)]
  | brTableLength {iss : List Nat} {c : I32} {i : Nat} :
    iss.length ≤ Int.natOfUint c →
    ReduceSimple [basic (.const (.int32 c)), basic (.brTable iss i)] [basic (.br i)]
  | localConst {es : List AdministrativeInstruction} {n : Nat} {f : Frame} :
    constList es = true → es.length = n → ReduceSimple [.local n f es] es
  | localTrap {n : Nat} {f : Frame} : ReduceSimple [.local n f [trap]] [trap]
  | return_ {n : Nat} (i : Nat) {vs es : List AdministrativeInstruction} (lh : Lholed) {f : Frame} :
    constList vs = true → vs.length = n → lfilled i lh (vs ++ [basic .return_]) es = true →
    ReduceSimple [.local n f es] vs
  | teeLocal {i : Nat} {v : AdministrativeInstruction} :
    isConst v = true → ReduceSimple [v, basic (.teeLocal i)] [v, v, basic (.setLocal i)]
  | trap {es : List AdministrativeInstruction} (lh : Lholed) :
    es ≠ [trap] → lfilled 0 lh [trap] es = true → ReduceSimple es [trap]

inductive Reduce : StoreRecord → Frame → List AdministrativeInstruction →
    StoreRecord → Frame → List AdministrativeInstruction → Prop where
  | simple {e e' : List AdministrativeInstruction} {s : StoreRecord} {f : Frame} :
    ReduceSimple e e' → Reduce s f e s f e'
  | block {s f bt tn tm vs es} :
      expandBlockType f.inst.types bt = some (.tf tn tm) → constList vs = true → vs.length = tn.length →
      Reduce s f (vs ++ [basic (.block bt es)]) s f [.label tm.length [] (vs ++ toEList es)]
  | loop {s f bt tn tm vs es} :
      expandBlockType f.inst.types bt = some (.tf tn tm) → constList vs = true → vs.length = tn.length →
      Reduce s f (vs ++ [basic (.loop bt es)]) s f
        [.label tn.length [basic (.loop bt es)] (vs ++ toEList es)]
  | call {s : StoreRecord} {f : Frame} {i a : Nat} :
    f.inst.funcs[i]? = some a → Reduce s f [basic (.call i)] s f [.invoke a]
  | callIndirectSuccess {s : StoreRecord} {f : Frame} {i a : Nat} (cl : FunctionClosure) {c : I32} :
    stabAddr s f (Int.natOfUint c) = some a → s.funcs[a]? = some cl →
    stypes s f.inst i = some (clType cl) →
    Reduce s f [basic (.const (.int32 c)), basic (.callIndirect i)] s f [.invoke a]
  | callIndirectFailure1 {s : StoreRecord} {f : Frame} {i : Nat} (a : Nat) (cl : FunctionClosure)
      {c : I32} :
    stabAddr s f (Int.natOfUint c) = some a → s.funcs[a]? = some cl →
    stypes s f.inst i ≠ some (clType cl) →
    Reduce s f [basic (.const (.int32 c)), basic (.callIndirect i)] s f [trap]
  | callIndirectFailure2 {s : StoreRecord} {f : Frame} {i : Nat} {c : I32} :
    stabAddr s f (Int.natOfUint c) = none →
    Reduce s f [basic (.const (.int32 c)), basic (.callIndirect i)] s f [trap]
  | invokeNative {a : Nat} (cl : FunctionClosure) (t1s : List ValueType) {t2s : List ValueType}
      (ts : List ValueType) {es : List BasicInstruction} {ves : List AdministrativeInstruction}
      (vcs : List Value) (n : Nat) {m : Nat} (k : Nat) (zs : List Value) {s : StoreRecord}
      {f f' : Frame} (i : Instance) :
    s.funcs[a]? = some cl → cl = .funcNative i (.tf t1s t2s) ts es → ves = vToEList vcs →
    vcs.length = n → ts.length = k → t1s.length = n → t2s.length = m → nZeros ts = zs →
    f'.inst = i → f'.locs = vcs ++ zs →
    Reduce s f (ves ++ [.invoke a]) s f [.local m f' [.label m [] (toEList es)]]
  | invokeHost {a : Nat} (cl : FunctionClosure) {h : Hostfuncidx} {t1s t2s : List ValueType}
      {ves : List AdministrativeInstruction} {vcs : List Value} (m n : Nat) {s : StoreRecord}
      {f : Frame} :
    s.funcs[a]? = some cl → cl = .funcHost (.tf t1s t2s) h → ves = vToEList vcs →
    vcs.length = n → t1s.length = n → t2s.length = m →
    Reduce s f (ves ++ [.invoke a]) s f [.callHost (.tf t1s t2s) h vcs]
  | getLocal {f : Frame} {v : Value} {j : Nat} {s : StoreRecord} :
    f.locs[j]? = some v → Reduce s f [basic (.getLocal j)] s f [basic (.const v)]
  | setLocal {f f' : Frame} {i : Nat} {v : Value} {s : StoreRecord} :
    f'.inst = f.inst → i < f.locs.length → f'.locs = f.locs.set i v →
    Reduce s f [basic (.const v), basic (.setLocal i)] s f' []
  | getGlobal {s : StoreRecord} {f : Frame} {i : Nat} {v : Value} :
    sglobVal s f.inst i = some v → Reduce s f [basic (.getGlobal i)] s f [basic (.const v)]
  | setGlobal {s : StoreRecord} {f : Frame} {i : Nat} {v : Value} {s' : StoreRecord} :
    supdateGlob s f.inst i v = some s' →
    Reduce s f [basic (.const v), basic (.setGlobal i)] s' f []
  | loadSuccess {s : StoreRecord} (i : Nat) {f : Frame} {t : ValueType} {bs : Bytes} {k : AddressOperand}
      {ma : MemArg} (m : Memory) :
    f.inst.memory[ma.memory]? = some i → s.mems[i]? = some m →
    load m k.unsigned ma.offset (lengthT t) = some bs →
    Reduce s f [basic (.const k.value), basic (.load t none ma)] s f
      [basic (.const (wasmDeserialise bs t))]
  | loadFailure {s : StoreRecord} (i : Nat) {f : Frame} {t : ValueType} {k : AddressOperand}
      {ma : MemArg} (m : Memory) :
    f.inst.memory[ma.memory]? = some i → s.mems[i]? = some m →
    load m k.unsigned ma.offset (lengthT t) = none →
    Reduce s f [basic (.const k.value), basic (.load t none ma)] s f [trap]
  | loadPackedSuccess {s : StoreRecord} (i : Nat) {f : Frame} {t : ValueType} {tp : PackedType}
      {k : AddressOperand} {ma : MemArg} (m : Memory) {bs : Bytes} {sx : Sx} :
    packedTypeOK tp t = true →
    f.inst.memory[ma.memory]? = some i → s.mems[i]? = some m →
    loadPacked sx m k.unsigned ma.offset (lengthTp tp) (lengthT t) = some bs →
    Reduce s f [basic (.const k.value), basic (.load t (some (tp, sx)) ma)] s f
      [basic (.const (wasmDeserialise bs t))]
  | loadPackedFailure {s : StoreRecord} (i : Nat) {f : Frame} {t : ValueType} {tp : PackedType}
      {k : AddressOperand} {ma : MemArg} (m : Memory) {sx : Sx} :
    packedTypeOK tp t = true →
    f.inst.memory[ma.memory]? = some i → s.mems[i]? = some m →
    loadPacked sx m k.unsigned ma.offset (lengthTp tp) (lengthT t) = none →
    Reduce s f [basic (.const k.value), basic (.load t (some (tp, sx)) ma)] s f [trap]
  | storeSuccess {t : ValueType} {v : Value} {s : StoreRecord} {i : Nat} {f : Frame} {mem' : Memory}
      {k : AddressOperand} {ma : MemArg} (m : Memory) :
    typesAgree t v = true → f.inst.memory[ma.memory]? = some i → s.mems[i]? = some m →
    store m k.unsigned ma.offset (bits v) (lengthT t) = some mem' →
    Reduce s f [basic (.const k.value), basic (.const v), basic (.store t none ma)]
      (updSMem s (updateListAt s.mems i mem')) f []
  | storeFailure {t : ValueType} {v : Value} {s : StoreRecord} (i : Nat) {f : Frame} (m : Memory)
      {k : AddressOperand} {ma : MemArg} :
    typesAgree t v = true → f.inst.memory[ma.memory]? = some i → s.mems[i]? = some m →
    store m k.unsigned ma.offset (bits v) (lengthT t) = none →
    Reduce s f [basic (.const k.value), basic (.const v), basic (.store t none ma)] s f [trap]
  | storePackedSuccess {t : ValueType} {v : Value} {s : StoreRecord} {i : Nat} {f : Frame}
      (m : Memory) {k : AddressOperand} {ma : MemArg} {mem' : Memory}
      {tp : PackedType} :
    packedTypeOK tp t = true →
    typesAgree t v = true → f.inst.memory[ma.memory]? = some i → s.mems[i]? = some m →
    storePacked m k.unsigned ma.offset (bits v) (lengthTp tp) = some mem' →
    Reduce s f [basic (.const k.value), basic (.const v), basic (.store t (some tp) ma)]
      (updSMem s (updateListAt s.mems i mem')) f []
  | storePackedFailure {t : ValueType} {v : Value} {s : StoreRecord} (i : Nat) {f : Frame}
      (m : Memory) {k : AddressOperand} {ma : MemArg} {tp : PackedType} :
    packedTypeOK tp t = true →
    typesAgree t v = true → f.inst.memory[ma.memory]? = some i → s.mems[i]? = some m →
    storePacked m k.unsigned ma.offset (bits v) (lengthTp tp) = none →
    Reduce s f [basic (.const k.value), basic (.const v), basic (.store t (some tp) ma)] s f
      [trap]
  | currentMemory (i : Nat) {f : Frame} (m : Memory) {n x : Nat} {s : StoreRecord} :
    f.inst.memory[x]? = some i → s.mems[i]? = some m → lengthMem m = n * pageSize →
    n < 2^m.type.address.width →
    Reduce s f [basic (.currentMemory x)] s f [basic (.const (m.type.address.natValue n))]
  | growMemorySuccess {s : StoreRecord} {i : Nat} {f : Frame} (m : Memory) {n : Nat} {mem' : Memory}
      {x : Nat} {c : AddressOperand} :
    f.inst.memory[x]? = some i → s.mems[i]? = some m → memSize m = n →
    n < 2^c.address.width →
    memGrow m c.unsigned = some mem' →
    Reduce s f [basic (.const c.value), basic (.growMemory x)]
      (updSMem s (updateListAt s.mems i mem')) f [basic (.const (c.result n))]
  | growMemoryFailure {f : Frame} {s : StoreRecord} {x : Nat} {c : AddressOperand} :
    Reduce s f [basic (.const c.value), basic (.growMemory x)] s f [basic (.const c.failure)]
  | label {s : StoreRecord} {f : Frame} (es : List AdministrativeInstruction)
      {les : List AdministrativeInstruction} {s' : StoreRecord} {f' : Frame}
      (es' : List AdministrativeInstruction) {les' : List AdministrativeInstruction} (k : Nat)
      (lh : Lholed) :
    Reduce s f es s' f' es' → lfilled k lh es les = true → lfilled k lh es' les' = true →
    Reduce s f les s' f' les'
  | local {s : StoreRecord} {f : Frame} {es : List AdministrativeInstruction} {s' : StoreRecord}
      {f' : Frame} {es' : List AdministrativeInstruction} {n : Nat} {f0 : Frame} :
    Reduce s f es s' f' es' → Reduce s f0 [.local n f es] s' f0 [.local n f' es']

@[rocq_alias iriswasm.reduce_tuple]
def ReduceTuple : StoreRecord × Frame × List AdministrativeInstruction →
    StoreRecord × Frame × List AdministrativeInstruction → Prop
  | (s, f, es), (s', f', es') => Reduce s f es s' f' es'

@[rocq_alias iriswasm.reduce_trans]
def ReduceTrans : StoreRecord × Frame × List AdministrativeInstruction →
    StoreRecord × Frame × List AdministrativeInstruction → Prop :=
  FromMathlib.Relation.ReflTransGen ReduceTuple

end Wasm
