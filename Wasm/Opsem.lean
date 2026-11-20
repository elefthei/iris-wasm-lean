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
    ReduceSimple [basic (.const v), basic (.unop t op)] [basic (.const (appUnop op v))]
  | binopSuccess {v1 v2 v : Value} {op : Binop} {t : ValueType} :
    appBinop op v1 v2 = some v →
    ReduceSimple [basic (.const v1), basic (.const v2), basic (.binop t op)] [basic (.const v)]
  | binopFailure {v1 v2 : Value} {op : Binop} {t : ValueType} :
    appBinop op v1 v2 = none →
    ReduceSimple [basic (.const v1), basic (.const v2), basic (.binop t op)] [trap]
  | testopI32 {c : I32} {testop : Testop} :
    ReduceSimple [basic (.const (.int32 c)), basic (.testop .i32 testop)]
      [basic (.const (.int32 (wasmBool (appTestopI testop c))))]
  | testopI64 {c : I64} {testop : Testop} :
    ReduceSimple [basic (.const (.int64 c)), basic (.testop .i64 testop)]
      [basic (.const (.int32 (wasmBool (appTestopI testop c))))]
  | relop {v1 v2 : Value} {t : ValueType} {op : Relop} :
    ReduceSimple [basic (.const v1), basic (.const v2), basic (.relop t op)]
      [basic (.const (.int32 (wasmBool (appRelop op v1 v2))))]
  | convertSuccess {t1 t2 : ValueType} {v v' : Value} {sx : Option Sx} :
    typesAgree t1 v = true → cvt t2 sx v = some v' →
    ReduceSimple [basic (.const v), basic (.cvtop t2 .convert t1 sx)] [basic (.const v')]
  | convertFailure {t1 t2 : ValueType} {v : Value} {sx : Option Sx} :
    typesAgree t1 v = true → cvt t2 sx v = none →
    ReduceSimple [basic (.const v), basic (.cvtop t2 .convert t1 sx)] [trap]
  | reinterpret {t1 t2 : ValueType} {v : Value} :
    typesAgree t1 v = true →
    ReduceSimple [basic (.const v), basic (.cvtop t2 .reinterpret t1 none)]
      [basic (.const (wasmDeserialise (bits v) t2))]
  | unreachable : ReduceSimple [basic .unreachable] [trap]
  | nop : ReduceSimple [basic .nop] []
  | drop {v : Value} : ReduceSimple [basic (.const v), basic .drop] []
  | selectFalse {n : I32} {v1 v2 : Value} :
    n = Int.zero →
    ReduceSimple [basic (.const v1), basic (.const v2), basic (.const (.int32 n)), basic .select]
      [basic (.const v2)]
  | selectTrue {n : I32} {v1 v2 : Value} :
    n ≠ Int.zero →
    ReduceSimple [basic (.const v1), basic (.const v2), basic (.const (.int32 n)), basic .select]
      [basic (.const v1)]
  | block {vs : List AdministrativeInstruction} {es : List BasicInstruction} (n : Nat) {m : Nat}
      {t1s t2s : List ValueType} :
    constList vs = true → vs.length = n → t1s.length = n → t2s.length = m →
    ReduceSimple (vs ++ [basic (.block (.tf t1s t2s) es)]) [.label m [] (vs ++ toEList es)]
  | loop {vs : List AdministrativeInstruction} {es : List BasicInstruction} {n : Nat} (m : Nat)
      {t1s t2s : List ValueType} :
    constList vs = true → vs.length = n → t1s.length = n → t2s.length = m →
    ReduceSimple (vs ++ [basic (.loop (.tf t1s t2s) es)])
      [.label n [basic (.loop (.tf t1s t2s) es)] (vs ++ toEList es)]
  | ifFalse {n : I32} {tf : FunctionType} {e1s e2s : List BasicInstruction} :
    n = Int.zero →
    ReduceSimple [basic (.const (.int32 n)), basic (.if_ tf e1s e2s)] [basic (.block tf e2s)]
  | ifTrue {n : I32} {tf : FunctionType} {e1s e2s : List BasicInstruction} :
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

@[rocq_alias iriswasm.reduce]
inductive Reduce : StoreRecord → Frame → List AdministrativeInstruction →
    StoreRecord → Frame → List AdministrativeInstruction → Prop where
  | simple {e e' : List AdministrativeInstruction} {s : StoreRecord} {f : Frame} :
    ReduceSimple e e' → Reduce s f e s f e'
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
    Reduce s f (ves ++ [.invoke a]) s f [.local m f' [basic (.block (.tf [] t2s) es)]]
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
  | loadSuccess {s : StoreRecord} (i : Nat) {f : Frame} {t : ValueType} {bs : Bytes} {k : I32}
      {a : AlignmentExponent} {off : StaticOffset} (m : Memory) :
    smemInd s f.inst = some i → s.mems[i]? = some m →
    load m (Int.nOfUint k) off (lengthT t) = some bs →
    Reduce s f [basic (.const (.int32 k)), basic (.load t none a off)] s f
      [basic (.const (wasmDeserialise bs t))]
  | loadFailure {s : StoreRecord} (i : Nat) {f : Frame} {t : ValueType} {k : I32}
      {a : AlignmentExponent} {off : StaticOffset} (m : Memory) :
    smemInd s f.inst = some i → s.mems[i]? = some m →
    load m (Int.nOfUint k) off (lengthT t) = none →
    Reduce s f [basic (.const (.int32 k)), basic (.load t none a off)] s f [trap]
  | loadPackedSuccess {s : StoreRecord} (i : Nat) {f : Frame} {t : ValueType} {tp : PackedType}
      {k : I32} {a : AlignmentExponent} {off : StaticOffset} (m : Memory) {bs : Bytes} {sx : Sx} :
    smemInd s f.inst = some i → s.mems[i]? = some m →
    loadPacked sx m (Int.nOfUint k) off (lengthTp tp) (lengthT t) = some bs →
    Reduce s f [basic (.const (.int32 k)), basic (.load t (some (tp, sx)) a off)] s f
      [basic (.const (wasmDeserialise bs t))]
  | loadPackedFailure {s : StoreRecord} (i : Nat) {f : Frame} {t : ValueType} {tp : PackedType}
      {k : I32} {a : AlignmentExponent} {off : StaticOffset} (m : Memory) {sx : Sx} :
    smemInd s f.inst = some i → s.mems[i]? = some m →
    loadPacked sx m (Int.nOfUint k) off (lengthTp tp) (lengthT t) = none →
    Reduce s f [basic (.const (.int32 k)), basic (.load t (some (tp, sx)) a off)] s f [trap]
  | storeSuccess {t : ValueType} {v : Value} {s : StoreRecord} {i : Nat} {f : Frame} {mem' : Memory}
      {k : I32} {a : AlignmentExponent} {off : StaticOffset} (m : Memory) :
    typesAgree t v = true → smemInd s f.inst = some i → s.mems[i]? = some m →
    store m (Int.nOfUint k) off (bits v) (lengthT t) = some mem' →
    Reduce s f [basic (.const (.int32 k)), basic (.const v), basic (.store t none a off)]
      (updSMem s (updateListAt s.mems i mem')) f []
  | storeFailure {t : ValueType} {v : Value} {s : StoreRecord} (i : Nat) {f : Frame} (m : Memory)
      {k : I32} {off : StaticOffset} {a : AlignmentExponent} :
    typesAgree t v = true → smemInd s f.inst = some i → s.mems[i]? = some m →
    store m (Int.nOfUint k) off (bits v) (lengthT t) = none →
    Reduce s f [basic (.const (.int32 k)), basic (.const v), basic (.store t none a off)] s f [trap]
  | storePackedSuccess {t : ValueType} {v : Value} {s : StoreRecord} {i : Nat} {f : Frame}
      (m : Memory) {k : I32} {off : StaticOffset} {a : AlignmentExponent} {mem' : Memory}
      {tp : PackedType} :
    typesAgree t v = true → smemInd s f.inst = some i → s.mems[i]? = some m →
    storePacked m (Int.nOfUint k) off (bits v) (lengthTp tp) = some mem' →
    Reduce s f [basic (.const (.int32 k)), basic (.const v), basic (.store t (some tp) a off)]
      (updSMem s (updateListAt s.mems i mem')) f []
  | storePackedFailure {t : ValueType} {v : Value} {s : StoreRecord} (i : Nat) {f : Frame}
      (m : Memory) {k : I32} {off : StaticOffset} {a : AlignmentExponent} {tp : PackedType} :
    typesAgree t v = true → smemInd s f.inst = some i → s.mems[i]? = some m →
    storePacked m (Int.nOfUint k) off (bits v) (lengthTp tp) = none →
    Reduce s f [basic (.const (.int32 k)), basic (.const v), basic (.store t (some tp) a off)] s f
      [trap]
  | currentMemory (i : Nat) {f : Frame} (m : Memory) {n : Nat} {s : StoreRecord} :
    smemInd s f.inst = some i → s.mems[i]? = some m → memSize m = n →
    Reduce s f [basic .currentMemory] s f
      [basic (.const (.int32 (Int.intOfZ (n : _root_.Int))))]
  | growMemorySuccess {s : StoreRecord} {i : Nat} {f : Frame} (m : Memory) {n : Nat} {mem' : Memory}
      {c : I32} :
    smemInd s f.inst = some i → s.mems[i]? = some m → memSize m = n →
    memGrow m (Int.nOfUint c) = some mem' →
    Reduce s f [basic (.const (.int32 c)), basic .growMemory]
      (updSMem s (updateListAt s.mems i mem')) f
      [basic (.const (.int32 (Int.intOfZ (n : _root_.Int))))]
  | growMemoryFailure (i : Nat) {f : Frame} (m : Memory) (n : Nat) {s : StoreRecord} {c : I32} :
    smemInd s f.inst = some i → s.mems[i]? = some m → memSize m = n →
    Reduce s f [basic (.const (.int32 c)), basic .growMemory] s f
      [basic (.const (.int32 int32MinusOne))]
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
