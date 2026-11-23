/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import Wasm.Numerics
import Wasm.Datatypes
import Wasm.Common
import Wasm.ListExtra

/-! Port of `theories/operations.v`: basic operations over Wasm datatypes. -/

namespace Wasm

#rocq_ignore iriswasm.b2p "eqType reflection; Lean uses DecidableEq directly"
#rocq_ignore iriswasm.cat_app "ssreflect cat is List.append in Lean"

/-- Read `len` bytes from `m` starting at `startIdx`. -/
@[rocq_alias iriswasm.read_bytes]
def readBytes (m : Memory) (startIdx : Nat) (len : Nat) : Option Bytes :=
  those ((List.range len).map fun off => m.data.memLookup (startIdx + off))

/-- Write bytes `bs` to `m` starting at `startIdx`. -/
@[rocq_alias iriswasm.write_bytes]
def writeBytes (m : Memory) (startIdx : Nat) (bs : Bytes) : Option Memory :=
  let x := foldLefti
    (fun off datO b => match datO with
      | none => none
      | some dat => dat.memUpdate (startIdx + off) b)
    bs (some m.data)
  match x with
  | some dat => some { m with data := dat }
  | none => none

@[rocq_alias iriswasm.upd_s_mem]
def updSMem (s : StoreRecord) (m : List Memory) : StoreRecord :=
  { funcs := s.funcs, tables := s.tables, mems := m, globals := s.globals }

#rocq_ignore iriswasm.page_limit "Use AddrType.pageLimit for the selected memory's width"

@[rocq_alias iriswasm.ml_valid]
def MlValid (m : MemoryList) : Prop := m.lengthMem % pageSize = 0

@[rocq_alias iriswasm.operations.length_mem]
def lengthMem (m : Memory) : Nat := m.data.lengthMem

@[rocq_alias iriswasm.mem_size]
def memSize (m : Memory) : Nat := lengthMem m / pageSize

/-- The authoritative extent includes the stored minimum even on malformed raw instances. -/
abbrev memLengthMeta (m : Memory) : AddrType × Nat × Nat :=
  (m.type.address, lengthMem m, m.type.limits.min)

/-- A typed extent token additionally agrees with the minimum implied by its byte length. -/
abbrev memLengthToken (p : AddrType × Nat) : AddrType × Nat × Nat := (p.1, p.2, p.2 / pageSize)

/-- A typed byte extent consists of whole pages and does not exceed the width's Core limit. -/
def WellSized (aw : AddrType) (n : Nat) : Prop :=
  n % pageSize = 0 ∧ n / pageSize ≤ aw.pageLimit

theorem WellSized.pages_mul {aw n} (h : WellSized aw n) : n = n / pageSize * pageSize := by
  have hdiv := Nat.mod_add_div n pageSize
  simpa [h.1, Nat.mul_comm] using hdiv.symm

theorem WellSized.pages_fit {aw n} (h : WellSized aw n) : n / pageSize < 2^aw.width :=
  Nat.lt_of_le_of_lt h.2 aw.pageLimit_lt_capacity

theorem WellSized.grow {aw n delta} (h : WellSized aw n)
    (hb : n / pageSize + delta ≤ aw.pageLimit) : WellSized aw (n + delta * pageSize) := by
  unfold WellSized at *
  simp [Nat.add_mod, Nat.add_mul_div_right, pageSize] at *
  omega

/-- Grow the memory by `lenDelta` pages. -/
def memGrow (m : Memory) (lenDelta : Nat) : Option Memory :=
  let newSize := memSize m + lenDelta
  if newSize ≤ m.type.address.pageLimit && m.type.limits.max.all (newSize ≤ ·) then
    some { data := m.data.memGrow (lenDelta * pageSize)
           type := {m.type with limits := {m.type.limits with min := newSize}} }
  else none

@[rocq_alias iriswasm.load]
def load (m : Memory) (n : Nat) (off : StaticOffset) (l : Nat) : Option Bytes :=
  if n + (off + l) ≤ lengthMem m then readBytes m (n + off) l else none

/-- Extend the most significant byte of a little-endian packed integer to `len` bytes. -/
def signExtend (sx : Sx) (len : Nat) (bs : Bytes) : Bytes :=
  let pad := if sx == .s && (bs.getLast?.getD 0).msb then 0xff else 0
  bytesTakefill pad len bs

@[rocq_alias iriswasm.load_packed]
def loadPacked (sx : Sx) (m : Memory) (n : Nat) (off : StaticOffset) (lp : Nat) (l : Nat) :
    Option Bytes :=
  (load m n off lp).map (signExtend sx l)

@[rocq_alias iriswasm.store]
def store (m : Memory) (n : Nat) (off : StaticOffset) (bs : Bytes) (l : Nat) : Option Memory :=
  if n + off + l ≤ lengthMem m then writeBytes m (n + off) (bytesTakefill 0 l bs) else none

@[rocq_alias iriswasm.store_packed]
abbrev storePacked := store

@[rocq_alias iriswasm.wasm_deserialise]
def wasmDeserialise (bs : Bytes) (vt : ValueType) : Value :=
  match vt with
  | .i32 => .int32 (BitVec.ofInt 32 (decodeInt bs))
  | .i64 => .int64 (BitVec.ofInt 64 (decodeInt bs))
  | .f32 => .float32 ⟨BitVec.ofInt 32 (decodeInt bs)⟩
  | .f64 => .float64 ⟨BitVec.ofInt 64 (decodeInt bs)⟩
  | .v128 => .vec128 (BitVec.ofInt 128 (decodeInt bs))

@[rocq_alias iriswasm.typeof]
def typeof (v : Value) : ValueType :=
  match v with
  | .int32 _ => .i32
  | .int64 _ => .i64
  | .float32 _ => .f32
  | .float64 _ => .f64
  | .vec128 _ => .v128

@[simp] theorem AddrType.typeof_natValue (aw : AddrType) (n : Nat) :
    typeof (aw.natValue n) = aw.valueType := by cases aw <;> rfl

@[simp] theorem AddressOperand.typeof_value (a : AddressOperand) :
    typeof a.value = a.address.valueType := by cases a <;> rfl

theorem AddressOperand.exists_of_type {v : Value} {aw : AddrType} (h : typeof v = aw.valueType) :
    ∃ a : AddressOperand, a.value = v ∧ a.address = aw := by
  cases aw <;> cases v <;> simp_all [typeof, AddrType.valueType]
  · exact ⟨.i32 _, rfl, rfl⟩
  · exact ⟨.i64 _, rfl, rfl⟩

@[rocq_alias iriswasm.option_projl]
def optionProjl {A B : Type} (x : Option (A × B)) : Option A := x.map Prod.fst

@[rocq_alias iriswasm.option_projr]
def optionProjr {A B : Type} (x : Option (A × B)) : Option B := x.map Prod.snd

@[rocq_alias iriswasm.length_t]
def lengthT (t : ValueType) : Nat :=
  match t with
  | .i32 => 4
  | .i64 => 8
  | .f32 => 4
  | .f64 => 8
  | .v128 => 16

@[rocq_alias iriswasm.length_tp]
def lengthTp (tp : PackedType) : Nat :=
  match tp with
  | .i8 => 1
  | .i16 => 2
  | .i32 => 4

@[rocq_alias iriswasm.is_int_t]
def isIntT (t : ValueType) : Bool :=
  match t with
  | .i32 | .i64 => true
  | _ => false

@[rocq_alias iriswasm.is_float_t]
def isFloatT (t : ValueType) : Bool :=
  match t with
  | .i32 | .i64 | .v128 => false
  | .f32 | .f64 => true

@[rocq_alias iriswasm.is_mut]
def isMut (tg : GlobalType) : Bool := tg.mut_ == .mut

@[rocq_alias iriswasm.app_unop_i]
def appUnopI {w : Nat} (iop : UnopI) : BitVec w → BitVec w :=
  match iop with
  | .ctz => Int.ictz
  | .clz => Int.iclz
  | .popcnt => Int.ipopcnt

@[rocq_alias iriswasm.app_unop_f]
def appUnopF {α : Type} [Float.MixinOf α] (fop : UnopF) : α → α :=
  match fop with
  | .neg => Float.MixinOf.neg
  | .abs => Float.MixinOf.abs
  | .ceil => Float.MixinOf.ceil
  | .floor => Float.MixinOf.floor
  | .trunc => Float.MixinOf.trunc
  | .nearest => Float.MixinOf.nearest
  | .sqrt => Float.MixinOf.sqrt

def unopTypeOK (t : ValueType) : Unop → Bool
  | .i _ => isIntT t
  | .f _ => isFloatT t
  | .extendS p => isIntT t && decide (lengthTp p < lengthT t)
  | .vnot => t == .v128

@[rocq_alias iriswasm.app_unop]
def appUnop (op : Unop) (v : Value) : Value :=
  match op, v with
  | .i iop, .int32 c => .int32 (appUnopI iop c)
  | .i iop, .int64 c => .int64 (appUnopI iop c)
  | .f fop, .float32 c => .float32 (appUnopF fop c)
  | .f fop, .float64 c => .float64 (appUnopF fop c)
  | .extendS p, .int32 c => .int32 ((c.setWidth (8 * lengthTp p)).signExtend 32)
  | .extendS p, .int64 c => .int64 ((c.setWidth (8 * lengthTp p)).signExtend 64)
  | .vnot, .vec128 x => .vec128 (~~~x)
  | _, _ => v

@[rocq_alias iriswasm.app_binop_i]
def appBinopI {w : Nat} (iop : BinopI) : BitVec w → BitVec w → Option (BitVec w) :=
  let addSome := fun (f : BitVec w → BitVec w → BitVec w) c1 c2 => some (f c1 c2)
  match iop with
  | .add => addSome Int.iadd
  | .sub => addSome Int.isub
  | .mul => addSome Int.imul
  | .div .u => Int.idivU
  | .div .s => Int.idivS
  | .rem .u => Int.iremU
  | .rem .s => Int.iremS
  | .and => addSome Int.iand
  | .or => addSome Int.ior
  | .xor => addSome Int.ixor
  | .shl => addSome Int.ishl
  | .shr .u => addSome Int.ishrU
  | .shr .s => addSome Int.ishrS
  | .rotl => addSome Int.irotl
  | .rotr => addSome Int.irotr

@[rocq_alias iriswasm.app_binop_f]
def appBinopF {α : Type} [Float.MixinOf α] (fop : BinopF) : α → α → Option α :=
  let addSome := fun (f : α → α → α) c1 c2 => some (f c1 c2)
  match fop with
  | .add => addSome Float.MixinOf.add
  | .sub => addSome Float.MixinOf.sub
  | .mul => addSome Float.MixinOf.mul
  | .div => addSome Float.MixinOf.div
  | .min => addSome Float.MixinOf.min
  | .max => addSome Float.MixinOf.max
  | .copysign => addSome Float.MixinOf.copysign

def vbitselect (x y mask : BitVec 128) : BitVec 128 := (x &&& mask) ||| (y &&& (~~~mask))

def appVecBinop (op : VecBinop) (x y : BitVec 128) : BitVec 128 :=
  match op with
  | .and => x &&& y
  | .andNot => x &&& (~~~y)
  | .or => x ||| y
  | .xor => x ^^^ y

def binopTypeOK (t : ValueType) : Binop → Bool
  | .i _ => isIntT t
  | .f _ => isFloatT t
  | .v _ => t == .v128

@[rocq_alias iriswasm.app_binop]
def appBinop (op : Binop) (v1 v2 : Value) : Option Value :=
  match op, v1, v2 with
  | .i iop, .int32 c1, .int32 c2 => (appBinopI iop c1 c2).map .int32
  | .i iop, .int64 c1, .int64 c2 => (appBinopI iop c1 c2).map .int64
  | .f fop, .float32 c1, .float32 c2 => (appBinopF fop c1 c2).map .float32
  | .f fop, .float64 c1, .float64 c2 => (appBinopF fop c1 c2).map .float64
  | .v vop, .vec128 x, .vec128 y => some (.vec128 (appVecBinop vop x y))
  | _, _, _ => none

def testopTypeOK (t : ValueType) : Testop → Bool
  | .eqz => isIntT t
  | .anyTrue => t == .v128

@[rocq_alias iriswasm.app_relop_i]
def appRelopI {w : Nat} (rop : RelopI) : BitVec w → BitVec w → Bool :=
  match rop with
  | .eq => Int.ieq
  | .ne => Int.ine
  | .lt .u => Int.iltU
  | .lt .s => Int.iltS
  | .gt .u => Int.igtU
  | .gt .s => Int.igtS
  | .le .u => Int.ileU
  | .le .s => Int.ileS
  | .ge .u => Int.igeU
  | .ge .s => Int.igeS

@[rocq_alias iriswasm.app_relop_f]
def appRelopF {α : Type} [Float.MixinOf α] (rop : RelopF) : α → α → Bool :=
  match rop with
  | .eq => Float.MixinOf.eq
  | .ne => Float.ne
  | .lt => Float.MixinOf.lt
  | .gt => Float.MixinOf.gt
  | .le => Float.MixinOf.le
  | .ge => Float.MixinOf.ge

def relopTypeOK (t : ValueType) : Relop → Bool
  | .i _ => isIntT t
  | .f _ => isFloatT t

@[rocq_alias iriswasm.app_relop]
def appRelop (op : Relop) (v1 v2 : Value) : Bool :=
  match op, v1, v2 with
  | .i iop, .int32 c1, .int32 c2 => appRelopI iop c1 c2
  | .i iop, .int64 c1, .int64 c2 => appRelopI iop c1 c2
  | .f fop, .float32 c1, .float32 c2 => appRelopF fop c1 c2
  | .f fop, .float64 c1, .float64 c2 => appRelopF fop c1 c2
  | _, _, _ => false

@[rocq_alias iriswasm.types_agree]
def typesAgree (t : ValueType) (v : Value) : Bool := typeof v == t

@[rocq_alias iriswasm.cl_type]
def clType (cl : FunctionClosure) : FunctionType :=
  match cl with
  | .funcNative _ tf _ _ => tf
  | .funcHost tf _ => tf

@[rocq_alias iriswasm.rglob_is_mut]
def rglobIsMut (g : Global) : Bool := g.mut_ == .mut

@[rocq_alias iriswasm.option_bind]
def optionBind {A B : Type} (f : A → Option B) (x : Option A) : Option B :=
  match x with
  | none => none
  | some y => f y

@[rocq_alias iriswasm.empty_instance]
def emptyInstance : Instance := ⟨[], [], [], [], []⟩

@[rocq_alias iriswasm.stypes]
def stypes (_s : StoreRecord) (i : Instance) (j : Nat) : Option FunctionType := i.types[j]?

@[rocq_alias iriswasm.sfunc_ind]
def sfuncInd (_s : StoreRecord) (i : Instance) (j : Nat) : Option Nat := i.funcs[j]?

@[rocq_alias iriswasm.sfunc]
def sfunc (s : StoreRecord) (i : Instance) (j : Nat) : Option FunctionClosure :=
  optionBind (fun k => s.funcs[k]?) (sfuncInd s i j)

@[rocq_alias iriswasm.sglob_ind]
def sglobInd (_s : StoreRecord) (i : Instance) (j : Nat) : Option Nat := i.globs[j]?

@[rocq_alias iriswasm.sglob]
def sglob (s : StoreRecord) (i : Instance) (j : Nat) : Option Global :=
  optionBind (fun k => s.globals[k]?) (sglobInd s i j)

@[rocq_alias iriswasm.sglob_val]
def sglobVal (s : StoreRecord) (i : Instance) (j : Nat) : Option Value :=
  (sglob s i j).map Global.val

@[rocq_alias iriswasm.tab_size]
def tabSize (t : Tableinst) : Nat := t.entries.size

/-- The `j`th entry of the `i`th table of the store. -/
@[rocq_alias iriswasm.stab_index]
def stabIndex (s : StoreRecord) (i j : Nat) : Option Nat :=
  optionBind (fun x => x) (optionBind (fun stabI => stabI.entries.get? j) s.tables[i]?)

@[rocq_alias iriswasm.stab_addr]
def stabAddr (s : StoreRecord) (f : Frame) (c : Nat) : Option Nat :=
  match f.inst.tab with
  | [] => none
  | ta :: _ => stabIndex s ta c

@[rocq_alias iriswasm.stab_s]
def stabS (s : StoreRecord) (i j : Nat) : Option FunctionClosure :=
  optionBind (fun id => s.funcs[id]?) (stabIndex s i j)

@[rocq_alias iriswasm.stab]
def stab (s : StoreRecord) (i : Instance) (j : Nat) : Option FunctionClosure :=
  match i.tab with
  | [] => none
  | k :: _ => stabS s k j

@[rocq_alias iriswasm.update_list_at]
def updateListAt {A : Type} (l : List A) (k : Nat) (a : A) : List A :=
  l.take k ++ [a] ++ l.drop (k + 1)

@[rocq_alias iriswasm.supdate_glob_s]
def supdateGlobS (s : StoreRecord) (k : Nat) (v : Value) : Option StoreRecord :=
  s.globals[k]?.map fun g =>
    ⟨s.funcs, s.tables, s.mems, updateListAt s.globals k ⟨g.mut_, v⟩⟩

@[rocq_alias iriswasm.supdate_glob]
def supdateGlob (s : StoreRecord) (i : Instance) (j : Nat) (v : Value) : Option StoreRecord :=
  optionBind (fun k => supdateGlobS s k v) (sglobInd s i j)

@[rocq_alias iriswasm.is_const]
def isConst (e : AdministrativeInstruction) : Bool :=
  match e with
  | .basic (.const _) => true
  | _ => false

@[rocq_alias iriswasm.const_list]
def constList (es : List AdministrativeInstruction) : Bool := es.all isConst

@[rocq_alias iriswasm.those_const_list]
def thoseConstList (es : List AdministrativeInstruction) : Option (List Value) :=
  those (es.map fun e => match e with
    | .basic (.const v) => some v
    | _ => none)

@[rocq_alias iriswasm.glob_extension]
def globExtension (g1 g2 : Global) : Bool :=
  match g1.mut_, g2.mut_ with
  | .immut, _ => g2.mut_ == .immut && g1.val == g2.val
  | .mut, .immut => false
  | .mut, .mut => typeof g1.val == typeof g2.val

@[rocq_alias iriswasm.tab_extension]
def tabExtension (t1 t2 : Tableinst) : Bool :=
  decide (tabSize t1 ≤ tabSize t2) && t1.maxOpt == t2.maxOpt

@[rocq_alias iriswasm.mem_extension]
def memExtension (m1 m2 : Memory) : Bool :=
  m1.type.address == m2.type.address && m1.type.limits.max == m2.type.limits.max &&
    decide (m1.type.limits.min ≤ m2.type.limits.min) && decide (lengthMem m1 ≤ lengthMem m2)

@[rocq_alias iriswasm.store_extension]
def storeExtension (s s' : StoreRecord) : Bool :=
  decide (s.funcs = s'.funcs) &&
  List.all2 tabExtension s.tables s'.tables &&
  List.all2 memExtension s.mems s'.mems &&
  List.all2 globExtension s.globals s'.globals

@[rocq_alias iriswasm.vs_to_vts]
def vsToVts (vs : List Value) : List ValueType := vs.map typeof

@[rocq_alias iriswasm.to_e_list]
def toEList (bes : List BasicInstruction) : List AdministrativeInstruction := bes.map .basic

@[rocq_alias iriswasm.to_b_single]
def toBSingle (e : AdministrativeInstruction) : BasicInstruction :=
  match e with
  | .basic x => x
  | _ => .const (.int32 Int.zero)

@[rocq_alias iriswasm.to_b_list]
def toBList (es : List AdministrativeInstruction) : List BasicInstruction := es.map toBSingle

@[rocq_alias iriswasm.e_is_basic]
def EIsBasic (e : AdministrativeInstruction) : Prop := ∃ be, e = .basic be

@[rocq_alias iriswasm.es_is_basic]
def EsIsBasic : List AdministrativeInstruction → Prop
  | [] => True
  | e :: es' => EIsBasic e ∧ EsIsBasic es'

/-- Maps each value `v` to `.basic (.const v)`. -/
@[rocq_alias iriswasm.v_to_e_list]
def vToEList (ves : List Value) : List AdministrativeInstruction :=
  ves.map fun v => .basic (.const v)

@[rocq_alias iriswasm.split_vals]
def splitVals : List BasicInstruction → List Value × List BasicInstruction
  | .const v :: es' => let (vs', es'') := splitVals es'; (v :: vs', es'')
  | es => ([], es)

/-- Splits off the maximal prefix of constants. -/
@[rocq_alias iriswasm.split_vals_e]
def splitValsE : List AdministrativeInstruction → List Value × List AdministrativeInstruction
  | .basic (.const v) :: es' => let (vs', es'') := splitValsE es'; (v :: vs', es'')
  | es => ([], es)

@[rocq_alias iriswasm.split_vals_not_empty_res]
theorem split_vals_not_empty_res (es : List AdministrativeInstruction) (v : Value)
    (vs : List Value) (es' : List AdministrativeInstruction) :
    splitValsE es = (v :: vs, es') → es ≠ [] := by
  rintro h rfl; simp [splitValsE] at h

@[rocq_alias iriswasm.split_vals_e_not_const]
theorem split_vals_e_not_const (es : List AdministrativeInstruction) (vs : List Value)
    (e : AdministrativeInstruction) (es' : List AdministrativeInstruction) :
    splitValsE es = (vs, e :: es') → isConst e = true → False := by
  induction es generalizing vs with
  | nil => simp [splitValsE]
  | cons a es ih =>
    intro h hc
    have nonconst (h₁ : isConst a = false) (h₂ : splitValsE (a :: es) = ([], a :: es)) : False := by
      simp only [h₂, Prod.mk.injEq, List.cons.injEq] at h
      obtain ⟨-, rfl, -⟩ := h
      simp_all
    cases a with
    | basic b =>
      cases b <;> first
        | exact nonconst rfl rfl
        | (simp only [splitValsE] at h; exact ih _ (by rw [← (Prod.mk.inj h).2]) hc)
    | _ => exact nonconst rfl rfl

@[rocq_alias iriswasm.split_n]
def splitN : List Value → Nat → List Value × List Value
  | [], _ => ([], [])
  | es, 0 => ([], es)
  | e :: esX, n + 1 => let (es', es'') := splitN esX n; (e :: es', es'')

@[rocq_alias iriswasm.expect]
def expect {A B : Type} (ao : Option A) (f : A → B) (b : B) : B :=
  match ao with
  | some a => f a
  | none => b

@[rocq_alias iriswasm.vs_to_es]
def vsToEs (vs : List Value) : List AdministrativeInstruction := vToEList vs.reverse

@[rocq_alias iriswasm.e_is_trap]
def eIsTrap (e : AdministrativeInstruction) : Bool :=
  match e with
  | .trap => true
  | _ => false

/-- Equivalent to `es == [.trap]`. -/
@[rocq_alias iriswasm.es_is_trap]
def esIsTrap (es : List AdministrativeInstruction) : Bool :=
  match es with
  | [e] => eIsTrap e
  | _ => false

@[rocq_alias iriswasm.result_to_stack]
def resultToStack (r : Result) : List AdministrativeInstruction :=
  match r with
  | .values vs => vToEList vs
  | .trap => [.trap]

@[rocq_alias iriswasm.lfill]
def lfill : Nat → Lholed → List AdministrativeInstruction → Option (List AdministrativeInstruction)
  | 0, .base vs es', es => if constList vs then some (vs ++ (es ++ es')) else none
  | k' + 1, .rec_ vs n es' lh' es'', es =>
    if constList vs then
      match lfill k' lh' es with
      | some lfilledk => some (vs ++ (.label n es' lfilledk :: es''))
      | none => none
    else none
  | _, _, _ => none

@[rocq_alias iriswasm.lfilled]
def lfilled (k : Nat) (lh : Lholed) (es es' : List AdministrativeInstruction) : Bool :=
  match lfill k lh es with
  | some es'' => es' == es''
  | none => false

@[rocq_alias iriswasm.lfilledInd]
inductive LfilledInd :
    Nat → Lholed → List AdministrativeInstruction → List AdministrativeInstruction → Prop where
  | lfilledBase (vs es es' : List AdministrativeInstruction) :
    constList vs = true → LfilledInd 0 (.base vs es') es (vs ++ es ++ es')
  | lfilledRec (k : Nat) (vs : List AdministrativeInstruction) (n : Nat)
      (es' : List AdministrativeInstruction) (lh' : Lholed) (es'' es LI : List AdministrativeInstruction) :
    constList vs = true → LfilledInd k lh' es LI →
    LfilledInd (k + 1) (.rec_ vs n es' lh' es'') es (vs ++ [.label n es' LI] ++ es'')

@[rocq_alias iriswasm.lfilled_Ind_Equivalent]
theorem lfilled_Ind_Equivalent (k : Nat) (lh : Lholed) (es LI : List AdministrativeInstruction) :
    lfilled k lh es LI = true ↔ LfilledInd k lh es LI := by
  constructor
  · induction k generalizing lh LI with
    | zero =>
      cases lh with
      | base vs es' =>
        intro h
        simp only [lfilled, lfill] at h
        split at h <;> rename_i h' <;> split at h' <;> simp_all
        subst h'; rw [← List.append_assoc]; exact .lfilledBase _ _ _ ‹_›
      | rec_ => simp [lfilled, lfill]
    | succ k ih =>
      cases lh with
      | base => simp [lfilled, lfill]
      | rec_ vs n es' lh' es'' =>
        intro h
        simp only [lfilled, lfill] at h
        split at h <;> rename_i h'
        · split at h' <;> rename_i hc
          · split at h' <;> rename_i lk heq
            · simp at h' h; subst h' h
              have := LfilledInd.lfilledRec _ _ n es' _ es'' _ _ hc
                (ih lh' lk (by simp [lfilled, heq]))
              simpa using this
            · simp at h'
          · simp at h'
        · simp at h
  · intro h
    induction h with
    | lfilledBase vs es es' hc => simp [lfilled, lfill, hc]
    | lfilledRec k vs n es' lh' es'' es LI hc _ ih =>
      simp only [lfilled] at ih
      split at ih <;> simp_all [lfilled, lfill]

#rocq_ignore iriswasm.lfilledP "reflect; use lfilled_Ind_Equivalent"

@[rocq_alias iriswasm.lfill_exact]
def lfillExact :
    Nat → Lholed → List AdministrativeInstruction → Option (List AdministrativeInstruction)
  | 0, .base [] [], es => some es
  | k' + 1, .rec_ vs n es' lh' es'', es =>
    if constList vs then
      match lfillExact k' lh' es with
      | some lfilledk => some (vs ++ (.label n es' lfilledk :: es''))
      | none => none
    else none
  | _, _, _ => none

@[rocq_alias iriswasm.lfilled_exact]
def lfilledExact (k : Nat) (lh : Lholed) (es es' : List AdministrativeInstruction) : Bool :=
  match lfillExact k lh es with
  | some es'' => es' == es''
  | none => false

@[rocq_alias iriswasm.lh_depth]
def lhDepth : Lholed → Nat
  | .base _ _ => 0
  | .rec_ _ _ _ lh _ => lhDepth lh + 1

@[rocq_alias iriswasm.result_types_agree]
def resultTypesAgree (ts : ResultType) (r : Result) : Bool :=
  match r with
  | .values vs => List.all2 typesAgree ts vs
  | .trap => true

/-- Scalar packed accesses extend or truncate an integer of strictly greater width. -/
def packedTypeOK (tp : PackedType) (t : ValueType) : Bool :=
  isIntT t && decide (lengthTp tp < lengthT t)

@[rocq_alias iriswasm.load_store_t_bounds]
def loadStoreTBounds (a : AlignmentExponent) (tp : Option PackedType) (t : ValueType) : Bool :=
  match tp with
  | none => decide (2 ^ a ≤ lengthT t)
  | some tp' => decide (2 ^ a ≤ lengthTp tp') && packedTypeOK tp' t

theorem packedTypeOK_of_bounds {a tp t} (h : loadStoreTBounds a (some tp) t = true) :
    packedTypeOK tp t = true := by
  simp only [loadStoreTBounds, Bool.and_eq_true] at h
  exact h.2

@[rocq_alias iriswasm.convert_helper]
def convertHelper (sxo : Option Sx) (t1 t2 : ValueType) : Bool :=
  t1 != .v128 && t2 != .v128 && ((sxo == none) ==
    ((isFloatT t1 && isFloatT t2) || (isIntT t1 && isIntT t2 && decide (lengthT t1 < lengthT t2))))

@[rocq_alias iriswasm.convert_cond]
def convertCond (t1 t2 : ValueType) (sxo : Option Sx) : Bool :=
  t1 != t2 && convertHelper sxo t1 t2

def reinterpretCond (dst src : ValueType) : Bool :=
  dst != src && lengthT dst == lengthT src

def cvtI32 (s : Option Sx) (v : Value) : Option I32 :=
  match v with
  | .int32 _ | .vec128 _ => none
  | .int64 c => some (wasmWrap c)
  | .float32 c => match s with
    | some .u => Float.MixinOf.ui32Trunc c
    | some .s => Float.MixinOf.si32Trunc c
    | none => none
  | .float64 c => match s with
    | some .u => Float.MixinOf.ui32Trunc c
    | some .s => Float.MixinOf.si32Trunc c
    | none => none

@[rocq_alias iriswasm.cvt_i64]
def cvtI64 (s : Option Sx) (v : Value) : Option I64 :=
  match v with
  | .int32 c => match s with
    | some .u => some (wasmExtendU c)
    | some .s => some (wasmExtendS c)
    | none => none
  | .int64 _ | .vec128 _ => none
  | .float32 c => match s with
    | some .u => Float.MixinOf.ui64Trunc c
    | some .s => Float.MixinOf.si64Trunc c
    | none => none
  | .float64 c => match s with
    | some .u => Float.MixinOf.ui64Trunc c
    | some .s => Float.MixinOf.si64Trunc c
    | none => none

@[rocq_alias iriswasm.cvt_f32]
def cvtF32 (s : Option Sx) (v : Value) : Option F32 :=
  match v with
  | .int32 c => match s with
    | some .u => some (Float.MixinOf.convertUi32 c)
    | some .s => some (Float.MixinOf.convertSi32 c)
    | none => none
  | .int64 c => match s with
    | some .u => some (Float.MixinOf.convertUi64 c)
    | some .s => some (Float.MixinOf.convertSi64 c)
    | none => none
  | .float32 _ | .vec128 _ => none
  | .float64 c => some (wasmDemote c)

@[rocq_alias iriswasm.cvt_f64]
def cvtF64 (s : Option Sx) (v : Value) : Option F64 :=
  match v with
  | .int32 c => match s with
    | some .u => some (Float.MixinOf.convertUi32 c)
    | some .s => some (Float.MixinOf.convertSi32 c)
    | none => none
  | .int64 c => match s with
    | some .u => some (Float.MixinOf.convertUi64 c)
    | some .s => some (Float.MixinOf.convertSi64 c)
    | none => none
  | .float32 c => some (wasmPromote c)
  | .float64 _ | .vec128 _ => none

@[rocq_alias iriswasm.cvt]
def cvt (t : ValueType) (s : Option Sx) (v : Value) : Option Value :=
  match t with
  | .i32 => (cvtI32 s v).map .int32
  | .i64 => (cvtI64 s v).map .int64
  | .f32 => (cvtF32 s v).map .float32
  | .v128 => none
  | .f64 => (cvtF64 s v).map .float64

/-- A saturating conversion is defined only for an integer target and a float operand.
Unlike `cvt`, `none` means an ill-shaped instruction, never a numeric trap. -/
def truncSat (dst : ValueType) (sx : Sx) (v : Value) : Option Value :=
  match dst, v with
  | .i32, .float32 x => some (.int32 (IEEE.Format.f32.truncSat (sx == .s) 32 x.bits))
  | .i32, .float64 x => some (.int32 (IEEE.Format.f64.truncSat (sx == .s) 32 x.bits))
  | .i64, .float32 x => some (.int64 (IEEE.Format.f32.truncSat (sx == .s) 64 x.bits))
  | .i64, .float64 x => some (.int64 (IEEE.Format.f64.truncSat (sx == .s) 64 x.bits))
  | _, _ => none

theorem truncSat_total {dst : ValueType} {v : Value} (sx : Sx)
    (hd : isIntT dst = true) (hs : isFloatT (typeof v) = true) :
    ∃ w, truncSat dst sx v = some w := by
  cases dst <;> cases v <;> simp_all [isIntT, isFloatT, typeof, truncSat]

theorem truncSat_typeof {dst : ValueType} {sx : Sx} {v w : Value}
    (h : truncSat dst sx v = some w) : typeof w = dst := by
  cases dst <;> cases v <;> simp [truncSat] at h <;> subst w <;> rfl

@[rocq_alias iriswasm.bits]
def bits (v : Value) : Bytes :=
  match v with
  | .int32 c => serialiseI32 c
  | .int64 c => serialiseI64 c
  | .float32 c => serialiseF32 c
  | .float64 c => serialiseF64 c
  | .vec128 c => encodeInt 16 c.toNat

@[rocq_alias iriswasm.bitzero]
def bitzero (t : ValueType) : Value :=
  match t with
  | .i32 => .int32 Int.zero
  | .i64 => .int64 Int.zero
  | .f32 => .float32 Float.MixinOf.zero
  | .f64 => .float64 Float.MixinOf.zero
  | .v128 => .vec128 0

@[rocq_alias iriswasm.n_zeros]
def nZeros (ts : List ValueType) : List Value := ts.map bitzero

@[rocq_alias iriswasm.is_none_or]
def isNoneOr {A : Type} (p : A → Bool) (x : Option A) : Bool :=
  match x with
  | none => true
  | some y => p y

@[rocq_alias iriswasm.first_values]
theorem first_values (vs1 : List AdministrativeInstruction) (e1 : AdministrativeInstruction)
    (es1 vs2 : List AdministrativeInstruction) (e2 : AdministrativeInstruction)
    (es2 : List AdministrativeInstruction) :
    isConst e1 = false → isConst e2 = false → constList vs1 = true → constList vs2 = true →
    vs1 ++ e1 :: es1 = vs2 ++ e2 :: es2 → vs1 = vs2 ∧ e1 = e2 ∧ es1 = es2 := by
  intro he1 he2 hvs1 hvs2 heq
  induction vs1 generalizing vs2 with
  | nil =>
    cases vs2 with
    | nil => simp only [List.nil_append, List.cons.injEq] at heq; exact ⟨rfl, heq⟩
    | cons b vs2 => simp_all [constList]
  | cons a vs1 ih =>
    cases vs2 with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at heq
      obtain ⟨rfl, -⟩ := heq
      simp [constList, he2] at hvs1
    | cons b vs2 =>
      simp only [List.cons_append, List.cons.injEq] at heq
      obtain ⟨rfl, heq⟩ := heq
      simp only [constList, List.all_cons, Bool.and_eq_true] at hvs1 hvs2
      have := ih vs2 hvs1.2 hvs2.2 heq
      simp_all

end Wasm
