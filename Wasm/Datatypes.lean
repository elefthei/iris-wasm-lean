/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import Wasm.Numerics
import Wasm.Bytes
import Wasm.MemoryList
import Wasm.RunTable
import Wasm.CoreTypes

/-! Port of `theories/datatypes.v`: Wasm syntax and runtime structures. -/

namespace Wasm

/-! ## Basic datatypes -/

@[rocq_alias iriswasm.depth]
abbrev Depth := Nat

@[rocq_alias iriswasm.immediate]
abbrev Immediate := Nat

@[rocq_alias iriswasm.static_offset]
abbrev StaticOffset := Nat

@[rocq_alias iriswasm.alignment_exponent]
abbrev AlignmentExponent := Nat

@[rocq_alias iriswasm.serialise_i32]
def serialiseI32 (i : I32) : Bytes := encodeInt 4 i.toNat

@[rocq_alias iriswasm.serialise_i64]
def serialiseI64 (i : I64) : Bytes := encodeInt 8 i.toNat

@[rocq_alias iriswasm.serialise_f32]
def serialiseF32 (f : F32) : Bytes := encodeInt 4 f.bits.toNat

@[rocq_alias iriswasm.serialise_f64]
def serialiseF64 (f : F64) : Bytes := encodeInt 8 f.bits.toNat

@[rocq_alias iriswasm.limits]
structure Limits where
  min : Nat
  max : Option Nat
  deriving DecidableEq, Repr, Inhabited

#rocq_ignore iriswasm.Byte_Index "array.v is not ported; data_vec is unused"
#rocq_ignore iriswasm.Byte_array "array.v is not ported; data_vec is unused"
#rocq_ignore iriswasm.data_vec "unused outside the unported interpreter"

structure MemArg where
  memory : Nat
  align : AlignmentExponent
  offset : StaticOffset
  deriving DecidableEq, Repr, Inhabited

inductive AddrType where
  | i32 | i64
  deriving DecidableEq, Repr, Inhabited

def AddrType.width : AddrType → Nat
  | .i32 => 32 | .i64 => 64

def AddrType.pageLimit (aw : AddrType) := 2 ^ (aw.width - 16)

theorem AddrType.pageLimit_lt_capacity (aw : AddrType) : aw.pageLimit < 2 ^ aw.width := by
  cases aw <;> decide

structure MemoryType where
  address : AddrType
  limits : Limits
  deriving DecidableEq, Repr, Inhabited

structure Memory where
  data : MemoryList
  type : MemoryType
  deriving DecidableEq, Repr, Inhabited

@[rocq_alias iriswasm.value_type]
inductive ValueType where
  | i32
  | i64
  | f32
  | f64
  | v128
  deriving DecidableEq, Repr, Inhabited

abbrev AddrType.valueType : AddrType → ValueType
  | .i32 => .i32 | .i64 => .i64

@[rocq_alias iriswasm.packed_type]
inductive PackedType where
  | i8
  | i16
  | i32
  deriving DecidableEq, Repr, Inhabited

@[rocq_alias iriswasm.mutability]
inductive Mutability where
  | immut
  | mut
  deriving DecidableEq, Repr, Inhabited

@[rocq_alias iriswasm.global_type]
structure GlobalType where
  mut_ : Mutability
  t : ValueType
  deriving DecidableEq, Repr, Inhabited

@[rocq_alias iriswasm.result_type]
abbrev ResultType := List ValueType

@[rocq_alias iriswasm.function_type]
inductive FunctionType where
  | tf : ResultType → ResultType → FunctionType
  deriving DecidableEq, Repr, Inhabited

abbrev BlockType := CoreTypes.BlockType ValueType

/-- Interpret the immediate in the active module. Only an indexed block can have parameters. -/
def expandBlockType (types : List FunctionType) : BlockType → Option FunctionType
  | .result v => some (.tf [] v.toList)
  | .index i => types[i]?

@[rocq_alias iriswasm.elem_type]
inductive ElemType where
  | funcref
  deriving DecidableEq, Repr, Inhabited

@[rocq_alias iriswasm.table_type]
structure TableType where
  limits : Limits
  elemType : ElemType
  deriving DecidableEq, Repr, Inhabited

/-- Typing context. -/
@[rocq_alias iriswasm.t_context]
structure TContext where
  typesT : List FunctionType
  funcT : List FunctionType
  global : List GlobalType
  table : List TableType
  memory : List MemoryType
  local_ : List ValueType
  label : List (List ValueType)
  return_ : Option (List ValueType)
  deriving DecidableEq, Repr, Inhabited

@[rocq_alias iriswasm.value]
inductive Value where
  | int32 : I32 → Value
  | int64 : I64 → Value
  | float32 : F32 → Value
  | float64 : F64 → Value
  | vec128 : BitVec 128 → Value
  deriving DecidableEq, Repr, Inhabited

abbrev AddrType.natValue (aw : AddrType) (n : Nat) : Value :=
  match aw with
  | .i32 => .int32 (Int.intOfZ n) | .i64 => .int64 (Int.intOfZ n)

/-- The two integer operand forms matched by Core memory rules. Store addresses remain `Nat`. -/
inductive AddressOperand where
  | i32 (bits : I32)
  | i64 (bits : I64)
  deriving DecidableEq, Repr

namespace AddressOperand

abbrev value : AddressOperand → Value
  | .i32 x => .int32 x | .i64 x => .int64 x

def ofValue? : Value → Option AddressOperand
  | .int32 x => some (.i32 x) | .int64 x => some (.i64 x) | _ => none

abbrev unsigned : AddressOperand → Nat
  | .i32 x => x.toNat | .i64 x => x.toNat

abbrev address : AddressOperand → AddrType
  | .i32 _ => .i32 | .i64 _ => .i64

abbrev result (a : AddressOperand) (pages : Nat) : Value := a.address.natValue pages

abbrev failure : AddressOperand → Value
  | .i32 _ => .int32 Int.mone | .i64 _ => .int64 Int.mone

@[simp] theorem value_inj {a b : AddressOperand} : a.value = b.value ↔ a = b := by
  cases a <;> cases b <;> simp [value]

@[simp] theorem ofValue?_value (a : AddressOperand) : ofValue? a.value = some a := by cases a <;> rfl

theorem ofValue?_eq_some {v : Value} {a : AddressOperand} : ofValue? v = some a ↔ v = a.value := by
  cases v <;> cases a <;> simp [ofValue?, value]

end AddressOperand

@[rocq_alias iriswasm.result]
inductive Result where
  | values : List Value → Result
  | trap : Result
  deriving DecidableEq, Repr, Inhabited

/-! ## Basic instructions -/

@[rocq_alias iriswasm.sx]
inductive Sx where
  | s
  | u
  deriving DecidableEq, Repr, Inhabited

@[rocq_alias iriswasm.unop_i]
inductive UnopI where
  | clz
  | ctz
  | popcnt
  deriving DecidableEq, Repr, Inhabited

@[rocq_alias iriswasm.unop_f]
inductive UnopF where
  | neg
  | abs
  | ceil
  | floor
  | trunc
  | nearest
  | sqrt
  deriving DecidableEq, Repr, Inhabited

@[rocq_alias iriswasm.unop]
inductive Unop where
  | i : UnopI → Unop
  | f : UnopF → Unop
  | extendS : PackedType → Unop
  | vnot
  deriving DecidableEq, Repr, Inhabited

@[rocq_alias iriswasm.binop_i]
inductive BinopI where
  | add
  | sub
  | mul
  | div : Sx → BinopI
  | rem : Sx → BinopI
  | and
  | or
  | xor
  | shl
  | shr : Sx → BinopI
  | rotl
  | rotr
  deriving DecidableEq, Repr, Inhabited

@[rocq_alias iriswasm.binop_f]
inductive BinopF where
  | add
  | sub
  | mul
  | div
  | min
  | max
  | copysign
  deriving DecidableEq, Repr, Inhabited

inductive VecBinop where
  | and | andNot | or | xor
  deriving DecidableEq, Repr, Inhabited

@[rocq_alias iriswasm.binop]
inductive Binop where
  | i : BinopI → Binop
  | f : BinopF → Binop
  | v : VecBinop → Binop
  deriving DecidableEq, Repr, Inhabited

inductive Testop where
  | eqz
  | anyTrue
  deriving DecidableEq, Repr, Inhabited

@[rocq_alias iriswasm.relop_i]
inductive RelopI where
  | eq
  | ne
  | lt : Sx → RelopI
  | gt : Sx → RelopI
  | le : Sx → RelopI
  | ge : Sx → RelopI
  deriving DecidableEq, Repr, Inhabited

@[rocq_alias iriswasm.relop_f]
inductive RelopF where
  | eq
  | ne
  | lt
  | gt
  | le
  | ge
  deriving DecidableEq, Repr, Inhabited

@[rocq_alias iriswasm.relop]
inductive Relop where
  | i : RelopI → Relop
  | f : RelopF → Relop
  deriving DecidableEq, Repr, Inhabited

@[rocq_alias iriswasm.cvtop]
inductive Cvtop where
  | convert
  | reinterpret
  | truncSat
  deriving DecidableEq, Repr, Inhabited

@[rocq_alias iriswasm.basic_instruction]
inductive BasicInstruction where
  | unreachable
  | nop
  | drop
  | select
  | vbitselect
  | block : BlockType → List BasicInstruction → BasicInstruction
  | loop : BlockType → List BasicInstruction → BasicInstruction
  | if_ : BlockType → List BasicInstruction → List BasicInstruction → BasicInstruction
  | br : Immediate → BasicInstruction
  | brIf : Immediate → BasicInstruction
  | brTable : List Immediate → Immediate → BasicInstruction
  | return_
  | call : Immediate → BasicInstruction
  | callIndirect : Immediate → BasicInstruction
  | getLocal : Immediate → BasicInstruction
  | setLocal : Immediate → BasicInstruction
  | teeLocal : Immediate → BasicInstruction
  | getGlobal : Immediate → BasicInstruction
  | setGlobal : Immediate → BasicInstruction
  | load : ValueType → Option (PackedType × Sx) → MemArg → BasicInstruction
  | store : ValueType → Option PackedType → MemArg → BasicInstruction
  | currentMemory : Immediate → BasicInstruction
  | growMemory : Immediate → BasicInstruction
  | const : Value → BasicInstruction
  | unop : ValueType → Unop → BasicInstruction
  | binop : ValueType → Binop → BasicInstruction
  | testop : ValueType → Testop → BasicInstruction
  | relop : ValueType → Relop → BasicInstruction
  | cvtop : ValueType → Cvtop → ValueType → Option Sx → BasicInstruction
  deriving Inhabited

mutual
/-- Boolean equality on basic instructions (`deriving DecidableEq` does not support nesting). -/
def BasicInstruction.beq : BasicInstruction → BasicInstruction → Bool
  | .unreachable, .unreachable => true
  | .nop, .nop => true
  | .drop, .drop => true
  | .select, .select => true
  | .vbitselect, .vbitselect => true
  | .block t1 es1, .block t2 es2 => decide (t1 = t2) && BasicInstruction.beqList es1 es2
  | .loop t1 es1, .loop t2 es2 => decide (t1 = t2) && BasicInstruction.beqList es1 es2
  | .if_ t1 a1 b1, .if_ t2 a2 b2 =>
    decide (t1 = t2) && BasicInstruction.beqList a1 a2 && BasicInstruction.beqList b1 b2
  | .br i, .br j => decide (i = j)
  | .brIf i, .brIf j => decide (i = j)
  | .brTable l1 i, .brTable l2 j => decide (l1 = l2) && decide (i = j)
  | .return_, .return_ => true
  | .call i, .call j => decide (i = j)
  | .callIndirect i, .callIndirect j => decide (i = j)
  | .getLocal i, .getLocal j => decide (i = j)
  | .setLocal i, .setLocal j => decide (i = j)
  | .teeLocal i, .teeLocal j => decide (i = j)
  | .getGlobal i, .getGlobal j => decide (i = j)
  | .setGlobal i, .setGlobal j => decide (i = j)
  | .load t1 p1 m1, .load t2 p2 m2 =>
    decide (t1 = t2) && decide (p1 = p2) && decide (m1 = m2)
  | .store t1 p1 m1, .store t2 p2 m2 =>
    decide (t1 = t2) && decide (p1 = p2) && decide (m1 = m2)
  | .currentMemory x, .currentMemory y | .growMemory x, .growMemory y => decide (x = y)
  | .const v1, .const v2 => decide (v1 = v2)
  | .unop t1 o1, .unop t2 o2 => decide (t1 = t2) && decide (o1 = o2)
  | .binop t1 o1, .binop t2 o2 => decide (t1 = t2) && decide (o1 = o2)
  | .testop t1 o1, .testop t2 o2 => decide (t1 = t2) && decide (o1 = o2)
  | .relop t1 o1, .relop t2 o2 => decide (t1 = t2) && decide (o1 = o2)
  | .cvtop t1 o1 u1 s1, .cvtop t2 o2 u2 s2 =>
    decide (t1 = t2) && decide (o1 = o2) && decide (u1 = u2) && decide (s1 = s2)
  | _, _ => false
/-- Boolean equality on lists of basic instructions. -/
def BasicInstruction.beqList : List BasicInstruction → List BasicInstruction → Bool
  | [], [] => true
  | a :: as, b :: bs => BasicInstruction.beq a b && BasicInstruction.beqList as bs
  | _, _ => false
end

theorem BasicInstruction.beq_iff (a b : BasicInstruction) : a.beq b = true ↔ a = b := by
  revert b
  apply BasicInstruction.rec (motive_1 := fun a => ∀ b, a.beq b = true ↔ a = b)
    (motive_2 := fun l => ∀ l', BasicInstruction.beqList l l' = true ↔ l = l')
  all_goals
    intros
    rename_i b
    cases b <;> simp_all [BasicInstruction.beq, BasicInstruction.beqList, and_assoc]

instance : DecidableEq BasicInstruction := fun a b =>
  decidable_of_iff _ (BasicInstruction.beq_iff a b)

/-! ## Functions and store -/

@[rocq_alias iriswasm.hostfuncidx]
inductive Hostfuncidx where
  | hostfuncidx : Nat → Hostfuncidx
  deriving DecidableEq, Repr, Inhabited

@[rocq_alias iriswasm.funcaddr]
abbrev Funcaddr := Immediate

@[rocq_alias iriswasm.tableaddr]
abbrev Tableaddr := Immediate

@[rocq_alias iriswasm.memaddr]
abbrev Memaddr := Immediate

@[rocq_alias iriswasm.globaladdr]
abbrev Globaladdr := Immediate

@[rocq_alias iriswasm.instance]
structure Instance where
  types : List FunctionType
  funcs : List Funcaddr
  tab : List Tableaddr
  memory : List Memaddr
  globs : List Globaladdr
  deriving DecidableEq, Repr, Inhabited

@[rocq_alias iriswasm.function_closure]
inductive FunctionClosure where
  | funcNative : Instance → FunctionType → List ValueType → List BasicInstruction → FunctionClosure
  | funcHost : FunctionType → Hostfuncidx → FunctionClosure
  deriving DecidableEq, Inhabited

@[rocq_alias iriswasm.funcelem]
abbrev Funcelem := Option Nat

@[rocq_alias iriswasm.tableinst]
structure Tableinst where
  entries : RunTable Funcelem
  maxOpt : Option Nat
  deriving DecidableEq, Repr, Inhabited

/-- Extensional contents used by store typing and the Iris heap interpretation. -/
def Tableinst.data (t : Tableinst) : List Funcelem := t.entries.toList

@[simp] theorem Tableinst.length_data (t : Tableinst) : t.data.length = t.entries.size :=
  RunTable.length_toList _

@[simp] theorem Tableinst.data_getElem? (t : Tableinst) (i : Nat) :
    t.data[i]? = t.entries.get? i := RunTable.toList_getElem? ..

@[rocq_alias iriswasm.global]
structure Global where
  mut_ : Mutability
  val : Value
  deriving DecidableEq, Repr, Inhabited

@[rocq_alias iriswasm.store_record]
structure StoreRecord where
  funcs : List FunctionClosure
  tables : List Tableinst
  mems : List Memory
  globals : List Global
  deriving DecidableEq, Inhabited

@[rocq_alias iriswasm.frame]
structure Frame where
  locs : List Value
  inst : Instance
  deriving DecidableEq, Repr, Inhabited

/-! ## Administrative instructions -/

@[rocq_alias iriswasm.administrative_instruction]
inductive AdministrativeInstruction where
  | basic : BasicInstruction → AdministrativeInstruction
  | trap
  | invoke : Funcaddr → AdministrativeInstruction
  | label : Nat → List AdministrativeInstruction → List AdministrativeInstruction →
      AdministrativeInstruction
  | local : Nat → Frame → List AdministrativeInstruction → AdministrativeInstruction
  | callHost : FunctionType → Hostfuncidx → List Value → AdministrativeInstruction
  deriving Inhabited

mutual
/-- Boolean equality on administrative instructions (`deriving` does not support nesting). -/
def AdministrativeInstruction.beq : AdministrativeInstruction → AdministrativeInstruction → Bool
  | .basic b1, .basic b2 => decide (b1 = b2)
  | .trap, .trap => true
  | .invoke a1, .invoke a2 => decide (a1 = a2)
  | .label n1 es1 es1', .label n2 es2 es2' =>
    decide (n1 = n2) && AdministrativeInstruction.beqList es1 es2 &&
      AdministrativeInstruction.beqList es1' es2'
  | .local n1 f1 es1, .local n2 f2 es2 =>
    decide (n1 = n2) && decide (f1 = f2) && AdministrativeInstruction.beqList es1 es2
  | .callHost t1 h1 vs1, .callHost t2 h2 vs2 => decide (t1 = t2) && decide (h1 = h2) && decide (vs1 = vs2)
  | _, _ => false
/-- Boolean equality on lists of administrative instructions. -/
def AdministrativeInstruction.beqList :
    List AdministrativeInstruction → List AdministrativeInstruction → Bool
  | [], [] => true
  | a :: as, b :: bs => AdministrativeInstruction.beq a b && AdministrativeInstruction.beqList as bs
  | _, _ => false
end

theorem AdministrativeInstruction.beq_iff (a b : AdministrativeInstruction) :
    a.beq b = true ↔ a = b := by
  revert b
  refine AdministrativeInstruction.rec (motive_1 := fun a => ∀ b, a.beq b = true ↔ a = b)
    (motive_2 := fun l => ∀ l', AdministrativeInstruction.beqList l l' = true ↔ l = l')
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ a
  all_goals
    intros
    rename_i b
    cases b <;> simp_all [AdministrativeInstruction.beq, AdministrativeInstruction.beqList, and_assoc]

instance : DecidableEq AdministrativeInstruction := fun a b =>
  decidable_of_iff _ (AdministrativeInstruction.beq_iff a b)

@[rocq_alias iriswasm.lholed]
inductive Lholed where
  | base : List AdministrativeInstruction → List AdministrativeInstruction → Lholed
  | rec_ : List AdministrativeInstruction → Nat → List AdministrativeInstruction → Lholed →
      List AdministrativeInstruction → Lholed
  deriving DecidableEq, Inhabited

@[rocq_alias iriswasm.expr]
abbrev Expr := List BasicInstruction

@[rocq_alias iriswasm.labelidx]
inductive Labelidx where
  | labelidx : Nat → Labelidx
  deriving DecidableEq, Repr, Inhabited

@[rocq_alias iriswasm.funcidx]
inductive Funcidx where
  | funcidx : Nat → Funcidx
  deriving DecidableEq, Repr, Inhabited

@[rocq_alias iriswasm.tableidx]
inductive Tableidx where
  | tableidx : Nat → Tableidx
  deriving DecidableEq, Repr, Inhabited

@[rocq_alias iriswasm.memidx]
inductive Memidx where
  | memidx : Nat → Memidx
  deriving DecidableEq, Repr, Inhabited

@[rocq_alias iriswasm.typeidx]
inductive Typeidx where
  | typeidx : Nat → Typeidx
  deriving DecidableEq, Repr, Inhabited

@[rocq_alias iriswasm.localidx]
inductive Localidx where
  | localidx : Nat → Localidx
  deriving DecidableEq, Repr, Inhabited

@[rocq_alias iriswasm.globalidx]
inductive Globalidx where
  | globalidx : Nat → Globalidx
  deriving DecidableEq, Repr, Inhabited

@[rocq_alias iriswasm.import_desc]
inductive ImportDesc where
  | func : Nat → ImportDesc
  | table : TableType → ImportDesc
  | mem : MemoryType → ImportDesc
  | global : GlobalType → ImportDesc
  deriving DecidableEq, Repr, Inhabited

/-- Coq `name := list Byte.byte` (Coq's ASCII bytes); represented by Wasm bytes. -/
@[rocq_alias iriswasm.name]
abbrev Name := List Byte

@[rocq_alias iriswasm.module_import]
structure ModuleImport where
  module : Name
  name : Name
  desc : ImportDesc
  deriving DecidableEq, Repr, Inhabited

@[rocq_alias iriswasm.module_table]
structure ModuleTable where
  type : TableType
  deriving DecidableEq, Repr, Inhabited

@[rocq_alias iriswasm.module_glob]
structure ModuleGlob where
  type : GlobalType
  init : Expr
  deriving DecidableEq, Inhabited

@[rocq_alias iriswasm.module_start]
structure ModuleStart where
  func : Funcidx
  deriving DecidableEq, Repr, Inhabited

@[rocq_alias iriswasm.module_element]
structure ModuleElement where
  table : Tableidx
  offset : Expr
  init : List Funcidx
  deriving DecidableEq, Inhabited

@[rocq_alias iriswasm.code_func]
structure CodeFunc where
  locals : List ValueType
  expr : Expr
  deriving DecidableEq, Inhabited

@[rocq_alias iriswasm.module_data]
structure ModuleData where
  data : Memidx
  offset : Expr
  init : List Byte
  deriving DecidableEq, Inhabited

@[rocq_alias iriswasm.module_export_desc]
inductive ModuleExportDesc where
  | func : Funcidx → ModuleExportDesc
  | table : Tableidx → ModuleExportDesc
  | mem : Memidx → ModuleExportDesc
  | global : Globalidx → ModuleExportDesc
  deriving DecidableEq, Repr, Inhabited

@[rocq_alias iriswasm.module_export]
structure ModuleExport where
  name : Name
  desc : ModuleExportDesc
  deriving DecidableEq, Repr, Inhabited

@[rocq_alias iriswasm.module_func]
structure ModuleFunc where
  type : Typeidx
  locals : List ValueType
  body : Expr
  deriving DecidableEq, Inhabited

@[rocq_alias iriswasm.module]
structure Module where
  types : List FunctionType
  funcs : List ModuleFunc
  tables : List ModuleTable
  mems : List MemoryType
  globals : List ModuleGlob
  elem : List ModuleElement
  data : List ModuleData
  start : Option ModuleStart
  imports : List ModuleImport
  exports : List ModuleExport
  deriving DecidableEq, Inhabited

@[rocq_alias iriswasm.extern_t]
inductive ExternT where
  | func : FunctionType → ExternT
  | tab : TableType → ExternT
  | mem : MemoryType → ExternT
  | glob : GlobalType → ExternT
  deriving DecidableEq, Repr, Inhabited

/-! ## Types used by the interpreter -/

@[rocq_alias iriswasm.config_tuple]
abbrev ConfigTuple := StoreRecord × Frame × List AdministrativeInstruction

@[rocq_alias iriswasm.config_one_tuple_without_e]
abbrev ConfigOneTupleWithoutE := StoreRecord × Frame × List Value

@[rocq_alias iriswasm.res_crash]
inductive ResCrash where
  | error
  deriving DecidableEq, Repr, Inhabited

@[rocq_alias iriswasm.res_step]
inductive ResStep where
  | crash : ResCrash → ResStep
  | break : Nat → List Value → ResStep
  | return_ : List Value → ResStep
  | normal : List AdministrativeInstruction → ResStep
  | callHost : FunctionType → Hostfuncidx → List Value → ResStep
  deriving DecidableEq, Inhabited

@[rocq_alias iriswasm.res_tuple]
abbrev ResTuple := StoreRecord × Frame × ResStep

end Wasm
