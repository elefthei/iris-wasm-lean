/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import Wasm.Opsem
import Wasm.Typing
import Wasm.MemoryList
import Wasm.ExternalTypes
import Wasm.ListExtra

/-! Port of `theories/instantiation.v`: module instantiation. -/

namespace Wasm

@[rocq_alias iriswasm.addr]
abbrev Addr := Nat

@[rocq_alias iriswasm.funaddr]
abbrev Funaddr := Addr

#rocq_ignore iriswasm.instantiation.tableaddr "identical to Wasm.Tableaddr (Nat) from datatypes.v"
#rocq_ignore iriswasm.instantiation.memaddr "identical to Wasm.Memaddr (Nat) from datatypes.v"
#rocq_ignore iriswasm.instantiation.globaladdr "identical to Wasm.Globaladdr (Nat) from datatypes.v"

@[rocq_alias iriswasm.alloc_Xs]
def allocXs {A B : Type} (f : StoreRecord → A → StoreRecord × B) (s : StoreRecord) (xs : List A) :
    StoreRecord × List B :=
  let (s', fas) := xs.foldl (fun (s, ys) x => let (s', y) := f s x; (s', y :: ys)) (s, [])
  (s', fas.reverse)

@[rocq_alias iriswasm.externval]
inductive Externval where
  | func : Funaddr → Externval
  | table : Tableaddr → Externval
  | mem : Memaddr → Externval
  | global : Globaladdr → Externval
  deriving DecidableEq, Repr, Inhabited

@[rocq_alias iriswasm.funcs_of_externals]
def funcsOfExternals (evs : List Externval) : List Addr :=
  evs.filterMap fun | .func fa => some fa | _ => none

@[rocq_alias iriswasm.tables_of_externals]
def tablesOfExternals (evs : List Externval) : List Addr :=
  evs.filterMap fun | .table ta => some ta | _ => none

@[rocq_alias iriswasm.mems_of_externals]
def memsOfExternals (evs : List Externval) : List Addr :=
  evs.filterMap fun | .mem ta => some ta | _ => none

@[rocq_alias iriswasm.globals_of_externals]
def globalsOfExternals (evs : List Externval) : List Addr :=
  evs.filterMap fun | .global ta => some ta | _ => none

@[rocq_alias iriswasm.add_func]
def addFunc (s : StoreRecord) (funcinst : FunctionClosure) : StoreRecord :=
  { s with funcs := s.funcs ++ [funcinst] }

@[rocq_alias iriswasm.alloc_func]
def allocFunc (s : StoreRecord) (mF : ModuleFunc) (mi : Instance) : StoreRecord × Funcidx :=
  let funcaddr := s.funcs.length
  let functype := mi.types.getD (match mF.type with | .typeidx n => n) (.tf [] [])
  let funcinst := FunctionClosure.funcNative mi functype mF.locals mF.body
  (addFunc s funcinst, .funcidx funcaddr)

@[rocq_alias iriswasm.alloc_funcs]
def allocFuncs (s : StoreRecord) (mFs : List ModuleFunc) (mi : Instance) :
    StoreRecord × List Funcidx :=
  allocXs (fun s mF => allocFunc s mF mi) s mFs

@[rocq_alias iriswasm.add_table]
def addTable (s : StoreRecord) (ti : Tableinst) : StoreRecord :=
  { s with tables := s.tables ++ [ti] }

@[rocq_alias iriswasm.alloc_tab]
def allocTab (s : StoreRecord) (tty : TableType) : StoreRecord × Tableidx :=
  let tableaddr := Tableidx.tableidx s.tables.length
  let tableinst : Tableinst := { entries := RunTable.uniform tty.limits.min none, maxOpt := tty.limits.max }
  (addTable s tableinst, tableaddr)

@[rocq_alias iriswasm.alloc_tabs]
def allocTabs (s : StoreRecord) (ts : List TableType) : StoreRecord × List Tableidx :=
  allocXs allocTab s ts

#rocq_ignore iriswasm.mem_mk "Memory allocation retains the address type and both limits"
def memMk (mt : MemoryType) : Memory :=
  { data := MemoryList.memMake 0 (pageSize * mt.limits.min), type := mt }

@[rocq_alias iriswasm.add_mem]
def addMem (s : StoreRecord) (mM : Memory) : StoreRecord :=
  { s with mems := s.mems ++ [mM] }

#rocq_ignore iriswasm.alloc_mem "Allocates a memory with its full Core memory type"
def allocMem (s : StoreRecord) (mM : MemoryType) : StoreRecord × Memidx :=
  (addMem s (memMk mM), .memidx s.mems.length)

#rocq_ignore iriswasm.alloc_mems "Allocates memories with their full Core memory types"
def allocMems (s : StoreRecord) (mMs : List MemoryType) : StoreRecord × List Memidx :=
  allocXs allocMem s mMs

@[rocq_alias iriswasm.add_glob]
def addGlob (s : StoreRecord) (mG : Global) : StoreRecord :=
  { s with globals := s.globals ++ [mG] }

@[rocq_alias iriswasm.alloc_glob]
def allocGlob (s : StoreRecord) (mGV : ModuleGlob × Value) : StoreRecord × Globalidx :=
  let (mG, v) := mGV
  (addGlob s ⟨mG.type.mut_, v⟩, .globalidx s.globals.length)

@[rocq_alias iriswasm.alloc_globs]
def allocGlobs (s : StoreRecord) (mGs : List ModuleGlob) (vs : List Value) :
    StoreRecord × List Globalidx :=
  allocXs allocGlob s (mGs.zip vs)

@[rocq_alias iriswasm.v_ext]
abbrev VExt := ModuleExportDesc

/-- Partiality is circumvented by providing 0 as a default. -/
@[rocq_alias iriswasm.export_get_v_ext]
def exportGetVExt (inst : Instance) (exp : ModuleExportDesc) : VExt :=
  match exp with
  | .func (.funcidx i) => .func (.funcidx (inst.funcs.getD i 0))
  | .table (.tableidx i) => .table (.tableidx (inst.tab.getD i 0))
  | .mem (.memidx i) => .mem (.memidx (inst.memory.getD i 0))
  | .global (.globalidx i) => .global (.globalidx (inst.globs.getD i 0))

@[rocq_alias iriswasm.ext_funcs]
def extFuncs : List ModuleExportDesc → List Funcidx :=
  List.filterMap fun | .func i => some i | _ => none

@[rocq_alias iriswasm.ext_tabs]
def extTabs : List ModuleExportDesc → List Tableidx :=
  List.filterMap fun | .table i => some i | _ => none

@[rocq_alias iriswasm.ext_mems]
def extMems : List ModuleExportDesc → List Memidx :=
  List.filterMap fun | .mem i => some i | _ => none

@[rocq_alias iriswasm.ext_globs]
def extGlobs : List ModuleExportDesc → List Globalidx :=
  List.filterMap fun | .global i => some i | _ => none

@[rocq_alias iriswasm.ext_t_funcs]
def extTFuncs : List ExternT → List FunctionType :=
  List.filterMap fun | .func tf => some tf | _ => none

@[rocq_alias iriswasm.ext_t_tabs]
def extTTabs : List ExternT → List TableType :=
  List.filterMap fun | .tab i => some i | _ => none

#rocq_ignore iriswasm.ext_t_mems "The memory interface includes the address type"
def extTMems : List ExternT → List MemoryType :=
  List.filterMap fun | .mem i => some i | _ => none

@[rocq_alias iriswasm.ext_t_globs]
def extTGlobs : List ExternT → List GlobalType :=
  List.filterMap fun | .glob i => some i | _ => none

#rocq_ignore iriswasm.alloc_module "Module allocation retains full memory types"
def allocModule (s : StoreRecord) (m : Module) (imps : List VExt) (gvs : List Value)
    (s'InstExps : StoreRecord × Instance × List ModuleExport) : Bool :=
  let (s'Goal, inst, exps) := s'InstExps
  let (s1, iFs) := allocFuncs s m.funcs inst
  let (s2, iTs) := allocTabs s1 (m.tables.map (·.type))
  let (s3, iMs) := allocMems s2 m.mems
  let (s', iGs) := allocGlobs s3 m.globals gvs
  decide (s'Goal = s') &&
  decide (inst.types = m.types) &&
  decide (inst.funcs = (extFuncs imps ++ iFs).map fun | .funcidx i => i) &&
  decide (inst.tab = (extTabs imps ++ iTs).map fun | .tableidx i => i) &&
  decide (inst.memory = (extMems imps ++ iMs).map fun | .memidx i => i) &&
  decide (inst.globs = (extGlobs imps ++ iGs).map fun | .globalidx i => i) &&
  decide (exps = m.exports.map fun mExp =>
    ({ name := mExp.name, desc := exportGetVExt inst mExp.desc } : ModuleExport))

#rocq_ignore iriswasm.interp_alloc_module "Module allocation retains full memory types"
def interpAllocModule (s : StoreRecord) (m : Module) (imps : List VExt) (gvs : List Value) :
    StoreRecord × Instance × List ModuleExport :=
  let iFs := (List.range' s.funcs.length m.funcs.length).map Funcidx.funcidx
  let iTs := (List.range' s.tables.length m.tables.length).map Tableidx.tableidx
  let iMs := (List.range' s.mems.length m.mems.length).map Memidx.memidx
  let iGs := (List.range' s.globals.length (min m.globals.length gvs.length)).map Globalidx.globalidx
  let inst : Instance :=
    { types := m.types
      funcs := (extFuncs imps ++ iFs).map fun | .funcidx i => i
      tab := (extTabs imps ++ iTs).map fun | .tableidx i => i
      memory := (extMems imps ++ iMs).map fun | .memidx i => i
      globs := (extGlobs imps ++ iGs).map fun | .globalidx i => i }
  let (s1, _) := allocFuncs s m.funcs inst
  let (s2, _) := allocTabs s1 (m.tables.map (·.type))
  let (s3, _) := allocMems s2 m.mems
  let (s', _) := allocGlobs s3 m.globals gvs
  let exps := m.exports.map fun mExp =>
    ({ name := mExp.name, desc := exportGetVExt inst mExp.desc } : ModuleExport)
  (s', inst, exps)

@[rocq_alias iriswasm.insert_at]
def insertAt {A : Type} (v : A) (n : Nat) (l : List A) : List A :=
  l.take n ++ ([v] ++ l.drop (n + 1))

@[rocq_alias iriswasm.dummy_table]
def dummyTable : Tableinst := { entries := RunTable.ofList [], maxOpt := none }

@[rocq_alias iriswasm.init_tab]
def initTab (s : StoreRecord) (inst : Instance) (eInd : Nat) (e : ModuleElement) : StoreRecord :=
  let tInd := inst.tab.getD (match e.table with | .tableidx i => i) 0
  let tab := s.tables.getD tInd dummyTable
  let ePay := e.init.map fun | .funcidx j => inst.funcs[j]?
  { s with tables := insertAt { tab with entries := tab.entries.overwrite eInd ePay } tInd s.tables }

@[rocq_alias iriswasm.init_tabs]
def initTabs (s : StoreRecord) (inst : Instance) (eInds : List Nat) (es : List ModuleElement) :
    StoreRecord :=
  (eInds.zip es).foldl (fun s' (eInd, e) => initTab s' inst eInd e) s

#rocq_ignore iriswasm.dummy_data_vec "Data initialization looks up its destination without a default"
#rocq_ignore iriswasm.dummy_mem "There is no default memory for a missing address"
#rocq_ignore iriswasm.init_mem "Initialization writes to the resolved memory, preserving its type"
def initMem (s : StoreRecord) (inst : Instance) (off : Nat) (d : ModuleData) :
    Except StoreRecord StoreRecord := do
  let some i := inst.memory[match d.data with | .memidx k => k]? | .error s
  let some mem := s.mems[i]? | .error s
  if off + d.init.length ≤ lengthMem mem then
    .ok { s with mems := s.mems.set i { mem with data := mem.data.splice off d.init } }
  else .error s

#rocq_ignore iriswasm.init_mems "Data initialization preserves memory types and resolves each address"
def initMems (s : StoreRecord) (inst : Instance) : List Nat → List ModuleData →
    Except StoreRecord StoreRecord
  | [], [] => .ok s
  | off :: os, d :: ds =>
    match initMem s inst off d with
    | .error failed => .error failed
    | .ok s' => initMems s' inst os ds
  | _, _ => .error s

theorem initMem_ok_iff {s t : StoreRecord} {inst : Instance} {off : Nat} {d : ModuleData} :
    initMem s inst off d = .ok t ↔
      ∃ i mem, inst.memory[match d.data with | .memidx k => k]? = some i ∧
        s.mems[i]? = some mem ∧ off + d.init.length ≤ lengthMem mem ∧
        t = { s with mems := s.mems.set i { mem with data := mem.data.splice off d.init } } := by
  cases hi : inst.memory[match d.data with | .memidx k => k]? with
  | none => simp [initMem, hi]
  | some i =>
    cases hm : s.mems[i]? with
    | none => simp [initMem, hi, hm]
    | some mem =>
      by_cases hb : off + d.init.length ≤ lengthMem mem <;> simp [initMem, hi, hm, hb, eq_comm]

@[simp] theorem initMems_nil (s : StoreRecord) (inst : Instance) :
    initMems s inst [] [] = .ok s := rfl

theorem initMems_cons {s t : StoreRecord} {inst : Instance}
    {off : Nat} {os : List Nat} {d : ModuleData} {ds : List ModuleData} :
    initMems s inst (off :: os) (d :: ds) = .ok t ↔
      ∃ mid, initMem s inst off d = .ok mid ∧ initMems mid inst os ds = .ok t := by
  cases h : initMem s inst off d <;> simp [initMems, h]

@[rocq_alias iriswasm.module_func_typing]
def ModuleFuncTyping (c : TContext) (m : ModuleFunc) (tf : FunctionType) : Prop :=
  match m, tf with
  | ⟨.typeidx i, tLocs, bEs⟩, .tf tn tm =>
    c.typesT[i]? = some tf ∧
    let c' : TContext :=
      { c with local_ := c.local_ ++ tn ++ tLocs, label := tm :: c.label, return_ := some tm }
    BeTyping c' bEs (.tf [] tm)

#rocq_ignore iriswasm.module_tab_typing "Core table32 limits are at most 2^32 - 1 entries"
def moduleTabTyping (t : ModuleTable) : Bool :=
  limitTyping t.type.limits (2 ^ 32 - 1)

#rocq_ignore iriswasm.module_mem_typing "Core memory limits depend on the declared address type"
def moduleMemTyping (mt : MemoryType) : Bool :=
  limitTyping mt.limits mt.address.pageLimit

#rocq_ignore iriswasm.const_expr "Core also permits integer add, sub and mul in constant expressions"
def constExpr (c : TContext) (bE : BasicInstruction) : Bool :=
  match bE with
  | .const _ => true
  | .binop .i32 (.i op) | .binop .i64 (.i op) =>
    match op with
    | .add | .sub | .mul => true
    | _ => false
  | .getGlobal k =>
    decide (k < c.global.length) &&
    match c.global[k]? with
    | none => false
    | some t => decide (t.mut_ = .immut)
  | _ => false

#rocq_ignore iriswasm.const_exprs "uses the extended Core constant-instruction predicate"
def constExprs (c : TContext) (es : List BasicInstruction) : Bool :=
  es.all (constExpr c)

@[rocq_alias iriswasm.module_glob_typing]
def ModuleGlobTyping (c : TContext) (g : ModuleGlob) (tg : GlobalType) : Prop :=
  constExprs c g.init = true ∧ tg = g.type ∧ BeTyping c g.init (.tf [] [tg.t])

/-- A global's initializer can read earlier immutable globals, but not itself or a later one. -/
inductive ModuleGlobalsTyping : TContext → List ModuleGlob → List GlobalType → Prop
  | nil {c : TContext} : ModuleGlobalsTyping c [] []
  | cons {c : TContext} {g : ModuleGlob} {t : GlobalType} {gs : List ModuleGlob}
      {ts : List GlobalType} : ModuleGlobTyping c g t →
      ModuleGlobalsTyping { c with global := c.global ++ [t] } gs ts →
      ModuleGlobalsTyping c (g :: gs) (t :: ts)

theorem ModuleGlobalsTyping.types_eq {c : TContext} {gs : List ModuleGlob} {ts : List GlobalType}
    (h : ModuleGlobalsTyping c gs ts) : ts = gs.map ModuleGlob.type := by
  induction h with
  | nil => rfl
  | cons head _ ih => simp [head.2.1, ih]

@[rocq_alias iriswasm.module_elem_typing]
def ModuleElemTyping (c : TContext) (e : ModuleElement) : Prop :=
  match e with
  | ⟨.tableidx t, es, is_⟩ =>
    constExprs c es = true ∧
    BeTyping c es (.tf [] [.i32]) ∧
    t < c.table.length ∧
    (is_.all fun | .funcidx i => decide (i < c.funcT.length)) = true

#rocq_ignore iriswasm.module_data_typing "An active offset must have its target memory's address type"
def ModuleDataTyping (c : TContext) (mD : ModuleData) : Prop :=
  match mD with
  | ⟨.memidx d, es, _⟩ =>
    match c.memory[d]? with
    | none => False
    | some mt => constExprs c es = true ∧ BeTyping c es (.tf [] [mt.address.valueType])

@[rocq_alias iriswasm.module_start_typing]
def moduleStartTyping (c : TContext) (ms : ModuleStart) : Bool :=
  match ms.func with
  | .funcidx i =>
    decide (i < c.funcT.length) &&
    match c.funcT[i]? with
    | none => false
    | some tf => decide (tf = .tf [] [])

#rocq_ignore iriswasm.module_import_typing "Memory import types include the address type"
def moduleImportTyping (c : TContext) (d : ImportDesc) (e : ExternT) : Bool :=
  match d, e with
  | .func i, .func tf =>
    decide (i < c.typesT.length) &&
    match c.typesT[i]? with
    | none => false
    | some tf' => decide (tf = tf')
  | .table tT, .tab tT' => decide (tT = tT') && moduleTabTyping { type := tT }
  | .mem mt, .mem mt' => decide (mt = mt') && moduleMemTyping mt
  | .global gt, .glob gt' => decide (gt = gt')
  | _, _ => false

#rocq_ignore iriswasm.module_export_typing "Memory export types include the address type"
def moduleExportTyping (c : TContext) (d : ModuleExportDesc) (e : ExternT) : Bool :=
  match d, e with
  | .func (.funcidx i), .func tf =>
    decide (i < c.funcT.length) &&
    match c.funcT[i]? with
    | none => false
    | some tf' => decide (tf = tf')
  | .table (.tableidx i), .tab tT =>
    decide (i < c.table.length) &&
    match c.table[i]? with
    | none => false
    | some lim' => decide (tT = lim')
  | .mem (.memidx i), .mem tM =>
    decide (i < c.memory.length) &&
    match c.memory[i]? with
    | none => false
    | some mt => decide (tM = mt)
  | .global (.globalidx i), .glob gt =>
    decide (i < c.global.length) &&
    match c.global[i]? with
    | none => false
    | some gt' => decide (gt = gt')
  | _, _ => false

@[rocq_alias iriswasm.pred_option]
def predOption {A : Type} (p : A → Bool) (aOpt : Option A) : Bool :=
  match aOpt with
  | none => true
  | some a => p a

def moduleContext (m : Module) (impts : List ExternT) (fts : List FunctionType)
    (gts : List GlobalType) : TContext :=
  { typesT := m.types, funcT := extTFuncs impts ++ fts, global := extTGlobs impts ++ gts
    table := extTTabs impts ++ m.tables.map (·.type), memory := extTMems impts ++ m.mems
    local_ := [], label := [], return_ := none }

def globalInitContext (impts : List ExternT) : TContext :=
  { typesT := [], funcT := [], global := extTGlobs impts, table := [], memory := []
    local_ := [], label := [], return_ := none }

def ModuleTypingFields (m : Module) (impts expts : List ExternT) (fts : List FunctionType)
    (gts : List GlobalType) : Prop :=
  let c := moduleContext m impts fts gts
  List.Forall₂ (ModuleFuncTyping c) m.funcs fts ∧
  m.tables.all moduleTabTyping = true ∧
  m.mems.all moduleMemTyping = true ∧
  ModuleGlobalsTyping (globalInitContext impts) m.globals gts ∧
  (∀ x ∈ m.elem, ModuleElemTyping c x) ∧
  (∀ x ∈ m.data, ModuleDataTyping c x) ∧
  predOption (moduleStartTyping c) m.start = true ∧
  List.Forall₂ (fun (imp : ModuleImport) e => moduleImportTyping c imp.desc e = true)
    m.imports impts ∧
  (m.exports.map ModuleExport.name).Nodup ∧
  List.Forall₂ (fun (exp : ModuleExport) e => moduleExportTyping c exp.desc e = true)
    m.exports expts

#rocq_ignore iriswasm.module_typing "Core module typing includes ordered globals and unique exports"
def ModuleTyping (m : Module) (impts expts : List ExternT) : Prop :=
  ∃ fts gts, ModuleTypingFields m impts expts fts gts

#rocq_ignore iriswasm.external_typing "Memory imports match both the address type and limits"
inductive ExternalTyping : StoreRecord → VExt → ExternT → Prop
  | func (s : StoreRecord) (i : Nat) (cl : FunctionClosure) (tf : FunctionType) :
    i < s.funcs.length → s.funcs[i]? = some cl → tf = clType cl →
    ExternalTyping s (.func (.funcidx i)) (.func tf)
  | tab (s : StoreRecord) (i : Nat) (ti : Tableinst) (tt : TableType) :
    i < s.tables.length → s.tables[i]? = some ti → tabTyping ti tt = true →
    ExternalTyping s (.table (.tableidx i)) (.tab tt)
  | mem (s : StoreRecord) (i : Nat) (m : Memory) (mt : MemoryType) :
    i < s.mems.length → s.mems[i]? = some m → memTyping m mt = true →
    ExternalTyping s (.mem (.memidx i)) (.mem mt)
  | glob (s : StoreRecord) (i : Nat) (g : Global) (gt : GlobalType) :
    i < s.globals.length → s.globals[i]? = some g → globalAgree g gt = true →
    ExternalTyping s (.global (.globalidx i)) (.glob gt)

@[rocq_alias iriswasm.instantiate_globals]
def InstantiateGlobals (inst : Instance) (s' : StoreRecord) (m : Module) (gInits : List Value) :
    Prop :=
  List.Forall₂ (fun (g : ModuleGlob) v =>
      ReduceTrans (s', ⟨[], inst⟩, toEList g.init) (s', ⟨[], inst⟩, [.basic (.const v)]))
    m.globals gInits

@[rocq_alias iriswasm.instantiate_elem]
def InstantiateElem (inst : Instance) (s' : StoreRecord) (m : Module) (eOffs : List I32) : Prop :=
  List.Forall₂ (fun (e : ModuleElement) c =>
      ReduceTrans (s', ⟨[], inst⟩, toEList e.offset) (s', ⟨[], inst⟩, [.basic (.const (.int32 c))]))
    m.elem eOffs

#rocq_ignore iriswasm.instantiate_data "Data offsets evaluate to either integer address width"
def InstantiateData (inst : Instance) (s' : StoreRecord) (m : Module)
    (dOffs : List AddressOperand) : Prop :=
  List.Forall₂ (fun (d : ModuleData) (c : AddressOperand) =>
      ReduceTrans (s', ⟨[], inst⟩, toEList d.offset) (s', ⟨[], inst⟩, [.basic (.const c.value)]))
    m.data dOffs

/-- Coq `Z.to_nat` of the (always non-negative) unsigned representation. -/
@[rocq_alias iriswasm.nat_of_int]
def natOfInt (i : I32) : Nat := i.toNat

@[rocq_alias iriswasm.N_of_int]
def nOfInt (i : I32) : Nat := i.toNat

@[rocq_alias iriswasm.check_bounds_elem]
def checkBoundsElem (inst : Instance) (s : StoreRecord) (m : Module) (eOffs : List I32) : Bool :=
  List.all2
    (fun eOff (e : ModuleElement) =>
      match inst.tab[match e.table with | .tableidx i => i]? with
      | none => false
      | some i =>
        match s.tables[i]? with
        | none => false
        | some ti => decide (nOfInt eOff + e.init.length ≤ ti.entries.size))
    eOffs m.elem

#rocq_ignore iriswasm.instantiation.length_mem "identical to Wasm.lengthMem (operations.v)"

#rocq_ignore iriswasm.check_bounds_data "Checks the full unsigned offset for either address width"
def checkBoundsData (inst : Instance) (s : StoreRecord) (m : Module)
    (dOffs : List AddressOperand) : Bool :=
  List.all2
    (fun (dOff : AddressOperand) (d : ModuleData) =>
      match inst.memory[match d.data with | .memidx i => i]? with
      | none => false
      | some i =>
        match s.mems[i]? with
        | none => false
        | some mem => decide (dOff.unsigned + d.init.length ≤ lengthMem mem))
    dOffs m.data

theorem initMems_exists_of_bounds {s : StoreRecord} {inst : Instance} {m : Module}
    {dOffs : List AddressOperand} (h : checkBoundsData inst s m dOffs = true) :
    ∃ t, initMems s inst (dOffs.map AddressOperand.unsigned) m.data = .ok t := by
  unfold checkBoundsData at h
  rw [List.all2_Forall₂] at h
  generalize m.data = ds at h ⊢
  suffices ∀ curr : StoreRecord, curr.mems.map lengthMem = s.mems.map lengthMem →
      ∃ t, initMems curr inst (dOffs.map AddressOperand.unsigned) ds = .ok t from this s rfl
  induction h with
  | nil => exact fun curr _ => ⟨curr, rfl⟩
  | @cons off d os ds head _ ih =>
    intro curr heq
    cases hi : inst.memory[match d.data with | .memidx k => k]? with
    | none => simp [hi] at head
    | some i =>
      cases hm : s.mems[i]? with
      | none => simp [hi, hm] at head
      | some m =>
        simp [hi, hm] at head
        have hget := congrArg (fun xs : List Nat => xs[i]?) heq
        cases hc : curr.mems[i]? with
        | none => simp [List.getElem?_map, hc, hm] at hget
        | some mem =>
          have hl : lengthMem mem = lengthMem m := by simpa [List.getElem?_map, hc, hm] using hget
          have hb : off.unsigned + d.init.length ≤ lengthMem mem := hl ▸ head
          let updated := { mem with data := mem.data.splice off.unsigned d.init }
          let mid := { curr with mems := curr.mems.set i updated }
          have hsize : lengthMem updated = lengthMem mem := by
            change max (lengthMem mem) (min off.unsigned (lengthMem mem) + d.init.length) = _
            rw [Nat.min_eq_left (by omega), Nat.max_eq_left hb]
          have hmid : mid.mems.map lengthMem = s.mems.map lengthMem := by
            change (curr.mems.set i updated).map lengthMem = _
            rw [List.map_set, hsize, ← heq]
            obtain ⟨hi', hv⟩ := List.getElem?_eq_some_iff.mp hc
            have he : (curr.mems.map lengthMem)[i]'(by simpa using hi') = lengthMem mem := by
              simp [hv]
            rw [← he, List.set_getElem_self]
          obtain ⟨t, ht⟩ := ih mid hmid
          exact ⟨t, initMems_cons.mpr ⟨mid, initMem_ok_iff.mpr ⟨i, mem, hi, hc, hb, rfl⟩, ht⟩⟩

@[rocq_alias iriswasm.check_start]
def checkStart (m : Module) (inst : Instance) (start : Option Nat) : Bool :=
  let start' := optionBind
    (fun (iS : ModuleStart) => inst.funcs[match iS.func with | .funcidx i => i]?) m.start
  decide (start' = start)

#rocq_ignore iriswasm.instantiate "Active data segment offsets preserve the selected integer width"
def Instantiate (s : StoreRecord) (m : Module) (vImps : List VExt)
    (z : (StoreRecord × Instance × List ModuleExport) × Option Nat) : Prop :=
  match z with
  | ((sEnd, inst, vExps), start) =>
    ∃ (tImps tExps : List ExternT) (s' : StoreRecord) (gInits : List Value)
        (eOffs : List I32) (dOffs : List AddressOperand),
      ModuleTyping m tImps tExps ∧
      List.Forall₂ (ExternalTyping s) vImps tImps ∧
      allocModule s m vImps gInits (s', inst, vExps) = true ∧
      InstantiateGlobals inst s' m gInits ∧
      InstantiateElem inst s' m eOffs ∧
      InstantiateData inst s' m dOffs ∧
      checkBoundsElem inst s' m eOffs = true ∧
      checkBoundsData inst s' m dOffs = true ∧
      checkStart m inst start = true ∧
      let s'' := initTabs s' inst (eOffs.map fun o => o.toNat) m.elem
      initMems s'' inst (dOffs.map AddressOperand.unsigned) m.data = .ok sEnd

end Wasm
