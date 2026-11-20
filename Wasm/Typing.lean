/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import Wasm.Operations

/-! Port of `theories/typing.v`: Wasm typing rules. -/

namespace Wasm

@[rocq_alias iriswasm.convert_helper]
def convertHelper (sxo : Option Sx) (t1 t2 : ValueType) : Bool :=
  (sxo == none) ==
  ((isFloatT t1 && isFloatT t2) || (isIntT t1 && isIntT t2 && decide (lengthT t1 < lengthT t2)))

@[rocq_alias iriswasm.convert_cond]
def convertCond (t1 t2 : ValueType) (sxo : Option Sx) : Bool :=
  t1 != t2 && convertHelper sxo t1 t2

@[rocq_alias iriswasm.upd_label]
def updLabel (C : TContext) (lab : List (List ValueType)) : TContext := { C with label := lab }

@[rocq_alias iriswasm.plop2]
def plop2 (C : TContext) (i : Nat) (ts : List ValueType) : Bool := C.label[i]? == some ts

@[rocq_alias iriswasm.result_typing]
inductive ResultTyping : Result → ResultType → Prop
  | values {vs : List Value} : ResultTyping (.values vs) (vs.map typeof)
  | trap {ts : ResultType} : ResultTyping .trap ts

@[rocq_alias iriswasm.unop_type_agree]
inductive UnopTypeAgree : ValueType → Unop → Prop
  | i32Agree {op} : UnopTypeAgree .i32 (.i op)
  | i64Agree {op} : UnopTypeAgree .i64 (.i op)
  | f32Agree {op} : UnopTypeAgree .f32 (.f op)
  | f64Agree {op} : UnopTypeAgree .f64 (.f op)

@[rocq_alias iriswasm.binop_type_agree]
inductive BinopTypeAgree : ValueType → Binop → Prop
  | i32Agree {op} : BinopTypeAgree .i32 (.i op)
  | i64Agree {op} : BinopTypeAgree .i64 (.i op)
  | f32Agree {op} : BinopTypeAgree .f32 (.f op)
  | f64Agree {op} : BinopTypeAgree .f64 (.f op)

@[rocq_alias iriswasm.relop_type_agree]
inductive RelopTypeAgree : ValueType → Relop → Prop
  | i32Agree {op} : RelopTypeAgree .i32 (.i op)
  | i64Agree {op} : RelopTypeAgree .i64 (.i op)
  | f32Agree {op} : RelopTypeAgree .f32 (.f op)
  | f64Agree {op} : RelopTypeAgree .f64 (.f op)

@[rocq_alias iriswasm.be_typing]
inductive BeTyping : TContext → List BasicInstruction → FunctionType → Prop
  | const {C v} : BeTyping C [.const v] (.tf [] [typeof v])
  | unop {C t op} : UnopTypeAgree t op → BeTyping C [.unop t op] (.tf [t] [t])
  | binop {C t op} : BinopTypeAgree t op → BeTyping C [.binop t op] (.tf [t, t] [t])
  | testop {C t op} : isIntT t = true → BeTyping C [.testop t op] (.tf [t] [.i32])
  | relop {C t op} : RelopTypeAgree t op → BeTyping C [.relop t op] (.tf [t, t] [.i32])
  | convert {C t1 t2 sx} : t1 ≠ t2 → convertHelper sx t1 t2 = true →
      BeTyping C [.cvtop t1 .convert t2 sx] (.tf [t2] [t1])
  | reinterpret {C t1 t2} : t1 ≠ t2 → Nat.beq (lengthT t1) (lengthT t2) = true →
      BeTyping C [.cvtop t1 .reinterpret t2 none] (.tf [t2] [t1])
  | unreachable {C ts ts'} : BeTyping C [.unreachable] (.tf ts ts')
  | nop {C} : BeTyping C [.nop] (.tf [] [])
  | drop {C t} : BeTyping C [.drop] (.tf [t] [])
  | select {C t} : BeTyping C [.select] (.tf [t, t, .i32] [t])
  | block {C tn tm es} : BeTyping (updLabel C ([tm] ++ C.label)) es (.tf tn tm) →
      BeTyping C [.block (.tf tn tm) es] (.tf tn tm)
  | loop {C tn tm es} : BeTyping (updLabel C ([tn] ++ C.label)) es (.tf tn tm) →
      BeTyping C [.loop (.tf tn tm) es] (.tf tn tm)
  | ifWasm {C tn tm es1 es2} :
      BeTyping (updLabel C ([tm] ++ C.label)) es1 (.tf tn tm) →
      BeTyping (updLabel C ([tm] ++ C.label)) es2 (.tf tn tm) →
      BeTyping C [.if_ (.tf tn tm) es1 es2] (.tf (tn ++ [.i32]) tm)
  | br {C i t1s ts t2s} : i < C.label.length → plop2 C i ts = true →
      BeTyping C [.br i] (.tf (t1s ++ ts) t2s)
  | brIf {C i ts} : i < C.label.length → plop2 C i ts = true →
      BeTyping C [.brIf i] (.tf (ts ++ [.i32]) ts)
  | brTable {C i ins ts t1s t2s} :
      (ins ++ [i]).all (fun i => decide (i < C.label.length) && plop2 C i ts) = true →
      BeTyping C [.brTable ins i] (.tf (t1s ++ (ts ++ [.i32])) t2s)
  | return_ {C ts t1s t2s} : C.return_ = some ts → BeTyping C [.return_] (.tf (t1s ++ ts) t2s)
  | call {C i tf} : i < C.funcT.length → C.funcT[i]? = some tf → BeTyping C [.call i] tf
  | callIndirect {C i t1s t2s} : i < C.typesT.length → C.typesT[i]? = some (.tf t1s t2s) →
      C.table ≠ [] → BeTyping C [.callIndirect i] (.tf (t1s ++ [.i32]) t2s)
  | getLocal {C i t} : i < C.local_.length → C.local_[i]? = some t →
      BeTyping C [.getLocal i] (.tf [] [t])
  | setLocal {C i t} : i < C.local_.length → C.local_[i]? = some t →
      BeTyping C [.setLocal i] (.tf [t] [])
  | teeLocal {C i t} : i < C.local_.length → C.local_[i]? = some t →
      BeTyping C [.teeLocal i] (.tf [t] [t])
  | getGlobal {C i t} : i < C.global.length → (C.global[i]?).map GlobalType.t = some t →
      BeTyping C [.getGlobal i] (.tf [] [t])
  | setGlobal {C i g t} : i < C.global.length → C.global[i]? = some g → g.t = t →
      isMut g = true → BeTyping C [.setGlobal i] (.tf [t] [])
  | load {C a off tpSx t} : C.memory ≠ [] → loadStoreTBounds a (optionProjl tpSx) t = true →
      BeTyping C [.load t tpSx a off] (.tf [.i32] [t])
  | store {C a off tp t} : C.memory ≠ [] → loadStoreTBounds a tp t = true →
      BeTyping C [.store t tp a off] (.tf [.i32, t] [])
  | currentMemory {C} : C.memory ≠ [] → BeTyping C [.currentMemory] (.tf [] [.i32])
  | growMemory {C} : C.memory ≠ [] → BeTyping C [.growMemory] (.tf [.i32] [.i32])
  | empty {C} : BeTyping C [] (.tf [] [])
  | composition {C es e t1s t2s t3s} : BeTyping C es (.tf t1s t2s) →
      BeTyping C [e] (.tf t2s t3s) → BeTyping C (es ++ [e]) (.tf t1s t3s)
  | weakening {C es ts t1s t2s} : BeTyping C es (.tf t1s t2s) →
      BeTyping C es (.tf (ts ++ t1s) (ts ++ t2s))

@[rocq_alias iriswasm.upd_local]
def updLocal (C : TContext) (loc : List ValueType) : TContext := { C with local_ := loc }

@[rocq_alias iriswasm.upd_return]
def updReturn (C : TContext) (ret : Option (List ValueType)) : TContext := { C with return_ := ret }

@[rocq_alias iriswasm.upd_local_return]
def updLocalReturn (C : TContext) (loc : List ValueType) (ret : Option (List ValueType)) :
    TContext := { C with local_ := loc, return_ := ret }

@[rocq_alias iriswasm.upd_local_label_return]
def updLocalLabelReturn (C : TContext) (loc : List ValueType) (lab : List (List ValueType))
    (ret : Option (List ValueType)) : TContext :=
  { C with local_ := loc, label := lab, return_ := ret }

@[rocq_alias iriswasm.global_agree]
def globalAgree (g : Global) (tg : GlobalType) : Bool :=
  tg.mut_ == g.mut_ && tg.t == typeof g.val

@[rocq_alias iriswasm.globals_agree]
def globalsAgree (gs : List Global) (n : Nat) (tg : GlobalType) : Bool :=
  decide (n < gs.length) && ((gs[n]?).map (globalAgree · tg) == some true)

@[rocq_alias iriswasm.mem_typing]
def memTyping (m : Memory) (mt : MemoryType) : Bool :=
  decide (mt.min ≤ memSize m) && m.maxOpt == mt.max

@[rocq_alias iriswasm.memi_agree]
def memiAgree (ms : List Memory) (n : Nat) (memT : MemoryType) : Bool :=
  decide (n < ms.length) &&
  match ms[n]? with
  | some mem => memTyping mem memT
  | none => false

@[rocq_alias iriswasm.functions_agree]
def functionsAgree (fs : List FunctionClosure) (n : Nat) (f : FunctionType) : Bool :=
  decide (n < fs.length) && ((fs[n]?).map clType == some f)

/-- Coq writes `table_max_opt t <= lim_max` on `option N`; it elaborates through the ssreflect
coercions `isSome : option >-> bool` and `nat_of_bool`, i.e. it only says
"if the table has a max then so does the type". Reproduced literally. -/
@[rocq_alias iriswasm.tab_typing]
def tabTyping (t : Tableinst) (tt : TableType) : Bool :=
  decide (tt.limits.min ≤ tabSize t) &&
  decide ((if t.maxOpt.isSome then 1 else 0) ≤ (if tt.limits.max.isSome then 1 else 0))

@[rocq_alias iriswasm.tabi_agree]
def tabiAgree (ts : List Tableinst) (n : Nat) (tabT : TableType) : Bool :=
  decide (n < ts.length) &&
  match ts[n]? with
  | none => false
  | some x => tabTyping x tabT

@[rocq_alias iriswasm.inst_typing]
def instTyping (s : StoreRecord) (inst : Instance) (C : TContext) : Bool :=
  match inst, C with
  | ⟨ts, fs, tbs, ms, gs⟩, ⟨ts', tfs, tgs, tabsT, memsT, [], [], none⟩ =>
    decide (ts = ts') &&
    List.all2 (functionsAgree s.funcs) fs tfs &&
    List.all2 (globalsAgree s.globals) gs tgs &&
    List.all2 (tabiAgree s.tables) tbs tabsT &&
    List.all2 (memiAgree s.mems) ms memsT
  | _, _ => false

@[rocq_alias iriswasm.frame_typing]
inductive FrameTyping : StoreRecord → Frame → TContext → Prop
  | frameTyping {s i tvs C} {f : Frame} : instTyping s i C = true → f.inst = i →
      f.locs.map typeof = tvs → FrameTyping s f (updLocal C (C.local_ ++ tvs))

@[rocq_alias iriswasm.functions_agree_injective]
theorem functions_agree_injective {s i t t'} (h1 : functionsAgree s i t = true)
    (h2 : functionsAgree s i t' = true) : t = t' := by
  simp only [functionsAgree, Bool.and_eq_true, beq_iff_eq] at h1 h2
  rw [h1.2] at h2; exact Option.some.inj h2.2

@[rocq_alias iriswasm.cl_typing]
inductive ClTyping : StoreRecord → FunctionClosure → FunctionType → Prop
  | native {i s C C' ts t1s t2s es tf} : instTyping s i C = true → tf = .tf t1s t2s →
      C' = updLocalLabelReturn C (C.local_ ++ t1s ++ ts) ([t2s] ++ C.label) (some t2s) →
      BeTyping C' es (.tf [] t2s) → ClTyping s (.funcNative i tf ts es) (.tf t1s t2s)
  | host {s tf h} : ClTyping s (.funcHost tf h) tf

mutual
@[rocq_alias iriswasm.e_typing]
inductive ETyping : StoreRecord → TContext → List AdministrativeInstruction → FunctionType → Prop
  | a {s C bes tf} : BeTyping C bes tf → ETyping s C (toEList bes) tf
  | composition {s C es e t1s t2s t3s} : ETyping s C es (.tf t1s t2s) →
      ETyping s C [e] (.tf t2s t3s) → ETyping s C (es ++ [e]) (.tf t1s t3s)
  | weakening {s C es ts t1s t2s} : ETyping s C es (.tf t1s t2s) →
      ETyping s C es (.tf (ts ++ t1s) (ts ++ t2s))
  | trap {s C tf} : ETyping s C [.trap] tf
  | local {s C n f es ts} : STyping s (some ts) f es ts → ts.length = n →
      ETyping s C [.local n f es] (.tf [] ts)
  | invoke {s a C cl tf} : s.funcs[a]? = some cl → ClTyping s cl tf →
      ETyping s C [.invoke a] tf
  | label {s C e0s es ts t2s n} : ETyping s C e0s (.tf ts t2s) →
      ETyping s (updLabel C ([ts] ++ C.label)) es (.tf [] t2s) → ts.length = n →
      ETyping s C [.label n e0s es] (.tf [] t2s)
  | callHost {s C t1s t2s h vs} : vs.length = t1s.length →
      ETyping s C [.callHost (.tf t1s t2s) h vs] (.tf [] t2s)

@[rocq_alias iriswasm.s_typing]
inductive STyping : StoreRecord → Option (List ValueType) → Frame →
    List AdministrativeInstruction → List ValueType → Prop
  | sTyping {s f es rs ts C C0} : FrameTyping s f C0 → C = updReturn C0 rs →
      ETyping s C es (.tf [] ts) → (rs = some ts ∨ rs = none) → STyping s rs f es ts
end

#rocq_ignore iriswasm.e_typing_ind' "Lean generates mutual recursors"
#rocq_ignore iriswasm.s_typing_ind' "Lean generates mutual recursors"

@[rocq_alias iriswasm.cl_typing_self]
def ClTypingSelf (s : StoreRecord) (fc : FunctionClosure) : Prop := ClTyping s fc (clType fc)

@[rocq_alias iriswasm.cl_typing_unique]
theorem cl_typing_unique {s cl tf} (h : ClTyping s cl tf) : tf = clType cl := by
  cases h <;> simp_all [clType]

@[rocq_alias iriswasm.cl_type_check_single]
def ClTypeCheckSingle (s : StoreRecord) (f : FunctionClosure) : Prop := ∃ tf, ClTyping s f tf

@[rocq_alias iriswasm.tabcl_agree]
def TabclAgree (s : StoreRecord) (tclIndex : Option Nat) : Prop :=
  match tclIndex with
  | none => True
  | some n => n < s.funcs.length

@[rocq_alias iriswasm.tabsize_agree]
def TabsizeAgree (t : Tableinst) : Prop :=
  match t.maxOpt with
  | none => True
  | some n => tabSize t ≤ n

@[rocq_alias iriswasm.tab_agree]
def TabAgree (s : StoreRecord) (t : Tableinst) : Prop :=
  (∀ x ∈ t.data, TabclAgree s x) ∧ TabsizeAgree t

@[rocq_alias iriswasm.mem_agree]
def MemAgree (m : Memory) : Prop :=
  match m.maxOpt with
  | none => True
  | some n => memSize m ≤ n

@[rocq_alias iriswasm.store_typing]
def StoreTyping (s : StoreRecord) : Prop :=
  (∀ f ∈ s.funcs, ClTypeCheckSingle s f) ∧
  (∀ t ∈ s.tables, TabAgree s t) ∧
  (∀ m ∈ s.mems, MemAgree m)

@[rocq_alias iriswasm.config_typing]
inductive ConfigTyping : StoreRecord → Frame → List AdministrativeInstruction → List ValueType → Prop
  | configTyping {s f es ts} : StoreTyping s → STyping s none f es ts → ConfigTyping s f es ts

end Wasm
