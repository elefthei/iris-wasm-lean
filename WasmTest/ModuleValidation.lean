import Wasm.ModuleValidation

namespace WasmTest.ModuleValidation

open Wasm

private def emptyModule : Module := ⟨[], [], [], [], [], [], [], none, [], []⟩
private def i32Global : GlobalType := ⟨.immut, .i32⟩
private def resultTy : FunctionType := .tf [] [.i32]

/-- Imported and earlier defined globals share a single ordered index space. -/
private def linked : Module := { emptyModule with
  types := [resultTy]
  imports := [⟨[], [105], .global i32Global⟩, ⟨[], [102], .func 0⟩]
  globals := [⟨i32Global, [.getGlobal 0]⟩, ⟨i32Global, [.getGlobal 1]⟩]
  funcs := [⟨.typeidx 0, [], [.getGlobal 2]⟩]
  exports := [⟨[103], .global (.globalidx 2)⟩, ⟨[102], .func (.funcidx 1)⟩] }

private def interface : ModuleType :=
  ⟨[.glob i32Global, .func resultTy], [.glob i32Global, .func resultTy]⟩

theorem declaredInterface : ModuleTyping linked interface.imports interface.exports :=
  (validateModule_iff linked interface).mp rfl

/-- The raw reduction's grow-failure alternative does not supply a memory to validation. -/
theorem missingMemoryGrow : validateModule
    { emptyModule with
      types := [resultTy]
      funcs := [⟨.typeidx 0, [], [.const (.int32 1), .growMemory 0]⟩] } =
    .error .invalidDefinition := rfl

theorem unknownTypeIndex : validateModule
    { emptyModule with funcs := [⟨.typeidx 0, [], []⟩] } = .error .unknownFunctionType := rfl

theorem unknownImportType : validateModule
    { emptyModule with imports := [⟨[], [], .func 0⟩] } = .error .invalidImport := rfl

theorem unknownExport : validateModule
    { emptyModule with exports := [⟨[], .global (.globalidx 0)⟩] } = .error .unknownExport := rfl

theorem duplicateNames : validateModule
    { linked with exports := [⟨[], .global (.globalidx 0)⟩, ⟨[], .func (.funcidx 0)⟩] } =
    .error .invalidDefinition := rfl

theorem selfReferentialGlobal : validateModule
    { emptyModule with globals := [⟨i32Global, [.getGlobal 0]⟩] } = .error .invalidDefinition := rfl

theorem invertedLimits : validateModule
    { emptyModule with mems := [⟨.i32, ⟨2, some 1⟩⟩] } = .error .invalidDefinition := rfl

theorem oversizedMinimum : validateModule
    { emptyModule with mems := [⟨.i32, ⟨65537, none⟩⟩] } = .error .invalidDefinition := rfl

theorem oversizedTableImport : validateModule
    { emptyModule with imports := [⟨[], [], .table ⟨⟨2^32, none⟩, .funcref⟩⟩] } =
    .error .invalidImport := rfl

private def tableWithLimit (n : Option Nat) : Tableinst := ⟨RunTable.uniform 2 none, n⟩
private def memoryWithLimit (n : Option Nat) : Memory :=
  ⟨MemoryList.memMake 0 pageSize, ⟨.i32, ⟨1, n⟩⟩⟩

theorem bounded_table_import :
    tabTyping (tableWithLimit (some 3)) ⟨⟨2, none⟩, .funcref⟩ = true ∧
    tabTyping (tableWithLimit none) ⟨⟨2, some 4⟩, .funcref⟩ = false ∧
    tabTyping (tableWithLimit (some 5)) ⟨⟨2, some 4⟩, .funcref⟩ = false := by decide

theorem narrower_memory_import :
    memTyping (memoryWithLimit (some 3)) ⟨.i32, ⟨1, some 4⟩⟩ = true ∧
    memTyping (memoryWithLimit none) ⟨.i32, ⟨1, some 4⟩⟩ = false ∧
    memTyping (memoryWithLimit (some 3)) ⟨.i32, ⟨2, none⟩⟩ = false ∧
    memTyping (memoryWithLimit (some 3)) ⟨.i64, ⟨1, some 4⟩⟩ = false := by decide

private def arithmetic (t : ValueType) (a : BasicInstruction) (b c d : Value) : Expr :=
  [a, .const b, .binop t (.i .sub), .const c, .binop t (.i .mul), .const d, .binop t (.i .add)]

private def offset : Expr := arithmetic .i32 (.getGlobal 0) (.int32 7) (.int32 3) (.int32 8)

private def extended : Module := { emptyModule with
  imports := [⟨[], [], .global i32Global⟩]
  globals := [⟨⟨.immut, .i64⟩, arithmetic .i64 (.const (.int64 3)) (.int64 7) (.int64 4) (.int64 20)⟩]
  tables := [⟨⟨⟨3, none⟩, .funcref⟩⟩]
  mems := [⟨.i32, ⟨1, none⟩⟩]
  elem := [⟨.tableidx 0, offset, []⟩]
  data := [⟨.memidx 0, offset, [12]⟩] }

theorem extendedValidated : validateModule extended = .ok ⟨[.glob i32Global], []⟩ := rfl

theorem mutableOffsetRejected : validateModule
    { extended with imports := [⟨[], [], .global ⟨.mut, .i32⟩⟩] } = .error .invalidDefinition := rfl

theorem divisionInitializerRejected : validateModule
    { emptyModule with globals := [⟨i32Global,
      [.const (.int32 4), .const (.int32 2), .binop .i32 (.i (.div .u))]⟩] } =
    .error .invalidDefinition := rfl

theorem mixedWidthInitializerRejected : validateModule
    { emptyModule with globals := [⟨i32Global,
      [.const (.int32 4), .const (.int64 2), .binop .i32 (.i .add)]⟩] } =
    .error .invalidDefinition := rfl

private theorem withSuffix {s : StoreRecord} {f : Frame} {es es' : Expr}
    (r : Reduce s f (toEList es) s f (toEList es')) (tail : Expr) :
    ReduceTuple (s, f, toEList (es ++ tail)) (s, f, toEList (es' ++ tail)) :=
  .label _ _ 0 (.base [] (toEList tail)) r
    (by simp [lfilled, lfill, toEList, constList]) (by simp [lfilled, lfill, toEList, constList])

private theorem arithmeticSteps {s : StoreRecord} {f : Frame} {t : ValueType} {a b c d x y z : Value}
    (sub : ReduceSimple (toEList [.const a, .const b, .binop t (.i .sub)]) [.basic (.const x)])
    (mul : ReduceSimple (toEList [.const x, .const c, .binop t (.i .mul)]) [.basic (.const y)])
    (add : ReduceSimple (toEList [.const y, .const d, .binop t (.i .add)]) [.basic (.const z)]) :
    ReduceTrans (s, f, toEList (arithmetic t (.const a) b c d)) (s, f, [.basic (.const z)]) :=
  .head (withSuffix (es := [.const a, .const b, .binop t (.i .sub)]) (es' := [.const x])
    (.simple sub) [.const c, .binop t (.i .mul), .const d, .binop t (.i .add)])
  (.head (withSuffix (es := [.const x, .const c, .binop t (.i .mul)]) (es' := [.const y])
    (.simple mul) [.const d, .binop t (.i .add)])
  (.single (Reduce.simple add)))

/-- The initialization premises run the same reductions, including the global read and wraparound. -/
theorem extendedInitializers (s : StoreRecord) (inst : Instance)
    (h : sglobVal s inst 0 = some (.int32 5)) :
    InstantiateGlobals inst s extended [.int64 4] ∧
      InstantiateElem inst s extended [2] ∧ InstantiateData inst s extended [.i32 2] := by
  have off : ReduceTrans (s, ⟨[], inst⟩, toEList offset) (s, ⟨[], inst⟩, [.basic (.const (.int32 2))]) :=
    .head (withSuffix (es := [.getGlobal 0]) (es' := [.const (.int32 5)]) (.getGlobal h)
      [.const (.int32 7), .binop .i32 (.i .sub), .const (.int32 3), .binop .i32 (.i .mul),
       .const (.int32 8), .binop .i32 (.i .add)])
      (by apply arithmeticSteps (x := .int32 (-2)) (y := .int32 (-6))
          all_goals exact .binopSuccess rfl rfl rfl rfl)
  refine ⟨.cons ?_ .nil,
    .cons off .nil, .cons off .nil⟩
  apply arithmeticSteps (x := .int64 (-4)) (y := .int64 (-16))
  all_goals exact .binopSuccess rfl rfl rfl rfl

end WasmTest.ModuleValidation
