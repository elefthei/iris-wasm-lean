import Wasm.Instantiation
import Wasm.TypeCheckerReflectsTyping

/-! Executable validation of modules and reflection to the declarative module judgment. -/

namespace Wasm

structure ModuleType where
  imports : List ExternT
  exports : List ExternT
  deriving DecidableEq, Repr

inductive ValidationError where
  | invalidImport | unknownFunctionType | invalidDefinition | unknownExport
  deriving DecidableEq, Repr

private def importType? (types : List FunctionType) (imp : ModuleImport) : Option ExternT :=
  match imp.desc with
  | .func i => types[i]?.map ExternT.func
  | .table t => if moduleTabTyping ⟨t⟩ then some (.tab t) else none
  | .mem m => if moduleMemTyping m then some (.mem m) else none
  | .global g => some (.glob g)

private def functionType? (types : List FunctionType) (f : ModuleFunc) : Option FunctionType :=
  match f.type with | .typeidx i => types[i]?

private def exportType? (c : TContext) (exp : ModuleExport) : Option ExternT :=
  match exp.desc with
  | .func (.funcidx i) => c.funcT[i]?.map ExternT.func
  | .table (.tableidx i) => c.table[i]?.map ExternT.tab
  | .mem (.memidx i) => c.memory[i]?.map ExternT.mem
  | .global (.globalidx i) => c.global[i]?.map ExternT.glob

private def checkBody (c : TContext) (f : ModuleFunc) : FunctionType → Bool
  | .tf args results => bETypeChecker
      { c with local_ := c.local_ ++ args ++ f.locals, label := results :: c.label,
               return_ := some results } f.body (.tf [] results)

private def checkGlobals : TContext → List ModuleGlob → Bool
  | _, [] => true
  | c, g :: gs => constExprs c g.init && bETypeChecker c g.init (.tf [] [g.type.t]) &&
      checkGlobals { c with global := c.global ++ [g.type] } gs

private instance (c : TContext) (e : ModuleElement) : Decidable (ModuleElemTyping c e) := by
  obtain ⟨⟨i⟩, es, is⟩ := e
  unfold ModuleElemTyping
  infer_instance

private instance (c : TContext) (d : ModuleData) : Decidable (ModuleDataTyping c d) := by
  obtain ⟨⟨i⟩, es, bytes⟩ := d
  dsimp only [ModuleDataTyping]
  cases c.memory[i]? <;> infer_instance

private def checkDefinitions (m : Module) (im : List ExternT) (fs : List FunctionType)
    (c : TContext) : Bool :=
  List.all2 (checkBody c) m.funcs fs && m.tables.all moduleTabTyping && m.mems.all moduleMemTyping &&
    checkGlobals (globalInitContext im) m.globals && m.elem.all (fun e => decide (ModuleElemTyping c e)) &&
    m.data.all (fun d => decide (ModuleDataTyping c d)) && predOption (moduleStartTyping c) m.start &&
    decide ((m.exports.map ModuleExport.name).Nodup)

/-- Validate the actual module, without running initializers or resolving imports in a store. -/
def validateModule (m : Module) : Except ValidationError ModuleType :=
  match m.imports.mapM (importType? m.types) with
  | none => .error .invalidImport
  | some im => match m.funcs.mapM (functionType? m.types) with
    | none => .error .unknownFunctionType
    | some fs =>
      let c := moduleContext m im fs (m.globals.map ModuleGlob.type)
      if checkDefinitions m im fs c then
        match m.exports.mapM (exportType? c) with
        | none => .error .unknownExport
        | some ex => .ok ⟨im, ex⟩
      else .error .invalidDefinition

private theorem mapM_iff {α β : Type} (f : α → Option β) (R : α → β → Prop)
    (spec : ∀ a b, f a = some b ↔ R a b) (xs : List α) (ys : List β) :
    xs.mapM f = some ys ↔ List.Forall₂ R xs ys := by
  constructor
  · induction xs generalizing ys with
    | nil => intro h; cases h; exact .nil
    | cons x xs ih =>
      intro h
      rw [List.mapM_cons] at h
      cases hx : f x <;> cases ht : xs.mapM f <;> simp [hx, ht] at h
      subst ys; exact .cons ((spec ..).1 hx) (ih _ ht)
  · intro h; induction h with
    | nil => rfl
    | cons h _ ih => simp [List.mapM_cons, (spec ..).2 h, ih]

private theorem importType_spec (c : TContext) (imp : ModuleImport) (e : ExternT) :
    importType? c.typesT imp = some e ↔ moduleImportTyping c imp.desc e = true := by
  rcases imp with ⟨mod, name, d⟩
  cases d with
  | func i =>
    cases h : c.typesT[i]? with
    | none => cases e <;> simp [importType?, moduleImportTyping, h]
    | some t =>
      have hi := (List.getElem?_eq_some_iff.mp h).1
      cases e <;> simp [importType?, moduleImportTyping, hi, eq_comm]
  | table t => cases e <;> simp [importType?, moduleImportTyping, and_comm]
  | mem m => cases e <;> simp [importType?, moduleImportTyping, and_comm]
  | global g => cases e <;> simp [importType?, moduleImportTyping]

private theorem exportType_spec (c : TContext) (exp : ModuleExport) (e : ExternT) :
    exportType? c exp = some e ↔ moduleExportTyping c exp.desc e = true := by
  rcases exp with ⟨_, (⟨i⟩ | ⟨i⟩ | ⟨i⟩ | ⟨i⟩)⟩
  all_goals
    cases e <;> simp [exportType?, moduleExportTyping, Option.map_eq_some_iff]
    split <;> rename_i h <;> first
      | obtain ⟨hi, hv⟩ := List.getElem?_eq_some_iff.mp h; simp [hi, hv, eq_comm]
      | simp [h]

private theorem func_spec (c : TContext) (f : ModuleFunc) (tf : FunctionType) :
    ModuleFuncTyping c f tf ↔ functionType? c.typesT f = some tf ∧ checkBody c f tf = true := by
  rcases f with ⟨⟨i⟩, locs, body⟩; cases tf
  simp only [ModuleFuncTyping, functionType?, checkBody, b_e_type_checker_reflects_typing]

private theorem globals_spec (c : TContext) (gs : List ModuleGlob) :
    checkGlobals c gs = true ↔ ModuleGlobalsTyping c gs (gs.map ModuleGlob.type) := by
  induction gs generalizing c with
  | nil => exact ⟨fun _ => .nil, fun _ => rfl⟩
  | cons g gs ih =>
    simp only [checkGlobals, Bool.and_eq_true, b_e_type_checker_reflects_typing, ih, List.map_cons]
    exact ⟨fun ⟨⟨hc, hb⟩, hs⟩ => .cons ⟨hc, rfl, hb⟩ hs, fun h => by
      cases h with | cons h hs => exact ⟨⟨h.1, h.2.2⟩, hs⟩⟩

private theorem funcs_spec (c : TContext) (xs : List ModuleFunc) (ys : List FunctionType) :
    List.Forall₂ (ModuleFuncTyping c) xs ys ↔
      xs.mapM (functionType? c.typesT) = some ys ∧ List.all2 (checkBody c) xs ys = true := by
  rw [mapM_iff _ _ (fun _ _ => Iff.rfl), List.all2_Forall₂]
  constructor
  · intro h; induction h with
    | nil => exact ⟨.nil, .nil⟩
    | cons h _ ih => exact ⟨.cons ((func_spec ..).1 h).1 ih.1, .cons ((func_spec ..).1 h).2 ih.2⟩
  · rintro ⟨h, hs⟩; induction h with
    | nil => exact .nil
    | cons h _ ih => cases hs with | cons hb ht => exact .cons ((func_spec ..).2 ⟨h, hb⟩) (ih ht)

private theorem fields_spec (m : Module) (im ex : List ExternT) :
    ModuleTyping m im ex ↔ m.imports.mapM (importType? m.types) = some im ∧
      ∃ fs, let c := moduleContext m im fs (m.globals.map ModuleGlob.type)
        m.funcs.mapM (functionType? m.types) = some fs ∧ checkDefinitions m im fs c = true ∧
        m.exports.mapM (exportType? c) = some ex := by
  constructor
  · rintro ⟨fs, gs, hf, ht, hm, hg, hel, hd, hs, hi, hn, he⟩
    cases hg.types_eq
    let c := moduleContext m im fs (m.globals.map ModuleGlob.type)
    have ⟨hty, hb⟩ := (funcs_spec ..).1 hf
    refine ⟨(mapM_iff _ _ (importType_spec c) ..).2 hi, fs, hty, ?_,
      (mapM_iff _ _ (exportType_spec c) ..).2 he⟩
    simp only [checkDefinitions, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, globals_spec]
    exact ⟨⟨⟨⟨⟨⟨⟨hb, List.all_eq_true.mp ht⟩, List.all_eq_true.mp hm⟩, hg⟩, hel⟩, hd⟩, hs⟩, hn⟩
  · rintro ⟨hi, fs, hf, valid, he⟩
    let c := moduleContext m im fs (m.globals.map ModuleGlob.type)
    simp only [checkDefinitions, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, globals_spec]
      at valid
    obtain ⟨⟨⟨⟨⟨⟨⟨hb, ht⟩, hm⟩, hg⟩, hel⟩, hd⟩, hs⟩, hn⟩ := valid
    exact ⟨fs, _, (funcs_spec c ..).2 ⟨hf, hb⟩, List.all_eq_true.mpr ht,
      List.all_eq_true.mpr hm, hg, hel, hd, hs, (mapM_iff _ _ (importType_spec c) ..).1 hi, hn,
      (mapM_iff _ _ (exportType_spec c) ..).1 he⟩

/-- Success computes exactly the ordered import and export types of the declarative judgment. -/
theorem validateModule_iff (m : Module) (mt : ModuleType) :
    validateModule m = .ok mt ↔ ModuleTyping m mt.imports mt.exports := by
  obtain ⟨im, ex⟩ := mt
  rw [fields_spec]
  unfold validateModule
  split <;> rename_i hi <;> simp [hi]
  split <;> rename_i hf <;> simp [hf]
  split <;> rename_i hd
  · split <;> rename_i he <;> simp_all <;> grind
  · grind

end Wasm
