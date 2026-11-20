/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import Wasm.Instantiation
import Wasm.TypePreservation
import Wasm.TypeProgress
import Wasm.StdppAux

/-! Port of `theories/iris/instantiation/instantiation_properties.v`. -/

namespace IrisWasm

open Wasm

/-! ### Section `module_typing_det` -/

private theorem forall2_det {A B : Type} {R1 R2 : A → B → Prop} :
    ∀ {l : List A} {l1 l2 : List B}, Wasm.List.Forall₂ R1 l l1 → Wasm.List.Forall₂ R2 l l2 →
      (∀ a ∈ l, ∀ b1 b2, R1 a b1 → R2 a b2 → b1 = b2) → l1 = l2
  | _, _, _, .nil, .nil, _ => rfl
  | _, _, _, .cons h1 t1, .cons h2 t2, hR => by
    rw [hR _ (List.mem_cons_self ..) _ _ h1 h2,
      forall2_det t1 t2 fun a ha => hR a (List.mem_cons_of_mem _ ha)]

private theorem forall2_mem_left {A B : Type} {R : A → B → Prop} :
    ∀ {l : List A} {l' : List B}, Wasm.List.Forall₂ R l l' → ∀ a ∈ l, ∃ b, R a b
  | _, _, .cons h t, a, ha => by
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨_, h⟩
    · exact forall2_mem_left t a ha

private theorem import_typing_det {c1 c2 : TContext} {d : ImportDesc} {e1 e2 : ExternT}
    (h1 : moduleImportTyping c1 d e1 = true) (h2 : moduleImportTyping c2 d e2 = true)
    (ht : c1.typesT = c2.typesT) : e1 = e2 := by
  cases d <;> cases e1 <;> cases e2 <;>
    simp only [moduleImportTyping, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true,
      ExternT.func.injEq, ExternT.tab.injEq, ExternT.mem.injEq, ExternT.glob.injEq] at h1 h2 ⊢
  case func.func.func n _ _ =>
    rw [ht] at h1
    obtain ⟨_, h1⟩ := h1; obtain ⟨_, h2⟩ := h2
    generalize c2.typesT[n]? = o at h1 h2
    cases o <;> simp_all
  all_goals simp_all

private theorem export_typing_det {c : TContext} {d : ModuleExportDesc} {e1 e2 : ExternT}
    (h1 : moduleExportTyping c d e1 = true) (h2 : moduleExportTyping c d e2 = true) : e1 = e2 := by
  rcases d with ⟨i⟩ | ⟨i⟩ | ⟨i⟩ | ⟨i⟩ <;> cases e1 <;> cases e2 <;>
    simp only [moduleExportTyping, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true,
      ExternT.func.injEq, ExternT.tab.injEq, ExternT.mem.injEq, ExternT.glob.injEq] at h1 h2 ⊢
  case func.func.func =>
    obtain ⟨_, h1⟩ := h1; obtain ⟨_, h2⟩ := h2
    generalize c.funcT[i.1]? = o at h1 h2
    cases o <;> simp_all
  case table.tab.tab =>
    obtain ⟨_, h1⟩ := h1; obtain ⟨_, h2⟩ := h2
    generalize c.table[i.1]? = o at h1 h2
    cases o <;> simp_all
  case mem.mem.mem =>
    obtain ⟨_, h1⟩ := h1; obtain ⟨_, h2⟩ := h2
    generalize c.memory[i.1]? = o at h1 h2
    cases o <;> simp_all
  case global.glob.glob =>
    obtain ⟨_, h1⟩ := h1; obtain ⟨_, h2⟩ := h2
    generalize c.global[i.1]? = o at h1 h2
    cases o <;> simp_all

private theorem func_typing_det {c1 c2 : TContext} {m : ModuleFunc} {tf1 tf2 : FunctionType}
    (h1 : ModuleFuncTyping c1 m tf1) (h2 : ModuleFuncTyping c2 m tf2)
    (ht : c1.typesT = c2.typesT) : tf1 = tf2 := by
  rcases m with ⟨⟨i⟩, _, _⟩
  cases tf1; cases tf2
  obtain ⟨_, h1, _⟩ := h1
  obtain ⟨_, h2, _⟩ := h2
  simp only [decide_eq_true_eq] at h1 h2
  rw [← h1, ← h2, ht]

@[rocq_alias iriswasm.module_typing_det_import_aux]
theorem module_typing_det_import_aux {m : Module} {it1 et1 it2 et2 : List ExternT}
    (h1 : ModuleTyping m it1 et1) (h2 : ModuleTyping m it2 et2) : it1 = it2 := by
  obtain ⟨fts1, gts1, h1⟩ := h1
  obtain ⟨fts2, gts2, h2⟩ := h2
  rcases m with ⟨tfs, fs, ts, ms, gs, els, ds, iOpt, imps, exps⟩
  obtain ⟨-, -, -, -, -, -, -, hi1, -⟩ := h1
  obtain ⟨-, -, -, -, -, -, -, hi2, -⟩ := h2
  exact forall2_det hi1 hi2 fun _ _ _ _ a b => import_typing_det a b rfl

@[rocq_alias iriswasm.module_typing_det]
theorem module_typing_det {m : Module} {it1 et1 it2 et2 : List ExternT}
    (h1 : ModuleTyping m it1 et1) (h2 : ModuleTyping m it2 et2) : (it1, et1) = (it2, et2) := by
  have hi := module_typing_det_import_aux h1 h2
  subst hi
  obtain ⟨fts1, gts1, h1⟩ := h1
  obtain ⟨fts2, gts2, h2⟩ := h2
  rcases m with ⟨tfs, fs, ts, ms, gs, els, ds, iOpt, imps, exps⟩
  obtain ⟨hf1, -, -, hg1, -, -, -, -, he1⟩ := h1
  obtain ⟨hf2, -, -, hg2, -, -, -, -, he2⟩ := h2
  obtain rfl := forall2_det hf1 hf2 fun _ _ _ _ a b => func_typing_det a b rfl
  obtain rfl := forall2_det hg1 hg2 fun _ _ _ _ a b => a.2.1.trans b.2.1.symm
  rw [forall2_det he1 he2 fun _ _ _ _ a b => export_typing_det a b]

@[rocq_alias iriswasm.exp_default]
def expDefault : ModuleExportDesc := .func (.funcidx 0)

/-- stdpp `<[n := v]> l` on lists is `List.set`. -/
@[rocq_alias iriswasm.insert_at_insert]
theorem insert_at_insert {T : Type} (v : T) (n : Nat) (l : List T) (h : n < l.length) :
    insertAt v n l = l.set n v := by
  simp [insertAt, List.set_eq_take_append_cons_drop, h]

/-! ### Section `Instantiation_properties` -/

@[rocq_alias iriswasm.ext_func_addrs]
def extFuncAddrs : List ModuleExportDesc → List Nat :=
  List.map (fun | .funcidx i => i) ∘ extFuncs

@[rocq_alias iriswasm.ext_tab_addrs]
def extTabAddrs : List ModuleExportDesc → List Nat :=
  List.map (fun | .tableidx i => i) ∘ extTabs

@[rocq_alias iriswasm.ext_mem_addrs]
def extMemAddrs : List ModuleExportDesc → List Nat :=
  List.map (fun | .memidx i => i) ∘ extMems

@[rocq_alias iriswasm.ext_glob_addrs]
def extGlobAddrs : List ModuleExportDesc → List Nat :=
  List.map (fun | .globalidx i => i) ∘ extGlobs

@[rocq_alias iriswasm.ext_func_addrs_aux]
theorem ext_func_addrs_aux (l : List ModuleExportDesc) :
    extFuncAddrs l = (extFuncs l).map (fun | .funcidx i => i) := rfl

@[rocq_alias iriswasm.ext_tab_addrs_aux]
theorem ext_tab_addrs_aux (l : List ModuleExportDesc) :
    extTabAddrs l = (extTabs l).map (fun | .tableidx i => i) := rfl

@[rocq_alias iriswasm.ext_mem_addrs_aux]
theorem ext_mem_addrs_aux (l : List ModuleExportDesc) :
    extMemAddrs l = (extMems l).map (fun | .memidx i => i) := rfl

@[rocq_alias iriswasm.ext_glob_addrs_aux]
theorem ext_glob_addrs_aux (l : List ModuleExportDesc) :
    extGlobAddrs l = (extGlobs l).map (fun | .globalidx i => i) := rfl

/-- Counts of each kind of import (Coq `pmap` → `List.filterMap`). -/
@[rocq_alias iriswasm.get_import_func_count]
def getImportFuncCount (m : Module) : Nat :=
  (m.imports.filterMap fun x => match x.desc with | .func id => some id | _ => none).length

@[rocq_alias iriswasm.get_import_table_count]
def getImportTableCount (m : Module) : Nat :=
  (m.imports.filterMap fun x => match x.desc with | .table id => some id | _ => none).length

@[rocq_alias iriswasm.get_import_mem_count]
def getImportMemCount (m : Module) : Nat :=
  (m.imports.filterMap fun x => match x.desc with | .mem id => some id | _ => none).length

@[rocq_alias iriswasm.get_import_global_count]
def getImportGlobalCount (m : Module) : Nat :=
  (m.imports.filterMap fun x => match x.desc with | .global id => some id | _ => none).length

@[rocq_alias iriswasm.ext_funcs_lookup_exist]
theorem ext_funcs_lookup_exist (modexps : List ModuleExportDesc) (n : Nat) (fn : Funcidx)
    (h : (extFuncs modexps)[n]? = some fn) :
    ∃ k : Nat, modexps[k]? = some (ModuleExportDesc.func fn) := by
  obtain ⟨x, hx, hfx⟩ := List.mem_filterMap.1 (List.mem_of_getElem? h)
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hx
  cases x <;> simp at hfx
  subst hfx; exact ⟨k, hk⟩

@[rocq_alias iriswasm.ext_tabs_lookup_exist]
theorem ext_tabs_lookup_exist (modexps : List ModuleExportDesc) (n : Nat) (tn : Tableidx)
    (h : (extTabs modexps)[n]? = some tn) :
    ∃ k : Nat, modexps[k]? = some (ModuleExportDesc.table tn) := by
  obtain ⟨x, hx, hfx⟩ := List.mem_filterMap.1 (List.mem_of_getElem? h)
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hx
  cases x <;> simp at hfx
  subst hfx; exact ⟨k, hk⟩

@[rocq_alias iriswasm.ext_mems_lookup_exist]
theorem ext_mems_lookup_exist (modexps : List ModuleExportDesc) (n : Nat) (mn : Memidx)
    (h : (extMems modexps)[n]? = some mn) :
    ∃ k : Nat, modexps[k]? = some (ModuleExportDesc.mem mn) := by
  obtain ⟨x, hx, hfx⟩ := List.mem_filterMap.1 (List.mem_of_getElem? h)
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hx
  cases x <;> simp at hfx
  subst hfx; exact ⟨k, hk⟩

@[rocq_alias iriswasm.ext_globs_lookup_exist]
theorem ext_globs_lookup_exist (modexps : List ModuleExportDesc) (n : Nat) (fn : Globalidx)
    (h : (extGlobs modexps)[n]? = some fn) :
    ∃ k : Nat, modexps[k]? = some (ModuleExportDesc.global fn) := by
  obtain ⟨x, hx, hfx⟩ := List.mem_filterMap.1 (List.mem_of_getElem? h)
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hx
  cases x <;> simp at hfx
  subst hfx; exact ⟨k, hk⟩

@[rocq_alias iriswasm.ext_funcs_lookup_exist_inv]
theorem ext_funcs_lookup_exist_inv (modexps : List ModuleExportDesc) (n : Nat) (idx : Funcidx)
    (h : modexps[n]? = some (.func idx)) : ∃ k : Nat, (extFuncs modexps)[k]? = some idx := by
  exact List.mem_iff_getElem?.1 (List.mem_filterMap.2 ⟨_, List.mem_of_getElem? h, rfl⟩)

@[rocq_alias iriswasm.ext_tabs_lookup_exist_inv]
theorem ext_tabs_lookup_exist_inv (modexps : List ModuleExportDesc) (n : Nat) (idx : Tableidx)
    (h : modexps[n]? = some (.table idx)) : ∃ k : Nat, (extTabs modexps)[k]? = some idx := by
  exact List.mem_iff_getElem?.1 (List.mem_filterMap.2 ⟨_, List.mem_of_getElem? h, rfl⟩)

@[rocq_alias iriswasm.ext_mems_lookup_exist_inv]
theorem ext_mems_lookup_exist_inv (modexps : List ModuleExportDesc) (n : Nat) (idx : Memidx)
    (h : modexps[n]? = some (.mem idx)) : ∃ k : Nat, (extMems modexps)[k]? = some idx := by
  exact List.mem_iff_getElem?.1 (List.mem_filterMap.2 ⟨_, List.mem_of_getElem? h, rfl⟩)

@[rocq_alias iriswasm.ext_globs_lookup_exist_inv]
theorem ext_globs_lookup_exist_inv (modexps : List ModuleExportDesc) (n : Nat) (idx : Globalidx)
    (h : modexps[n]? = some (.global idx)) : ∃ k : Nat, (extGlobs modexps)[k]? = some idx := by
  exact List.mem_iff_getElem?.1 (List.mem_filterMap.2 ⟨_, List.mem_of_getElem? h, rfl⟩)

@[rocq_alias iriswasm.gen_func_instance]
def genFuncInstance (mf : ModuleFunc) (inst : Instance) : FunctionClosure :=
  let ft := inst.types.getD (match mf.type with | .typeidx n => n) (.tf [] [])
  .funcNative inst ft mf.locals mf.body

private theorem genIndex_eq_range' (n l : Nat) : genIndex n l = List.range' n l := by
  apply List.ext_getElem <;> simp [genIndex]; intros; omega

private theorem allocXs_foldl {A B : Type} (f : StoreRecord → A → StoreRecord × B) (xs : List A)
    (s : StoreRecord) (ys : List B) :
    xs.foldl (fun (p : StoreRecord × List B) x => ((f p.1 x).1, (f p.1 x).2 :: p.2)) (s, ys) =
      ((xs.foldl (fun (p : StoreRecord × List B) x => ((f p.1 x).1, (f p.1 x).2 :: p.2)) (s, [])).1,
       (xs.foldl (fun (p : StoreRecord × List B) x => ((f p.1 x).1, (f p.1 x).2 :: p.2)) (s, [])).2
         ++ ys) := by
  induction xs generalizing s ys with
  | nil => simp
  | cons x xs ih => simp only [List.foldl_cons]; rw [ih, ih (ys := [_])]; simp

private theorem allocXs_cons {A B : Type} (f : StoreRecord → A → StoreRecord × B)
    (s : StoreRecord) (x : A) (xs : List A) :
    allocXs f s (x :: xs) =
      ((allocXs f (f s x).1 xs).1, (f s x).2 :: (allocXs f (f s x).1 xs).2) := by
  have e : ∀ s xs, allocXs f s xs =
      ((xs.foldl (fun (p : StoreRecord × List B) x => ((f p.1 x).1, (f p.1 x).2 :: p.2)) (s, [])).1,
       (xs.foldl (fun (p : StoreRecord × List B) x => ((f p.1 x).1, (f p.1 x).2 :: p.2))
         (s, [])).2.reverse) := by
    intro s xs; simp only [allocXs]
  rw [e, e, List.foldl_cons, allocXs_foldl]; simp

@[rocq_alias iriswasm.alloc_func_gen_index]
theorem alloc_func_gen_index {modfuncs : List ModuleFunc} {ws : StoreRecord} {inst : Instance}
    {ws' : StoreRecord} {l : List Funcidx} (h : allocFuncs ws modfuncs inst = (ws', l)) :
    l.map (fun | .funcidx i => i) = genIndex ws.funcs.length modfuncs.length ∧
    ws'.funcs = ws.funcs ++ modfuncs.map (fun mf => genFuncInstance mf inst) ∧
    ws.tables = ws'.tables ∧ ws.mems = ws'.mems ∧ ws.globals = ws'.globals := by
  induction modfuncs generalizing ws l with
  | nil => cases h; simp [genIndex]
  | cons x xs ih =>
    unfold allocFuncs at h ih
    rw [allocXs_cons] at h
    have hs := congrArg Prod.fst h
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih (ws := (allocFunc ws x inst).1)
      (l := (allocXs (fun s mF => allocFunc s mF inst) (allocFunc ws x inst).1 xs).2)
      (Prod.ext hs rfl)
    generalize allocXs (fun s mF => allocFunc s mF inst) (allocFunc ws x inst).1 xs = r at h h1
    cases h
    simp only [allocFunc, addFunc] at h1 h2 h3 h4 h5 ⊢
    refine ⟨?_, ?_, h3, h4, h5⟩
    · simp [h1, genIndex_eq_range', List.range'_succ]
    · simp [h2, genFuncInstance]

@[rocq_alias iriswasm.alloc_tab_gen_index]
theorem alloc_tab_gen_index {modtabtypes : List TableType} {ws ws' : StoreRecord}
    {l : List Tableidx} (h : allocTabs ws modtabtypes = (ws', l)) :
    l.map (fun | .tableidx i => i) = genIndex ws.tables.length modtabtypes.length ∧
    ws'.tables = ws.tables ++ modtabtypes.map (fun tt =>
      ({ data := List.replicate tt.limits.min none, maxOpt := tt.limits.max } : Tableinst)) ∧
    ws.funcs = ws'.funcs ∧ ws.mems = ws'.mems ∧ ws.globals = ws'.globals := by
  induction modtabtypes generalizing ws l with
  | nil => cases h; simp [genIndex]
  | cons x xs ih =>
    unfold allocTabs at h ih
    rw [allocXs_cons] at h
    have hs := congrArg Prod.fst h
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih (ws := (allocTab ws x).1)
      (l := (allocXs allocTab (allocTab ws x).1 xs).2) (Prod.ext hs rfl)
    generalize allocXs allocTab (allocTab ws x).1 xs = r at h h1
    cases h
    simp only [allocTab, addTable] at h1 h2 h3 h4 h5 ⊢
    refine ⟨?_, ?_, h3, h4, h5⟩
    · simp [h1, genIndex_eq_range', List.range'_succ]
    · simp [h2]

@[rocq_alias iriswasm.alloc_mem_gen_index]
theorem alloc_mem_gen_index {modmemtypes : List MemoryType} {ws ws' : StoreRecord}
    {l : List Memidx} (h : allocMems ws modmemtypes = (ws', l)) :
    l.map (fun | .memidx i => i) = genIndex ws.mems.length modmemtypes.length ∧
    ws'.mems = ws.mems ++ modmemtypes.map (fun lim =>
      ({ data := MemoryList.memMake 0 (pageSize * lim.min), maxOpt := lim.max } : Memory)) ∧
    ws.funcs = ws'.funcs ∧ ws.tables = ws'.tables ∧ ws.globals = ws'.globals := by
  induction modmemtypes generalizing ws l with
  | nil => cases h; simp [genIndex]
  | cons x xs ih =>
    unfold allocMems at h ih
    rw [allocXs_cons] at h
    have hs := congrArg Prod.fst h
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih (ws := (allocMem ws x).1)
      (l := (allocXs allocMem (allocMem ws x).1 xs).2) (Prod.ext hs rfl)
    generalize allocXs allocMem (allocMem ws x).1 xs = r at h h1
    cases h
    simp only [allocMem, addMem] at h1 h2 h3 h4 h5 ⊢
    refine ⟨?_, ?_, h3, h4, h5⟩
    · simp [h1, genIndex_eq_range', List.range'_succ]
    · simp [h2, memMk]

@[rocq_alias iriswasm.alloc_glob_gen_index]
theorem alloc_glob_gen_index {modglobs : List ModuleGlob} {ws : StoreRecord} {g_inits : List Value}
    {ws' : StoreRecord} {l : List Globalidx} (hlen : g_inits.length = modglobs.length)
    (h : allocGlobs ws modglobs g_inits = (ws', l)) :
    l.map (fun | .globalidx i => i) = genIndex ws.globals.length modglobs.length ∧
    ws'.globals = ws.globals ++ (modglobs.zip g_inits).map (fun (mg, v) =>
      ({ mut_ := mg.type.mut_, val := v } : Global)) ∧
    ws.funcs = ws'.funcs ∧ ws.tables = ws'.tables ∧ ws.mems = ws'.mems := by
  induction modglobs generalizing ws l g_inits with
  | nil => cases h; simp [genIndex]
  | cons x xs ih =>
    cases g_inits with
    | nil => simp at hlen
    | cons v vs =>
    unfold allocGlobs at h ih
    rw [List.zip_cons_cons, allocXs_cons] at h
    have hs := congrArg Prod.fst h
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih (ws := (allocGlob ws (x, v)).1) (g_inits := vs)
      (l := (allocXs allocGlob (allocGlob ws (x, v)).1 (xs.zip vs)).2) (by simpa using hlen)
      (Prod.ext hs rfl)
    generalize allocXs allocGlob (allocGlob ws (x, v)).1 (xs.zip vs) = r at h h1
    cases h
    simp only [allocGlob, addGlob] at h1 h2 h3 h4 h5 ⊢
    refine ⟨?_, ?_, h3, h4, h5⟩
    · simp [h1, genIndex_eq_range', List.range'_succ]
    · simp [h2]

@[rocq_alias iriswasm.init_tabs_preserve]
theorem init_tabs_preserve {ws : StoreRecord} {inst : Instance} {e_inits : List Nat}
    {melem : List ModuleElement} {ws' : StoreRecord} (h : initTabs ws inst e_inits melem = ws') :
    ws.funcs = ws'.funcs ∧ ws.mems = ws'.mems ∧ ws.globals = ws'.globals := by
  subst h
  exact fold_left_preserve
    (fun s : StoreRecord => ws.funcs = s.funcs ∧ ws.mems = s.mems ∧ ws.globals = s.globals)
    _ _ _ ⟨rfl, rfl, rfl⟩ fun _ _ hx => hx

@[rocq_alias iriswasm.init_mems_preserve]
theorem init_mems_preserve {ws : StoreRecord} {inst : Instance} {d_inits : List Nat}
    {mdata : List ModuleData} {ws' : StoreRecord} (h : initMems ws inst d_inits mdata = ws') :
    ws.funcs = ws'.funcs ∧ ws.tables = ws'.tables ∧ ws.globals = ws'.globals := by
  subst h
  exact fold_left_preserve
    (fun s : StoreRecord => ws.funcs = s.funcs ∧ ws.tables = s.tables ∧ ws.globals = s.globals)
    _ _ _ ⟨rfl, rfl, rfl⟩ fun _ _ hx => hx

private theorem import_counts {c : TContext} {imps : List ModuleImport} {ts : List ExternT}
    (h : Wasm.List.Forall₂ (fun (imp : ModuleImport) e => moduleImportTyping c imp.desc e = true)
      imps ts) :
    (imps.filterMap fun x => match x.desc with | .func id => some id | _ => none).length =
      (extTFuncs ts).length ∧
    (imps.filterMap fun x => match x.desc with | .table id => some id | _ => none).length =
      (extTTabs ts).length ∧
    (imps.filterMap fun x => match x.desc with | .mem id => some id | _ => none).length =
      (extTMems ts).length ∧
    (imps.filterMap fun x => match x.desc with | .global id => some id | _ => none).length =
      (extTGlobs ts).length := by
  induction h with
  | nil => simp [extTFuncs, extTTabs, extTMems, extTGlobs]
  | @cons imp e _ _ he _ ih =>
    rcases imp with ⟨_, _, d⟩
    cases d <;> cases e <;> simp [moduleImportTyping] at he <;>
      simp_all [extTFuncs, extTTabs, extTMems, extTGlobs]

@[rocq_alias iriswasm.mod_imps_len_t]
theorem mod_imps_len_t {m : Module} {t_imps t_exps : List ExternT}
    (h : ModuleTyping m t_imps t_exps) :
    getImportFuncCount m = (extTFuncs t_imps).length ∧
    getImportTableCount m = (extTTabs t_imps).length ∧
    getImportMemCount m = (extTMems t_imps).length ∧
    getImportGlobalCount m = (extTGlobs t_imps).length := by
  obtain ⟨fts, gts, h⟩ := h
  rcases m with ⟨tfs, fs, ts, ms, gs, els, ds, iOpt, imps, exps⟩
  obtain ⟨-, -, -, -, -, -, -, hi, -⟩ := h
  exact import_counts hi

/-! ### Section `Instantiation_det` -/

@[rocq_alias iriswasm.bet_const_exprs_len]
theorem bet_const_exprs_len {tc : TContext} {es : List BasicInstruction} {t1 t2 : List ValueType}
    (hc : constExprs tc es = true) (h : BeTyping tc es (.tf t1 t2)) :
    t2.length = es.length + t1.length := by
  induction es generalizing t1 t2 with
  | nil => rw [empty_typing h]; simp
  | cons a es ih =>
    simp only [constExprs, List.all_cons, Bool.and_eq_true] at hc
    obtain ⟨ts, t1s', t2s', t3s, rfl, rfl, h1, h2⟩ :=
      composition_typing (es1 := [a]) (es2 := es) h
    have ih' := ih hc.2 h2
    have : t3s.length = t1s'.length + 1 := by
      have ha := hc.1
      cases a <;> simp [constExpr] at ha
      · obtain ⟨_, _, rfl, _⟩ := Get_global_typing h1; simp
      · rw [BI_const_typing h1]; simp
    simp; omega

@[rocq_alias iriswasm.const_exprs_impl]
theorem const_exprs_impl {tc : TContext} {es : List BasicInstruction} {t : ValueType}
    (hc : constExprs tc es = true) (h : BeTyping tc es (.tf [] [t])) :
    ∃ e, es = [e] ∧ constExpr tc e = true := by
  have hl := bet_const_exprs_len hc h
  match es, hl with
  | [e], _ => exact ⟨e, rfl, by simpa [constExprs] using hc⟩

private theorem lfilled_singleton {k : Nat} {lh : Lholed} {es : List AdministrativeInstruction}
    {e : AdministrativeInstruction} (h : lfilled k lh es [e] = true) (hne : es ≠ [])
    (hl : ∀ n es1 es2, e ≠ .label n es1 es2) : k = 0 ∧ lh = .base [] [] ∧ es = [e] := by
  rw [lfilled_Ind_Equivalent] at h
  generalize hx : [e] = x at h
  cases h with
  | lfilledBase vs _ es' =>
    have := congrArg List.length hx
    simp only [List.length_append, List.length_cons, List.length_nil] at this
    have : es.length ≠ 0 := by simpa using hne
    rcases vs with _ | ⟨a, vs⟩
    · rcases es' with _ | ⟨b, es'⟩
      · simp_all
      · simp at this; omega
    · simp at this; omega
  | lfilledRec _ vs n es' lh' es'' _ LI _ _ =>
    rcases vs with _ | ⟨a, vs⟩ <;> simp at hx
    exact absurd hx.1 (hl _ _ _)

private theorem lfilled_zero_base {es les : List AdministrativeInstruction}
    (h : lfilled 0 (.base [] []) es les = true) : les = es := by
  rw [lfilled_Ind_Equivalent] at h
  cases h; simp

@[rocq_alias iriswasm.const_no_reduce]
theorem const_no_reduce {s : StoreRecord} {f : Frame} {v : Value} {s' : StoreRecord} {f' : Frame}
    {e' : List AdministrativeInstruction} (h : Reduce s f [.basic (.const v)] s' f' e') :
    False := by
  generalize he : [AdministrativeInstruction.basic (.const v)] = es at h
  induction h with
  | simple hs =>
    cases hs <;> simp_all [List.cons_eq_append_iff]
    subst he
    rename_i h1 h2
    obtain ⟨-, -, h3⟩ := lfilled_singleton h2 (by simp) (by simp)
    simp at h3
  | label es es' k lh hr h1 _ ih =>
    obtain ⟨-, -, rfl⟩ := lfilled_singleton (he ▸ h1) (reduce_not_nil hr) (by simp)
    exact ih rfl
  | _ => simp_all [List.cons_eq_append_iff]

@[rocq_alias iriswasm.reduce_trans_const]
theorem reduce_trans_const {s1 : StoreRecord} {f1 : Frame} {v1 : Value} {s2 : StoreRecord}
    {f2 : Frame} {v2 : Value}
    (h : ReduceTrans (s1, f1, [.basic (.const v1)]) (s2, f2, [.basic (.const v2)])) : v1 = v2 := by
  rcases FromMathlib.Relation.ReflTransGen.cases_head h with h | ⟨⟨_, _, _⟩, hr, _⟩
  · simp at h; exact h.2.2
  · exact (const_no_reduce hr).elim

@[rocq_alias iriswasm.reduce_get_global]
theorem reduce_get_global {s : StoreRecord} {f : Frame} {s' : StoreRecord} {f' : Frame} {i : Nat}
    {e : List AdministrativeInstruction} (h : Reduce s f [.basic (.getGlobal i)] s' f' e) :
    ∃ v, sglobVal s f.inst i = some v ∧ e = [.basic (.const v)] := by
  generalize he : [AdministrativeInstruction.basic (.getGlobal i)] = es at h
  induction h with
  | simple hs =>
    cases hs <;> simp_all [List.cons_eq_append_iff]
    subst he
    rename_i h1 h2
    obtain ⟨-, -, h3⟩ := lfilled_singleton h2 (by simp) (by simp)
    simp at h3
  | getGlobal hv => simp at he; subst he; exact ⟨_, hv, rfl⟩
  | label es es' k lh hr h1 h2 ih =>
    obtain ⟨rfl, rfl, rfl⟩ := lfilled_singleton (he ▸ h1) (reduce_not_nil hr) (by simp)
    obtain ⟨v, hv, rfl⟩ := ih rfl
    exact ⟨v, hv, lfilled_zero_base h2⟩
  | _ => simp_all [List.cons_eq_append_iff]

@[rocq_alias iriswasm.reduce_trans_get_global]
theorem reduce_trans_get_global {s : StoreRecord} {f : Frame} {s' : StoreRecord} {f' : Frame}
    {i : Nat} {v : Value}
    (h : ReduceTrans (s, f, [.basic (.getGlobal i)]) (s', f', [.basic (.const v)])) :
    sglobVal s f.inst i = some v := by
  rcases FromMathlib.Relation.ReflTransGen.cases_head h with h | ⟨⟨_, _, _⟩, hr, hrest⟩
  · simp at h
  · obtain ⟨v', hv, rfl⟩ := reduce_get_global hr
    rw [hv, reduce_trans_const hrest]

/-- A typed constant initialiser evaluates to the same value in stores agreeing on the globals
visible to it. -/
private theorem const_init_det {tc : TContext} {es : List BasicInstruction} {t : ValueType}
    {s1 s2 : StoreRecord} {inst : Instance} {v1 v2 : Value}
    (hc : constExprs tc es = true) (hbet : BeTyping tc es (.tf [] [t]))
    (hs : ∀ i, i < tc.global.length → sglobVal s1 inst i = sglobVal s2 inst i)
    (h1 : ReduceTrans (s1, ⟨[], inst⟩, toEList es) (s1, ⟨[], inst⟩, [.basic (.const v1)]))
    (h2 : ReduceTrans (s2, ⟨[], inst⟩, toEList es) (s2, ⟨[], inst⟩, [.basic (.const v2)])) :
    v1 = v2 := by
  obtain ⟨e, rfl, he⟩ := const_exprs_impl hc hbet
  cases e <;> simp [constExpr] at he
  · rename_i k
    have g1 := reduce_trans_get_global h1
    have g2 := reduce_trans_get_global h2
    simp only at g1 g2
    rw [hs k he.1, g2] at g1
    exact (Option.some.inj g1).symm
  · exact (reduce_trans_const h1).symm.trans (reduce_trans_const h2)

@[rocq_alias iriswasm.module_glob_init_det]
theorem module_glob_init_det {m : Module} {v_imps t_imps : List ExternT} {inst : Instance}
    {s1 s2 : StoreRecord} {gi1 gi2 : List Value} (hmt : ModuleTyping m v_imps t_imps)
    (h1 : InstantiateGlobals inst s1 m gi1) (h2 : InstantiateGlobals inst s2 m gi2)
    (hs : ∀ i, i < (extTGlobs v_imps).length → sglobVal s1 inst i = sglobVal s2 inst i) :
    gi1 = gi2 := by
  obtain ⟨fts, gts, hmt⟩ := hmt
  rcases m with ⟨tfs, fs, ts, ms, gs, els, ds, iOpt, imps, exps⟩
  obtain ⟨-, -, -, hg, -⟩ := hmt
  refine forall2_det h1 h2 fun g hg' v1 v2 r1 r2 => ?_
  obtain ⟨tg, hc, -, hbet⟩ := forall2_mem_left hg g hg'
  exact const_init_det hc hbet hs r1 r2

@[rocq_alias iriswasm.module_elem_init_det]
theorem module_elem_init_det {m : Module} {v_imps t_imps : List ExternT} {inst : Instance}
    {s : StoreRecord} {eo1 eo2 : List I32} (hmt : ModuleTyping m v_imps t_imps)
    (h1 : InstantiateElem inst s m eo1) (h2 : InstantiateElem inst s m eo2) : eo1 = eo2 := by
  obtain ⟨fts, gts, hmt⟩ := hmt
  rcases m with ⟨tfs, fs, ts, ms, gs, els, ds, iOpt, imps, exps⟩
  obtain ⟨-, -, -, -, he, -⟩ := hmt
  refine forall2_det h1 h2 fun e he' c1 c2 r1 r2 => ?_
  have hty := he e he'
  rcases e with ⟨⟨t⟩, off, init⟩
  obtain ⟨hc, hbet, -⟩ := hty
  simpa using const_init_det hc hbet (fun _ _ => rfl) r1 r2

@[rocq_alias iriswasm.module_data_init_det]
theorem module_data_init_det {m : Module} {v_imps t_imps : List ExternT} {inst : Instance}
    {s : StoreRecord} {do1 do2 : List I32} (hmt : ModuleTyping m v_imps t_imps)
    (h1 : InstantiateData inst s m do1) (h2 : InstantiateData inst s m do2) : do1 = do2 := by
  obtain ⟨fts, gts, hmt⟩ := hmt
  rcases m with ⟨tfs, fs, ts, ms, gs, els, ds, iOpt, imps, exps⟩
  obtain ⟨-, -, -, -, -, hd, -⟩ := hmt
  refine forall2_det h1 h2 fun d hd' c1 c2 r1 r2 => ?_
  have hty := hd d hd'
  rcases d with ⟨⟨t⟩, off, init⟩
  obtain ⟨hc, hbet, -⟩ := hty
  simpa using const_init_det hc hbet (fun _ _ => rfl) r1 r2

@[rocq_alias iriswasm.vt_imps_comp_len]
theorem vt_imps_comp_len {s : StoreRecord} {v_imps : List VExt} {t_imps : List ExternT}
    (h : Wasm.List.Forall₂ (ExternalTyping s) v_imps t_imps) :
    (extFuncs v_imps).length = (extTFuncs t_imps).length ∧
    (extTabs v_imps).length = (extTTabs t_imps).length ∧
    (extMems v_imps).length = (extTMems t_imps).length ∧
    (extGlobs v_imps).length = (extTGlobs t_imps).length := by
  induction h with
  | nil => simp [extFuncs, extTFuncs, extTabs, extTTabs, extMems, extTMems, extGlobs, extTGlobs]
  | cons he _ ih =>
    cases he <;>
      simp_all [extFuncs, extTFuncs, extTabs, extTTabs, extMems, extTMems, extGlobs, extTGlobs]

@[rocq_alias iriswasm.alloc_module_det]
theorem alloc_module_det {s : StoreRecord} {m : Module} {v_imps : List VExt}
    {t_imps t_exps : List ExternT} {g_inits g_inits' : List Value} {s_res1 s_res2 : StoreRecord}
    {inst inst' : Instance} {exps exps' : List ModuleExport}
    (hmt : ModuleTyping m t_imps t_exps)
    (hext : Wasm.List.Forall₂ (ExternalTyping s) v_imps t_imps)
    (hglen1 : g_inits.length = m.globals.length) (hglen2 : g_inits'.length = m.globals.length)
    (ham1 : allocModule s m v_imps g_inits (s_res1, inst, exps) = true)
    (ham2 : allocModule s m v_imps g_inits' (s_res2, inst', exps') = true)
    (hinitg1 : InstantiateGlobals inst s_res1 m g_inits)
    (hinitg2 : InstantiateGlobals inst' s_res2 m g_inits') :
    (inst, exps) = (inst', exps') ∧ g_inits = g_inits' ∧ s_res1 = s_res2 := by
  simp only [allocModule] at ham1 ham2
  generalize hf1 : allocFuncs s m.funcs inst = rf1 at ham1
  rcases rf1 with ⟨s0, idf⟩
  generalize ht1 : allocTabs s0 (m.tables.map (·.type)) = rt1 at ham1
  rcases rt1 with ⟨s1, idt⟩
  generalize hm1 : allocMems s1 m.mems = rm1 at ham1
  rcases rm1 with ⟨s2, idm⟩
  generalize hg1 : allocGlobs s2 m.globals g_inits = rg1 at ham1
  rcases rg1 with ⟨s3, idg⟩
  generalize hf2 : allocFuncs s m.funcs inst' = rf2 at ham2
  rcases rf2 with ⟨s0', idf'⟩
  generalize ht2 : allocTabs s0' (m.tables.map (·.type)) = rt2 at ham2
  rcases rt2 with ⟨s1', idt'⟩
  generalize hm2 : allocMems s1' m.mems = rm2 at ham2
  rcases rm2 with ⟨s2', idm'⟩
  generalize hg2 : allocGlobs s2' m.globals g_inits' = rg2 at ham2
  rcases rg2 with ⟨s3', idg'⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ham1 ham2
  obtain ⟨⟨⟨⟨⟨⟨rfl, hty1⟩, hfu1⟩, hta1⟩, hme1⟩, hgl1⟩, hex1⟩ := ham1
  obtain ⟨⟨⟨⟨⟨⟨rfl, hty2⟩, hfu2⟩, hta2⟩, hme2⟩, hgl2⟩, hex2⟩ := ham2
  obtain ⟨af1, af2, af3, af4, af5⟩ := alloc_func_gen_index hf1
  obtain ⟨bf1, bf2, bf3, bf4, bf5⟩ := alloc_func_gen_index hf2
  obtain ⟨at1, at2, at3, at4, at5⟩ := alloc_tab_gen_index ht1
  obtain ⟨bt1, bt2, bt3, bt4, bt5⟩ := alloc_tab_gen_index ht2
  obtain ⟨am1, am2, am3, am4, am5⟩ := alloc_mem_gen_index hm1
  obtain ⟨bm1, bm2, bm3, bm4, bm5⟩ := alloc_mem_gen_index hm2
  obtain ⟨ag1, ag2, ag3, ag4, ag5⟩ := alloc_glob_gen_index hglen1 hg1
  obtain ⟨bg1, bg2, bg3, bg4, bg5⟩ := alloc_glob_gen_index hglen2 hg2
  have hinst : inst = inst' := by
    rcases inst with ⟨_, _, _, _, _⟩
    rcases inst' with ⟨_, _, _, _, _⟩
    simp only at hty1 hty2 hfu1 hfu2 hta1 hta2 hme1 hme2 hgl1 hgl2
    simp only [hty1, hty2, hfu1, hfu2, hta1, hta2, hme1, hme2, hgl1, hgl2,
      List.map_append, af1, bf1, at1, bt1, am1, bm1, ag1, bg1, ← af3, ← bf3, ← af4, ← bf4,
      ← at4, ← bt4, ← af5, ← bf5, ← at5, ← bt5, ← am5, ← bm5]
  subst hinst
  have hglob : s_res1.globals = s.globals ++ (m.globals.zip g_inits).map (fun (mg, v) =>
      ({ mut_ := mg.type.mut_, val := v } : Global)) := by rw [ag2, ← am5, ← at5, ← af5]
  have hglob' : s_res2.globals = s.globals ++ (m.globals.zip g_inits').map (fun (mg, v) =>
      ({ mut_ := mg.type.mut_, val := v } : Global)) := by rw [bg2, ← bm5, ← bt5, ← bf5]
  have hgi : g_inits = g_inits' := by
    refine module_glob_init_det hmt hinitg1 hinitg2 fun i hi => ?_
    rw [← (vt_imps_comp_len hext).2.2.2] at hi
    obtain ⟨⟨n⟩, hn⟩ : ∃ x, (extGlobs v_imps)[i]? = some x := ⟨_, List.getElem?_eq_getElem hi⟩
    have hmem : ModuleExportDesc.global (.globalidx n) ∈ v_imps :=
      List.mem_filterMap.1 (List.mem_of_getElem? hn) |>.elim fun x ⟨hx, he⟩ => by
        cases x <;> simp at he; subst he; exact hx
    obtain ⟨_, hty⟩ := forall2_mem_left hext _ hmem
    have hn' : n < s.globals.length := by cases hty; assumption
    simp only [sglobVal, sglob, sglobInd, hgl1, List.map_append]
    rw [List.getElem?_append_left (by simpa using hi), List.getElem?_map, hn]
    simp [optionBind, hglob, hglob', List.getElem?_append_left hn']
  subst hgi
  refine ⟨by rw [hex1, hex2], rfl, ?_⟩
  rw [hf1] at hf2; cases hf2
  rw [ht1] at ht2; cases ht2
  rw [hm1] at hm2; cases hm2
  rw [hg1] at hg2; cases hg2
  rfl

@[rocq_alias iriswasm.instantiate_det]
theorem instantiate_det {s : StoreRecord} {m : Module} {vimps : List VExt}
    {res res' : (StoreRecord × Instance × List ModuleExport) × Option Nat}
    (h1 : Instantiate s m vimps res) (h2 : Instantiate s m vimps res') : res = res' := by
  rcases res with ⟨⟨s1, inst1, exp1⟩, start1⟩
  rcases res' with ⟨⟨s2, inst2, exp2⟩, start2⟩
  obtain ⟨ti1, te1, ws1, gi1, eo1, do1, hmt1, hext1, ham1, hig1, hie1, hid1, -, -, hcs1, hws1⟩ := h1
  obtain ⟨ti2, te2, ws2, gi2, eo2, do2, hmt2, hext2, ham2, hig2, hie2, hid2, -, -, hcs2, hws2⟩ := h2
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (module_typing_det hmt1 hmt2)
  obtain ⟨hie, rfl, rfl⟩ := alloc_module_det hmt1 hext1 (Wasm.List.Forall₂.length_eq hig1).symm
    (Wasm.List.Forall₂.length_eq hig2).symm ham1 ham2 hig1 hig2
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hie
  obtain rfl := module_elem_init_det hmt1 hie1 hie2
  obtain rfl := module_data_init_det hmt1 hid1 hid2
  simp only [checkStart, decide_eq_true_eq] at hcs1 hcs2 hws1 hws2
  rw [← hcs1, hcs2, hws1, hws2]

end IrisWasm
