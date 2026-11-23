/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import Wasm.ModuleValidation
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

@[rocq_alias iriswasm.module_typing_det]
theorem module_typing_det {m : Module} {it1 et1 it2 et2 : List ExternT}
    (h1 : ModuleTyping m it1 et1) (h2 : ModuleTyping m it2 et2) : (it1, et1) = (it2, et2) := by
  have a := (validateModule_iff m ⟨it1, et1⟩).2 h1
  have b := (validateModule_iff m ⟨it2, et2⟩).2 h2
  cases Except.ok.inj (a.symm.trans b)
  rfl

@[rocq_alias iriswasm.module_typing_det_import_aux]
theorem module_typing_det_import_aux {m : Module} {it1 et1 it2 et2 : List ExternT}
    (h1 : ModuleTyping m it1 et1) (h2 : ModuleTyping m it2 et2) : it1 = it2 :=
  congrArg Prod.fst (module_typing_det h1 h2)

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
      ({ entries := RunTable.uniform tt.limits.min none, maxOpt := tt.limits.max } : Tableinst)) ∧
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

#rocq_ignore iriswasm.alloc_mem_gen_index "fresh memories retain their full descriptor"
theorem alloc_mem_gen_index {modmemtypes : List MemoryType} {ws ws' : StoreRecord}
    {l : List Memidx} (h : allocMems ws modmemtypes = (ws', l)) :
    l.map (fun | .memidx i => i) = genIndex ws.mems.length modmemtypes.length ∧
    ws'.mems = ws.mems ++ modmemtypes.map memMk ∧
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
    · simp [h2]

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

/-- A failed active data segment keeps the store reached by the preceding writes;
    neither successful nor failing initialization changes the other store components. -/
theorem init_mems_preserve_result (ws : StoreRecord) (inst : Instance)
    (offs : List Nat) (data : List ModuleData) (out : StoreRecord)
    (h : initMems ws inst offs data = .ok out ∨ initMems ws inst offs data = .error out) :
    ws.funcs = out.funcs ∧ ws.tables = out.tables ∧ ws.globals = out.globals := by
  induction data generalizing ws offs with
  | nil =>
    cases offs <;> rcases h with h | h <;> cases h <;> exact ⟨rfl, rfl, rfl⟩
  | cons d ds ih =>
    cases offs with
    | nil => rcases h with h | h <;> cases h <;> exact ⟨rfl, rfl, rfl⟩
    | cons off os =>
      cases hh : initMem ws inst off d with
      | error failed =>
        simp [initMems, hh] at h
        subst out
        unfold initMem at hh
        repeat' split at hh
        all_goals cases hh <;> exact ⟨rfl, rfl, rfl⟩
      | ok mid =>
        simp only [initMems, hh] at h
        have htail := ih mid os h
        obtain ⟨i, mem, -, -, -, rfl⟩ := initMem_ok_iff.mp hh
        exact htail

#rocq_ignore iriswasm.init_mems_preserve "successful checked initialization preserves the other fields"
theorem init_mems_preserve {ws : StoreRecord} {inst : Instance} {d_inits : List Nat}
    {mdata : List ModuleData} {ws' : StoreRecord} (h : initMems ws inst d_inits mdata = .ok ws') :
    ws.funcs = ws'.funcs ∧ ws.tables = ws'.tables ∧ ws.globals = ws'.globals :=
  init_mems_preserve_result ws inst d_inits mdata ws' (.inl h)

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

#rocq_ignore iriswasm.bet_const_exprs_len "integer binary operators consume two operands"
#rocq_ignore iriswasm.const_exprs_impl "a singleton result need not come from a singleton initializer"

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

-- A stack invariant for the actual reduction path, including a trapping intermediate expression.
private def constResidual (tc : TContext) : AdministrativeInstruction → Bool
  | .basic b => constExpr tc b
  | .trap => true
  | _ => false

-- `none` is malformed; only a matched arithmetic redex or an explicit trap yields `.trap`.
private def stackOp (read : Nat → Option Value) :
    Option Result → AdministrativeInstruction → Option Result
  | some .trap, _ => some .trap
  | some (.values _), .trap => some .trap
  | some (.values vs), .basic (.const v) => some (.values (v :: vs))
  | some (.values vs), .basic (.getGlobal i) => (read i).map fun v => .values (v :: vs)
  | some (.values (rhs :: lhs :: vs)), .basic (.binop t op) =>
    if typesAgree t lhs && typesAgree t rhs && binopTypeOK t op then
      some (match appBinop op lhs rhs with | some v => .values (v :: vs) | none => .trap)
    else none
  | _, _ => none

private theorem fold_none (read : Nat → Option Value) (es : List AdministrativeInstruction) :
    es.foldl (stackOp read) none = none := by
  induction es with
  | nil => rfl
  | cons _ _ ih => exact ih

private theorem fold_trap (read : Nat → Option Value) (es : List AdministrativeInstruction) :
    es.foldl (stackOp read) (some .trap) = some .trap := by
  induction es with
  | nil => rfl
  | cons _ _ ih => exact ih

private theorem fold_trap_context (read : Nat → Option Value) (pre : List Value)
    (tail : List AdministrativeInstruction) (z : Option Result) :
    (vToEList pre ++ .trap :: tail).foldl (stackOp read) z = stackOp read z .trap := by
  induction pre generalizing z with
  | nil =>
    cases z with
    | none => exact fold_none read tail
    | some r => cases r <;> exact fold_trap read tail
  | cons v pre ih =>
    change (vToEList pre ++ .trap :: tail).foldl (stackOp read) (stackOp read z (.basic (.const v))) = _
    rw [ih]
    rcases z with _ | (_ | _) <;> rfl

private theorem const_step {tc : TContext} {read : Nat → Option Value}
    {s s' : StoreRecord} {f f' : Frame} {es es' : List AdministrativeInstruction}
    (r : Reduce s f es s' f' es') (hc : es.all (constResidual tc) = true)
    (hg : ∀ i, i < tc.global.length → read i = sglobVal s f.inst i) :
    s' = s ∧ f' = f ∧ es'.all (constResidual tc) = true ∧
      ∀ z, es.foldl (stackOp read) z = es'.foldl (stackOp read) z := by
  induction r with
  | simple h =>
    cases h with
    | binopSuccess h1 h2 hop h | binopFailure h1 h2 hop h =>
      refine ⟨rfl, rfl, rfl, fun z => ?_⟩
      rcases z with _ | (_ | _) <;> simp [List.foldl, stackOp, h1, h2, hop, h]
    | trap _ _ fill =>
      rw [lfilled_Ind_Equivalent] at fill
      cases fill with
      | lfilledBase bef _ aft hpre =>
        obtain ⟨pre, rfl⟩ := Wasm.const_es_exists hpre
        exact ⟨rfl, rfl, rfl, fun z => by
          simpa only [List.append_assoc, List.singleton_append, List.foldl_cons, List.foldl_nil]
            using fold_trap_context read pre aft z⟩
    | _ => simp [constResidual, constExpr] at hc
  | getGlobal h =>
    simp [constResidual, constExpr] at hc
    refine ⟨rfl, rfl, rfl, fun z => ?_⟩
    rcases z with _ | (_ | _) <;> simp [List.foldl, stackOp, hg _ hc.1, h]
  | label es es' _ _ _ fill fill' ih =>
    rw [lfilled_Ind_Equivalent] at fill fill'
    cases fill with
    | lfilledBase bef _ aft _ =>
      cases fill'
      simp only [List.all_append, Bool.and_eq_true] at hc
      obtain ⟨hs, hf, hc', h⟩ := ih hc.1.2 hg
      exact ⟨hs, hf, by simp [hc.1.1, hc', hc.2], fun z => by simp only [List.foldl_append, h]⟩
    | lfilledRec => simp [constResidual] at hc
  | _ => simp [constResidual, constExpr] at hc

private theorem const_path {tc : TContext} {read : Nat → Option Value}
    {x y : StoreRecord × Frame × List AdministrativeInstruction}
    (r : ReduceTrans x y) (hc : x.2.2.all (constResidual tc) = true)
    (hg : ∀ i, i < tc.global.length → read i = sglobVal x.1 x.2.1.inst i) :
    y.1 = x.1 ∧ y.2.1 = x.2.1 ∧ y.2.2.all (constResidual tc) = true ∧
      ∀ z, x.2.2.foldl (stackOp read) z = y.2.2.foldl (stackOp read) z := by
  induction r with
  | refl => exact ⟨rfl, rfl, hc, fun _ => rfl⟩
  | @tail b c _ step ih =>
    obtain ⟨s, f, es⟩ := b
    obtain ⟨s', f', es'⟩ := c
    obtain ⟨hs, hf, he, eq⟩ := ih
    change s = _ at hs
    change f = _ at hf
    obtain ⟨hs', hf', he', eq'⟩ := const_step (s := s) (f := f) step he (by rwa [hs, hf])
    exact ⟨hs'.trans hs, hf'.trans hf, he', fun z => (eq z).trans (eq' z)⟩

/-- A constant initializer evaluates to the same value in stores agreeing on visible globals. -/
private theorem const_init_det {tc : TContext} {es : List BasicInstruction}
    {s1 s2 : StoreRecord} {inst : Instance} {v1 v2 : Value}
    (hc : constExprs tc es = true)
    (hs : ∀ i, i < tc.global.length → sglobVal s1 inst i = sglobVal s2 inst i)
    (h1 : ReduceTrans (s1, ⟨[], inst⟩, toEList es) (s1, ⟨[], inst⟩, [.basic (.const v1)]))
    (h2 : ReduceTrans (s2, ⟨[], inst⟩, toEList es) (s2, ⟨[], inst⟩, [.basic (.const v2)])) :
    v1 = v2 := by
  have h : (toEList es).all (constResidual tc) = true := by
    simpa [toEList, List.all_map, Function.comp_def, constResidual, constExprs] using hc
  have p := (const_path (read := sglobVal s1 inst) h1 h (fun _ _ => rfl)).2.2.2 (some (.values []))
  have q := (const_path h2 h hs).2.2.2 (some (.values []))
  simpa [List.foldl, stackOp] using p.symm.trans q

private theorem globals_init_det {s₁ s₂ : StoreRecord} {inst : Instance} {c : TContext}
    {gs : List ModuleGlob} {ts : List GlobalType} (ht : ModuleGlobalsTyping c gs ts) :
    ∀ {vs ws : List Value},
      Wasm.List.Forall₂ (fun (g : ModuleGlob) v =>
        ReduceTrans (s₁, ⟨[], inst⟩, toEList g.init) (s₁, ⟨[], inst⟩, [.basic (.const v)])) gs vs →
      Wasm.List.Forall₂ (fun (g : ModuleGlob) w =>
        ReduceTrans (s₂, ⟨[], inst⟩, toEList g.init) (s₂, ⟨[], inst⟩, [.basic (.const w)])) gs ws →
      (∀ i, i < c.global.length → sglobVal s₁ inst i = sglobVal s₂ inst i) →
      (∀ j, j < gs.length → vs[j]? = ws[j]? →
        sglobVal s₁ inst (c.global.length + j) = sglobVal s₂ inst (c.global.length + j)) →
      vs = ws := by
  induction ht with
  | nil => intro vs ws h₁ h₂ _ _; cases h₁; cases h₂; rfl
  | @cons c g t gs ts head _ ih =>
    intro vs ws h₁ h₂ hs hlocal
    cases h₁ with | cons r₁ tail₁ =>
    cases h₂ with | cons r₂ tail₂ =>
    obtain rfl := const_init_det head.1 hs r₁ r₂
    congr 1
    refine ih tail₁ tail₂ (fun i hi => ?_) (fun j hj he => ?_)
    · by_cases h : i < c.global.length
      · exact hs i h
      · simp only [List.length_append, List.length_singleton] at hi
        have : i = c.global.length := by omega
        subst i; simpa using hlocal 0 (by simp) rfl
    · simpa [Nat.add_assoc, Nat.add_comm 1] using
        hlocal (j + 1) (by simpa using hj) (by simpa using he)

#rocq_ignore iriswasm.module_glob_init_det "earlier defined globals are visible to initializers"
theorem module_glob_init_det {m : Module} {v_imps t_imps : List ExternT} {inst : Instance}
    {s1 s2 : StoreRecord} {gi1 gi2 : List Value} (hmt : ModuleTyping m v_imps t_imps)
    (h1 : InstantiateGlobals inst s1 m gi1) (h2 : InstantiateGlobals inst s2 m gi2)
    (hs : ∀ i, i < (extTGlobs v_imps).length → sglobVal s1 inst i = sglobVal s2 inst i)
    (hlocal : ∀ j, j < m.globals.length → gi1[j]? = gi2[j]? →
      let i := (extTGlobs v_imps).length + j
      sglobVal s1 inst i = sglobVal s2 inst i) : gi1 = gi2 := by
  obtain ⟨_, _, h⟩ := hmt
  exact globals_init_det h.2.2.2.1 h1 h2 hs hlocal

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
  simpa using const_init_det hty.1 (fun _ _ => rfl) r1 r2

#rocq_ignore iriswasm.module_data_init_det "active data offsets retain their address type"
theorem module_data_init_det {m : Module} {v_imps t_imps : List ExternT} {inst : Instance}
    {s : StoreRecord} {do1 do2 : List AddressOperand} (hmt : ModuleTyping m v_imps t_imps)
    (h1 : InstantiateData inst s m do1) (h2 : InstantiateData inst s m do2) : do1 = do2 := by
  obtain ⟨fts, gts, hmt⟩ := hmt
  rcases m with ⟨tfs, fs, ts, ms, gs, els, ds, iOpt, imps, exps⟩
  obtain ⟨-, -, -, -, -, hd, -⟩ := hmt
  refine forall2_det h1 h2 fun d hd' c1 c2 r1 r2 => ?_
  have hty := hd d hd'
  rcases d with ⟨⟨t⟩, off, init⟩
  dsimp only [ModuleDataTyping] at hty
  split at hty
  · exact hty.elim
  · exact AddressOperand.value_inj.mp (const_init_det hty.1 (fun _ _ => rfl) r1 r2)

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
    apply module_glob_init_det hmt hinitg1 hinitg2
    · intro i hi
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
    · intro j hj he
      simp only [sglobVal, sglob, sglobInd, hgl1, List.map_append, ag1,
        ← am5, ← at5, ← af5, ← (vt_imps_comp_len hext).2.2.2]
      rw [List.getElem?_append_right (by simp)]
      simp [gen_index_lookup _ _ _ hj, optionBind, hglob, hglob', List.getElem?_append_right,
        List.zip, List.getElem?_zipWith, he]
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
  simp only [checkStart, decide_eq_true_eq] at hcs1 hcs2
  obtain rfl := Except.ok.inj (hws1.symm.trans hws2)
  rw [← hcs1, hcs2]

end IrisWasm
