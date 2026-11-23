/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Instantiation.IrisInstantiationSpec
import IrisWasm.Helpers.IrisProperties
import IrisWasm.Rules.IrisRules

/-! Port of `theories/iris/host/iris_host.v`: the host language wrapping Wasm (module
instantiation and host actions), its Iris instance using iris-lean's standard weakest
precondition, the host lifting rules, and the operational instantiation specifications.

Names clashing with `iris.v` (`of_val`, `to_val`, `prim_step`, `state`, …) are `hostOfVal`,
`hostToVal`, `hostPrimStep`, `HostState`; clashing lemma names live in `IrisWasm.IrisHost`. -/

namespace IrisWasm

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm
open scoped Iris.Std.PartialMap

/-! ## The host language -/

section Iris_host_def

/-- Domain of the variable instantiation store. -/
@[rocq_alias iriswasm.vi]
abbrev Vi := Nat

/-- Variable import/export store. -/
@[rocq_alias iriswasm.vi_store]
abbrev ViStore := NatMap ModuleExport

@[rocq_alias iriswasm.module_decl]
abbrev ModuleDecl := Module

/-- An import is the index (in the vi store) of the export it is bound to. -/
@[rocq_alias iriswasm.vimp]
abbrev Vimp := Vi

@[rocq_alias iriswasm.host_e]
inductive HostE where
  | instantiate : List Vi → Nat → List Vimp → HostE
  | getGlobal : Globaladdr → HostE
  deriving DecidableEq, Repr, Inhabited

/-- What a host function can do. -/
@[rocq_alias iriswasm.host_action]
inductive HostAction where
  | nothing
  | print
  | instantiate : HostE → HostAction
  | callWasm
  | modifyTable
  deriving DecidableEq, Repr, Inhabited

@[rocq_alias iriswasm.map_start]
def mapStart : Option Nat → List AdministrativeInstruction
  | some n => [.invoke n]
  | none => []

@[rocq_alias iriswasm.lookup_export_vi]
def lookupExportVi (vis : ViStore) (vimp : Vimp) : Option ModuleExport :=
  get? vis vimp

@[rocq_alias iriswasm.insert_exports]
def insertExports (vis : ViStore) : List Vi → List ModuleExport → Option ViStore
  | [], _ => some vis
  | _ :: _, [] => none
  | i :: iexps', exp :: exps' =>
    match insertExports vis iexps' exps' with
    | some vis' => some (insert vis' i exp)
    | none => none

#rocq_ignore iriswasm.iris_host.empty_instance "identical to operations.v's `empty_instance`; use `Wasm.emptyInstance`"

@[rocq_alias iriswasm.empty_frame]
def emptyFrame : Frame := ⟨[], emptyInstance⟩

#rocq_ignore iriswasm.stab_update "the host rejects writes at or beyond the table size"
def stabUpdate (s : StoreRecord) (i idx : Nat) (newval : Nat) : Option StoreRecord := do
  let tab ← s.tables[i]?
  let entries ← tab.entries.set? idx (some newval)
  return { s with tables := s.tables.set i { tab with entries } }

@[rocq_alias iriswasm.update_table]
def updateTable (s : StoreRecord) (f : Frame) (idx : Nat) (newval : Nat) : Option StoreRecord :=
  match f.inst.tab with
  | [] => none
  | ta :: _ => stabUpdate s ta idx newval

@[rocq_alias iriswasm.no_more_locals]
def noMoreLocals : Llholed → Bool
  | .base _ _ => true
  | .label _ _ _ llh _ => noMoreLocals llh
  | .local _ _ _ _ _ => false

@[rocq_alias iriswasm.innermost_frame]
def innermostFrame : Llholed → Frame → Frame
  | .base _ _, defaultf => defaultf
  | .label _ _ _ llh _, defaultf => innermostFrame llh defaultf
  | .local _ _ f llh _, defaultf => if noMoreLocals llh then f else innermostFrame llh defaultf

/-- Coq declares it mutually with `host_reduce`, which it does not mention. -/
@[rocq_alias iriswasm.execute_action]
inductive ExecuteAction : HostAction → StoreRecord → Frame → List Value → StoreRecord →
    List AdministrativeInstruction → Prop where
  | nothing (s : StoreRecord) (f : Frame) : ExecuteAction .nothing s f [] s []
  | print (s : StoreRecord) (f : Frame) (v : Value) : ExecuteAction .print s f [v] s []
  | callWasm (s : StoreRecord) (f : Frame) (i : I32) :
    ExecuteAction .callWasm s f [.int32 i] s [.basic (.call (Wasm.Int.natOfUint i))]
  | modifyTable (s : StoreRecord) (f : Frame) (tabIdx funcIdx : I32) (s' : StoreRecord) (a : Nat) :
    f.inst.funcs[Wasm.Int.natOfUint funcIdx]? = some a →
    updateTable s f (Wasm.Int.natOfUint tabIdx) a = some s' →
    ExecuteAction .modifyTable s f [.int32 tabIdx, .int32 funcIdx] s' []

@[rocq_alias iriswasm.host_reduce]
inductive HostReduce : StoreRecord → ViStore → List Module → List HostE → List HostAction → Frame →
    List AdministrativeInstruction → StoreRecord → ViStore → List Module → List HostE →
    List HostAction → Frame → List AdministrativeInstruction → Prop where
  | hostStep (s : StoreRecord) (vis : ViStore) (m : Module) (viexps : List Vi) (vm : Nat)
      (vimps : List Vimp) (imps : List ModuleExport) (impDescs : List ModuleExportDesc)
      (s' : StoreRecord) (vis' : ViStore) (ms : List Module) (idecs' : List HostE) (inst : Instance)
      (exps : List ModuleExport) (start : Option Nat) (vs : List AdministrativeInstruction)
      (f : Frame) (fs : List HostAction) :
    ms[vm]? = some m →
    those (vimps.map (lookupExportVi vis)) = some imps →
    imps.map (·.desc) = impDescs →
    Instantiate s m impDescs ((s', inst, exps), start) →
    viexps.length = exps.length →
    constList vs = true →
    insertExports vis viexps exps = some vis' →
    HostReduce s vis ms (.instantiate viexps vm vimps :: idecs') fs f vs
      s' vis' ms idecs' fs f (mapStart start)
  | hostStepInitOob (s : StoreRecord) (vis : ViStore) (m : Module) (viexps : List Vi) (vm : Nat)
      (vimps : List Vimp) (imps : List ModuleExport) (impDescs : List ModuleExportDesc)
      (ms : List Module) (idecs' : List HostE) (exps : List ModuleExport) (f : Frame)
      (vs : List AdministrativeInstruction) (fs : List HostAction) :
    ms[vm]? = some m →
    those (vimps.map (lookupExportVi vis)) = some imps →
    imps.map (·.desc) = impDescs →
    constList vs = true →
    ¬ (ModuleElemBoundCheckGmap (gmapOfList s.tables) impDescs m ∧
        ModuleDataBoundCheckGmap (gmapOfList s.mems) impDescs m) →
    HostReduce s vis ms (.instantiate viexps vm vimps :: idecs') fs f vs
      s vis ms idecs' fs f [.trap]
  | callHostAction (s : StoreRecord) (vis : ViStore) (ms : List Module) (idecs : List HostE)
      (s' : StoreRecord) (tf : FunctionType) (h : Hostfuncidx) (hi : Nat) (f : HostAction)
      (vcs : List Value) (fs : List HostAction) (res LI LI' : List AdministrativeInstruction)
      (lh : Llholed) (f0 : Frame) :
    h = .hostfuncidx hi →
    fs[hi]? = some f →
    -- an action needing the frame looks up the innermost frame around the `callHost`
    ExecuteAction f s (innermostFrame lh f0) vcs s' res →
    llfill lh [.callHost tf h vcs] = LI →
    llfill lh res = LI' →
    HostReduce s vis ms idecs fs f0 LI s' vis ms idecs fs f0 LI'
  | callHostInstantiate (s : StoreRecord) (vis : ViStore) (ms : List Module) (idecs : List HostE)
      (h : Hostfuncidx) (hi : Nat) (f : HostE) (fs : List HostAction)
      (LI LI' : List AdministrativeInstruction) (lh : Llholed) (f0 : Frame) :
    h = .hostfuncidx hi →
    fs[hi]? = some (.instantiate f) →
    llfill lh [.callHost (.tf [] []) h []] = LI →
    llfill lh [] = LI' →
    HostReduce s vis ms idecs fs f0 LI s vis ms (f :: idecs) fs f0 LI'
  | wasmStep (s : StoreRecord) (vis : ViStore) (ms : List Module) (idecs : List HostE)
      (s' : StoreRecord) (es es' : List AdministrativeInstruction) (f1 f2 : Frame)
      (fs : List HostAction) :
    Reduce s f1 es s' f2 es' →
    HostReduce s vis ms idecs fs f1 es s' vis ms idecs fs f2 es'
  | getGlobal (s : StoreRecord) (f : Frame) (vis : ViStore) (ms : List Module) (g : Globaladdr)
      (vGlob : Global) (fs : List HostAction) (vs : List AdministrativeInstruction) :
    s.globals[g]? = some vGlob →
    constList vs = true →
    HostReduce s vis ms [.getGlobal g] fs f vs s vis ms [] fs f (.basic (.const vGlob.val) :: vs)
  | trap (s : StoreRecord) (vis : ViStore) (ms : List Module) (g : Globaladdr)
      (fs : List HostAction) (f : Frame) :
    HostReduce s vis ms [.getGlobal g] fs f [.trap] s vis ms [] fs f [.trap]

@[rocq_alias iriswasm.llfill_const]
theorem llfill_const (es : List AdministrativeInstruction) (lh : Llholed)
    (LI : List AdministrativeInstruction) (hfill : llfill lh es = LI) (hconst : constList LI = true) :
    constList es = true := by
  subst hfill
  cases lh <;> simp_all [llfill, constList, isConst, vToEList]

@[rocq_alias iriswasm.lh_of_sh_inj]
theorem lh_of_sh_inj (s0 s1 : SimpleValidHoled) (h : lhOfSh s0 = lhOfSh s1) : s0 = s1 := by
  induction s0 generalizing s1 with
  | base b a =>
    cases s1 <;> simp_all [lhOfSh, List.map_inj_right]
  | rec_ b n es sh a ih =>
    cases s1 with
    | base => simp [lhOfSh] at h
    | rec_ b' n' es' sh' a' =>
      simp only [lhOfSh, Lholed.rec_.injEq] at h
      obtain ⟨hb, rfl, rfl, hsh, rfl⟩ := h
      rw [List.map_inj_right (by simp)] at hb
      rw [hb, ih _ hsh]

@[rocq_alias iriswasm.llfill_unique]
theorem llfill_unique (e1 : AdministrativeInstruction) (lh1 : Llholed) (e2 : AdministrativeInstruction)
    (lh2 : Llholed) (h : llfill lh1 [e1] = llfill lh2 [e2]) :
    (e1 = e2 ∧ lh1 = lh2) ∨ isConst e1 = true ∨ isConst e2 = true ∨
      (∃ a b c, e1 = .label a b c ∨ e2 = .label a b c) ∨
      (∃ a b c, e1 = .local a b c ∨ e2 = .local a b c) := by
  have h' : llfill lh1 ([] ++ [e1]) = llfill lh2 ([] ++ [e2]) := by simpa using h
  by_cases c1 : isConst e1 = true
  · exact Or.inr (Or.inl c1)
  by_cases c2 : isConst e2 = true
  · exact Or.inr (Or.inr (Or.inl c2))
  by_cases l1 : ∃ a b c, e1 = .label a b c
  · obtain ⟨a, b, c, hh⟩ := l1; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, c, .inl hh⟩)))
  by_cases l2 : ∃ a b c, e2 = .label a b c
  · obtain ⟨a, b, c, hh⟩ := l2; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, c, .inr hh⟩)))
  by_cases o1 : ∃ a b c, e1 = .local a b c
  · obtain ⟨a, b, c, hh⟩ := o1; exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a, b, c, .inl hh⟩)))
  by_cases o2 : ∃ a b c, e2 = .local a b c
  · obtain ⟨a, b, c, hh⟩ := o2; exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a, b, c, .inr hh⟩)))
  obtain ⟨he, hrest⟩ := llfill_first_values h' rfl rfl rfl (by simpa using c1) (by simpa using c2)
    (fun a b c hh => l1 ⟨a, b, c, hh⟩) (fun a b c hh => l2 ⟨a, b, c, hh⟩)
    (fun a b c hh => o1 ⟨a, b, c, hh⟩) (fun a b c hh => o2 ⟨a, b, c, hh⟩)
  exact Or.inl ⟨he, (hrest rfl).2⟩

@[rocq_alias iriswasm.sfill_const_list]
theorem sfill_const_list (sh : SimpleValidHoled) (es : List AdministrativeInstruction)
    (h : constList (sfill sh es) = true) : constList es = true := by
  cases sh <;> simp_all [sfill, constList, isConst, vToEList]

@[rocq_alias iriswasm.call_host_no_reduce]
theorem call_host_no_reduce (tf : FunctionType) (h : Hostfuncidx) (vcs : List Value)
    (s0 : StoreRecord) (f : Frame) (s'0 : StoreRecord) (f' : Frame)
    (es' : List AdministrativeInstruction) (llh : Llholed) (LI : List AdministrativeInstruction)
    (hLI : llfill llh [.callHost tf h vcs] = LI) (hred : Reduce s0 f LI s'0 f' es') : False := by
  subst hLI
  have h1 := val_head_stuck_reduce hred
  have h2 := to_of_val (.callHostV tf h vcs llh)
  simp only [ofVal] at h2
  simp [h1] at h2

@[rocq_alias iriswasm.execute_action_det]
theorem execute_action_det (f : HostAction) (s : StoreRecord) (vcs : List Value) (s1 : StoreRecord)
    (f0 : Frame) (res1 : List AdministrativeInstruction) (s2 : StoreRecord)
    (res2 : List AdministrativeInstruction) (h1 : ExecuteAction f s f0 vcs s1 res1)
    (h2 : ExecuteAction f s f0 vcs s2 res2) : s1 = s2 ∧ res1 = res2 := by
  cases h1 <;> cases h2 <;> simp_all

@[rocq_alias iriswasm.llfill_trap_singleton]
theorem llfill_trap_singleton (es : AdministrativeInstruction) (lh : Llholed)
    (h : llfill lh [es] = [.trap]) : lh = .base [] [] ∧ es = .trap := by
  cases lh with
  | base bef aft =>
    cases bef <;> cases aft <;> simp_all [llfill, vToEList]
  | label bef => cases bef <;> simp [llfill, vToEList] at h
  | «local» bef => cases bef <;> simp [llfill, vToEList] at h

@[rocq_alias iriswasm.call_host_reduce_det]
theorem call_host_reduce_det (s : StoreRecord) (vis : ViStore) (ms : List Module) (idecs : List HostE)
    (fs : List HostAction) (tf : FunctionType) (h : Hostfuncidx) (vcs : List Value)
    (s1 : StoreRecord) (vis1 : ViStore) (ms1 : List Module) (idecs1 : List HostE)
    (fs1 : List HostAction) (f1 : Frame) (es1 : List AdministrativeInstruction)
    (s2 : StoreRecord) (vis2 : ViStore) (ms2 : List Module) (idecs2 : List HostE)
    (fs2 : List HostAction) (f2 : Frame) (es2 : List AdministrativeInstruction) (f0 : Frame)
    (llh : Llholed) (LI : List AdministrativeInstruction)
    (hLI : llfill llh [.callHost tf h vcs] = LI)
    (hred1 : HostReduce s vis ms idecs fs f0 LI s1 vis1 ms1 idecs1 fs1 f1 es1)
    (hred2 : HostReduce s vis ms idecs fs f0 LI s2 vis2 ms2 idecs2 fs2 f2 es2) :
    (s1, vis1, ms1, idecs1, fs1, f1, es1) = (s2, vis2, ms2, idecs2, fs2, f2, es2) := by
  have hnc : constList LI = true → False := fun hc => by
    have := llfill_const _ _ _ hLI hc; simp [constList, isConst] at this
  have hnr : ∀ {s f s' f' es'}, Reduce s f LI s' f' es' → False :=
    fun hr => call_host_no_reduce _ _ _ _ _ _ _ _ _ _ hLI hr
  have hnt : LI = [.trap] → False := fun ht => by
    have := (llfill_trap_singleton _ _ (hLI.trans ht)).2; cases this
  have huniq : ∀ lh tf' h' vcs', llfill lh [.callHost tf' h' vcs'] = LI →
      tf' = tf ∧ h' = h ∧ vcs' = vcs ∧ lh = llh := by
    intro lh tf' h' vcs' hl
    rcases llfill_unique _ _ _ _ (hl.trans hLI.symm) with
      ⟨he, hlh⟩ | hc | hc | ⟨_, _, _, hc | hc⟩ | ⟨_, _, _, hc | hc⟩ <;> simp_all [isConst]
  cases hred1 with
  | callHostAction =>
    rename_i hh1 hf1 hl1 hex1 hl1'
    subst hh1
    obtain ⟨rfl, rfl, rfl, rfl⟩ := huniq _ _ _ _ hl1
    cases hred2 with
    | callHostAction =>
      rename_i hh2 hf2 hl2 hex2 hl2'
      subst hh2
      obtain ⟨-, hheq, rfl, rfl⟩ := huniq _ _ _ _ hl2
      cases hheq; rw [hf1] at hf2; cases hf2
      obtain ⟨rfl, rfl⟩ := execute_action_det _ _ _ _ _ _ _ _ hex1 hex2
      subst hl1' hl2'; rfl
    | callHostInstantiate =>
      rename_i hh2 hf2 hl2 hl2'
      subst hh2
      obtain ⟨-, hheq, -, rfl⟩ := huniq _ _ _ _ hl2
      cases hheq; rw [hf1] at hf2; cases hf2; cases hex1
    | hostStep => exact (hnc ‹_›).elim
    | hostStepInitOob => exact (hnc ‹_›).elim
    | wasmStep => exact (hnr ‹_›).elim
    | getGlobal => exact (hnc ‹_›).elim
    | trap => exact (hnt rfl).elim
  | callHostInstantiate =>
    rename_i hh1 hf1 hl1 hl1'
    subst hh1
    obtain ⟨rfl, rfl, rfl, rfl⟩ := huniq _ _ _ _ hl1
    cases hred2 with
    | callHostAction =>
      rename_i hh2 hf2 hl2 hex2 hl2'
      subst hh2
      obtain ⟨-, hheq, -, rfl⟩ := huniq _ _ _ _ hl2
      cases hheq; rw [hf1] at hf2; cases hf2; cases hex2
    | callHostInstantiate =>
      rename_i hh2 hf2 hl2 hl2'
      subst hh2
      obtain ⟨-, hheq, -, rfl⟩ := huniq _ _ _ _ hl2
      cases hheq; rw [hf1] at hf2; cases hf2
      subst hl1' hl2'; rfl
    | hostStep => exact (hnc ‹_›).elim
    | hostStepInitOob => exact (hnc ‹_›).elim
    | wasmStep => exact (hnr ‹_›).elim
    | getGlobal => exact (hnc ‹_›).elim
    | trap => exact (hnt rfl).elim
  | hostStep => exact (hnc ‹_›).elim
  | hostStepInitOob => exact (hnc ‹_›).elim
  | wasmStep => exact (hnr ‹_›).elim
  | getGlobal => exact (hnc ‹_›).elim
  | trap => exact (hnt rfl).elim

@[rocq_alias iriswasm.get_global_host_det]
theorem get_global_host_det (he : Globaladdr) (s : StoreRecord) (vis : ViStore) (ms : List Module)
    (fs : List HostAction) (f0 : Frame) (vs : List AdministrativeInstruction)
    (s1 : StoreRecord) (vis1 : ViStore) (ms1 : List Module) (idecs1 : List HostE)
    (fs1 : List HostAction) (f1 : Frame) (vs1 vs2 : List AdministrativeInstruction)
    (s2 : StoreRecord) (vis2 : ViStore) (ms2 : List Module) (idecs2 : List HostE)
    (fs2 : List HostAction) (f2 : Frame) (hconst : constList vs = true)
    (hred1 : HostReduce s vis ms [.getGlobal he] fs f0 vs s1 vis1 ms1 idecs1 fs1 f1 vs1)
    (hred2 : HostReduce s vis ms [.getGlobal he] fs f0 vs s2 vis2 ms2 idecs2 fs2 f2 vs2) :
    (s1, vis1, ms1, idecs1, fs1, f1, vs1) = (s2, vis2, ms2, idecs2, fs2, f2, vs2) := by
  have hncall : ∀ {lh tf h vcs}, llfill lh [.callHost tf h vcs] = vs → False := fun hl => by
    have := llfill_const _ _ _ hl hconst; simp [constList, isConst] at this
  cases hred1 with
  | getGlobal =>
    rename_i hg1 _
    cases hred2 with
    | getGlobal => rename_i hg2 _; rw [hg1] at hg2; cases hg2; rfl
    | callHostAction => exact (hncall ‹_›).elim
    | callHostInstantiate => exact (hncall ‹_›).elim
    | wasmStep => exact (values_no_reduce ‹_› hconst).elim
    | trap => simp [constList, isConst] at hconst
  | callHostAction => exact (hncall ‹_›).elim
  | callHostInstantiate => exact (hncall ‹_›).elim
  | wasmStep => exact (values_no_reduce ‹_› hconst).elim
  | trap => simp [constList, isConst] at hconst

@[rocq_alias iriswasm.trap_host_det]
theorem trap_host_det (g : HostE) (s : StoreRecord) (vis : ViStore) (ms : List Module)
    (fs : List HostAction) (f0 : Frame)
    (s1 : StoreRecord) (vis1 : ViStore) (ms1 : List Module) (idecs1 : List HostE)
    (fs1 : List HostAction) (f1 : Frame) (vs1 vs2 : List AdministrativeInstruction)
    (s2 : StoreRecord) (vis2 : ViStore) (ms2 : List Module) (idecs2 : List HostE)
    (fs2 : List HostAction) (f2 : Frame)
    (hred1 : HostReduce s vis ms [g] fs f0 [.trap] s1 vis1 ms1 idecs1 fs1 f1 vs1)
    (hred2 : HostReduce s vis ms [g] fs f0 [.trap] s2 vis2 ms2 idecs2 fs2 f2 vs2) :
    (s1, vis1, ms1, idecs1, fs1, f1, vs1) = (s2, vis2, ms2, idecs2, fs2, f2, vs2) := by
  have hncall : ∀ {lh tf h vcs}, llfill lh [.callHost tf h vcs] = [.trap] → False := fun hl => by
    have := (llfill_trap_singleton _ _ hl).2; cases this
  cases hred1 with
  | trap =>
    cases hred2 with
    | trap => rfl
    | callHostAction => exact (hncall ‹_›).elim
    | callHostInstantiate => exact (hncall ‹_›).elim
    | wasmStep => exact (test_no_reduce_trap ‹_›).elim
    | getGlobal => simp [constList, isConst] at *
  | callHostAction => exact (hncall ‹_›).elim
  | callHostInstantiate => exact (hncall ‹_›).elim
  | wasmStep => exact (test_no_reduce_trap ‹_›).elim
  | hostStep => simp [constList, isConst] at *
  | hostStepInitOob => simp [constList, isConst] at *
  | getGlobal => simp [constList, isConst] at *

@[rocq_alias iriswasm.host_expr]
abbrev HostExpr := List HostE × List AdministrativeInstruction

/-- Like `Val`, without `callHostV`, `brV` and `retV`. -/
@[rocq_alias iriswasm.host_val]
inductive HostVal where
  | immHV : List Value → HostVal
  | trapHV
  deriving DecidableEq, Inhabited

@[rocq_alias iriswasm.val_of_host_val]
def valOfHostVal : HostVal → Val
  | .immHV vs => .immV vs
  | .trapHV => .trapV

@[rocq_alias iriswasm.iris_host.state]
abbrev HostState := StoreRecord × ViStore × List Module × List HostAction × Frame

#rocq_ignore iriswasm.iris_host.observation "`unit`, identical to `IrisWasm.Observation`"

@[rocq_alias iriswasm.iris_host.of_val]
def hostOfVal (v : HostVal) : HostExpr := ([], ofVal (valOfHostVal v))

@[rocq_alias iriswasm.iris_host.of_val_imm]
theorem IrisHost.of_val_imm (vs : List Value) :
    (([], vs.map fun v => .basic (.const v)) : HostExpr) = hostOfVal (.immHV vs) := rfl

@[rocq_alias iriswasm.iris_host.to_val]
def hostToVal : HostExpr → Option HostVal
  | (_ :: _, _) => none
  | ([], wes) =>
    match toVal wes with
    | some (.immV vs) => some (.immHV vs)
    | some .trapV => some .trapHV
    | _ => none

@[rocq_alias iriswasm.iris_host.prim_step]
def hostPrimStep : HostExpr × HostState → List Observation → HostExpr × HostState × List HostExpr →
    Prop
  | ((hes, wes), (ws, vis, ms, fs, f)), os, ((hes', wes'), (ws', vis', ms', fs', f'), forkEs') =>
    HostReduce ws vis ms hes fs f wes ws' vis' ms' hes' fs' f' wes' ∧ os = [] ∧ forkEs' = []

@[rocq_alias iriswasm.iris_host.to_of_val]
theorem IrisHost.to_of_val (v : HostVal) : hostToVal (hostOfVal v) = some v := by
  cases v <;> simp [hostOfVal, hostToVal, valOfHostVal, IrisWasm.to_of_val]

@[rocq_alias iriswasm.iris_host.of_to_val]
theorem IrisHost.of_to_val (e : HostExpr) (v : HostVal) (h : hostToVal e = some v) :
    hostOfVal v = e := by
  obtain ⟨_ | _, wes⟩ := e
  · simp only [hostToVal] at h
    split at h <;> cases h <;> simp [hostOfVal, valOfHostVal, IrisWasm.of_to_val _ _ ‹_›]
  · simp [hostToVal] at h

@[rocq_alias iriswasm.iris_host.val_head_stuck]
theorem IrisHost.val_head_stuck (e1 : HostExpr) (s1 : HostState) (κ : List Observation)
    (e2 : HostExpr) (s2 : HostState) (efs : List HostExpr)
    (h : hostPrimStep (e1, s1) κ (e2, s2, efs)) : hostToVal e1 = none := by
  obtain ⟨hes, wes⟩ := e1; obtain ⟨_, _, _, _, _⟩ := s1; obtain ⟨_, _⟩ := e2
  obtain ⟨_, _, _, _, _⟩ := s2
  have hcall : ∀ lh tf h vcs, toVal (llfill lh [.callHost tf h vcs]) = some (.callHostV tf h vcs lh) :=
    fun lh tf h vcs => IrisWasm.to_of_val (.callHostV tf h vcs lh)
  cases hes with
  | cons => rfl
  | nil =>
    obtain ⟨hr, -, -⟩ := h
    cases hr with
    | callHostAction => subst_vars; simp [hostToVal, hcall]
    | callHostInstantiate => subst_vars; simp [hostToVal, hcall]
    | wasmStep => simp [hostToVal, IrisWasm.val_head_stuck_reduce ‹_›]

@[rocq_alias iriswasm.wasm_host_lang, rocq_alias iriswasm.wasm_host_mixin]
instance hostLanguage : Language HostExpr HostState Observation HostVal where
  primStep := hostPrimStep
  toVal := hostToVal
  ofVal := hostOfVal
  coe_of_toVal_eq_some := IrisHost.of_to_val _ _
  toVal_coe := IrisHost.to_of_val
  val_stuck := IrisHost.val_head_stuck _ _ _ _ _ _

/-- The host extends the Wasm store with the vi store, module declarations and host actions. -/
@[rocq_alias iriswasm.hvisG]
class HvisG (GF : BundledGFunctors) where
  genG : GhostMapG GF Nat ModuleExport NatMap
  visGName : GName

@[rocq_alias iriswasm.hmsG]
class HmsG (GF : BundledGFunctors) where
  genG : GhostMapG GF Nat Module NatMap
  msGName : GName

@[rocq_alias iriswasm.hasG]
class HasG (GF : BundledGFunctors) where
  genG : GhostMapG GF Nat HostAction NatMap
  haGName : GName

attribute [reducible, instance] HvisG.genG HmsG.genG HasG.genG

#rocq_ignore iriswasm.iris_host.proph_id "unused"
#rocq_ignore iriswasm.eqdecision_vi "`Vi = Nat` has `DecidableEq`"
#rocq_ignore iriswasm.iris_host.eqdecision_frame "`Frame` derives `DecidableEq`"
#rocq_ignore iriswasm.eqdecision_module "`Module` derives `DecidableEq`"
#rocq_ignore iriswasm.eqdecision_module_export "`ModuleExport` derives `DecidableEq`"
#rocq_ignore iriswasm.eqdecision_inst_decl "`HostE` derives `DecidableEq`"
#rocq_ignore iriswasm.eqdecision_host_action "`HostAction` derives `DecidableEq`"

end Iris_host_def

/-! ### Host ghost-state notations -/

section notations

/-- `n ↦[ha]{ q } f`: host action `f` at host function index `n`. -/
syntax:50 term:51 " ↦[ha]{ " term " } " term:51 : term
syntax:50 term:51 " ↦[ha] " term:51 : term
/-- `n ↪[vis]{ q } v`: export `v` at vi `n`. -/
syntax:50 term:51 " ↪[vis]{ " term " } " term:51 : term
syntax:50 term:51 " ↪[vis] " term:51 : term
/-- `n ↪[mods]{ q } m`: module declaration `m` at index `n`. -/
syntax:50 term:51 " ↪[mods]{ " term " } " term:51 : term
syntax:50 term:51 " ↪[mods] " term:51 : term

section
variable {GF : BundledGFunctors}

/-- Body of `n ↦[ha]{ q } f`. -/
def haOwn [HasG GF] (q : DFrac) (n : Nat) (f : HostAction) : IProp GF :=
  ghost_map_elem (H := NatMap) (HasG.haGName GF) q n f

/-- Body of `n ↪[vis]{ q } v`. -/
def visOwn [HvisG GF] (q : DFrac) (n : Nat) (v : ModuleExport) : IProp GF :=
  ghost_map_elem (H := NatMap) (HvisG.visGName GF) q n v

/-- Body of `n ↪[mods]{ q } m`. -/
def modsOwn [HmsG GF] (q : DFrac) (n : Nat) (m : Module) : IProp GF :=
  ghost_map_elem (H := NatMap) (HmsG.msGName GF) q n m

end

macro_rules
  | `($n ↦[ha]{ $q } $f) => `(haOwn $q $n $f)
  | `($n ↦[ha] $f) => `(haOwn (DFrac.own 1) $n $f)
  | `($n ↪[vis]{ $q } $v) => `(visOwn $q $n $v)
  | `($n ↪[vis] $v) => `(visOwn (DFrac.own 1) $n $v)
  | `($n ↪[mods]{ $q } $v) => `(modsOwn $q $n $v)
  | `($n ↪[mods] $v) => `(modsOwn (DFrac.own 1) $n $v)

end notations

variable {hlc : HasLC} {GF : BundledGFunctors}

section host_irisGS
variable [WasmG hlc GF] [HvisG GF] [HmsG GF] [HasG GF]

/-- Body of the host state interpretation (Coq `host_heapG_irisG`'s `state_interp`). -/
def hostStateInterp : HostState → IProp GF
  | (s, vis, ms, fs, f) => iprop(
    genHeapInterp (G := WasmG.funcHs) (gmapOfList s.funcs) ∗
    genHeapInterp (G := WasmG.tabHs) (gmapOfTable s.tables) ∗
    genHeapInterp (G := WasmG.memHs) (gmapOfMemory s.mems) ∗
    genHeapInterp (G := WasmG.globHs) (gmapOfList s.globals) ∗
    ghost_map_auth (HvisG.visGName GF) (DFrac.own 1) vis ∗
    ghost_map_auth (HmsG.msGName GF) (DFrac.own 1) (gmapOfList ms) ∗
    ghost_map_auth (HasG.haGName GF) (DFrac.own 1) (gmapOfList fs) ∗
    ghost_map_auth (WasmG.frameGName GF) (DFrac.own 1)
      (insert (PartialMap.empty : UnitMapF Frame) () f) ∗
    genHeapInterp (G := WasmG.memsizeHs) (gmapOfList (s.mems.map memLengthMeta)) ∗
    genHeapInterp (G := WasmG.tabsizeHs) (gmapOfList (s.tables.map tabSize)) ∗
    genHeapInterp (G := WasmG.memlimitHs) (gmapOfList (s.mems.map (·.type.limits.max))) ∗
    genHeapInterp (G := WasmG.tablimitHs) (gmapOfList (s.tables.map (·.maxOpt))))

instance hostStateInterpInst : StateInterp HostState Observation GF where
  stateInterp σ _ _ _ := hostStateInterp σ

/-- Coq `host_heapG_irisG`: the host language uses iris-lean's standard weakest precondition. -/
@[rocq_alias iriswasm.host_heapG_irisG]
instance hostIrisGS : IrisGS_gen hlc HostExpr GF where
  invGS := WasmG.invGS
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono _ _ _ _ := by
    let := @WasmG.invGS hlc GF _
    exact fupd_intro

theorem hostStateInterp_eq (σ : HostState) (ns : Nat) (obs : List Observation) (nt : Nat) :
    Iris.stateInterp (GF := GF) σ ns obs nt = hostStateInterp σ := rfl

end host_irisGS

/-! ## Host lifting rules -/

/-- The Wasm state interpretation, unfolded. -/
private theorem wasm_stateInterp_eq [WasmG hlc GF] {ws : StoreRecord} {locs : List Value} {inst : Instance}
    {ns : Nat} {obs : List Observation} {nt : Nat} :
    @Iris.stateInterp State Observation GF (wasmIrisGS (hlc := hlc)).toStateInterp
      (ws, locs, inst) ns obs nt ⊣⊢ iprop(
    genHeapInterp (G := WasmG.funcHs) (gmapOfList ws.funcs) ∗
    genHeapInterp (G := WasmG.tabHs) (gmapOfTable ws.tables) ∗
    genHeapInterp (G := WasmG.memHs) (gmapOfMemory ws.mems) ∗
    genHeapInterp (G := WasmG.globHs) (gmapOfList ws.globals) ∗
    ghost_map_auth (WasmG.frameGName GF) (DFrac.own 1)
      (insert (PartialMap.empty : UnitMapF Frame) () ⟨locs, inst⟩) ∗
    genHeapInterp (G := WasmG.memsizeHs) (gmapOfList (ws.mems.map memLengthMeta)) ∗
    genHeapInterp (G := WasmG.tabsizeHs) (gmapOfList (ws.tables.map tabSize)) ∗
    genHeapInterp (G := WasmG.memlimitHs) (gmapOfList (ws.mems.map (·.type.limits.max))) ∗
    genHeapInterp (G := WasmG.tablimitHs) (gmapOfList (ws.tables.map (·.maxOpt)))) := .rfl

/-- `genHeap_valid` without the update modality (and without consuming the resources). -/
private theorem host_heap_lookup {L V : Type _} {H : Type _ → Type _} [LawfulFiniteMap H L]
    {G : genHeapGS L V GF H} {σ : H V} {l : L} {dq : DFrac} {v : V} :
    ⊢ (genHeapInterp (G := G) σ -∗ pointsTo (G := G) l dq v -∗ ⌜get? σ l = some v⌝ : IProp GF) := by
  unfold genHeapInterp pointsTo
  iintro ⟨%m, -, Hσ, -⟩ Hl
  iapply ghost_map_lookup $$ Hσ Hl

theorem callHost_hostToVal {hes : List HostE} {llh : Llholed} {tf : FunctionType}
    {h : Hostfuncidx} {vcs : List Value} {LI : List AdministrativeInstruction}
    (hLI : llfill llh [.callHost tf h vcs] = LI) : hostToVal ((hes, LI) : HostExpr) = none := by
  cases hes with
  | cons => rfl
  | nil =>
    have := IrisWasm.to_of_val (.callHostV tf h vcs llh)
    simp only [ofVal] at this
    subst hLI; simp [hostToVal, this]

section host_lifting
variable [WasmG hlc GF] [HvisG GF] [HmsG GF] [HasG GF]

@[rocq_alias iriswasm.wp_call_host_action_no_state_change]
theorem wp_call_host_action_no_state_change (s : Stuckness) (E : CoPset) (hes : List HostE)
    (tf : FunctionType) (h : Hostfuncidx) (hi : Nat) (f : HostAction) (vcs : List Value)
    (Φ : HostVal → IProp GF) (res : List AdministrativeInstruction) (llh : Llholed)
    (LI LI' : List AdministrativeInstruction) (hh : h = .hostfuncidx hi)
    (hLI : llfill llh [.callHost tf h vcs] = LI) (hLI' : llfill llh res = LI')
    (hexec : ∀ s0 f0, ExecuteAction f s0 f0 vcs s0 res) :
    iprop(hi ↦[ha] f ∗ ▷ (hi ↦[ha] f -∗ WP ((hes, LI') : HostExpr) @ s ; E {{ v, Φ v }}))
      ⊢ WP ((hes, LI) : HostExpr) @ s ; E {{ v, Φ v }} := by
  let := @WasmG.invGS hlc GF _
  iintro ⟨Hhi, Hwp⟩
  iapply wp_lift_step (callHost_hostToVal hLI)
  iintro %σ %ns %obs %obs' %nt Hσ
  obtain ⟨ws, vi, ms, has, f0⟩ := σ
  rw [hostStateInterp_eq]; simp only [hostStateInterp]
  icases Hσ with ⟨Hf, Ht, Hm, Hg, Hvis, Hms, Hha, Hfr, Hmsz, Htsz, Hml, Htl⟩
  unfold haOwn
  ihave %hf := ghost_map_lookup $$ [$Hha] [$Hhi]
  rw [gmap_of_list_lookup] at hf
  have hred := HostReduce.callHostAction ws vi ms hes _ tf h hi f vcs has res LI LI' llh f0 hh hf
    (hexec _ _) hLI hLI'
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplit
  · ipureintro; cases s <;> simp only [Stuckness.MaybeReducible] <;>
      exact ⟨[], (hes, LI'), (ws, vi, ms, has, f0), [], hred, rfl, rfl⟩
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  obtain ⟨hes2, es2⟩ := e₂
  obtain ⟨ws2, vi2, ms2, has2, f2⟩ := σ₂
  obtain ⟨Hstep, rfl, rfl⟩ := Hstep
  have := call_host_reduce_det (hLI := hLI) (hred1 := Hstep) (hred2 := hred)
  simp only [Prod.mk.injEq] at this
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := this
  imod Hclose
  imodintro
  rw [hostStateInterp_eq]; simp only [hostStateInterp]
  iframe
  simp only [Algebra.BigOpL.bigOpL_nil]
  isplitl [Hwp Hhi]
  · iapply Hwp $$ Hhi
  · iempintro

@[rocq_alias iriswasm.wp_get_global_host]
theorem wp_get_global_host (s : Stuckness) (E : CoPset) (g : Nat) (v : Global) (vs : List Value)
    (Φ : HostVal → IProp GF) :
    ⊢ g ↦[wg] v -∗ ▷ (g ↦[wg] v -∗ Φ (.immHV (v.val :: vs))) -∗
      WP (([.getGlobal g], vToEList vs) : HostExpr) @ s ; E {{ Φ }} := by
  let := @WasmG.invGS hlc GF _
  iintro Hglob HΦ
  iapply wp_lift_atomic_step (rfl : hostToVal (([.getGlobal g], vToEList vs) : HostExpr) = none)
  iintro %σ %ns %obs %obs' %nt Hσ
  obtain ⟨ws, vi, ms, has, f0⟩ := σ
  rw [hostStateInterp_eq]; simp only [hostStateInterp]
  icases Hσ with ⟨Hf, Ht, Hm, Hg, Hvis, Hms, Hha, Hfr, Hmsz, Htsz, Hml, Htl⟩
  ihave %hg := host_heap_lookup $$ [$Hg] [$Hglob]
  rw [gmap_of_list_lookup] at hg
  have hred := HostReduce.getGlobal ws f0 vi ms g v has _ hg (v_to_e_is_const_list vs)
  imodintro
  isplit
  · ipureintro; cases s <;> simp only [Stuckness.MaybeReducible] <;>
      exact ⟨[], ([], _), (ws, vi, ms, has, f0), [], hred, rfl, rfl⟩
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  obtain ⟨hes2, es2⟩ := e₂
  obtain ⟨ws2, vi2, ms2, has2, f2⟩ := σ₂
  obtain ⟨Hstep, rfl, rfl⟩ := Hstep
  have := get_global_host_det (hconst := v_to_e_is_const_list vs) (hred1 := Hstep) (hred2 := hred)
  simp only [Prod.mk.injEq] at this
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := this
  imodintro
  rw [hostStateInterp_eq]; simp only [hostStateInterp]
  iframe
  simp only [Algebra.BigOpL.bigOpL_nil]
  isplitl [HΦ Hglob]
  · iexists .immHV (v.val :: vs)
    isplit
    · ipureintro; exact IrisHost.to_of_val (.immHV (v.val :: vs))
    · iapply HΦ $$ Hglob
  · iempintro

@[rocq_alias iriswasm.wp_get_global_trap_host]
theorem wp_get_global_trap_host (s : Stuckness) (E : CoPset) (g : Nat) (Φ : HostVal → IProp GF) :
    ⊢ ▷ Φ .trapHV -∗ WP (([.getGlobal g], [.trap]) : HostExpr) @ s ; E {{ Φ }} := by
  let := @WasmG.invGS hlc GF _
  iintro HΦ
  iapply wp_lift_atomic_step (rfl : hostToVal (([.getGlobal g], [.trap]) : HostExpr) = none)
  iintro %σ %ns %obs %obs' %nt Hσ
  obtain ⟨ws, vi, ms, has, f0⟩ := σ
  have hred := HostReduce.trap ws vi ms g has f0
  imodintro
  isplit
  · ipureintro; cases s <;> simp only [Stuckness.MaybeReducible] <;>
      exact ⟨[], ([], _), (ws, vi, ms, has, f0), [], hred, rfl, rfl⟩
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  obtain ⟨hes2, es2⟩ := e₂
  obtain ⟨ws2, vi2, ms2, has2, f2⟩ := σ₂
  obtain ⟨Hstep, rfl, rfl⟩ := Hstep
  have := trap_host_det (hred1 := Hstep) (hred2 := hred)
  simp only [Prod.mk.injEq] at this
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := this
  imodintro
  simp only [Algebra.BigOpL.bigOpL_nil]
  isplitl [Hσ]
  · iexact Hσ
  isplitl [HΦ]
  · iexists .trapHV
    isplit
    · ipureintro; exact IrisHost.to_of_val .trapHV
    · iexact HΦ
  · iempintro

@[rocq_alias iriswasm.wp_call_host_instantiate]
theorem wp_call_host_instantiate (s : Stuckness) (E : CoPset) (hes : List HostE) (h : Hostfuncidx)
    (hi : Nat) (f : HostE) (Φ : HostVal → IProp GF) (llh : Llholed)
    (LI LI' : List AdministrativeInstruction) (hh : h = .hostfuncidx hi)
    (hLI : llfill llh [.callHost (.tf [] []) h []] = LI) (hLI' : llfill llh [] = LI') :
    iprop(hi ↦[ha] .instantiate f ∗
      ▷ (hi ↦[ha] .instantiate f -∗ WP ((f :: hes, LI') : HostExpr) @ s ; E {{ v, Φ v }}))
      ⊢ WP ((hes, LI) : HostExpr) @ s ; E {{ v, Φ v }} := by
  let := @WasmG.invGS hlc GF _
  iintro ⟨Hhi, Hwp⟩
  iapply wp_lift_step (callHost_hostToVal hLI)
  iintro %σ %ns %obs %obs' %nt Hσ
  obtain ⟨ws, vi, ms, has, f0⟩ := σ
  rw [hostStateInterp_eq]; simp only [hostStateInterp]
  icases Hσ with ⟨Hf, Ht, Hm, Hg, Hvis, Hms, Hha, Hfr, Hmsz, Htsz, Hml, Htl⟩
  unfold haOwn
  ihave %hf := ghost_map_lookup $$ [$Hha] [$Hhi]
  rw [gmap_of_list_lookup] at hf
  have hred := HostReduce.callHostInstantiate ws vi ms hes h hi f has LI LI' llh f0 hh hf hLI hLI'
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplit
  · ipureintro; cases s <;> simp only [Stuckness.MaybeReducible] <;>
      exact ⟨[], (f :: hes, LI'), (ws, vi, ms, has, f0), [], hred, rfl, rfl⟩
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  obtain ⟨hes2, es2⟩ := e₂
  obtain ⟨ws2, vi2, ms2, has2, f2⟩ := σ₂
  obtain ⟨Hstep, rfl, rfl⟩ := Hstep
  have := call_host_reduce_det (hLI := hLI) (hred1 := Hstep) (hred2 := hred)
  simp only [Prod.mk.injEq] at this
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := this
  imod Hclose
  imodintro
  rw [hostStateInterp_eq]; simp only [hostStateInterp]
  iframe
  simp only [Algebra.BigOpL.bigOpL_nil]
  isplitl [Hwp Hhi]
  · iapply Hwp $$ Hhi
  · iempintro

@[rocq_alias iriswasm.wp_call_host_modify_table]
theorem wp_call_host_modify_table (s : Stuckness) (E : CoPset) (h : Hostfuncidx) (hi : Nat)
    (tabIdx funcIdx : I32) (LI LI' : List AdministrativeInstruction) (llh : Llholed) (f0 : Frame)
    (n : Nat) (funcIdx0 : Funcelem) (hes : List HostE) (a : Nat) (Φ : HostVal → IProp GF)
    (hh : h = .hostfuncidx hi)
    (hLI : llfill llh [.callHost (.tf [.i32, .i32] []) h [.int32 tabIdx, .int32 funcIdx]] = LI)
    (hLI' : llfill llh [] = LI')
    (ha : (innermostFrame llh f0).inst.funcs[Wasm.Int.natOfUint funcIdx]? = some a)
    (hn : (innermostFrame llh f0).inst.tab[0]? = some n) :
    iprop(↪[frame] f0 ∗ hi ↦[ha] .modifyTable ∗ n ↦[wt][ Wasm.Int.nOfUint tabIdx ] funcIdx0 ∗
      ▷ (↪[frame] f0 ∗ hi ↦[ha] .modifyTable ∗ n ↦[wt][ Wasm.Int.nOfUint tabIdx ] some a -∗
        WP ((hes, LI') : HostExpr) @ s ; E {{ Φ }}))
      ⊢ WP ((hes, LI) : HostExpr) @ s ; E {{ Φ }} := by
  let := @WasmG.invGS hlc GF _
  iintro ⟨Hf, Hhi, Hwt, Hwp⟩
  iapply wp_lift_step (callHost_hostToVal hLI)
  iintro %σ %ns %obs %obs' %nt Hσ
  obtain ⟨ws, vi, ms, has, f1⟩ := σ
  rw [hostStateInterp_eq]; simp only [hostStateInterp]
  icases Hσ with ⟨Hfn, Htab, Hm, Hg, Hvis, Hms, Hha, Hfr, Hmsz, Htsz, Hml, Htl⟩
  unfold haOwn frameOwn
  ihave %hf := ghost_map_lookup $$ [$Hha] [$Hhi]
  ihave %hfr := ghost_map_lookup $$ [$Hfr] [$Hf]
  ihave %ht := host_heap_lookup $$ [$Htab] [$Hwt]
  rw [gmap_of_list_lookup] at hf
  rw [get?_insert_eq rfl] at hfr
  cases hfr
  obtain ⟨tabs, htabs⟩ : ∃ rest, (innermostFrame llh f0).inst.tab = n :: rest := by
    cases h' : (innermostFrame llh f0).inst.tab <;> simp_all
  simp only [gmapOfTable, gmap_of_list_2d_lookup, List.getElem?_map] at ht
  obtain ⟨t, htn, htd⟩ : ∃ t, ws.tables[n]? = some t ∧ t.data[Wasm.Int.nOfUint tabIdx]? = some funcIdx0 := by
    cases h' : ws.tables[n]? <;> simp_all [tableToList]
  have hlt : Wasm.Int.nOfUint tabIdx < t.data.length := (List.getElem?_eq_some_iff.1 htd).1
  obtain ⟨entries, hset, hview⟩ := RunTable.set?_of_lt t.entries (Wasm.Int.nOfUint tabIdx)
    (some a) (by simpa [Tableinst.data] using hlt)
  let t' : Tableinst := { t with entries }
  let ws' : StoreRecord := { ws with tables := ws.tables.set n t' }
  have hupd : updateTable ws (innermostFrame llh f0) (Wasm.Int.natOfUint tabIdx) a = some ws' := by
    simp [updateTable, htabs, stabUpdate, htn, hset, ws', t']
  have hred := HostReduce.callHostAction ws vi ms hes ws' _ h hi .modifyTable _ has [] LI LI' llh f0 hh
    hf (.modifyTable _ _ _ _ _ _ ha hupd) hLI hLI'
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplit
  · ipureintro; cases s <;> simp only [Stuckness.MaybeReducible] <;>
      exact ⟨[], (hes, LI'), (ws', vi, ms, has, f0), [], hred, rfl, rfl⟩
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  obtain ⟨hes2, es2⟩ := e₂
  obtain ⟨ws2, vi2, ms2, has2, f2⟩ := σ₂
  obtain ⟨Hstep, rfl, rfl⟩ := Hstep
  have := call_host_reduce_det (hLI := hLI) (hred1 := Hstep) (hred2 := hred)
  simp only [Prod.mk.injEq] at this
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := this
  imod @genHeap_update _ _ _ _ _ WasmG.tabHs _ _ _ _ (some a) $$ [$Htab $Hwt] with ⟨Htab, Hwt⟩
  imod Hclose
  imodintro
  rw [hostStateInterp_eq]; simp only [hostStateInterp]
  have hmap : ∀ {β} (g : Tableinst → β), g t' = g t →
      (ws.tables.set n t').map g = ws.tables.map g := by
    intro β g hg
    rw [List.map_set, hg]
    apply List.ext_getElem?; intro i
    rw [List.getElem?_set]
    split <;> simp_all
    exact (List.getElem?_eq_some_iff.mp htn).1
  rw [gmap_of_table_insert n _ _ ws.tables t htn hlt t' hview] at *
  have hsize := congrArg List.length hview
  rw [hmap tabSize (by simpa [tabSize, t'] using hsize), hmap (·.maxOpt) rfl]
  iframe
  simp only [Algebra.BigOpL.bigOpL_nil]
  isplitl [Hwp Hhi Hf Hwt]
  · iapply Hwp
    iframe
  · iempintro

#rocq_ignore iriswasm.iris_host.reducible "use `PrimStep.Reducible`"

@[rocq_alias iriswasm.iris_host.wp_value]
theorem IrisHost.wp_value (s : Stuckness) (E : CoPset) (e : HostExpr) (v : HostVal)
    (Φ : HostVal → IProp GF) (h : hostToVal e = some v) : Φ v ⊢ WP e @ s ; E {{ Φ }} :=
  Iris.wp_value ⟨IrisHost.of_to_val e v h⟩

@[rocq_alias iriswasm.wp_lift_wasm]
theorem wp_lift_wasm (s : Stuckness) (E : CoPset) (δ : List HostE) (es : Expr)
    (Φ : HostVal → IProp GF) :
    WP es @ Stuckness.NotStuck ; E {{ v, WP ((δ, ofVal v) : HostExpr) @ s ; E {{ Φ }} }}
      ⊢ WP ((δ, es) : HostExpr) @ s ; E {{ Φ }} := by
  let := @WasmG.invGS hlc GF _
  iloeb as IH generalizing %es
  iintro Hwp
  cases he : toVal es with
  | some w =>
    ihave H := (IrisWp.wp_value_fupd (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)
      ⟨IrisWasm.of_to_val _ _ he⟩).1 $$ Hwp
    rw [← IrisWasm.of_to_val _ _ he]
    iapply Iris.fupd_wp
    iexact H
  | none =>
    have hnone : hostToVal ((δ, es) : HostExpr) = none := by
      cases δ <;> simp [hostToVal, he]
    iapply wp_lift_step_fupdN hnone
    iintro %σ %ns %obs %obs' %nt Hσ
    obtain ⟨ws, vis, ms, has, f⟩ := σ
    rw [hostStateInterp_eq]; simp only [hostStateInterp]
    icases Hσ with ⟨Hfn, Htab, Hm, Hg, Hvis, Hms, Hha, Hfr, Hmsz, Htsz, Hml, Htl⟩
    ihave H := (IrisWp.wp_unfold (ι := wasmIrisGS) (fun f => iprop(↪[frame] f))).1 $$ Hwp
    have he' : Iris.ProgramLogic.toVal es = none := he
    simp only [IrisWp.wp.pre, he']
    icases H $$ %(ws, f.locs, f.inst) %ns %obs %obs' %nt
      [Hfn Htab Hm Hg Hfr Hmsz Htsz Hml Htl] with >⟨%Hred, H⟩
    · iapply (wasm_stateInterp_eq (hlc := hlc)).2
      iframe
    imodintro
    isplitr
    · ipureintro
      simp only [Stuckness.MaybeReducible] at Hred
      obtain ⟨obs0, e₂, ⟨ws', locs', inst'⟩, eₜ, Hst, -, -⟩ := Hred
      cases s <;> simp only [Stuckness.MaybeReducible] <;>
        exact ⟨[], (δ, e₂), (ws', vis, ms, has, ⟨locs', inst'⟩), [], .wasmStep _ _ _ _ _ _ _ _ _ _ Hst,
          rfl, rfl⟩
    iintro %e₂ %σ₂ %eₜ %Hstep Hc
    obtain ⟨δ2, es2⟩ := e₂
    obtain ⟨ws2, vis2, ms2, has2, f2⟩ := σ₂
    obtain ⟨Hst, rfl, rfl⟩ := Hstep
    have hcl : constList es = true → False := fun hc => by
      obtain ⟨_, h⟩ := const_list_to_val es hc; simp [h] at he
    have hcall : ∀ {lh tf h vcs}, llfill lh [.callHost tf h vcs] = es → False := by
      intro lh tf h vcs hl
      have := IrisWasm.to_of_val (.callHostV tf h vcs lh); simp only [ofVal] at this
      rw [hl] at this; simp [this] at he
    have : Reduce ws f es ws2 f2 es2 ∧ vis2 = vis ∧ ms2 = ms ∧ δ2 = δ ∧ has2 = has := by
      cases Hst with
      | wasmStep => exact ⟨‹_›, rfl, rfl, rfl, rfl⟩
      | hostStep => exact (hcl ‹_›).elim
      | hostStepInitOob => exact (hcl ‹_›).elim
      | callHostAction => exact (hcall ‹_›).elim
      | callHostInstantiate => exact (hcall ‹_›).elim
      | getGlobal => exact (hcl ‹_›).elim
      | trap => simp [toVal, toValInstr, mergeValuesList, mergeValues] at he
    obtain ⟨hr, rfl, rfl, rfl, rfl⟩ := this
    dsimp only [step_fupdN]
    imod H $$ %es2 %(ws2, f2.locs, f2.inst) %([] : List Expr)
      %(show primStep (es, ws, f.locs, f.inst) [] (es2, (ws2, f2.locs, f2.inst), []) from
        ⟨hr, rfl, rfl⟩) Hc with H
    iintro !> !>
    imod H
    iintro !>
    iapply step_fupdN_wand $$ H
    iintro >⟨Hσ, %a, Ha, H, -⟩
    imodintro
    icases (wasm_stateInterp_eq (hlc := hlc)).1 $$ Hσ with
      ⟨Hfn, Htab, Hm, Hg, Hfr, Hmsz, Htsz, Hml, Htl⟩
    ihave H := H $$ Ha
    rw [hostStateInterp_eq]; simp only [hostStateInterp]
    isplitl [Hfn Htab Hm Hg Hvis Hms Hha Hfr Hmsz Htsz Hml Htl]
    · iframe
    simp only [Algebra.BigOpL.bigOpL_nil]
    isplitl [H]
    · iapply IH $$ %es2 H
    · iempintro

end host_lifting

/-! ## Structural host rules -/

section host_structural
variable [WasmG hlc GF] [HvisG GF] [HmsG GF] [HasG GF]

@[rocq_alias iriswasm.prim_step_inst_cons_reduce_nostart]
theorem prim_step_inst_cons_reduce_nostart (v_exps : List Vi) (modi : Nat) (m : Module)
    (v_imps : List Vimp) (ws1 : StoreRecord) (vis1 : ViStore) (ms1 : List Module)
    (ha1 : List HostAction) (f1 : Frame) (κ : List Observation) (es es' : List HostE)
    (wes : List AdministrativeInstruction) (σ2 : HostState) (efs : List HostExpr)
    (vs : List AdministrativeInstruction) (hmodi : ms1[modi]? = some m) (hstart : m.start = none)
    (hconst : constList vs = true)
    (hstep : hostPrimStep (((.instantiate v_exps modi v_imps :: es), vs), (ws1, vis1, ms1, ha1, f1))
      κ ((es', wes), σ2, efs)) :
    hostPrimStep (([.instantiate v_exps modi v_imps], []), (ws1, vis1, ms1, ha1, f1)) []
        (([], wes), σ2, []) ∧
      κ = [] ∧ efs = [] ∧ es' = es ∧ (wes = [] ∨ wes = [.trap]) := by
  obtain ⟨_, _, _, _, _⟩ := σ2
  obtain ⟨hr, rfl, rfl⟩ := hstep
  have hncall : ∀ {lh tf h vcs}, llfill lh [.callHost tf h vcs] = vs → False := fun hl => by
    have := llfill_const _ _ _ hl hconst; simp [constList, isConst] at this
  cases hr with
  | hostStep =>
    rename_i _ start hmap hlen hms hthose _ hinst hins
    have hst : start = none := by
      obtain ⟨_, _, _, _, _, _, -, -, -, -, -, -, -, -, hcs, -⟩ := hinst
      rw [hms] at hmodi; cases hmodi
      simpa [checkStart, hstart, optionBind, eq_comm] using hcs
    subst hst
    exact ⟨⟨.hostStep _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hms hthose hmap hinst hlen rfl hins,
      rfl, rfl⟩,
      rfl, rfl, rfl, Or.inl rfl⟩
  | hostStepInitOob =>
    exact ⟨⟨.hostStepInitOob (exps := []) _ _ _ _ _ _ _ _ _ _ _ _ _ ‹_› ‹_› ‹_› rfl ‹_›, rfl, rfl⟩,
      rfl, rfl, rfl, Or.inr rfl⟩
  | callHostAction => exact (hncall ‹_›).elim
  | callHostInstantiate => exact (hncall ‹_›).elim
  | wasmStep => exact (values_no_reduce ‹_› hconst).elim

omit [HvisG GF] [HasG GF] in
private theorem mods_lookup {M : NatMap Module} {n : Nat} {m : Module} :
    ⊢ (ghost_map_auth (HmsG.msGName GF) (DFrac.own 1) M -∗ n ↪[mods] m -∗
      ⌜get? M n = some m⌝ : IProp GF) := by
  unfold modsOwn
  iintro H1 H2
  iapply ghost_map_lookup $$ H1 H2

@[rocq_alias iriswasm.wp_seq_host_nostart]
theorem wp_seq_host_nostart (_s : Stuckness) (E : CoPset) (Φ Ψ : HostVal → IProp GF)
    (v_exps : List Vi) (modi : Nat) (v_imps : List Vimp) (m : Module) (es : List HostE)
    (vs : List AdministrativeInstruction) (hstart : m.start = none) (hconst : constList vs = true) :
    ⊢ (¬ Ψ .trapHV) -∗ modi ↪[mods] m -∗
      (modi ↪[mods] m -∗ WP (([.instantiate v_exps modi v_imps], []) : HostExpr) @ E
        {{ w, Ψ w ∗ modi ↪[mods] m }}) -∗
      (∀ w, Ψ w -∗ modi ↪[mods] m -∗ WP ((es, []) : HostExpr) @ E {{ v, Φ v }}) -∗
      WP ((.instantiate v_exps modi v_imps :: es, vs) : HostExpr) @ E {{ v, Φ v }} := by
  let := @WasmG.invGS hlc GF _
  iintro Hntrap Hmod Hes1 Hes2
  iapply wp_lift_step_fupdN
    (rfl : hostToVal ((.instantiate v_exps modi v_imps :: es, vs) : HostExpr) = none)
  iintro %σ %ns %obs %obs' %nt Hσ
  obtain ⟨ws, vis, ms, ha, f⟩ := σ
  rw [hostStateInterp_eq]; simp only [hostStateInterp]
  icases Hσ with ⟨Hfn, Htab, Hm, Hg, Hvis, Hms, Hha, Hfr, Hmsz, Htsz, Hml, Htl⟩
  ihave %hmod := mods_lookup $$ [$Hms] [$Hmod]
  rw [gmap_of_list_lookup] at hmod
  ihave Hes1 := Hes1 $$ Hmod
  ihave H := Iris.wp_unfold.1 $$ Hes1
  have hnv : Iris.ProgramLogic.toVal (([.instantiate v_exps modi v_imps], []) : HostExpr) = none :=
    rfl
  simp only [wp.pre, hnv]
  icases H $$ %(ws, vis, ms, ha, f) %ns %obs %obs' %nt
    [Hfn Htab Hm Hg Hvis Hms Hha Hfr Hmsz Htsz Hml Htl] with >⟨%Hred, H⟩
  · rw [hostStateInterp_eq]; simp only [hostStateInterp]; iframe
  imodintro
  isplitr
  · ipureintro
    simp only [Stuckness.MaybeReducible, PrimStep.Reducible] at Hred ⊢
    obtain ⟨obs0, ⟨he', we'⟩, ⟨ws', vis', ms', ha', f'⟩, eₜ, Hst, -, -⟩ := Hred
    cases Hst with
    | hostStep =>
      exact ⟨[], (es, _), (ws', vis', ms, ha, f), [],
        .hostStep _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ‹_› ‹_› ‹_› ‹_› ‹_› hconst ‹_›, rfl, rfl⟩
    | hostStepInitOob =>
      exact ⟨[], (es, _), (ws, vis, ms, ha, f), [],
        .hostStepInitOob (exps := []) _ _ _ _ _ _ _ _ _ _ _ _ _ ‹_› ‹_› ‹_› hconst ‹_›, rfl, rfl⟩
    | callHostAction =>
      exact absurd (llfill_is_nil _ _ ‹_›).1 (by simp)
    | callHostInstantiate =>
      exact absurd (llfill_is_nil _ _ ‹_›).1 (by simp)
    | wasmStep => exact (empty_no_reduce ‹_›).elim
  iintro %e₂ %σ₂ %eₜ %Hstep Hc
  obtain ⟨he2, we2⟩ := e₂
  obtain ⟨hstep', rfl, rfl, rfl, hwe⟩ :=
    prim_step_inst_cons_reduce_nostart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hmod hstart hconst Hstep
  dsimp only [step_fupdN]
  imod H $$ %([], we2) %σ₂ %([] : List HostExpr) %hstep' Hc with H
  iintro !> !>
  imod H
  iintro !>
  iapply step_fupdN_wand $$ H
  iintro >⟨Hσ, Hwp, -⟩
  simp only [Algebra.BigOpL.bigOpL_nil]
  rcases hwe with rfl | rfl
  · imod (Iris.wp_value_fupd (e := (([], []) : HostExpr)) (v := HostVal.immHV []) ⟨rfl⟩).1 $$ Hwp with ⟨HΨ, Hmod⟩
    imodintro
    isplitl [Hσ]
    · iexact Hσ
    isplitl [HΨ Hmod Hes2]
    · iapply Hes2 $$ HΨ Hmod
    · iempintro
  · imod (Iris.wp_value_fupd (e := (([], [.trap]) : HostExpr)) (v := HostVal.trapHV) ⟨rfl⟩).1 $$ Hwp with ⟨HΨ, -⟩
    iexfalso
    iapply Hntrap $$ HΨ

end host_structural

/-! ## Pure facts about instantiation used by the operational specification -/

private theorem forall₂_of_map_eq {A B C : Type} {R : A → B → Prop} {f : A → C} {g : B → C} :
    ∀ {l1 : List A} {l2 : List B}, l1.map f = l2.map g →
      (∀ a b, a ∈ l1 → b ∈ l2 → f a = g b → R a b) → Wasm.List.Forall₂ R l1 l2
  | [], [], _, _ => .nil
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: l1, b :: l2, h, hR => by
    simp only [List.map_cons, List.cons.injEq] at h
    exact .cons (hR a b (by simp) (by simp) h.1)
      (forall₂_of_map_eq h.2 fun a b ha hb => hR a b (by simp [ha]) (by simp [hb]))

private theorem forall₂_of_getElem? {A B : Type} {R : A → B → Prop} :
    ∀ {l1 : List A} {l2 : List B}, l1.length = l2.length →
      (∀ (k : Nat) a b, l1[k]? = some a → l2[k]? = some b → R a b) → Wasm.List.Forall₂ R l1 l2
  | [], [], _, _ => .nil
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: l1, b :: l2, h, hR =>
    .cons (hR 0 a b rfl rfl)
      (forall₂_of_getElem? (by simpa using h) fun k a b ha hb => hR (k + 1) a b ha hb)

private theorem those_lookup_export_vi (vis : ViStore) :
    ∀ (hs_imps : List Vimp) (v_imps : List ModuleExport), hs_imps.length = v_imps.length →
      (∀ (k : Nat) hs_imp v_imp, hs_imps[k]? = some hs_imp → v_imps[k]? = some v_imp →
        get? vis hs_imp = some v_imp) →
      those (hs_imps.map (lookupExportVi vis)) = some v_imps
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | x :: xs, y :: ys, hl, h => by
    have ih := those_lookup_export_vi vis xs ys (by simpa using hl)
      fun k a b ha hb => h (k + 1) a b ha hb
    rw [← those_those0] at ih ⊢
    simp [those0, lookupExportVi, h 0 x y rfl rfl, ih]

/-- The `Instantiate` predicate is satisfiable under the resources' pure side conditions. -/
private theorem instantiate_exists (ws : StoreRecord) (m : Module) (impDescs : List ModuleExportDesc)
    (t_imps t_exps : List ExternT) (hmt : ModuleTyping m t_imps t_exps)
    (hmr : ModuleRestrictions m) (hext : Wasm.List.Forall₂ (ExternalTyping ws) impDescs t_imps)
    (heb : ModuleElemBoundCheckGmap (gmapOfList ws.tables) impDescs m)
    (hdb : ModuleDataBoundCheckGmap (gmapOfList ws.mems) impDescs m) :
    ∃ s' inst, Instantiate ws m impDescs ((s', inst, m.exports.map fun e =>
        ({ name := e.name, desc := exportGetVExt inst e.desc } : ModuleExport)),
      optionBind (fun (iS : ModuleStart) => inst.funcs[match iS.func with | .funcidx i => i]?)
        m.start) := by
  obtain ⟨⟨g_inits, hg⟩, ⟨e_inits, he⟩, ⟨d_inits, hd⟩⟩ := hmr
  let inst : Instance :=
    { types := m.types
      funcs := extFuncAddrs impDescs ++ genIndex ws.funcs.length m.funcs.length
      tab := extTabAddrs impDescs ++ genIndex ws.tables.length m.tables.length
      memory := extMemAddrs impDescs ++ genIndex ws.mems.length m.mems.length
      globs := extGlobAddrs impDescs ++ genIndex ws.globals.length m.globals.length }
  have hglen : g_inits.length = m.globals.length := by
    simpa using (congrArg List.length hg).symm
  generalize hf : allocFuncs ws m.funcs inst = rf; rcases rf with ⟨s0, idf⟩
  generalize ht : allocTabs s0 (m.tables.map (·.type)) = rt; rcases rt with ⟨s1, idt⟩
  generalize hm : allocMems s1 m.mems = rm; rcases rm with ⟨s2, idm⟩
  generalize hgl : allocGlobs s2 m.globals g_inits = rg; rcases rg with ⟨s3, idg⟩
  obtain ⟨af1, -, af3, af4, af5⟩ := alloc_func_gen_index hf
  obtain ⟨at1, at2, -, at4, at5⟩ := alloc_tab_gen_index ht
  obtain ⟨am1, am2, -, am4, am5⟩ := alloc_mem_gen_index hm
  obtain ⟨ag1, -, -, ag4, ag5⟩ := alloc_glob_gen_index hglen hgl
  have htabs : s3.tables = ws.tables ++ m.tables.map (fun t =>
      ({ entries := RunTable.uniform t.type.limits.min none, maxOpt := t.type.limits.max } : Tableinst)) := by
    rw [← ag4, ← am4, at2, ← af3]; simp [Function.comp_def]
  have hmems : s3.mems = ws.mems ++ m.mems.map memMk := by
    rw [← ag5, am2, ← at4, ← af4]
  have hdata : checkBoundsData inst s3 m d_inits = true := by
    rw [checkBoundsData, Wasm.List.all2_Forall₂]
    refine forall₂_of_map_eq hd.symm fun c d _ hmem hoff => ?_
    have hb := hdb d hmem
    rcases d with ⟨⟨n⟩, off, ini⟩
    dsimp only at hoff hb ⊢
    subst hoff
    simp only [literalDataOffset, assertConst1Address_value, Option.map_some] at hb
    rcases hk : (extMems impDescs)[n]? with _ | ⟨⟨k⟩⟩
    · rw [hk] at hb
      rw [List.getElem?_eq_none_iff] at hk
      rcases hmt' : m.mems[n - (extMems impDescs).length]? with _ | mt
      · rw [hmt'] at hb; exact hb.elim
      rw [hmt'] at hb
      have hlt := (List.getElem?_eq_some_iff.1 hmt').1
      have hi : inst.memory[n]? = some (ws.mems.length + (n - (extMems impDescs).length)) := by
        simp only [inst, extMemAddrs, Function.comp_apply]
        rw [List.getElem?_append_right (by simpa using hk), List.length_map, gen_index_lookup _ _ _ hlt]
      rw [hi, hmems]; simp only
      rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
      simpa [hi, hmt', memMk, lengthMem] using hb
    · rw [hk] at hb
      simp only at hb
      rw [gmap_of_list_lookup] at hb
      rcases hti : ws.mems[k]? with _ | ti
      · rw [hti] at hb; exact hb.elim
      rw [hti] at hb
      have hn := (List.getElem?_eq_some_iff.1 hk).1
      have hkl := (List.getElem?_eq_some_iff.1 hti).1
      have hi : inst.memory[n]? = some k := by
        simp only [inst, extMemAddrs, Function.comp_apply]
        rw [List.getElem?_append_left (by simpa using hn), List.getElem?_map, hk]; rfl
      simp only [hi, hmems, List.getElem?_append_left hkl, hti]
      exact decide_eq_true hb
  let sTabs := initTabs s3 inst (e_inits.map BitVec.toNat) m.elem
  have hmemTabs : s3.mems = sTabs.mems :=
    (init_tabs_preserve (ws := s3) (inst := inst) (e_inits := e_inits.map BitVec.toNat)
      (melem := m.elem) (ws' := sTabs) rfl).2.1
  have hdataTabs : checkBoundsData inst sTabs m d_inits = true := by
    simpa only [checkBoundsData, ← hmemTabs] using hdata
  obtain ⟨s', hinit⟩ := initMems_exists_of_bounds hdataTabs
  refine ⟨s', inst, t_imps, t_exps, s3, g_inits, e_inits, d_inits, hmt, hext,
    ?_, ?_, ?_, ?_, ?_, hdata, by simp [checkStart], hinit⟩
  · simp only [allocModule, hf, ht, hm, hgl, Bool.and_eq_true, decide_eq_true_eq]
    and_intros <;> simp [inst, af1, extFuncAddrs, at1, extTabAddrs, af3, am1, extMemAddrs, af4, at4,
      ag1, extGlobAddrs, af5, at5, am5]
  · exact forall₂_of_map_eq hg fun g v _ _ h => by
      rw [h]; exact .refl
  · exact forall₂_of_map_eq he fun e v _ _ h => by
      rw [h]; exact .refl
  · exact forall₂_of_map_eq hd fun d v _ _ h => by
      rw [h]; exact .refl
  · rw [checkBoundsElem, Wasm.List.all2_Forall₂]
    refine forall₂_of_map_eq he.symm fun c e _ hmem hoff => ?_
    have hb := heb e hmem
    rcases e with ⟨⟨n⟩, off, ini⟩
    dsimp only at hoff hb ⊢
    subst hoff
    simp only [assertConst1I32] at hb
    rcases hk : (extTabs impDescs)[n]? with _ | ⟨⟨k⟩⟩
    · rw [hk] at hb
      rw [List.getElem?_eq_none_iff] at hk
      rcases hmt' : m.tables[n - (extTabs impDescs).length]? with _ | mt
      · rw [hmt'] at hb; exact hb.elim
      rw [hmt'] at hb
      have hlt := (List.getElem?_eq_some_iff.1 hmt').1
      have hi : inst.tab[n]? = some (ws.tables.length + (n - (extTabs impDescs).length)) := by
        simp only [inst, extTabAddrs, Function.comp_apply]
        rw [List.getElem?_append_right (by simpa using hk), List.length_map, gen_index_lookup _ _ _ hlt]
      rw [hi, htabs]; simp only
      rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
      simpa [hi, hmt', nOfInt, natOfInt, tabSize] using hb
    · rw [hk] at hb
      simp only at hb
      rw [gmap_of_list_lookup] at hb
      rcases hti : ws.tables[k]? with _ | ti
      · rw [hti] at hb; exact hb.elim
      rw [hti] at hb
      have hn := (List.getElem?_eq_some_iff.1 hk).1
      have hkl := (List.getElem?_eq_some_iff.1 hti).1
      have hi : inst.tab[n]? = some k := by
        simp only [inst, extTabAddrs, Function.comp_apply]
        rw [List.getElem?_append_left (by simpa using hn), List.getElem?_map, hk]; rfl
      simp only [hi, htabs, List.getElem?_append_left hkl, hti]
      exact decide_eq_true hb

/-- The exports and the start function of an instantiation result. -/
private theorem instantiate_exps_start {s : StoreRecord} {m : Module} {vimps : List VExt}
    {s' : StoreRecord} {inst : Instance} {exps : List ModuleExport} {start : Option Nat}
    (h : Instantiate s m vimps ((s', inst, exps), start)) :
    exps = m.exports.map (fun e =>
        ({ name := e.name, desc := exportGetVExt inst e.desc } : ModuleExport)) ∧
      start = optionBind (fun (iS : ModuleStart) => inst.funcs[match iS.func with
        | .funcidx i => i]?) m.start := by
  obtain ⟨_, _, _, _, _, _, -, -, ham, -, -, -, -, -, hcs, -⟩ := h
  simp only [allocModule, Bool.and_eq_true, decide_eq_true_eq] at ham
  simp only [checkStart, decide_eq_true_eq] at hcs
  exact ⟨ham.2, hcs.symm⟩

/-- A well-typed start function always resolves to a function address. -/
private theorem instantiate_start_some {s : StoreRecord} {m : Module} {vimps : List VExt}
    {s' : StoreRecord} {inst : Instance} {exps : List ModuleExport} {start : Option Nat}
    {nstart : Nat} (hstart : m.start = some ⟨.funcidx nstart⟩)
    (h : Instantiate s m vimps ((s', inst, exps), start)) : ∃ i, start = some i := by
  have hst := (instantiate_exps_start h).2
  obtain ⟨tImps, _, _, gInits, _, _, hmt, hext, ham, -⟩ := h
  simp only [allocModule] at ham
  generalize hf : allocFuncs s m.funcs inst = rf at ham
  rcases rf with ⟨s0, idf⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ham
  have hfu := ham.1.1.1.1.2
  obtain ⟨af1, -⟩ := alloc_func_gen_index hf
  have hcl := (vt_imps_comp_len hext).1
  obtain ⟨fts, _, hmt⟩ := hmt
  rcases m with ⟨_, mfs, _, _, _, _, _, mst, _, _⟩
  dsimp only at hstart hmt hst hfu af1
  subst hstart
  obtain ⟨hfts, -, -, -, -, -, hst', -⟩ := hmt
  simp only [predOption, moduleStartTyping, Bool.and_eq_true, decide_eq_true_eq] at hst'
  have hlen : nstart < inst.funcs.length := by
    have := congrArg List.length af1
    simp only [List.length_map, gen_index_length] at this
    rw [hfu]
    simp only [List.length_map, List.length_append, hcl, this, Wasm.List.Forall₂.length_eq hfts]
    simpa [moduleContext] using hst'.1
  simp only [optionBind] at hst
  exact ⟨_, hst.trans (List.getElem?_eq_getElem hlen)⟩

/-- Inversion of a host step instantiating a module whose bound checks hold. -/
private theorem instantiate_step_inv {ws : StoreRecord} {vis : ViStore} {ms : List Module}
    {hs_exps : List Vi} {hs_mod : Nat} {hs_imps : List Vimp} {idecls : List HostE}
    {has : List HostAction} {f : Frame} {m : Module} {v_imps : List ModuleExport}
    {ws2 : StoreRecord} {vis2 : ViStore} {ms2 : List Module} {idecls2 : List HostE}
    {has2 : List HostAction} {f2 : Frame} {es2 : List AdministrativeInstruction}
    (hmod : ms[hs_mod]? = some m) (hthose : those (hs_imps.map (lookupExportVi vis)) = some v_imps)
    (heb : ModuleElemBoundCheckGmap (gmapOfList ws.tables) (v_imps.map (·.desc)) m)
    (hdb : ModuleDataBoundCheckGmap (gmapOfList ws.mems) (v_imps.map (·.desc)) m)
    (hstep : HostReduce ws vis ms (.instantiate hs_exps hs_mod hs_imps :: idecls) has f []
      ws2 vis2 ms2 idecls2 has2 f2 es2) :
    ∃ inst start, Instantiate ws m (v_imps.map (·.desc)) ((ws2, inst, m.exports.map fun e =>
        ({ name := e.name, desc := exportGetVExt inst e.desc } : ModuleExport)), start) ∧
      insertExports vis hs_exps (m.exports.map fun e =>
        ({ name := e.name, desc := exportGetVExt inst e.desc } : ModuleExport)) = some vis2 ∧
      ms2 = ms ∧ idecls2 = idecls ∧ has2 = has ∧ f2 = f ∧ es2 = mapStart start := by
  cases hstep with
  | hostStep =>
    rename_i hmap' _ hm' hth' _ hinst' hins'
    rw [hmod] at hm'; cases hm'
    rw [hthose] at hth'; cases hth'
    subst hmap'
    obtain ⟨rfl, -⟩ := instantiate_exps_start hinst'
    exact ⟨_, _, hinst', hins', rfl, rfl, rfl, rfl, rfl⟩
  | hostStepInitOob =>
    rename_i hmap' hn hm' hth' _
    rw [hmod] at hm'; cases hm'
    rw [hthose] at hth'; cases hth'
    subst hmap'
    exact absurd ⟨heb, hdb⟩ hn
  | callHostAction => exact absurd (llfill_is_nil _ _ ‹_›).1 (by simp)
  | callHostInstantiate => exact absurd (llfill_is_nil _ _ ‹_›).1 (by simp)
  | wasmStep => exact (empty_no_reduce ‹_›).elim

/-! ## Operational instantiation specification -/

#rocq_ignore iriswasm.iris_host.forward "Ltac `assert`/`specialize` helper (duplicate of stdpp_aux.v); Lean uses `have`"

section Instantiation_spec_operational
variable [WasmG hlc GF] [HvisG GF] [HmsG GF] [HasG GF]

/-- Resources in the host vis store for the imports. -/
@[rocq_alias iriswasm.import_resources_host]
def importResourcesHost (hs_imps : List Vimp) (v_imps : List ModuleExport) : IProp GF :=
  iprop([∗list] _i ↦ hs_imp;v_imp ∈ hs_imps;v_imps, hs_imp ↪[vis] v_imp)

@[rocq_alias iriswasm.export_ownership_host]
def exportOwnershipHost (hs_exps : List Vi) : IProp GF :=
  iprop([∗list] _i ↦ hs_exp ∈ hs_exps, ∃ hv, hs_exp ↪[vis] hv)

/-- The export resources; the exports may re-export imports. -/
@[rocq_alias iriswasm.module_export_resources_host]
def moduleExportResourcesHost (hs_exps : List Vi) (m_exps : List ModuleExport) (inst : Instance) :
    IProp GF :=
  iprop([∗list] hs_exp;m_exp ∈ hs_exps;m_exps,
    ∃ nm, hs_exp ↪[vis] (ModuleExport.mk nm
      (match m_exp.desc with
        | .func (.funcidx n) => .func (.funcidx (inst.funcs.getD n 0))
        | .table (.tableidx n) => .table (.tableidx (inst.tab.getD n 0))
        | .mem (.memidx n) => .mem (.memidx (inst.memory.getD n 0))
        | .global (.globalidx n) => .global (.globalidx (inst.globs.getD n 0)))))

omit [HmsG GF] [HasG GF] in
@[rocq_alias iriswasm.import_resources_host_lookup]
theorem import_resources_host_lookup (hs_imps : List Vimp) (v_imps : List ModuleExport)
    (vis : ViStore) :
    ⊢ ghost_map_auth (GF := GF) (HvisG.visGName GF) (DFrac.own 1) vis -∗
      ([∗list] hs_imp;v_imp ∈ hs_imps;v_imps, hs_imp ↪[vis] v_imp) -∗
      ⌜hs_imps.length = v_imps.length ∧ ∀ (k : Nat) hs_imp v_imp, hs_imps[k]? = some hs_imp →
        v_imps[k]? = some v_imp → get? vis hs_imp = some v_imp⌝ := by
  induction hs_imps generalizing v_imps with
  | nil =>
    iintro _ H
    ihave %h := BigSepL2.bigSepL2_nil_inv_left $$ H
    subst h; ipureintro; simp
  | cons x xs ih =>
    iintro Hvis H
    icases BigSepL2.bigSepL2_cons_inv_left.1 $$ H with ⟨%y, %ys, %hv, Hx, Hrest⟩
    subst hv
    ihave %h2 := ih ys $$ [$Hvis] Hrest
    unfold visOwn
    ihave %h1 := ghost_map_lookup $$ Hvis Hx
    ipureintro
    refine ⟨by simp [h2.1], fun k a b ha hb => ?_⟩
    cases k with
    | zero => simp_all
    | succ k => exact h2.2 k a b (by simpa using ha) (by simpa using hb)

@[rocq_alias iriswasm.instantiation_resources_pre]
def instantiationResourcesPre (hs_mod : Nat) (m : Module) (hs_imps : List Vimp)
    (v_imps : List ModuleExport) (t_imps : List ExternT) (wfs : NatMap FunctionClosure)
    (wts : NatMap Tableinst) (wms : NatMap Memory) (wgs : NatMap Global) (hs_exps : List Vi) :
    IProp GF :=
  iprop(hs_mod ↪[mods] m ∗
    importResourcesHost hs_imps v_imps ∗
    instantiationResourcesPreWasm m v_imps t_imps wfs wts wms wgs ∗
    exportOwnershipHost hs_exps ∗
    ⌜hs_exps.length = m.exports.length⌝)

@[rocq_alias iriswasm.instantiation_resources_post]
def instantiationResourcesPost (hs_mod : Nat) (m : Module) (hs_imps : List Vimp)
    (v_imps : List ModuleExport) (t_imps : List ExternT) (wfs : NatMap FunctionClosure)
    (wts : NatMap Tableinst) (wms : NatMap Memory) (wgs : NatMap Global) (hs_exps : List Vi)
    (idfstart : Option Nat) : IProp GF :=
  iprop(hs_mod ↪[mods] m ∗
    importResourcesHost hs_imps v_imps ∗
    ∃ inst : Instance,
      instantiationResourcesPostWasm m v_imps t_imps wfs wts wms wgs idfstart inst ∗
      moduleExportResourcesHost hs_exps m.exports inst)

@[rocq_alias iriswasm.insert_exports_none_len]
theorem insert_exports_none_len (vis : ViStore) (iexps : List Vi) (exps : List ModuleExport)
    (h : insertExports vis iexps exps = none) : iexps.length ≠ exps.length := by
  induction iexps generalizing exps with
  | nil => simp [insertExports] at h
  | cons i iexps ih =>
    cases exps with
    | nil => simp
    | cons exp exps =>
      simp only [insertExports] at h
      split at h
      · cases h
      · simpa using ih exps ‹_›

omit [HmsG GF] [HasG GF] in
@[rocq_alias iriswasm.host_export_state_update]
theorem host_export_state_update (vis vis' : ViStore) (inst : Instance) (hs_exps : List Vi)
    (mexp : List ModuleExport) :
    ⊢ ⌜hs_exps.length = mexp.length⌝ -∗
      ⌜insertExports vis hs_exps (mexp.map fun m_exp =>
        ({ name := m_exp.name, desc := exportGetVExt inst m_exp.desc } : ModuleExport)) = some vis'⌝ -∗
      ghost_map_auth (HvisG.visGName GF) (DFrac.own 1) vis -∗
      exportOwnershipHost (GF := GF) hs_exps -∗ |==>
      (ghost_map_auth (HvisG.visGName GF) (DFrac.own 1) vis' ∗
        moduleExportResourcesHost hs_exps mexp inst) := by
  induction hs_exps generalizing vis' mexp with
  | nil =>
    iintro %hlen %hins Hvis -
    simp only [insertExports, Option.some.injEq] at hins; subst hins
    cases mexp with
    | nil =>
      imodintro
      isplitl [Hvis]
      · iexact Hvis
      · unfold moduleExportResourcesHost; iempintro
    | cons => simp at hlen
  | cons a hs ih =>
    iintro %hlen %hins Hvis Hexp
    cases mexp with
    | nil => simp at hlen
    | cons e es =>
      simp only [insertExports, List.map_cons] at hins
      split at hins
      · rename_i v2 hv2
        cases hins
        have hcons : exportOwnershipHost (GF := GF) (a :: hs) =
            iprop((∃ hv, a ↪[vis] hv) ∗ exportOwnershipHost hs) := rfl
        rw [hcons]
        icases Hexp with ⟨⟨%hv, Ha⟩, Hrest⟩
        imod ih v2 es $$ %(by simpa using hlen) %hv2 Hvis Hrest with ⟨Hvis, Hres⟩
        unfold visOwn
        imod ghost_map_update (ModuleExport.mk e.name (exportGetVExt inst e.desc)) $$ Hvis Ha with
          ⟨Hvis, Ha⟩
        imodintro
        isplitl [Hvis]
        · iexact Hvis
        · have hcons' : moduleExportResourcesHost (GF := GF) (a :: hs) (e :: es) inst =
              iprop((∃ nm, a ↪[vis] (ModuleExport.mk nm (exportGetVExt inst e.desc))) ∗
                moduleExportResourcesHost hs es inst) := by
            cases e with | mk nm d => cases d <;> rename_i x <;> cases x <;> rfl
          rw [hcons']
          isplitl [Ha]
          · iexists e.name
            unfold visOwn
            iexact Ha
          · iexact Hres
      · cases hins

/-- Shared core of the operational instantiation specs: one host step instantiating `m`. -/
private theorem instantiation_spec_core (s : Stuckness) (E : CoPset) (hs_mod : Nat)
    (hs_imps : List Vimp) (v_imps : List ModuleExport) (hs_exps : List Vi) (m : Module)
    (t_imps t_exps : List ExternT) (wfs : NatMap FunctionClosure) (wts : NatMap Tableinst)
    (wms : NatMap Memory) (wgs : NatMap Global) (Φ : HostVal → IProp GF) (idecls : List HostE)
    (hmt : ModuleTyping m t_imps t_exps) (hmr : ModuleRestrictions m) :
    ⊢ instantiationResourcesPre hs_mod m hs_imps v_imps t_imps wfs wts wms wgs hs_exps -∗
      (∀ start, ⌜m.start = none → start = none⌝ -∗
        ⌜∀ n, m.start = some ⟨.funcidx n⟩ → ∃ i, start = some i⌝ -∗
        instantiationResourcesPost hs_mod m hs_imps v_imps t_imps wfs wts wms wgs hs_exps start -∗
        WP ((idecls, mapStart start) : HostExpr) @ s ; E {{ Φ }}) -∗
      WP ((.instantiate hs_exps hs_mod hs_imps :: idecls, []) : HostExpr) @ s ; E {{ Φ }} := by
  let := @WasmG.invGS hlc GF _
  unfold instantiationResourcesPre instantiationResourcesPreWasm importResourcesHost
  iintro ⟨Hmod, Himphost, ⟨Himpwasm, %Hebound, %Hdbound⟩, Hexphost, %Hlenexp⟩ Hcont
  iapply wp_lift_step
    (rfl : hostToVal ((.instantiate hs_exps hs_mod hs_imps :: idecls, []) : HostExpr) = none)
  iintro %σ %ns %obs %obs' %nt Hσ
  obtain ⟨ws, vis, ms, has, f⟩ := σ
  rw [hostStateInterp_eq]; simp only [hostStateInterp]
  icases Hσ with ⟨Hwf, Hwt, Hwm, Hwg, Hvis, Hms, Hhas, Hframe, Hmsize, Htsize, Hmlimit, Htlimit⟩
  ihave %hmod := mods_lookup $$ [$Hms] [$Hmod]
  rw [gmap_of_list_lookup] at hmod
  ihave %himphost := import_resources_host_lookup hs_imps v_imps vis $$ [$Hvis] [$Himphost]
  ihave %himpwasm := import_resources_wasm_lookup v_imps t_imps wfs wts wms wgs ws $$ [$Hwf] [$Hwt]
    [$Hwm] [$Hwg] [$Htsize] [$Htlimit] [$Hmsize] [$Hmlimit] [$Himpwasm]
  iunfold importResourcesWasmTypecheck at Himpwasm
  icases Himpwasm with ⟨Hif, Hit, Him, Hig⟩
  ihave %hwt := import_resources_wts_subset v_imps t_imps wts ws $$ [$Hwt] [$Htsize] [$Htlimit] [$Hit]
    %himpwasm.1
  ihave %hwm := import_resources_wms_subset v_imps t_imps wms ws $$ [$Hwm] [$Hmsize] [$Hmlimit] [$Him]
    %himpwasm.1
  have hext : Wasm.List.Forall₂ (ExternalTyping ws) (v_imps.map (·.desc)) t_imps :=
    forall₂_of_getElem? (by simpa using himpwasm.1) fun k d t hd ht => by
      rw [List.getElem?_map] at hd
      rcases hv : v_imps[k]? with _ | v
      · simp [hv] at hd
      simp only [hv, Option.map_some, Option.some.injEq] at hd
      subst hd
      have h := himpwasm.2 k v t hv ht
      rcases v with ⟨_, (⟨⟨i⟩⟩ | ⟨⟨i⟩⟩ | ⟨⟨i⟩⟩ | ⟨⟨i⟩⟩)⟩
      · obtain ⟨cl, h1, -, rfl⟩ := h
        exact .func _ _ _ _ (List.getElem?_eq_some_iff.1 h1).1 h1 rfl
      · obtain ⟨tab, tt, h1, -, rfl, h2⟩ := h
        exact .tab _ _ _ _ (List.getElem?_eq_some_iff.1 h1).1 h1 h2
      · obtain ⟨mem, mt, h1, -, rfl, h2⟩ := h
        exact .mem _ _ _ _ (List.getElem?_eq_some_iff.1 h1).1 h1 h2
      · obtain ⟨g, gt, h1, -, rfl, h2⟩ := h
        exact .glob _ _ _ _ (List.getElem?_eq_some_iff.1 h1).1 h1 h2
  have heb := module_elem_bound_check_gmap_extend _ _ _ _ Hebound hwt
  have hdb := module_data_bound_check_gmap_extend _ _ _ _ Hdbound hwm
  obtain ⟨wsr, instr, hinst⟩ := instantiate_exists ws m _ t_imps t_exps hmt hmr hext heb hdb
  have hthose := those_lookup_export_vi vis hs_imps v_imps himphost.1 himphost.2
  obtain ⟨vis', hins⟩ : ∃ vis', insertExports vis hs_exps (m.exports.map fun e =>
      ({ name := e.name, desc := exportGetVExt instr e.desc } : ModuleExport)) = some vis' := by
    cases h : insertExports vis hs_exps _ with
    | none => exact absurd Hlenexp (by simpa using insert_exports_none_len _ _ _ h)
    | some vis' => exact ⟨vis', rfl⟩
  have hred := HostReduce.hostStep ws vis m hs_exps hs_mod hs_imps v_imps _ _ vis' ms idecls instr _ _
    [] f has hmod hthose rfl hinst (by simp [Hlenexp]) rfl hins
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplit
  · ipureintro; cases s <;> simp only [Stuckness.MaybeReducible] <;>
      exact ⟨[], (idecls, _), (wsr, vis', ms, has, f), [], hred, rfl, rfl⟩
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep -
  obtain ⟨hes2, es2⟩ := e₂
  obtain ⟨ws2, vis2, ms2, has2, f2⟩ := σ₂
  obtain ⟨Hstep, rfl, rfl⟩ := Hstep
  obtain ⟨inst', start', hinst', hins', rfl, rfl, rfl, rfl, rfl⟩ :=
    instantiate_step_inv hmod hthose heb hdb Hstep
  have hst := (instantiate_exps_start hinst').2
  imod Hclose
  ihave Hspec := instantiation_wasm_spec v_imps m t_imps t_exps wfs wts wms wgs ws ws2 inst' _ start'
    hmt hmr hinst' $$ [Hif Hit Him Hig] [Hwf Hwt Hwm Hwg Hmsize Htsize Hmlimit Htlimit]
  · unfold instantiationResourcesPreWasm importResourcesWasmTypecheck
    iframe
    isplit <;> ipureintro <;> assumption
  · unfold genHeapWasmStore; iframe
  imod Hspec with ⟨Hpost, Hσ'⟩
  iunfold genHeapWasmStore at Hσ'
  icases Hσ' with ⟨Hwf, Hwt, Hwm, Hwg, Hmsize, Htsize, Hmlimit, Htlimit⟩
  imod host_export_state_update vis vis2 inst' hs_exps m.exports $$ %(by simpa using Hlenexp)
    %hins' Hvis Hexphost with ⟨Hvis, Hexpres⟩
  imodintro
  rw [hostStateInterp_eq]; simp only [hostStateInterp]
  iframe
  simp only [Algebra.BigOpL.bigOpL_nil]
  isplitl
  · iapply Hcont $$ %start' %(fun h => by simp [hst, h, optionBind])
      %(fun n h => instantiate_start_some h hinst')
    unfold instantiationResourcesPost importResourcesHost
    iframe
  · iempintro

@[rocq_alias iriswasm.instantiation_spec_operational_no_start]
theorem instantiation_spec_operational_no_start (s : Stuckness) (E : CoPset) (hs_mod : Nat)
    (hs_imps : List Vimp) (v_imps : List ModuleExport) (hs_exps : List Vi) (m : Module)
    (t_imps t_exps : List ExternT) (wfs : NatMap FunctionClosure) (wts : NatMap Tableinst)
    (wms : NatMap Memory) (wgs : NatMap Global) (hstart : m.start = none)
    (hmt : ModuleTyping m t_imps t_exps) (hmr : ModuleRestrictions m) :
    ⊢ instantiationResourcesPre (GF := GF) hs_mod m hs_imps v_imps t_imps wfs wts wms wgs hs_exps -∗
      WP (([.instantiate hs_exps hs_mod hs_imps], []) : HostExpr) @ s ; E
        {{ v, ⌜v = HostVal.immHV []⌝ ∗
          instantiationResourcesPost hs_mod m hs_imps v_imps t_imps wfs wts wms wgs hs_exps none }} := by
  iintro Hpre
  iapply instantiation_spec_core s E hs_mod hs_imps v_imps hs_exps m t_imps t_exps wfs wts wms wgs _ []
    hmt hmr $$ Hpre
  iintro %start %hnone - Hpost
  rw [hnone hstart]
  iapply IrisHost.wp_value s E (([], mapStart none) : HostExpr) (.immHV []) _ rfl
  isplitr
  · ipureintro; rfl
  · iexact Hpost

/-- Instantiation of a module with a start function, followed by the remaining declarations. -/
@[rocq_alias iriswasm.instantiation_spec_operational_start_seq]
theorem instantiation_spec_operational_start_seq (s : Stuckness) (E : CoPset) (hs_mod : Nat)
    (hs_imps : List Vimp) (v_imps : List ModuleExport) (hs_exps : List Vi) (m : Module)
    (t_imps t_exps : List ExternT) (wfs : NatMap FunctionClosure) (wts : NatMap Tableinst)
    (wms : NatMap Memory) (wgs : NatMap Global) (nstart : Nat) (Φ : HostVal → IProp GF)
    (idecls : List HostE) (hstart : m.start = some ⟨.funcidx nstart⟩)
    (hmt : ModuleTyping m t_imps t_exps) (hmr : ModuleRestrictions m) :
    ⊢ ↪[frame] emptyFrame -∗
      instantiationResourcesPre hs_mod m hs_imps v_imps t_imps wfs wts wms wgs hs_exps -∗
      (∀ idnstart, ↪[frame] emptyFrame -∗
        instantiationResourcesPost hs_mod m hs_imps v_imps t_imps wfs wts wms wgs hs_exps
          (some idnstart) -∗
        WP ((idecls, [.invoke idnstart]) : HostExpr) @ s ; E {{ Φ }}) -∗
      WP ((.instantiate hs_exps hs_mod hs_imps :: idecls, []) : HostExpr) @ s ; E {{ Φ }} := by
  iintro Hframe Hpre Hwpstart
  iapply instantiation_spec_core s E hs_mod hs_imps v_imps hs_exps m t_imps t_exps wfs wts wms wgs _
    idecls hmt hmr $$ Hpre
  iintro %start - %hsome Hpost
  obtain ⟨i, rfl⟩ := hsome nstart hstart
  simp only [mapStart]
  iapply Hwpstart $$ Hframe Hpost

@[rocq_alias iriswasm.instantiation_spec_operational_start]
theorem instantiation_spec_operational_start (s : Stuckness) (E : CoPset) (hs_mod : Nat)
    (hs_imps : List Vimp) (v_imps : List ModuleExport) (hs_exps : List Vi) (m : Module)
    (t_imps t_exps : List ExternT) (wfs : NatMap FunctionClosure) (wts : NatMap Tableinst)
    (wms : NatMap Memory) (wgs : NatMap Global) (nstart : Nat) (Φ : HostVal → IProp GF)
    (hstart : m.start = some ⟨.funcidx nstart⟩)
    (hmt : ModuleTyping m t_imps t_exps) (hmr : ModuleRestrictions m) :
    ⊢ ↪[frame] emptyFrame -∗
      instantiationResourcesPre hs_mod m hs_imps v_imps t_imps wfs wts wms wgs hs_exps -∗
      (∀ idnstart, ↪[frame] emptyFrame -∗
        instantiationResourcesPost hs_mod m hs_imps v_imps t_imps wfs wts wms wgs hs_exps
          (some idnstart) -∗
        WP (([], [.invoke idnstart]) : HostExpr) @ s ; E {{ Φ }}) -∗
      WP (([.instantiate hs_exps hs_mod hs_imps], []) : HostExpr) @ s ; E {{ Φ }} :=
  instantiation_spec_operational_start_seq s E hs_mod hs_imps v_imps hs_exps m t_imps t_exps
    wfs wts wms wgs nstart Φ [] hstart hmt hmr

end Instantiation_spec_operational

end IrisWasm
