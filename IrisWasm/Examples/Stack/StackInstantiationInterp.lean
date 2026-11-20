/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Examples.Stack.StackInstantiation
import IrisWasm.Logrel.IrisFundamentalHelpers

/-! Port of `theories/iris/examples/stack/stack_instantiation_interp.v`. -/

namespace IrisWasm.Examples.Stack

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm
open scoped Iris.Std.PartialMap

section StackModule
variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF]

attribute [local instance] WasmG.invGS

/-- Coq `≡` on `iProp` is equality in iris-lean. -/
@[rocq_alias iriswasm.stackModuleInvIff]
theorem stackModuleInvIff (P1 P2 : Nat → List I32 → IProp GF) (Q : Nat → IProp GF) :
    (∀ n l, P1 n l = P2 n l) → ⊢ (stackModuleInv P1 Q ∗-∗ stackModuleInv P2 Q) := by
  intro hcond
  have : P1 = P2 := funext fun n => funext fun l => hcond n l
  subst this
  exact BI.wandIff_refl

variable [HvisG GF] [HmsG GF] [HasG GF]

@[rocq_alias iriswasm.instantiate_stack_valid]
theorem instantiate_stack_valid [LogrelNaInvs GF] (s : Stuckness) (E : CoPset)
    (exp_addrs : List Nat) (stack_mod_addr : Nat) :
    exp_addrs.length = 8 →
    -- Knowing we hold the stack module …
    ⊢ (stack_mod_addr ↪[mods] stackModule -∗
      -- … and we own the vis pointers …
      ownVisPointers exp_addrs -∗
      -- … instantiating the stack module yields the following:
      WP ((stackInstantiatePara exp_addrs stack_mod_addr, []) : HostExpr) @ s ; E
        {{ v,
          -- instantiation succeeds
          ⌜v = .immHV []⌝ ∗
          -- we still own the stack module
          stack_mod_addr ↪[mods] stackModule ∗
          ∃ (idf0 idf1 idf2 idf3 idf4 idf5 idf6 idt : Nat)
            (name0 name1 name2 name3 name4 name5 name6 name7 : Name)
            (f0 f1 f2 f3 f4 f5 f6 : List BasicInstruction)
            (i0 : Instance)
            (l0 l1 l2 l3 l4 l5 l6 : List ValueType)
            (tab : Tableinst)
            (isStack : Nat → List I32 → IProp GF)
            (nextStackAddrIs : Nat → IProp GF),
            -- `wf`/`vis` pointers of the exports, so that a client can import them
            importResourcesHost exp_addrs
              (stackInstVis idf0 idf1 idf2 idf3 idf4 idf5 idf6 idt
                name0 name1 name2 name3 name4 name5 name6 name7) ∗
            importResourcesWasmTypecheckSepL2
              (stackInstVis idf0 idf1 idf2 idf3 idf4 idf5 idf6 idt
                name0 name1 name2 name3 name4 name5 name6 name7) expts
              (stackInstMap idf0 idf1 idf2 idf3 idf4 idf5 idf6 i0
                l0 l1 l2 l3 l4 l5 l6 f0 f1 f2 f3 f4 f5 f6)
              (insert (∅ : NatMap Tableinst) idt tab) ∅ ∅ ∗
            ⌜((stackInstVis idf0 idf1 idf2 idf3 idf4 idf5 idf6 idt
                name0 name1 name2 name3 name4 name5 name6 name7).map (·.desc)).Nodup⌝ ∗
            -- technically redundant, but commonly used by modules importing the stack
            ⌜[idf0, idf1, idf2, idf3, idf4, idf5, idf6].Nodup⌝ ∗
            ⌜tab.data.length ≥ 1⌝ ∗
            NonAtomicInvariant.inv (LogrelNaInvs.logrelNais (GF := GF)) stkN
              (stackModuleInv (fun n => isStack n) nextStackAddrIs) ∗
            -- the table starts out empty
            ([∗list] elem ∈ tab.data, ⌜elem = none⌝) ∗
            -- each exported function is valid (`inst_map_exp` in Coq)
            [∗map] _f ↦ cl ∈ (PartialMap.ofList ([idf0, idf1, idf2, idf3, idf4].zip
                [.funcNative i0 (.tf [] [.i32]) l0 f0,
                 .funcNative i0 (.tf [.i32] [.i32]) l1 f1,
                 .funcNative i0 (.tf [.i32] [.i32]) l2 f2,
                 .funcNative i0 (.tf [.i32] [.i32]) l3 f3,
                 .funcNative i0 (.tf [.i32, .i32] []) l4 f4]) : NatMap FunctionClosure),
              interpClosure [] (clType cl) cl }} : IProp GF) := by
  intro hlen
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, rfl⟩ :
      ∃ e0 e1 e2 e3 e4 e5 e6 e7, exp_addrs = [e0, e1, e2, e3, e4, e5, e6, e7] := by
    match exp_addrs, hlen with
    | [e0, e1, e2, e3, e4, e5, e6, e7], _ => exact ⟨e0, e1, e2, e3, e4, e5, e6, e7, rfl⟩
  iintro Hmod Hvis
  ihave %Hnodup := own_vis_pointers_nodup $$ Hvis
  ihave Hwp := instantiation_spec_operational_no_start s E stack_mod_addr [] []
      [e0, e1, e2, e3, e4, e5, e6, e7] stackModule [] expts ∅ ∅ ∅ ∅ rfl module_typing_stack
      ⟨⟨[], rfl⟩, ⟨[], rfl⟩, ⟨[], rfl⟩⟩ $$ [Hmod Hvis]
  · simp only [instantiationResourcesPre, instantiationResourcesPreWasm]
    isplitl [Hmod]
    · iexact Hmod
    isplitr [Hvis]
    · simp only [importResourcesHost]
      iapply BI.BigSepL2.bigSepL2_nil.2
      iempintro
    isplitr [Hvis]
    · isplitr
      · iapply (irwt_nodup_equiv [] [] ∅ ∅ ∅ ∅ .nil).2
        simp only [importResourcesWasmTypecheckSepL2, importResourcesWasmDomcheck]
        isplitl
        · ipureintro; simp [PartialMap.dom, get?_empty, extFuncAddrs, extTabAddrs, extMemAddrs,
            extGlobAddrs, extFuncs, extTabs, extMems, extGlobs]
        · iapply BI.BigSepL2.bigSepL2_nil.2
          iempintro
      isplit
      · ipureintro; simp [ModuleElemBoundCheckGmap, stackModule]
      · ipureintro; simp [ModuleDataBoundCheckGmap, stackModule]
    isplitl [Hvis]
    · simp only [ownVisPointers, exportOwnershipHost]
      iexact Hvis
    · ipureintro; trivial
  simp only [stackInstantiatePara]
  iapply Iris.wp_strong_mono (Std.IsPreorder.le_refl s) LawfulSet.subset_refl $$ Hwp
  iintro %v ⟨%Hv, Hpost⟩
  subst Hv
  simp only [instantiationResourcesPost, instantiationResourcesPostWasm, moduleInstResourcesWasm,
    moduleInstResourcesTab, moduleInstResourcesMem, moduleInstResourcesGlob]
  icases Hpost with ⟨Hmod, -, %inst, ⟨%g_inits, %tabAllocs, %memAllocs, %globAllocs, %wts', %wms',
    -, %Hinst, %Htab, %_, %_, %Hmem, %_, %_, %_, %Hglob, Hwf, Hwt, Hwm, Hwg⟩, Hexphost⟩
  ihave %Hnodupwf := module_inst_resources_func_nodup _ _ _ $$ Hwf
  simp only [moduleInstResourcesFunc]
  ihave %Hflen := BI.BigSepL2.bigSepL2_length $$ Hwf
  ihave %Htlen := BI.BigSepL2.bigSepL2_length $$ Hwt
  ihave %Hmlen := BI.BigSepL2.bigSepL2_length $$ Hwm
  ihave %Hglen := BI.BigSepL2.bigSepL2_length $$ Hwg
  obtain ⟨itypes, ifuncs, itab, imem, iglobs⟩ := inst
  obtain ⟨Htypes, -⟩ := Hinst
  simp only at Htypes
  subst Htypes Htab Hmem Hglob
  simp [getImportFuncCount, getImportTableCount, getImportMemCount, getImportGlobalCount,
    stackModule, moduleInstBuildTables, moduleInstBuildMems, moduleInstGlobalInit,
    moduleInstBuildGlobals, moduleInstTableBase, moduleInstMemBase] at Hflen Htlen Hmlen Hglen
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, rfl⟩ :
      ∃ f0 f1 f2 f3 f4 f5 f6, ifuncs = [f0, f1, f2, f3, f4, f5, f6] := by
    match ifuncs, Hflen with
    | [f0, f1, f2, f3, f4, f5, f6], _ => exact ⟨f0, f1, f2, f3, f4, f5, f6, rfl⟩
  obtain ⟨t, rfl⟩ : ∃ t, itab = [t] := by
    match itab, Htlen with
    | [t], _ => exact ⟨t, rfl⟩
  obtain ⟨m, rfl⟩ : ∃ m, imem = [m] := by
    match imem, Hmlen with
    | [m], _ => exact ⟨m, rfl⟩
  obtain rfl : iglobs = [] := List.eq_nil_of_length_eq_zero Hglen.symm
  iframe Hmod
  simp only [getImportFuncCount, getImportTableCount, getImportMemCount, getImportGlobalCount,
    stackModule, moduleInstBuildTables, moduleInstBuildMems, moduleInstGlobalInit,
    moduleInstBuildGlobals, moduleInstTableBase, moduleInstMemBase, moduleExportResourcesHost,
    List.drop_zero, List.filterMap_nil, List.length_nil, List.foldl_nil, List.map_cons,
    List.map_nil]
  icases Hwf with ⟨Hf0, Hf1, Hf2, Hf3, Hf4, Hf5, Hf6, -⟩
  icases Hwt with ⟨Ht, -⟩
  icases Hwm with ⟨Hm, -⟩
  simp only [memBlock, moduleInstMemBaseFunc, Wasm.lengthMem, MemoryList.lengthMem, List.length_replicate,
    Nat.mul_zero]
  icases Hm with ⟨-, Hmemlength, -⟩
  icases Hexphost with ⟨⟨%n0, Hx0⟩, ⟨%n1, Hx1⟩, ⟨%n2, Hx2⟩, ⟨%n3, Hx3⟩, ⟨%n4, Hx4⟩, ⟨%n5, Hx5⟩,
    ⟨%n6, Hx6⟩, ⟨%n7, Hx7⟩, -⟩
  simp only [moduleInstTableBaseCreate, List.getD_cons_succ, List.getD_cons_zero] at ⊢
  simp only [show getImportFuncCount stackModule = 0 from rfl, List.drop_zero] at Hnodupwf
  ihave Hstk := NonAtomicInvariant.inv_alloc (p := LogrelNaInvs.logrelNais (GF := GF)) (E := E)
      (N := stkN) (P := stackModuleInv (fun a b => isStack a b m) (fun n => m ↦[wmlength] n))
      $$ [Hmemlength]
  · inext
    simp only [stackModuleInv]
    iexists 0
    isplitr
    · ipureintro; exact Nat.dvd_zero _
    isplitl [Hmemlength]
    · iexact Hmemlength
    iexists []
    isplit
    · ipureintro; exact .baseNil _ (by decide)
    · iempintro
  imod Hstk with #Hstk
  imodintro
  iexists f0, f1, f2, f3, f4, f5, f6, t, n0, n1, n2, n3, n4, n5, n6, n7, newStack, isEmpty, isFull,
    pop, push, stackMap, lengthStack,
    ⟨[.tf [] [.i32], .tf [.i32] [.i32], .tf [.i32, .i32] []], [f0, f1, f2, f3, f4, f5, f6], [t], [m], []⟩,
    [.i32], [], [], [.i32], [.i32], [.i32, .i32], [],
    ⟨[none], none⟩, (fun a b => isStack a b m), (fun n => m ↦[wmlength] n)
  have hkeys : ∀ (ks : List Nat) (l : List FunctionClosure), ks.Nodup → NoDupKeys (ks.zip l) := by
    intro ks l h
    induction ks generalizing l with
    | nil => exact .nil
    | cons k ks ih =>
      cases l with
      | nil => exact .nil
      | cons v l =>
        obtain ⟨hk, hks⟩ := List.nodup_cons.1 h
        refine List.nodup_cons.2 ⟨fun hm => hk ?_, ih l hks⟩
        obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.1 hm
        exact (List.of_mem_zip hab).1
  isplitl [Hx0 Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7]
  · simp only [importResourcesHost, stackInstVis, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append]
    iapply BI.BigSepL2.bigSepL2_cons.2
    iframe
    iapply BI.BigSepL2.bigSepL2_nil.2
    iempintro
  isplitl [Hf0 Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Ht]
  · simp only [importResourcesWasmTypecheckSepL2]
    isplitr
    · simp only [importResourcesWasmDomcheck]
      ipureintro
      simp only [stackInstMap, List.zip_cons_cons, List.zip_nil_left, LawfulPartialMap.ofList_cons,
        LawfulPartialMap.dom_insert_iff]
      simp [PartialMap.ofList, PartialMap.dom, get?_empty, extFuncAddrs,
        extTabAddrs, extMemAddrs, extGlobAddrs, extFuncs, extTabs, extMems, extGlobs]
      grind
    simp only [stackInstVis, expts, funcTypes, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append]
    iapply BI.BigSepL2.bigSepL2_cons.2
    isplitl [Hf0]
    · iexists _; isplitl [Hf0]; · iexact Hf0
      ipureintro; exact ⟨LawfulPartialMap.get?_ofList_some (by simp) (hkeys _ _ Hnodupwf), rfl⟩
    iapply BI.BigSepL2.bigSepL2_cons.2
    isplitl [Hf1]
    · iexists _; isplitl [Hf1]; · iexact Hf1
      ipureintro; exact ⟨LawfulPartialMap.get?_ofList_some (by simp) (hkeys _ _ Hnodupwf), rfl⟩
    iapply BI.BigSepL2.bigSepL2_cons.2
    isplitl [Hf2]
    · iexists _; isplitl [Hf2]; · iexact Hf2
      ipureintro; exact ⟨LawfulPartialMap.get?_ofList_some (by simp) (hkeys _ _ Hnodupwf), rfl⟩
    iapply BI.BigSepL2.bigSepL2_cons.2
    isplitl [Hf3]
    · iexists _; isplitl [Hf3]; · iexact Hf3
      ipureintro; exact ⟨LawfulPartialMap.get?_ofList_some (by simp) (hkeys _ _ Hnodupwf), rfl⟩
    iapply BI.BigSepL2.bigSepL2_cons.2
    isplitl [Hf4]
    · iexists _; isplitl [Hf4]; · iexact Hf4
      ipureintro; exact ⟨LawfulPartialMap.get?_ofList_some (by simp) (hkeys _ _ Hnodupwf), rfl⟩
    iapply BI.BigSepL2.bigSepL2_cons.2
    isplitl [Hf5]
    · iexists _; isplitl [Hf5]; · iexact Hf5
      ipureintro; exact ⟨LawfulPartialMap.get?_ofList_some (by simp) (hkeys _ _ Hnodupwf), rfl⟩
    iapply BI.BigSepL2.bigSepL2_cons.2
    isplitl [Hf6]
    · iexists _; isplitl [Hf6]; · iexact Hf6
      ipureintro; exact ⟨LawfulPartialMap.get?_ofList_some (by simp) (hkeys _ _ Hnodupwf), rfl⟩
    iapply BI.BigSepL2.bigSepL2_cons.2
    isplitl [Ht]
    · iexists _, _
      isplitl [Ht]
      · iexact Ht
      ipureintro
      exact ⟨by simp [get?_insert_eq], rfl, by decide⟩
    iapply BI.BigSepL2.bigSepL2_nil.2
    iempintro
  isplitr
  · ipureintro
    simpa [List.nodup_cons] using Hnodupwf
  isplitr
  · ipureintro; exact Hnodupwf
  isplitr
  · ipureintro; decide
  isplitr
  · iexact Hstk
  isplitr
  · iapply BI.BigSepL.bigSepL_singleton.2
    ipureintro; rfl
  iapply (BI.BigSepM.bigSepM_ofList (hkeys _ _ (by simp at Hnodupwf ⊢; grind))).2
  simp only [List.zip_cons_cons, List.zip_nil_left]
  iapply BI.BigSepL.bigSepL_cons.2
  isplitr
  · simp only [clType, interpClosure]
    isplitr
    · ipureintro; trivial
    imodintro
    inext
    iapply valid_new_stack m t [f0, f1, f2, f3, f4, f5, f6] $$ Hstk
  iapply BI.BigSepL.bigSepL_cons.2
  isplitr
  · simp only [clType, interpClosure]
    isplitr
    · ipureintro; trivial
    imodintro
    inext
    iapply valid_is_empty m t [f0, f1, f2, f3, f4, f5, f6] $$ Hstk
  iapply BI.BigSepL.bigSepL_cons.2
  isplitr
  · simp only [clType, interpClosure]
    isplitr
    · ipureintro; trivial
    imodintro
    inext
    iapply valid_is_full m t [f0, f1, f2, f3, f4, f5, f6] $$ Hstk
  iapply BI.BigSepL.bigSepL_cons.2
  isplitr
  · simp only [clType, interpClosure]
    isplitr
    · ipureintro; trivial
    imodintro
    inext
    iapply valid_pop m t [f0, f1, f2, f3, f4, f5, f6] $$ Hstk
  iapply BI.BigSepL.bigSepL_cons.2
  isplitr
  · simp only [clType, interpClosure]
    isplitr
    · ipureintro; trivial
    imodintro
    inext
    iapply valid_push m t [f0, f1, f2, f3, f4, f5, f6] $$ Hstk
  iapply BI.BigSepL.bigSepL_nil.2
  iempintro

end StackModule

end IrisWasm.Examples.Stack
