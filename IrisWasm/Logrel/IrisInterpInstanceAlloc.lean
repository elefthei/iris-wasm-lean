/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Host.IrisHost
import IrisWasm.Logrel.IrisFundamental

/-! Port of `theories/iris/logrel/iris_interp_instance_alloc.v`: allocating the invariants of a
freshly instantiated module and establishing the instance relation `interpInstance` for it.

The Coq section also assumes `hvisG Σ, hmsG Σ`; no statement uses them, so they are not
`variable`s here (an unused instance binder would become a hypothesis of every lemma).
Coq `gmap N T` is `NatMap T`; `dom m = dom m'` is stated pointwise via `PartialMap.dom`;
`imap` is `List.mapIdx`; stdpp's `filter` on a `Decision` predicate is `List.filter (decide ·)`;
`is_Some x` is `x.isSome = true`; `k <? n` is `decide (k < n)`. -/

namespace IrisWasm

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm
open scoped Iris.Std.PartialMap

variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF] [LogrelNaInvs GF]

attribute [local instance] WasmG.invGS

local notation "logrelNais" => LogrelNaInvs.logrelNais (GF := GF)

private theorem forall2_lookup_l {A B : Type} {R : A → B → Prop} {l1 : List A} {l2 : List B}
    {k : Nat} {a : A} (h : Wasm.List.Forall₂ R l1 l2) (hk : l1[k]? = some a) :
    ∃ b, l2[k]? = some b ∧ R a b := by
  induction h generalizing k with
  | nil => simp at hk
  | cons hr _ ih =>
    cases k with
    | zero => simp at hk; subst hk; exact ⟨_, rfl, hr⟩
    | succ k => exact ih (by simpa using hk)

private theorem forall2_lookup_r {A B : Type} {R : A → B → Prop} {l1 : List A} {l2 : List B}
    {k : Nat} {b : B} (h : Wasm.List.Forall₂ R l1 l2) (hk : l2[k]? = some b) :
    ∃ a, l1[k]? = some a ∧ R a b := by
  induction h generalizing k with
  | nil => simp at hk
  | cons hr _ ih =>
    cases k with
    | zero => simp at hk; subst hk; exact ⟨_, rfl, hr⟩
    | succ k => exact ih (by simpa using hk)

/-! ### The pre-instance relation -/

@[rocq_alias iriswasm.interp_closure_pre]
def interpClosurePre (τctx : TContext) (fimps : NatMap FunctionClosure) (i : Instance)
    (hl : List (Hostfuncidx × FunctionType)) (n : Nat) (τf : FunctionType) :
    FunctionClosure → IProp GF
  | .funcNative j τ' tLocs bEs =>
    match get? fimps n with
    | some cl' => iprop(⌜cl' = .funcNative j τ' tLocs bEs⌝ ∗
        interpClosure hl τf (.funcNative j τ' tLocs bEs))
    | none => iprop(⌜i = j ∧ τf = τ' ∧
        match τf with
        | .tf tn tm =>
          BeTyping (updLocalLabelReturn τctx (tn ++ tLocs) [tm] (some tm)) bEs (.tf [] tm)⌝)
  | .funcHost tf h => interpClosure hl τf (.funcHost tf h)

@[rocq_alias iriswasm.interp_closure_persistent]
instance interpClosure_persistent (hl : List (Hostfuncidx × FunctionType)) (τf : FunctionType)
    (cl : FunctionClosure) : Persistent (interpClosure (GF := GF) hl τf cl) := by
  rcases cl with ⟨_, ⟨_, _⟩, _, _⟩ | ⟨⟨_, _⟩, _⟩ <;> dsimp only [interpClosure] <;> infer_instance

@[rocq_alias iriswasm.interp_closure_pre_persistent]
instance interpClosurePre_persistent (τctx : TContext) (fimps : NatMap FunctionClosure)
    (n : Nat) (i : Instance) (τf : FunctionType) (cl : FunctionClosure)
    (hl : List (Hostfuncidx × FunctionType)) :
    Persistent (interpClosurePre (GF := GF) τctx fimps i hl n τf cl) := by
  rcases cl with ⟨_, _, _, _⟩ | ⟨_, _⟩ <;> dsimp only [interpClosurePre]
  · split <;> infer_instance
  · infer_instance

@[rocq_alias iriswasm.interp_instance_pre]
def interpInstancePre (τctx : TContext) (fimps : NatMap FunctionClosure)
    (hl : List (Hostfuncidx × FunctionType)) (i : Instance) : IProp GF :=
  interpInstance' τctx (interpClosurePre τctx fimps i hl) (interpClosurePre τctx fimps i hl) i

@[rocq_alias iriswasm.interp_instance_pre_persistent]
instance interpInstancePre_persistent (τctx : TContext) (fimps : NatMap FunctionClosure)
    (i : Instance) (hl : List (Hostfuncidx × FunctionType)) :
    Persistent (interpInstancePre (GF := GF) τctx fimps hl i) :=
  interpInstance_persistent' _ _ _ _

@[rocq_alias iriswasm.n_zeros_interp_values]
theorem n_zeros_interp_values (l : List ValueType) :
    ⊢ ([∗list] y1;y2 ∈ nZeros l;l, interpValue y2 y1 : IProp GF) := by
  induction l with
  | nil => exact BigSepL2.bigSepL2_nil.mpr
  | cons t l ih =>
    refine .trans ?_ BigSepL2.bigSepL2_cons.mpr
    refine .trans sep_emp.mpr (sep_mono ?_ ih)
    cases t <;> exact pure_intro ⟨_, rfl⟩

@[rocq_alias iriswasm.interp_closure_pre_ind]
theorem interp_closure_pre_ind (C : TContext) (i : Instance) (ft : FunctionType)
    (cl : FunctionClosure) (fimps : NatMap FunctionClosure) (n : Nat)
    (hl : List (Hostfuncidx × FunctionType)) (hnil : C.label = [] ∧ C.return_ = none) :
    ⊢ (□ ▷ interpInstance C hl i) -∗ interpClosurePre (GF := GF) C fimps i hl n ft cl -∗
      interpClosure hl ft cl := by
  rcases cl with ⟨j, τ', tLocs, bEs⟩ | ⟨tf, h⟩
  · cases hlook : get? fimps n with
    | some cl' =>
      simp only [interpClosurePre, hlook]
      iintro #IH ⟨-, #Hcl⟩
      iexact Hcl
    | none =>
      simp only [interpClosurePre, hlook]
      iintro #IH %hp
      obtain ⟨rfl, rfl, htyp⟩ := hp
      rcases ft with ⟨tn, tm⟩
      simp only [interpClosure]
      isplitr
      · ipureintro; trivial
      imodintro
      inext
      unfold interpClosureNative wpWasmCtxFrame
      iintro %vcs %f Hv Hown Hf
      ihave HH := be_fundamental_local_stuck_host (GF := GF) C bEs tn tm tLocs hl hnil htyp
      unfold semanticTypingLocalStuckHost interpExpressionClosureStuckHost
      icases HH with ⟨-, HH⟩
      ihave Hcont := HH $$ %i IH %f %(vcs ++ nZeros tLocs) Hf Hown [Hv]
      · unfold interpVal interpValues
        icases Hv with (%hc | ⟨%v', %heqv, Hv⟩)
        · cases hc
        cases heqv
        iright; iexists (vcs ++ nZeros tLocs)
        isplitr
        · ipureintro; rfl
        iapply BigSepL2.bigSepL2_app_wand $$ Hv
        iapply n_zeros_interp_values
      iintro %LI %hfill
      have hLI : LI = [.label tm.length [] (toEList bEs)] := lfilled_inj hfill
        (IrisWasm.Helpers.ReduceDetPrelude.lfilled_label _ _
          (IrisWasm.Helpers.ReduceDetPrelude.lfilled_base.2 rfl))
      subst hLI
      iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ Hcont
      iintro %v ⟨⟨H1, H2⟩, H3⟩
      iframe
  · simp only [interpClosurePre]
    iintro #IH #Hcl
    iexact Hcl

@[rocq_alias iriswasm.interp_instance_pre_create]
theorem interp_instance_pre_create (τctx : TContext) (i : Instance)
    (fimps : NatMap FunctionClosure) (hl : List (Hostfuncidx × FunctionType))
    (hnil : τctx.label = [] ∧ τctx.return_ = none) :
    ⊢ interpInstancePre (GF := GF) τctx fimps hl i -∗ interpInstance τctx hl i := by
  iintro #Hpre
  iloeb as IH
  unfold interpInstancePre
  iapply (show interpInstance' τctx (fun _ => interpClosure hl) (fun _ => interpClosure hl) i ⊢
    interpInstance (GF := GF) τctx hl i from .rfl)
  unfold interpInstance'
  icases Hpre with ⟨%Htypes, #Hfunc, #Htable, #Hmem, #Hglob⟩
  isplitr
  · ipureintro; exact Htypes
  isplitr
  · iapply BigSepL2.bigSepL2_impl $$ Hfunc
    imodintro
    unfold interpFunction
    iintro %k %kf %tf %_ %_ ⟨%cl, #Hinv, #Hcl⟩
    iexists cl
    isplitr
    · iexact Hinv
    iapply interp_closure_pre_ind τctx i tf cl fimps kf hl hnil $$ IH Hcl
  isplitr
  · iapply BigSepL2.bigSepL2_impl $$ Htable
    imodintro
    unfold interpTableAt
    iintro %j %a %τt %_ %_ ⟨%tableSize, %tableLim, %hlim, Hlim, Hsize, Ht⟩
    iexists tableSize, tableLim
    isplitr
    · ipureintro; exact hlim
    isplitl [Hlim]
    · iexact Hlim
    isplitl [Hsize]
    · iexact Hsize
    unfold interpTable
    iapply BigSepL.bigSepL_impl $$ Ht
    imodintro
    unfold interpTableEntry
    iintro %k %x %_ ⟨%τf, %fe, #Hfna, Hfe⟩
    iexists τf, fe
    isplitr
    · iexact Hfna
    rcases fe with _ | fa
    · dsimp only; ipureintro; trivial
    unfold interpFunction
    icases Hfe with ⟨%cl, #Hna, #Hcl⟩
    iexists cl
    isplitr
    · iexact Hna
    iapply interp_closure_pre_ind τctx i τf cl fimps fa hl hnil $$ IH Hcl
  isplitr
  · iexact Hmem
  iexact Hglob

/-! ### Invariants for the imports -/

@[rocq_alias iriswasm.import_func_nainv]
def importFuncNainv (wfs : NatMap FunctionClosure) : IProp GF :=
  iprop([∗map] i ↦ v ∈ wfs, NonAtomicInvariant.inv logrelNais (wfN i) iprop(i ↦[wf] v))

@[rocq_alias iriswasm.import_tab_nainv]
def importTabNainv (wts : NatMap Tableinst) : IProp GF :=
  iprop([∗map] i ↦ v ∈ wts, (i ↪[wtsize] tabSize v) ∗ (i ↪[wtlimit] v.maxOpt) ∗
    ([∗list] j ↦ tabelem ∈ v.data,
      NonAtomicInvariant.inv logrelNais (wtN i j) iprop(i ↦[wt][ j ] tabelem)))

private instance interpMem_persistent (aw : AddrType) (n : Nat) :
    Persistent (interpMem (GF := GF) aw n) := by
  unfold interpMem; infer_instance

#rocq_ignore iriswasm.import_mem_nainv "memory invariants carry the imported memory's address width"
def importMemNainv (wms : NatMap Memory) : IProp GF :=
  iprop([∗map] i ↦ v ∈ wms, interpMem v.type.address i ∗ i ↪[wmlimit] v.type.limits.max)

@[rocq_alias iriswasm.import_glob_nainv]
def importGlobNainv (wgs : NatMap Global) : IProp GF :=
  iprop([∗map] i ↦ v ∈ wgs, NonAtomicInvariant.inv logrelNais (wgN i)
    iprop(∃ w, i ↦[wg] (⟨v.mut_, w⟩ : Global) ∗ interpValue (typeof v.val) w))

@[rocq_alias iriswasm.import_func_wasm_check_invs]
def importFuncWasmCheckInvs (v_imps : List ModuleExport) (t_imps : List ExternT)
    (wfs : NatMap FunctionClosure) : IProp GF :=
  iprop(importFuncNainv wfs ∗ ⌜funcDomcheck v_imps wfs ∧ funcTypecheck v_imps t_imps wfs⌝)

@[rocq_alias iriswasm.import_tab_wasm_check_invs]
def importTabWasmCheckInvs (v_imps : List ModuleExport) (t_imps : List ExternT)
    (wts : NatMap Tableinst) : IProp GF :=
  iprop(importTabNainv wts ∗ ⌜tabDomcheck v_imps wts ∧ tabTypecheck v_imps t_imps wts⌝)

@[rocq_alias iriswasm.import_mem_wasm_check_invs]
def importMemWasmCheckInvs (v_imps : List ModuleExport) (t_imps : List ExternT)
    (wms : NatMap Memory) : IProp GF :=
  iprop(importMemNainv wms ∗ ⌜memDomcheck v_imps wms ∧ memTypecheck v_imps t_imps wms⌝)

@[rocq_alias iriswasm.import_glob_wasm_check_invs]
def importGlobWasmCheckInvs (v_imps : List ModuleExport) (t_imps : List ExternT)
    (wgs : NatMap Global) : IProp GF :=
  iprop(importGlobNainv wgs ∗ ⌜globDomcheck v_imps wgs ∧ globTypecheck v_imps t_imps wgs⌝)

@[rocq_alias iriswasm.import_resources_wasm_typecheck_invs]
def importResourcesWasmTypecheckInvs (v_imps : List ModuleExport) (t_imps : List ExternT)
    (wfs : NatMap FunctionClosure) (wts : NatMap Tableinst) (wms : NatMap Memory)
    (wgs : NatMap Global) : IProp GF :=
  iprop(importFuncWasmCheckInvs v_imps t_imps wfs ∗ importTabWasmCheckInvs v_imps t_imps wts ∗
    importMemWasmCheckInvs v_imps t_imps wms ∗ importGlobWasmCheckInvs v_imps t_imps wgs)

@[rocq_alias iriswasm.imports_invs_persistent]
instance importsInvsPersistent (v_imps : List ModuleExport) (t_imps : List ExternT)
    (wfs : NatMap FunctionClosure) (wts : NatMap Tableinst) (wms : NatMap Memory)
    (wgs : NatMap Global) :
    Persistent (importResourcesWasmTypecheckInvs (GF := GF) v_imps t_imps wfs wts wms wgs) := by
  unfold importResourcesWasmTypecheckInvs importFuncWasmCheckInvs importTabWasmCheckInvs
    importMemWasmCheckInvs importGlobWasmCheckInvs importFuncNainv importTabNainv importMemNainv
    importGlobNainv
  infer_instance

private theorem na_alloc_of (E : CoPset) (N : Namespace) (P : IProp GF) :
    P ⊢ |={E}=> NonAtomicInvariant.inv logrelNais N P :=
  later_intro.trans (wand_entails NonAtomicInvariant.inv_alloc)

@[rocq_alias iriswasm.import_func_wasm_check_alloc]
theorem import_func_wasm_check_alloc (E : CoPset) (v_imps : List ModuleExport)
    (t_imps : List ExternT) (wfs : NatMap FunctionClosure) :
    ⊢ importFuncWasmCheck (GF := GF) v_imps t_imps wfs ={E}=∗
      importFuncWasmCheckInvs v_imps t_imps wfs := by
  unfold importFuncWasmCheck importFuncWasmCheckInvs importFuncResources importFuncNainv
  iintro ⟨Hm, %⟨Ht, Hd⟩⟩
  ihave Hm := BigSepM.bigSepM_mono_of_forall (na_alloc_of E _ _) $$ Hm
  imod BigSepM.bigSepM_fupd E _ _ $$ Hm with Hm
  iframe
  ipureintro; exact ⟨Hd, Ht⟩

@[rocq_alias iriswasm.import_tab_wasm_check_alloc]
theorem import_tab_wasm_check_alloc (E : CoPset) (v_imps : List ModuleExport)
    (t_imps : List ExternT) (wfs : NatMap Tableinst) :
    ⊢ importTabWasmCheck (GF := GF) v_imps t_imps wfs ={E}=∗
      importTabWasmCheckInvs v_imps t_imps wfs := by
  unfold importTabWasmCheck importTabWasmCheckInvs importTabResources importTabNainv
  iintro ⟨Hm, %⟨Ht, Hd⟩⟩
  ihave Hm := BigSepM.bigSepM_mono_of_forall (Ψ := fun k v => iprop(|={E}=>
    (k ↪[wtsize] tabSize v) ∗ (k ↪[wtlimit] v.maxOpt) ∗
    ([∗list] j ↦ te ∈ v.data, NonAtomicInvariant.inv logrelNais (wtN k j) iprop(k ↦[wt][ j ] te))))
    (fun {k v} => by
      unfold tabBlock
      iintro ⟨Hl, Hs, Hlim⟩
      ihave Hl := BigSepL.bigSepL_mono_of_forall
        (fun {j te} => na_alloc_of E (wtN k j) iprop(k ↦[wt][ j ] te)) $$ Hl
      imod BigSepL2.bigSepL_fupd E _ _ $$ Hl with Hl
      imodintro; iframe) $$ Hm
  imod BigSepM.bigSepM_fupd E _ _ $$ Hm with Hm
  iframe
  ipureintro; exact ⟨Hd, Ht⟩

private theorem memBlock_alloc (E : CoPset) (k : Nat) (v : Memory) :
    memBlock (GF := GF) k v ⊢ |={E}=> interpMem v.type.address k ∗ k ↪[wmlimit] v.type.limits.max := by
  unfold memBlock interpMem
  iintro ⟨%hs, Hb, Hlen, Hlim⟩
  ihave Hi := na_alloc_of E (wmN k) iprop(∃ (m : Memory),
    ⌜WellSized v.type.address (lengthMem m)⌝ ∗ ([∗list] j ↦ b ∈ m.data.data, k ↦[wm][ j ] b) ∗
    k ↦[wmlength] (v.type.address, lengthMem m)) $$ [Hb Hlen]
  · iexists v; isplitr
    · ipureintro; exact hs.wellSized
    iframe
  imod Hi
  imodintro; iframe

#rocq_ignore iriswasm.import_mem_wasm_check_alloc "allocates a width-indexed memory invariant"
theorem import_mem_wasm_check_alloc (E : CoPset) (v_imps : List ModuleExport)
    (t_imps : List ExternT) (wfs : NatMap Memory) :
    ⊢ importMemWasmCheck (GF := GF) v_imps t_imps wfs ={E}=∗
      importMemWasmCheckInvs v_imps t_imps wfs := by
  unfold importMemWasmCheck importMemWasmCheckInvs importMemResources importMemNainv
  iintro ⟨Hm, %⟨Ht, Hd⟩⟩
  ihave Hm := BigSepM.bigSepM_mono_of_forall (fun {k v} => memBlock_alloc E k v) $$ Hm
  imod BigSepM.bigSepM_fupd E _ _ $$ Hm with Hm
  iframe
  ipureintro; exact ⟨Hd, Ht⟩

@[rocq_alias iriswasm.import_glob_wasm_check_alloc]
theorem import_glob_wasm_check_alloc (E : CoPset) (v_imps : List ModuleExport)
    (t_imps : List ExternT) (wfs : NatMap Global) :
    ⊢ importGlobWasmCheck (GF := GF) v_imps t_imps wfs ={E}=∗
      importGlobWasmCheckInvs v_imps t_imps wfs := by
  unfold importGlobWasmCheck importGlobWasmCheckInvs importGlobResources importGlobNainv
  iintro ⟨Hm, %⟨Ht, Hd⟩⟩
  ihave Hm := BigSepM.bigSepM_mono_of_forall (Ψ := fun k v => iprop(|={E}=>
    NonAtomicInvariant.inv logrelNais (wgN k)
      iprop(∃ w, k ↦[wg] (⟨v.mut_, w⟩ : Global) ∗ interpValue (typeof v.val) w)))
    (fun {k v} => by
      refine .trans ?_ (na_alloc_of E (wgN k) _)
      iintro H
      iexists v.val
      iframe
      rcases v with ⟨_, w⟩
      cases w <;> exact pure_intro ⟨_, rfl⟩) $$ Hm
  imod BigSepM.bigSepM_fupd E _ _ $$ Hm with Hm
  iframe
  ipureintro; exact ⟨Hd, Ht⟩

@[rocq_alias iriswasm.import_resources_wasm_typecheck_alloc]
theorem import_resources_wasm_typecheck_alloc (E : CoPset) (v_imps : List ModuleExport)
    (t_imps : List ExternT) (wfs : NatMap FunctionClosure) (wts : NatMap Tableinst)
    (wms : NatMap Memory) (wgs : NatMap Global) :
    ⊢ importResourcesWasmTypecheck (GF := GF) v_imps t_imps wfs wts wms wgs ={E}=∗
      importResourcesWasmTypecheckInvs v_imps t_imps wfs wts wms wgs := by
  unfold importResourcesWasmTypecheck importResourcesWasmTypecheckInvs
  iintro ⟨Hf, Ht, Hm, Hg⟩
  imod import_func_wasm_check_alloc E _ _ _ $$ Hf with Hf
  imod import_tab_wasm_check_alloc E _ _ _ $$ Ht with Ht
  imod import_mem_wasm_check_alloc E _ _ _ $$ Hm with Hm
  imod import_glob_wasm_check_alloc E _ _ _ $$ Hg with Hg
  imodintro; iframe

/-! ### Lengths of the imports -/

private theorem func_typecheck_len {v_imps : List ModuleExport} {t_imps : List ExternT}
    {wfs : NatMap FunctionClosure} (Ht : funcTypecheck v_imps t_imps wfs) :
    (extFuncAddrs (v_imps.map (·.desc))).length ≤ (extTFuncs t_imps).length := by
  induction Ht with
  | nil => simp [extFuncAddrs, extFuncs, extTFuncs]
  | @cons a b _ _ hr _ ih =>
    rcases a with ⟨_, ⟨_⟩ | ⟨_⟩ | ⟨_⟩ | ⟨_⟩⟩
    · obtain ⟨_, _, rfl⟩ := hr
      simp [extFuncAddrs, extFuncs, extTFuncs] at ih ⊢; omega
    all_goals cases b <;> simp [extFuncAddrs, extFuncs, extTFuncs] at ih ⊢ <;> omega

private theorem tab_typecheck_len {v_imps : List ModuleExport} {t_imps : List ExternT}
    {wts : NatMap Tableinst} (Ht : tabTypecheck v_imps t_imps wts) :
    (extTabAddrs (v_imps.map (·.desc))).length ≤ (extTTabs t_imps).length := by
  induction Ht with
  | nil => simp [extTabAddrs, extTabs, extTTabs]
  | @cons a b _ _ hr _ ih =>
    rcases a with ⟨_, ⟨_⟩ | ⟨_⟩ | ⟨_⟩ | ⟨_⟩⟩
    case table =>
      obtain ⟨_, _, _, rfl, _⟩ := hr
      simp [extTabAddrs, extTabs, extTTabs] at ih ⊢; omega
    all_goals cases b <;> simp [extTabAddrs, extTabs, extTTabs] at ih ⊢ <;> omega

private theorem mem_typecheck_len {v_imps : List ModuleExport} {t_imps : List ExternT}
    {wms : NatMap Memory} (Ht : memTypecheck v_imps t_imps wms) :
    (extMemAddrs (v_imps.map (·.desc))).length ≤ (extTMems t_imps).length := by
  induction Ht with
  | nil => simp [extMemAddrs, extMems, extTMems]
  | @cons a b _ _ hr _ ih =>
    rcases a with ⟨_, ⟨_⟩ | ⟨_⟩ | ⟨_⟩ | ⟨_⟩⟩
    case mem =>
      obtain ⟨_, _, _, rfl, _⟩ := hr
      simp [extMemAddrs, extMems, extTMems] at ih ⊢; omega
    all_goals cases b <;> simp [extMemAddrs, extMems, extTMems] at ih ⊢ <;> omega

private theorem glob_typecheck_len {v_imps : List ModuleExport} {t_imps : List ExternT}
    {wgs : NatMap Global} (Ht : globTypecheck v_imps t_imps wgs) :
    (extGlobAddrs (v_imps.map (·.desc))).length ≤ (extTGlobs t_imps).length := by
  induction Ht with
  | nil => simp [extGlobAddrs, extGlobs, extTGlobs]
  | @cons a b _ _ hr _ ih =>
    rcases a with ⟨_, ⟨_⟩ | ⟨_⟩ | ⟨_⟩ | ⟨_⟩⟩
    case global =>
      obtain ⟨_, _, _, rfl, _⟩ := hr
      simp [extGlobAddrs, extGlobs, extTGlobs] at ih ⊢; omega
    all_goals cases b <;> simp [extGlobAddrs, extGlobs, extTGlobs] at ih ⊢ <;> omega

@[rocq_alias iriswasm.import_func_wasm_check_lengths]
theorem import_func_wasm_check_lengths (v_imps : List ModuleExport) (t_imps : List ExternT)
    (wfs : NatMap FunctionClosure) :
    ⊢ importFuncWasmCheck (GF := GF) v_imps t_imps wfs -∗
      ⌜(extFuncAddrs (v_imps.map (·.desc))).length ≤ (extTFuncs t_imps).length⌝ := by
  unfold importFuncWasmCheck
  iintro ⟨_, %⟨Ht, _⟩⟩
  ipureintro; exact func_typecheck_len Ht

@[rocq_alias iriswasm.import_tab_wasm_check_lengths]
theorem import_tab_wasm_check_lengths (v_imps : List ModuleExport) (t_imps : List ExternT)
    (wfs : NatMap Tableinst) :
    ⊢ importTabWasmCheck (GF := GF) v_imps t_imps wfs -∗
      ⌜(extTabAddrs (v_imps.map (·.desc))).length ≤ (extTTabs t_imps).length⌝ := by
  unfold importTabWasmCheck
  iintro ⟨_, %⟨Ht, _⟩⟩
  ipureintro; exact tab_typecheck_len Ht

@[rocq_alias iriswasm.import_mem_wasm_check_lengths]
theorem import_mem_wasm_check_lengths (v_imps : List ModuleExport) (t_imps : List ExternT)
    (wfs : NatMap Memory) :
    ⊢ importMemWasmCheck (GF := GF) v_imps t_imps wfs -∗
      ⌜(extMemAddrs (v_imps.map (·.desc))).length ≤ (extTMems t_imps).length⌝ := by
  unfold importMemWasmCheck
  iintro ⟨_, %⟨Ht, _⟩⟩
  ipureintro; exact mem_typecheck_len Ht

@[rocq_alias iriswasm.import_glob_wasm_check_lengths]
theorem import_glob_wasm_check_lengths (v_imps : List ModuleExport) (t_imps : List ExternT)
    (wfs : NatMap Global) :
    ⊢ importGlobWasmCheck (GF := GF) v_imps t_imps wfs -∗
      ⌜(extGlobAddrs (v_imps.map (·.desc))).length ≤ (extTGlobs t_imps).length⌝ := by
  unfold importGlobWasmCheck
  iintro ⟨_, %⟨Ht, _⟩⟩
  ipureintro; exact glob_typecheck_len Ht

private theorem mem_extFuncAddrs {ds : List ModuleExportDesc} {fa : Nat} :
    fa ∈ extFuncAddrs ds ↔ ModuleExportDesc.func (.funcidx fa) ∈ ds := by
  induction ds with
  | nil => simp [extFuncAddrs, extFuncs]
  | cons d ds ih =>
    rcases d with ⟨⟨k⟩⟩ | ⟨⟨k⟩⟩ | ⟨⟨k⟩⟩ | ⟨⟨k⟩⟩ <;>
      simp_all [extFuncAddrs, extFuncs, eq_comm]

private theorem mem_extTabAddrs {ds : List ModuleExportDesc} {fa : Nat} :
    fa ∈ extTabAddrs ds ↔ ModuleExportDesc.table (.tableidx fa) ∈ ds := by
  induction ds with
  | nil => simp [extTabAddrs, extTabs]
  | cons d ds ih =>
    rcases d with ⟨⟨k⟩⟩ | ⟨⟨k⟩⟩ | ⟨⟨k⟩⟩ | ⟨⟨k⟩⟩ <;>
      simp_all [extTabAddrs, extTabs, eq_comm]

private theorem mem_extMemAddrs {ds : List ModuleExportDesc} {fa : Nat} :
    fa ∈ extMemAddrs ds ↔ ModuleExportDesc.mem (.memidx fa) ∈ ds := by
  induction ds with
  | nil => simp [extMemAddrs, extMems]
  | cons d ds ih =>
    rcases d with ⟨⟨k⟩⟩ | ⟨⟨k⟩⟩ | ⟨⟨k⟩⟩ | ⟨⟨k⟩⟩ <;>
      simp_all [extMemAddrs, extMems, eq_comm]

private theorem mem_extGlobAddrs {ds : List ModuleExportDesc} {fa : Nat} :
    fa ∈ extGlobAddrs ds ↔ ModuleExportDesc.global (.globalidx fa) ∈ ds := by
  induction ds with
  | nil => simp [extGlobAddrs, extGlobs]
  | cons d ds ih =>
    rcases d with ⟨⟨k⟩⟩ | ⟨⟨k⟩⟩ | ⟨⟨k⟩⟩ | ⟨⟨k⟩⟩ <;>
      simp_all [extGlobAddrs, extGlobs, eq_comm]

@[rocq_alias iriswasm.length_v_split]
theorem length_v_split (v_imps : List ModuleExportDesc) :
    v_imps.length = (extFuncAddrs v_imps).length + (extTabAddrs v_imps).length +
      (extMemAddrs v_imps).length + (extGlobAddrs v_imps).length := by
  induction v_imps with
  | nil => rfl
  | cons a l ih =>
    rcases a with ⟨_⟩ | ⟨_⟩ | ⟨_⟩ | ⟨_⟩ <;>
      simp [extFuncAddrs, extTabAddrs, extMemAddrs, extGlobAddrs, extFuncs, extTabs, extMems,
        extGlobs] at ih ⊢ <;> omega

@[rocq_alias iriswasm.length_t_split]
theorem length_t_split (t_imps : List ExternT) :
    t_imps.length = (extTFuncs t_imps).length + (extTTabs t_imps).length +
      (extTMems t_imps).length + (extTGlobs t_imps).length := by
  induction t_imps with
  | nil => rfl
  | cons a l ih =>
    rcases a with _ | _ | _ | _ <;>
      simp [extTFuncs, extTTabs, extTMems, extTGlobs] at ih ⊢ <;> omega

@[rocq_alias iriswasm.irwt_vtlen]
theorem irwt_vtlen (v_imps : List ModuleExport) (t_imps : List ExternT)
    (wfs : NatMap FunctionClosure) (wts : NatMap Tableinst) (wms : NatMap Memory)
    (wgs : NatMap Global) :
    ⊢ importResourcesWasmTypecheck (GF := GF) v_imps t_imps wfs wts wms wgs -∗
      ⌜v_imps.length = t_imps.length⌝ := by
  unfold importResourcesWasmTypecheck importFuncWasmCheck
  iintro ⟨⟨_, %⟨Ht, _⟩⟩, _⟩
  ipureintro; exact Wasm.List.Forall₂.length_eq Ht

@[rocq_alias iriswasm.import_resources_wasm_typecheck_lengths]
theorem import_resources_wasm_typecheck_lengths (v_imps : List ModuleExport)
    (t_imps : List ExternT) (wfs : NatMap FunctionClosure) (wts : NatMap Tableinst)
    (wms : NatMap Memory) (wgs : NatMap Global) :
    ⊢ importResourcesWasmTypecheck (GF := GF) v_imps t_imps wfs wts wms wgs -∗
      ⌜(extFuncAddrs (v_imps.map (·.desc))).length = (extTFuncs t_imps).length ∧
        (extTabAddrs (v_imps.map (·.desc))).length = (extTTabs t_imps).length ∧
        (extMemAddrs (v_imps.map (·.desc))).length = (extTMems t_imps).length ∧
        (extGlobAddrs (v_imps.map (·.desc))).length = (extTGlobs t_imps).length⌝ := by
  unfold importResourcesWasmTypecheck importFuncWasmCheck importTabWasmCheck importMemWasmCheck
    importGlobWasmCheck
  iintro ⟨⟨_, %⟨Hf, _⟩⟩, ⟨_, %⟨Ht, _⟩⟩, ⟨_, %⟨Hm, _⟩⟩, ⟨_, %⟨Hg, _⟩⟩⟩
  ipureintro
  have h1 := func_typecheck_len Hf
  have h2 := tab_typecheck_len Ht
  have h3 := mem_typecheck_len Hm
  have h4 := glob_typecheck_len Hg
  have hv := length_v_split (v_imps.map (·.desc))
  have ht := length_t_split t_imps
  have hl := Wasm.List.Forall₂.length_eq Hf
  simp only [List.length_map] at hv
  omega

/-! ### Invariants for the module's own resources -/

@[rocq_alias iriswasm.module_inst_resources_func_invs]
def moduleInstResourcesFuncInvs (mfuncs : List ModuleFunc) (inst : Instance)
    (inst_f : List Funcaddr) : IProp GF :=
  iprop([∗list] f;addr ∈ mfuncs;inst_f,
    NonAtomicInvariant.inv logrelNais (wfN addr) iprop(addr ↦[wf] (.funcNative inst
      (inst.types.getD (match f.type with | .typeidx k => k) (.tf [] [])) f.locals f.body)))

@[rocq_alias iriswasm.module_inst_resources_func_invs_alloc]
theorem module_inst_resources_func_invs_alloc (E : CoPset) (mfuncs : List ModuleFunc)
    (inst : Instance) (inst_f : List Funcaddr) :
    ⊢ moduleInstResourcesFunc (GF := GF) mfuncs inst inst_f ={E}=∗
      moduleInstResourcesFuncInvs mfuncs inst inst_f := by
  unfold moduleInstResourcesFunc moduleInstResourcesFuncInvs
  iintro H
  ihave H := BigSepL2.bigSepL2_mono_of_forall (na_alloc_of E _ _) $$ H
  iapply BigSepL2.bigSepL2_fupd E _ _ _ $$ H

@[rocq_alias iriswasm.ext_func_addrs_elem_of]
theorem ext_func_addrs_elem_of (fa : Nat) (v_imps : List ModuleExport)
    (h : fa ∈ extFuncAddrs (v_imps.map (·.desc))) :
    ∃ name, ({ name, desc := .func (.funcidx fa) } : ModuleExport) ∈ v_imps := by
  obtain ⟨⟨nm, d⟩, he, hd⟩ := List.mem_map.1 (mem_extFuncAddrs.1 h)
  simp only at hd; subst hd; exact ⟨nm, he⟩

@[rocq_alias iriswasm.ext_tab_addrs_elem_of]
theorem ext_tab_addrs_elem_of (fa : Nat) (v_imps : List ModuleExport)
    (h : fa ∈ extTabAddrs (v_imps.map (·.desc))) :
    ∃ name, ({ name, desc := .table (.tableidx fa) } : ModuleExport) ∈ v_imps := by
  obtain ⟨⟨nm, d⟩, he, hd⟩ := List.mem_map.1 (mem_extTabAddrs.1 h)
  simp only at hd; subst hd; exact ⟨nm, he⟩

@[rocq_alias iriswasm.ext_mem_addrs_elem_of]
theorem ext_mem_addrs_elem_of (fa : Nat) (v_imps : List ModuleExport)
    (h : fa ∈ extMemAddrs (v_imps.map (·.desc))) :
    ∃ name, ({ name, desc := .mem (.memidx fa) } : ModuleExport) ∈ v_imps := by
  obtain ⟨⟨nm, d⟩, he, hd⟩ := List.mem_map.1 (mem_extMemAddrs.1 h)
  simp only at hd; subst hd; exact ⟨nm, he⟩

@[rocq_alias iriswasm.ext_glob_addrs_elem_of]
theorem ext_glob_addrs_elem_of (fa : Nat) (v_imps : List ModuleExport)
    (h : fa ∈ extGlobAddrs (v_imps.map (·.desc))) :
    ∃ name, ({ name, desc := .global (.globalidx fa) } : ModuleExport) ∈ v_imps := by
  obtain ⟨⟨nm, d⟩, he, hd⟩ := List.mem_map.1 (mem_extGlobAddrs.1 h)
  simp only at hd; subst hd; exact ⟨nm, he⟩

@[rocq_alias iriswasm.module_res_imports_disj]
theorem module_res_imports_disj (v_imps : List ModuleExport) (t_imps : List ExternT)
    (wfs : NatMap FunctionClosure) (m : Module) (inst : Instance) :
    ⊢ importFuncWasmCheck (GF := GF) v_imps t_imps wfs -∗
      moduleInstResourcesFunc m.funcs inst (inst.funcs.drop (getImportFuncCount m)) -∗
      ⌜∀ (i fa : Nat), (inst.funcs.drop (getImportFuncCount m))[i]? = some fa →
        get? wfs fa = none⌝ := by
  unfold importFuncWasmCheck importFuncResources moduleInstResourcesFunc
  iintro ⟨Hr, %⟨_, _⟩⟩ Hf %i %fa %Hsome
  ihave %Hlen := BigSepL2.bigSepL2_length $$ Hf
  obtain ⟨f, hf⟩ : ∃ f, m.funcs[i]? = some f := by
    have := (List.getElem?_eq_some_iff.mp Hsome).1
    exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
  ihave H := BigSepL2.bigSepL2_lookup hf Hsome $$ Hf
  cases hw : get? wfs fa with
  | none => ipureintro; rfl
  | some cl =>
    ihave H' := BigSepM.bigSepM_lookup hw $$ Hr
    ihave %Hne := @pointsTo_ne GF Nat FunctionClosure NatMap _ WasmG.funcHs _ _ _ _ _ $$ H H'
    exact (Hne rfl).elim

@[rocq_alias iriswasm.module_inst_resources_tab_invs]
def moduleInstResourcesTabInvs (mtabs : List Tableinst) (inst_t : List Tableaddr) : IProp GF :=
  iprop([∗list] _i ↦ tab;addr ∈ mtabs;inst_t,
    addr ↪[wtsize] tabSize tab ∗ addr ↪[wtlimit] tab.maxOpt ∗
    ([∗list] j ↦ tabelem ∈ tab.data,
      NonAtomicInvariant.inv logrelNais (wtN addr j) iprop(addr ↦[wt][ j ] tabelem)))

@[rocq_alias iriswasm.module_inst_resources_tab_invs_alloc]
theorem module_inst_resources_tab_invs_alloc (E : CoPset) (mtabs : List Tableinst)
    (inst_t : List Tableaddr) :
    ⊢ moduleInstResourcesTab (GF := GF) mtabs inst_t ={E}=∗
      moduleInstResourcesTabInvs mtabs inst_t := by
  unfold moduleInstResourcesTab moduleInstResourcesTabInvs
  iintro H
  ihave H := BigSepL2.bigSepL2_mono_of_forall (Ψ := fun _ tab addr => iprop(|={E}=>
    addr ↪[wtsize] tabSize tab ∗ addr ↪[wtlimit] tab.maxOpt ∗
    ([∗list] j ↦ te ∈ tab.data,
      NonAtomicInvariant.inv logrelNais (wtN addr j) iprop(addr ↦[wt][ j ] te))))
    (fun {_ tab addr} => by
      unfold tabBlock
      iintro ⟨Hl, Hs, Hlim⟩
      ihave Hl := BigSepL.bigSepL_mono_of_forall
        (fun {j te} => na_alloc_of E (wtN addr j) iprop(addr ↦[wt][ j ] te)) $$ Hl
      imod BigSepL2.bigSepL_fupd E _ _ $$ Hl with Hl
      imodintro; iframe) $$ H
  iapply BigSepL2.bigSepL2_fupd E _ _ _ $$ H

#rocq_ignore iriswasm.module_inst_resources_mem_invs "each new memory retains its address width"
def moduleInstResourcesMemInvs (mmems : List Memory) (inst_m : List Memaddr) : IProp GF :=
  iprop([∗list] mem;addr ∈ mmems;inst_m,
    interpMem mem.type.address addr ∗ addr ↪[wmlimit] mem.type.limits.max)

#rocq_ignore iriswasm.module_inst_resources_mem_invs_alloc "allocates well-sized typed memory invariants"
theorem module_inst_resources_mem_invs_alloc (E : CoPset) (mmems : List Memory)
    (inst_m : List Memaddr) :
    ⊢ moduleInstResourcesMem (GF := GF) mmems inst_m ={E}=∗
      moduleInstResourcesMemInvs mmems inst_m := by
  unfold moduleInstResourcesMem moduleInstResourcesMemInvs
  iintro H
  ihave H := BigSepL2.bigSepL2_mono_of_forall
    (fun {_ mem addr} => memBlock_alloc E addr mem) $$ H
  iapply BigSepL2.bigSepL2_fupd E _ _ _ $$ H

@[rocq_alias iriswasm.module_inst_resources_glob_invs]
def moduleInstResourcesGlobInvs (mglobs : List Global) (inst_g : List Globaladdr)
    (gts : List GlobalType) : IProp GF :=
  iprop([∗list] i ↦ _g;addr ∈ mglobs;inst_g, ∃ τg, ⌜gts[i]? = some τg⌝ ∗
    NonAtomicInvariant.inv logrelNais (wgN addr)
      iprop(∃ w, addr ↦[wg] (⟨τg.mut_, w⟩ : Global) ∗ interpValue τg.t w))

@[rocq_alias iriswasm.module_inst_resources_glob_invs_persistent]
instance moduleInstResourcesGlobInvs_persistent (mglobs : List Global)
    (inst_g : List Globaladdr) (gts : List GlobalType) :
    Persistent (moduleInstResourcesGlobInvs (GF := GF) mglobs inst_g gts) := by
  unfold moduleInstResourcesGlobInvs; infer_instance

@[rocq_alias iriswasm.module_inst_global_init_lookup]
theorem module_inst_global_init_lookup (mglob_base : List Global) (g_inits : List Value)
    (k : Nat) (x : Global) (h : (moduleInstGlobalInit mglob_base g_inits)[k]? = some x) :
    (∃ v g, g_inits[k]? = some v ∧ mglob_base[k]? = some g ∧ x = globalInitReplaceSingle g v) ∨
      mglob_base[k]? = some x := by
  induction mglob_base generalizing g_inits k with
  | nil => simp [moduleInstGlobalInit] at h
  | cons g gs ih =>
    cases g_inits with
    | nil => right; simpa [moduleInstGlobalInit] using h
    | cons v vs =>
      cases k with
      | zero => left; simp [moduleInstGlobalInit] at h; exact ⟨v, g, rfl, rfl, h.symm⟩
      | succ k => simpa [moduleInstGlobalInit] using ih vs k (by simpa [moduleInstGlobalInit] using h)

@[rocq_alias iriswasm.bitzero_interp_value]
theorem bitzero_interp_value (tg_t : ValueType) :
    ⊢ (interpValue tg_t (bitzero tg_t) : IProp GF) := by
  cases tg_t <;> exact pure_intro ⟨_, rfl⟩

#rocq_ignore iriswasm.module_inst_resources_glob_invs_alloc "global initializers type in order"
theorem module_inst_resources_glob_invs_alloc (E : CoPset) (glob_inits : List Global)
    (mglobs : List ModuleGlob) (g_inits : List Value) (inst_g : List Globaladdr)
    (impts : List ExternT) (gts : List GlobalType) :
    ModuleGlobalsTyping (globalInitContext impts) mglobs gts →
    g_inits.map typeof = mglobs.map (·.type.t) →
    glob_inits = moduleInstGlobalInit (moduleInstBuildGlobals mglobs) g_inits →
    ⊢ moduleInstResourcesGlob (GF := GF) glob_inits inst_g ={E}=∗
      moduleInstResourcesGlobInvs glob_inits inst_g gts := by
  intro hgt htyp hgi
  subst hgi
  unfold moduleInstResourcesGlob moduleInstResourcesGlobInvs
  iintro H
  ihave H := BigSepL2.bigSepL2_mono (Ψ := fun k _ addr => iprop(|={E}=> ∃ τg, ⌜gts[k]? = some τg⌝ ∗
    NonAtomicInvariant.inv logrelNais (wgN addr)
      iprop(∃ w, addr ↦[wg] (⟨τg.mut_, w⟩ : Global) ∗ interpValue τg.t w)))
    (fun {k g addr} hl1 _ => by
      -- the global's type, and a value of that type it holds
      obtain ⟨mg, hmg, v, hg, hv⟩ : ∃ mg, mglobs[k]? = some mg ∧ ∃ v,
          g = ⟨mg.type.mut_, v⟩ ∧ typeof v = mg.type.t := by
        rcases module_inst_global_init_lookup _ _ _ _ hl1 with ⟨v, g0, hv, hg0, rfl⟩ | hg0
        · simp only [moduleInstBuildGlobals, List.getElem?_map, Option.map_eq_some_iff] at hg0
          obtain ⟨mg, hmg, rfl⟩ := hg0
          refine ⟨mg, hmg, v, rfl, ?_⟩
          have := congrArg (·[k]?) htyp
          simp [hv, hmg] at this
          exact this
        · simp only [moduleInstBuildGlobals, List.getElem?_map, Option.map_eq_some_iff] at hg0
          obtain ⟨mg, hmg, rfl⟩ := hg0
          refine ⟨mg, hmg, _, rfl, ?_⟩
          cases mg.type.t <;> rfl
      have hgt' : gts[k]? = some mg.type := by simp [hgt.types_eq, hmg]
      subst hg
      iintro Hg
      ihave Hi := na_alloc_of E (wgN addr) iprop(∃ w, addr ↦[wg] (⟨mg.type.mut_, w⟩ : Global) ∗
        interpValue mg.type.t w) $$ [Hg]
      · iexists v; iframe; rw [← hv]; iapply interp_value_type_of
      imod Hi
      imodintro; iexists mg.type; iframe; ipureintro; exact hgt') $$ H
  iapply BigSepL2.bigSepL2_fupd E _ _ _ $$ H

/-! ### Counting imports -/

@[rocq_alias iriswasm.get_import_count_length]
theorem get_import_count_length (m : Module) (t_imps : List ExternT) (c : TContext)
    (h : Wasm.List.Forall₂ (fun (imp : ModuleImport) e => moduleImportTyping c imp.desc e = true)
      m.imports t_imps) :
    getImportFuncCount m = (extTFuncs t_imps).length ∧
      getImportTableCount m = (extTTabs t_imps).length ∧
      getImportMemCount m = (extTMems t_imps).length ∧
      getImportGlobalCount m = (extTGlobs t_imps).length := by
  unfold getImportFuncCount getImportTableCount getImportMemCount getImportGlobalCount
  generalize m.imports = l at h ⊢
  induction h with
  | nil => simp [extTFuncs, extTTabs, extTMems, extTGlobs]
  | @cons imp t _ _ hr _ ih =>
    rcases imp with ⟨_, _, d⟩
    cases d <;> cases t <;> simp [moduleImportTyping] at hr <;>
      simp_all [extTFuncs, extTTabs, extTMems, extTGlobs]

@[rocq_alias iriswasm.inst_funcs_length_imp_app]
theorem inst_funcs_length_imp_app (ifts : List FunctionType) (t_imps : List ExternT)
    (v_imps : List ModuleExport) (inst_funcs : List Nat) (m : Module) (fts : List FunctionType)
    (c : TContext) :
    ifts = extTFuncs t_imps →
    extFuncAddrs (v_imps.map (·.desc)) <+: inst_funcs →
    (extFuncAddrs (v_imps.map (·.desc))).length = (extTFuncs t_imps).length →
    m.funcs.length = (inst_funcs.drop (getImportFuncCount m)).length →
    v_imps.length = t_imps.length →
    m.funcs.length = fts.length →
    Wasm.List.Forall₂ (fun (imp : ModuleImport) e => moduleImportTyping c imp.desc e = true)
      m.imports t_imps →
    inst_funcs.length = (ifts ++ fts).length := by
  intro hifts ⟨rest, hrest⟩ hlen hdrop _ hfts himps
  subst hifts hrest
  have hc := (get_import_count_length m t_imps c himps).1
  simp only [List.length_drop, List.length_append] at hdrop ⊢
  omega

@[rocq_alias iriswasm.inst_tabs_length_imp_app]
theorem inst_tabs_length_imp_app (ifts : List TableType) (t_imps : List ExternT)
    (v_imps : List ModuleExport) (inst_funcs : List Nat) (m : Module) (fts : List TableType)
    (c : TContext) :
    ifts = extTTabs t_imps →
    extTabAddrs (v_imps.map (·.desc)) <+: inst_funcs →
    (extTabAddrs (v_imps.map (·.desc))).length = (extTTabs t_imps).length →
    m.tables.length = (inst_funcs.drop (getImportTableCount m)).length →
    v_imps.length = t_imps.length →
    m.tables.length = fts.length →
    Wasm.List.Forall₂ (fun (imp : ModuleImport) e => moduleImportTyping c imp.desc e = true)
      m.imports t_imps →
    inst_funcs.length = (ifts ++ fts).length := by
  intro hifts ⟨rest, hrest⟩ hlen hdrop _ hfts himps
  subst hifts hrest
  have hc := (get_import_count_length m t_imps c himps).2.1
  simp only [List.length_drop, List.length_append] at hdrop ⊢
  omega

@[rocq_alias iriswasm.inst_mem_length_imp_app]
theorem inst_mem_length_imp_app (ifts : List MemoryType) (t_imps : List ExternT)
    (v_imps : List ModuleExport) (inst_funcs : List Nat) (m : Module) (fts : List MemoryType)
    (c : TContext) :
    ifts = extTMems t_imps →
    extMemAddrs (v_imps.map (·.desc)) <+: inst_funcs →
    (extMemAddrs (v_imps.map (·.desc))).length = (extTMems t_imps).length →
    m.mems.length = (inst_funcs.drop (getImportMemCount m)).length →
    v_imps.length = t_imps.length →
    m.mems.length = fts.length →
    Wasm.List.Forall₂ (fun (imp : ModuleImport) e => moduleImportTyping c imp.desc e = true)
      m.imports t_imps →
    inst_funcs.length = (ifts ++ fts).length := by
  intro hifts ⟨rest, hrest⟩ hlen hdrop _ hfts himps
  subst hifts hrest
  have hc := (get_import_count_length m t_imps c himps).2.2.1
  simp only [List.length_drop, List.length_append] at hdrop ⊢
  omega

@[rocq_alias iriswasm.inst_glob_length_imp_app]
theorem inst_glob_length_imp_app (ifts : List GlobalType) (t_imps : List ExternT)
    (v_imps : List ModuleExport) (inst_funcs : List Nat) (m : Module) (fts : List GlobalType)
    (c : TContext) :
    ifts = extTGlobs t_imps →
    extGlobAddrs (v_imps.map (·.desc)) <+: inst_funcs →
    (extGlobAddrs (v_imps.map (·.desc))).length = (extTGlobs t_imps).length →
    m.globals.length = (inst_funcs.drop (getImportGlobalCount m)).length →
    v_imps.length = t_imps.length →
    m.globals.length = fts.length →
    Wasm.List.Forall₂ (fun (imp : ModuleImport) e => moduleImportTyping c imp.desc e = true)
      m.imports t_imps →
    inst_funcs.length = (ifts ++ fts).length := by
  intro hifts ⟨rest, hrest⟩ hlen hdrop _ hfts himps
  subst hifts hrest
  have hc := (get_import_count_length m t_imps c himps).2.2.2
  simp only [List.length_drop, List.length_append] at hdrop ⊢
  omega

/-! ### Looking up imports -/

@[rocq_alias iriswasm.import_funcs_lookup]
theorem import_funcs_lookup (t_imps : List ExternT) (v_imps : List ModuleExport) (k : Nat)
    (ft : FunctionType) (fa : Nat) (wfs : NatMap FunctionClosure) (wts : NatMap Tableinst)
    (wms : NatMap Memory) (wgs : NatMap Global) :
    (extTFuncs t_imps)[k]? = some ft →
    (extFuncAddrs (v_imps.map (·.desc)))[k]? = some fa →
    funcTypecheck v_imps t_imps wfs → tabTypecheck v_imps t_imps wts →
    memTypecheck v_imps t_imps wms → globTypecheck v_imps t_imps wgs →
    ∃ k' : Nat, t_imps[k']? = some (ExternT.func ft) ∧
      ∃ fm : ModuleExport, v_imps[k']? = some fm ∧ fm.desc = .func (.funcidx fa) := by
  intro htl hvl hfc htc hmc hgc
  induction hfc generalizing k with
  | nil => simp [extTFuncs] at htl
  | @cons v t vs ts hr _ ih =>
    cases htc with | cons htr htc =>
    cases hmc with | cons hmr hmc =>
    cases hgc with | cons hgr hgc =>
    have next : ∀ k, (extTFuncs ts)[k]? = some ft →
        (extFuncAddrs (vs.map (·.desc)))[k]? = some fa →
        ∃ k' : Nat, (t :: ts)[k']? = some (ExternT.func ft) ∧
          ∃ fm : ModuleExport, (v :: vs)[k']? = some fm ∧ fm.desc = .func (.funcidx fa) :=
      fun k h1 h2 => let ⟨k', a, fm, b, c⟩ := ih k h1 h2 htc hmc hgc; ⟨k' + 1, a, fm, b, c⟩
    rcases v with ⟨nm, ⟨⟨i⟩⟩ | ⟨⟨i⟩⟩ | ⟨⟨i⟩⟩ | ⟨⟨i⟩⟩⟩
    · obtain ⟨_, _, rfl⟩ := hr
      cases k with
      | zero =>
        simp [extTFuncs, extFuncAddrs, extFuncs] at htl hvl
        exact ⟨0, by simp [htl], _, rfl, by simp [hvl]⟩
      | succ k =>
        exact next k (by simpa [extTFuncs] using htl)
          (by simpa [extFuncAddrs, extFuncs] using hvl)
    · obtain ⟨_, _, _, rfl, _⟩ := htr
      exact next k (by simpa [extTFuncs] using htl) (by simpa [extFuncAddrs, extFuncs] using hvl)
    · obtain ⟨_, _, _, rfl, _⟩ := hmr
      exact next k (by simpa [extTFuncs] using htl) (by simpa [extFuncAddrs, extFuncs] using hvl)
    · obtain ⟨_, _, _, rfl, _⟩ := hgr
      exact next k (by simpa [extTFuncs] using htl) (by simpa [extFuncAddrs, extFuncs] using hvl)

@[rocq_alias iriswasm.import_tabs_lookup]
theorem import_tabs_lookup (t_imps : List ExternT) (v_imps : List ModuleExport) (k : Nat)
    (ft : TableType) (fa : Nat) (wfs : NatMap FunctionClosure) (wts : NatMap Tableinst)
    (wms : NatMap Memory) (wgs : NatMap Global) :
    (extTTabs t_imps)[k]? = some ft →
    (extTabAddrs (v_imps.map (·.desc)))[k]? = some fa →
    funcTypecheck v_imps t_imps wfs → tabTypecheck v_imps t_imps wts →
    memTypecheck v_imps t_imps wms → globTypecheck v_imps t_imps wgs →
    ∃ k' : Nat, t_imps[k']? = some (ExternT.tab ft) ∧
      ∃ fm : ModuleExport, v_imps[k']? = some fm ∧ fm.desc = .table (.tableidx fa) := by
  intro htl hvl hfc htc hmc hgc
  induction hfc generalizing k with
  | nil => simp [extTTabs] at htl
  | @cons v t vs ts hr _ ih =>
    cases htc with | cons htr htc =>
    cases hmc with | cons hmr hmc =>
    cases hgc with | cons hgr hgc =>
    have next : ∀ k, (extTTabs ts)[k]? = some ft →
        (extTabAddrs (vs.map (·.desc)))[k]? = some fa →
        ∃ k' : Nat, (t :: ts)[k']? = some (ExternT.tab ft) ∧
          ∃ fm : ModuleExport, (v :: vs)[k']? = some fm ∧ fm.desc = .table (.tableidx fa) :=
      fun k h1 h2 => let ⟨k', a, fm, b, c⟩ := ih k h1 h2 htc hmc hgc; ⟨k' + 1, a, fm, b, c⟩
    rcases v with ⟨nm, ⟨⟨i⟩⟩ | ⟨⟨i⟩⟩ | ⟨⟨i⟩⟩ | ⟨⟨i⟩⟩⟩
    · obtain ⟨_, _, rfl⟩ := hr
      exact next k (by simpa [extTTabs] using htl) (by simpa [extTabAddrs, extTabs] using hvl)
    · obtain ⟨_, _, _, rfl, _⟩ := htr
      cases k with
      | zero =>
        simp [extTTabs, extTabAddrs, extTabs] at htl hvl
        exact ⟨0, by simp [htl], _, rfl, by simp [hvl]⟩
      | succ k =>
        exact next k (by simpa [extTTabs] using htl) (by simpa [extTabAddrs, extTabs] using hvl)
    · obtain ⟨_, _, _, rfl, _⟩ := hmr
      exact next k (by simpa [extTTabs] using htl) (by simpa [extTabAddrs, extTabs] using hvl)
    · obtain ⟨_, _, _, rfl, _⟩ := hgr
      exact next k (by simpa [extTTabs] using htl) (by simpa [extTabAddrs, extTabs] using hvl)

@[rocq_alias iriswasm.import_mems_lookup]
theorem import_mems_lookup (t_imps : List ExternT) (v_imps : List ModuleExport) (k : Nat)
    (ft : MemoryType) (fa : Nat) (wfs : NatMap FunctionClosure) (wts : NatMap Tableinst)
    (wms : NatMap Memory) (wgs : NatMap Global) :
    (extTMems t_imps)[k]? = some ft →
    (extMemAddrs (v_imps.map (·.desc)))[k]? = some fa →
    funcTypecheck v_imps t_imps wfs → tabTypecheck v_imps t_imps wts →
    memTypecheck v_imps t_imps wms → globTypecheck v_imps t_imps wgs →
    ∃ k' : Nat, t_imps[k']? = some (ExternT.mem ft) ∧
      ∃ fm : ModuleExport, v_imps[k']? = some fm ∧ fm.desc = .mem (.memidx fa) := by
  intro htl hvl hfc htc hmc hgc
  induction hfc generalizing k with
  | nil => simp [extTMems] at htl
  | @cons v t vs ts hr _ ih =>
    cases htc with | cons htr htc =>
    cases hmc with | cons hmr hmc =>
    cases hgc with | cons hgr hgc =>
    have next : ∀ k, (extTMems ts)[k]? = some ft →
        (extMemAddrs (vs.map (·.desc)))[k]? = some fa →
        ∃ k' : Nat, (t :: ts)[k']? = some (ExternT.mem ft) ∧
          ∃ fm : ModuleExport, (v :: vs)[k']? = some fm ∧ fm.desc = .mem (.memidx fa) :=
      fun k h1 h2 => let ⟨k', a, fm, b, c⟩ := ih k h1 h2 htc hmc hgc; ⟨k' + 1, a, fm, b, c⟩
    rcases v with ⟨nm, ⟨⟨i⟩⟩ | ⟨⟨i⟩⟩ | ⟨⟨i⟩⟩ | ⟨⟨i⟩⟩⟩
    · obtain ⟨_, _, rfl⟩ := hr
      exact next k (by simpa [extTMems] using htl) (by simpa [extMemAddrs, extMems] using hvl)
    · obtain ⟨_, _, _, rfl, _⟩ := htr
      exact next k (by simpa [extTMems] using htl) (by simpa [extMemAddrs, extMems] using hvl)
    · obtain ⟨_, _, _, rfl, _⟩ := hmr
      cases k with
      | zero =>
        simp [extTMems, extMemAddrs, extMems] at htl hvl
        exact ⟨0, by simp [htl], _, rfl, by simp [hvl]⟩
      | succ k =>
        exact next k (by simpa [extTMems] using htl) (by simpa [extMemAddrs, extMems] using hvl)
    · obtain ⟨_, _, _, rfl, _⟩ := hgr
      exact next k (by simpa [extTMems] using htl) (by simpa [extMemAddrs, extMems] using hvl)

@[rocq_alias iriswasm.import_globs_lookup]
theorem import_globs_lookup (t_imps : List ExternT) (v_imps : List ModuleExport) (k : Nat)
    (ft : GlobalType) (fa : Nat) (wfs : NatMap FunctionClosure) (wts : NatMap Tableinst)
    (wms : NatMap Memory) (wgs : NatMap Global) :
    (extTGlobs t_imps)[k]? = some ft →
    (extGlobAddrs (v_imps.map (·.desc)))[k]? = some fa →
    funcTypecheck v_imps t_imps wfs → tabTypecheck v_imps t_imps wts →
    memTypecheck v_imps t_imps wms → globTypecheck v_imps t_imps wgs →
    ∃ k' : Nat, t_imps[k']? = some (ExternT.glob ft) ∧
      ∃ fm : ModuleExport, v_imps[k']? = some fm ∧ fm.desc = .global (.globalidx fa) := by
  intro htl hvl hfc htc hmc hgc
  induction hfc generalizing k with
  | nil => simp [extTGlobs] at htl
  | @cons v t vs ts hr _ ih =>
    cases htc with | cons htr htc =>
    cases hmc with | cons hmr hmc =>
    cases hgc with | cons hgr hgc =>
    have next : ∀ k, (extTGlobs ts)[k]? = some ft →
        (extGlobAddrs (vs.map (·.desc)))[k]? = some fa →
        ∃ k' : Nat, (t :: ts)[k']? = some (ExternT.glob ft) ∧
          ∃ fm : ModuleExport, (v :: vs)[k']? = some fm ∧ fm.desc = .global (.globalidx fa) :=
      fun k h1 h2 => let ⟨k', a, fm, b, c⟩ := ih k h1 h2 htc hmc hgc; ⟨k' + 1, a, fm, b, c⟩
    rcases v with ⟨nm, ⟨⟨i⟩⟩ | ⟨⟨i⟩⟩ | ⟨⟨i⟩⟩ | ⟨⟨i⟩⟩⟩
    · obtain ⟨_, _, rfl⟩ := hr
      exact next k (by simpa [extTGlobs] using htl) (by simpa [extGlobAddrs, extGlobs] using hvl)
    · obtain ⟨_, _, _, rfl, _⟩ := htr
      exact next k (by simpa [extTGlobs] using htl) (by simpa [extGlobAddrs, extGlobs] using hvl)
    · obtain ⟨_, _, _, rfl, _⟩ := hmr
      exact next k (by simpa [extTGlobs] using htl) (by simpa [extGlobAddrs, extGlobs] using hvl)
    · obtain ⟨_, _, _, rfl, _⟩ := hgr
      cases k with
      | zero =>
        simp [extTGlobs, extGlobAddrs, extGlobs] at htl hvl
        exact ⟨0, by simp [htl], _, rfl, by simp [hvl]⟩
      | succ k =>
        exact next k (by simpa [extTGlobs] using htl) (by simpa [extGlobAddrs, extGlobs] using hvl)

@[rocq_alias iriswasm.repeat_imap_eq]
theorem repeat_imap_eq {A B C : Type} (a : A) (b : B) (f : Nat → C) (m : Nat) :
    (List.replicate m a).mapIdx (fun i _ => f i) = (List.replicate m b).mapIdx (fun i _ => f i) := by
  apply List.ext_getElem?
  intro i
  simp only [List.getElem?_mapIdx, List.getElem?_replicate]
  split <;> rfl

@[rocq_alias iriswasm.repeat_imap_lookup]
theorem repeat_imap_lookup {A B : Type} (a a' : A) (f : Nat → B) (m k : Nat)
    (h : (List.replicate m a)[k]? = some a') :
    ((List.replicate m a).mapIdx (fun i _ => f i))[k]? = some (f k) := by
  simp [List.getElem?_mapIdx, h]

/-! ### Module typing, unfolded -/

#rocq_ignore iriswasm.module_typing_body "the Core module judgment has unique exports and ordered globals"
abbrev ModuleTypingBody := Wasm.ModuleTypingFields

@[rocq_alias iriswasm.module_typing_body_eq]
theorem module_typing_body_eq (m : Module) (impts expts : List ExternT) :
    ModuleTyping m impts expts ↔ ∃ fts gts, ModuleTypingBody m impts expts fts gts :=
  Iff.rfl

/-! ### Table initialisers -/

@[rocq_alias iriswasm.module_tab_init_values_lookup]
theorem module_tab_init_values_lookup (m : Module) (inst : Instance) (l : List ModuleElement)
    (k : Nat) (n : Funcelem) (h : get? (moduleTabInitValues m inst l) (0, k) = some n) :
    ∃ (j : Nat) (elem : ModuleElement), l[j]? = some elem ∧
      match elem.table with
      | .tableidx i =>
        get? (buildTabInitialiser inst.funcs elem i (assertConst1I32ToNat elem.offset)) (0, k) =
          some n := by
  induction l with
  | nil => simp [moduleTabInitValues, get?_empty] at h
  | cons e es ih =>
    rcases e with ⟨⟨i⟩, off, init⟩
    simp only [moduleTabInitValues, LawfulPartialMap.get?_union] at h
    cases hr : get? (moduleTabInitValues m inst es) (0, k) with
    | some n' =>
      rw [hr] at h
      obtain ⟨j, el, hj, hm⟩ := ih (by simpa [Option.orElse] using hr.trans h)
      exact ⟨j + 1, el, by simpa using hj, hm⟩
    | none =>
      rw [hr] at h
      exact ⟨0, _, rfl, by simpa [Option.orElse] using h⟩

@[rocq_alias iriswasm.build_tab_initialiser_lookup]
theorem build_tab_initialiser_lookup (instfuncs : List Funcaddr) (elem : ModuleElement)
    (i k n : Nat)
    (h : get? (buildTabInitialiser instfuncs elem i (assertConst1I32ToNat elem.offset)) (0, k) =
      some (some n)) :
    ∃ (j fid : Nat), k = i + j + assertConst1I32ToNat elem.offset ∧
      elem.init[j]? = some (.funcidx fid) ∧ instfuncs[fid]? = some n := by
  rcases elem with ⟨tab, off, init⟩
  simp only [buildTabInitialiser] at h ⊢
  generalize assertConst1I32ToNat off = o at h ⊢
  obtain ⟨r, rfl⟩ : ∃ r, init = r.reverse := ⟨init.reverse, by simp⟩
  induction r generalizing k with
  | nil => simp [get?_empty] at h
  | cons x r ih =>
    rcases x with ⟨fid⟩
    simp only [List.reverse_cons, List.mapIdx_append, List.foldl_append, List.mapIdx_cons,
      List.mapIdx_nil, List.foldl_cons, List.foldl_nil, LawfulPartialMap.get?_insert] at h
    split at h
    · rename_i heq
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact ⟨r.reverse.length, fid, by omega, by simp, Option.some.inj h ▸ rfl⟩
    · obtain ⟨j, fid', hk, hj, hf⟩ := ih k h
      exact ⟨j, fid', hk, by
        rw [List.reverse_cons, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hj).1, hj],
        hf⟩

/-! ### `fold_left` invariants -/

@[rocq_alias iriswasm.fold_left_preserve_index]
theorem fold_left_preserve_index {A B : Type} (P : A → Prop) (f : A → B → A) (l : List B)
    (acc : A) (hacc : P acc)
    (hf : ∀ (x : A) (act : B), P x → (∃ i : Nat, l[i]? = some act) → P (f x act)) :
    P (l.foldl f acc) := by
  induction l generalizing acc with
  | nil => exact hacc
  | cons b l ih =>
    exact ih (f acc b) (hf acc b hacc ⟨0, rfl⟩) fun x act hx ⟨i, hi⟩ => hf x act hx ⟨i + 1, hi⟩

@[rocq_alias iriswasm.fold_left_preserve_filter]
theorem fold_left_preserve_filter {A B C : Type} (F : B → Prop) [DecidablePred F]
    (P : A → C → Prop) (f : A → B → A) (f' : C → B → C) (l : List B) (acc : A) (acc' : C)
    (hacc : P acc acc')
    (hnext : ∀ (x : A) (y : C) (act : B), F act → P x y → P (f x act) (f' y act))
    (hskip : ∀ (x : A) (y : C) (act : B), ¬ F act → P x y → P (f x act) y) :
    P (l.foldl f acc) ((l.filter (decide <| F ·)).foldl f' acc') := by
  induction l generalizing acc acc' with
  | nil => exact hacc
  | cons b l ih =>
    by_cases hb : F b
    · simp only [List.foldl_cons, List.filter_cons, hb, decide_true, ite_true]
      exact ih _ _ (hnext _ _ _ hb hacc)
    · simp only [List.foldl_cons, List.filter_cons, hb, decide_false]
      exact ih _ _ (hskip _ _ _ hb hacc)

@[rocq_alias iriswasm.fold_left_preserve_filter_index]
theorem fold_left_preserve_filter_index {A B C : Type} (F : B → Prop) [DecidablePred F]
    (P : A → C → Prop) (f : A → B → A) (f' : C → B → C) (l : List B) (acc : A) (acc' : C)
    (hacc : P acc acc')
    (hnext : ∀ (x : A) (y : C) (act : B), F act → (∃ i : Nat, l[i]? = some act) → P x y →
      P (f x act) (f' y act))
    (hskip : ∀ (x : A) (y : C) (act : B), ¬ F act → (∃ i : Nat, l[i]? = some act) → P x y →
      P (f x act) y) :
    P (l.foldl f acc) ((l.filter (decide <| F ·)).foldl f' acc') := by
  induction l generalizing acc acc' with
  | nil => exact hacc
  | cons b l ih =>
    have hn := fun x y act hF (⟨i, hi⟩ : ∃ i : Nat, l[i]? = some act) =>
      hnext x y act hF ⟨i + 1, hi⟩
    have hs := fun x y act hF (⟨i, hi⟩ : ∃ i : Nat, l[i]? = some act) =>
      hskip x y act hF ⟨i + 1, hi⟩
    by_cases hb : F b
    · simp only [List.foldl_cons, List.filter_cons, hb, decide_true, ite_true]
      exact ih _ _ (hnext _ _ _ hb ⟨0, rfl⟩ hacc) hn hs
    · simp only [List.foldl_cons, List.filter_cons, hb, decide_false]
      exact ih _ _ (hskip _ _ _ hb ⟨0, rfl⟩ hacc) hn hs

@[rocq_alias iriswasm.fold_left_preserve_filter_twice]
theorem fold_left_preserve_filter_twice {A B C : Type} (F : B → Prop) [DecidablePred F]
    (P : A → C → Prop) (f : A → B → A) (f' : C → B → C) (l : List B) (acc : A) (acc' : C)
    (hacc : P acc acc')
    (hnext : ∀ (x : A) (y : C) (act : B), F act → P x y → P (f x act) (f' y act))
    (hskip : ∀ (x : A) (y : C) (act : B), ¬ F act → P x y → P (f x act) y) :
    P (l.foldl f acc) ((l.filter (decide <| F ·)).foldl f' acc') := by
  exact fold_left_preserve_filter F P f f' l acc acc' hacc hnext hskip

@[rocq_alias iriswasm.fold_left_preserve_twice]
theorem fold_left_preserve_twice {A B C : Type} (P : A → C → Prop) (f : A → B → A)
    (f' : C → B → C) (l : List B) (acc : A) (acc' : C) (hacc : P acc acc')
    (hnext : ∀ (x : A) (y : C) (act : B), P x y → P (f x act) (f' y act)) :
    P (l.foldl f acc) (l.foldl f' acc') := by
  induction l generalizing acc acc' with
  | nil => exact hacc
  | cons b l ih => exact ih _ _ (hnext _ _ _ hacc)

@[rocq_alias iriswasm.fold_left_preserve_twice_index]
theorem fold_left_preserve_twice_index {A B C : Type} (P : A → C → Prop) (f : A → B → A)
    (f' : C → B → C) (l : List B) (acc : A) (acc' : C) (hacc : P acc acc')
    (hnext : ∀ (x : A) (y : C) (act : B), (∃ i : Nat, l[i]? = some act) → P x y →
      P (f x act) (f' y act)) :
    P (l.foldl f acc) (l.foldl f' acc') := by
  induction l generalizing acc acc' with
  | nil => exact hacc
  | cons b l ih =>
    exact ih _ _ (hnext _ _ _ ⟨0, rfl⟩ hacc) fun x y act ⟨i, hi⟩ => hnext x y act ⟨i + 1, hi⟩

@[rocq_alias iriswasm.fold_left_preserve_filter_impl]
theorem fold_left_preserve_filter_impl {A B C : Type} (F : B → Prop) [DecidablePred F]
    (P : A → Prop) (Q : C → Prop) (f : A → B → A) (f' : C → B → C) (l : List B) (acc : A)
    (acc' : C) (hacc : P acc → Q acc')
    (hnext : ∀ (x : A) (y : C) (act : B), F act → (P x → Q y) → P (f x act) → Q (f' y act))
    (hskip : ∀ (x : A) (y : C) (act : B), ¬ F act → (P x → Q y) → P (f x act) → Q y) :
    P (l.foldl f acc) → Q ((l.filter (decide <| F ·)).foldl f' acc') := by
  induction l generalizing acc acc' with
  | nil => exact hacc
  | cons b l ih =>
    by_cases hb : F b
    · simp only [List.foldl_cons, List.filter_cons, hb, decide_true, ite_true]
      exact ih _ _ (hnext _ _ _ hb hacc)
    · simp only [List.foldl_cons, List.filter_cons, hb, decide_false]
      exact ih _ _ (hskip _ _ _ hb hacc)

@[rocq_alias iriswasm.module_inst_resources_wasm_invs]
def moduleInstResourcesWasmInvs (m : Module) (inst : Instance) (gts : List GlobalType)
    (t_inits : List Tableinst) (m_inits : List Memory) (g_inits : List Global) : IProp GF :=
  iprop(moduleInstResourcesFuncInvs m.funcs inst (inst.funcs.drop (getImportFuncCount m)) ∗
    moduleInstResourcesTabInvs t_inits (inst.tab.drop (getImportTableCount m)) ∗
    moduleInstResourcesMemInvs m_inits (inst.memory.drop (getImportMemCount m)) ∗
    moduleInstResourcesGlobInvs g_inits (inst.globs.drop (getImportGlobalCount m)) gts)

#rocq_ignore iriswasm.modelem_filter_dec
  "List.filter takes a Bool predicate; `module_element_filter_relevant_idx` uses `decide`"

/-! ### Building the module's own tables -/

@[rocq_alias iriswasm.module_element_filter_relevant_idx]
def moduleElementFilterRelevantIdx (e : List ModuleElement) (n : Nat) : List ModuleElement :=
  e.filter fun me => decide (match me.table with | .tableidx m => n = m)

@[rocq_alias iriswasm.module_inst_build_table_filter]
def moduleInstBuildTableFilter (m : Module) (inst : Instance) (n : Nat) (mt : ModuleTable) :
    Tableinst :=
  (moduleElementFilterRelevantIdx m.elem n).foldl (fun t me =>
    let itc := getImportTableCount m
    match me.table with
    | .tableidx k =>
      if k < itc then t else
        tableInitReplaceSingle t (assertConst1I32ToNat me.offset) (lookupFuncaddr inst me.init))
    (moduleInstTableBaseCreate mt)

@[rocq_alias iriswasm.module_inst_build_table]
def moduleInstBuildTable (m : Module) (inst : Instance) (n : Nat) (mt : ModuleTable) :
    Tableinst :=
  m.elem.foldl (fun t me =>
    let itc := getImportTableCount m
    match me.table with
    | .tableidx k =>
      if k < itc then t else
        if k = n then
          tableInitReplaceSingle t (assertConst1I32ToNat me.offset) (lookupFuncaddr inst me.init)
        else t)
    (moduleInstTableBaseCreate mt)

@[rocq_alias iriswasm.module_inst_build_table_filter_eq]
theorem module_inst_build_table_filter_eq (m : Module) (inst : Instance) (n : Nat)
    (mt : ModuleTable) :
    moduleInstBuildTableFilter m inst n mt = moduleInstBuildTable m inst n mt := by
  unfold moduleInstBuildTableFilter moduleInstBuildTable moduleElementFilterRelevantIdx
  generalize moduleInstTableBaseCreate mt = t
  induction m.elem generalizing t with
  | nil => rfl
  | cons e l ih =>
    rcases e with ⟨⟨k⟩, off, init⟩
    by_cases hk : n = k
    · subst hk; simp [ih]
    · simp [hk, Ne.symm hk, ih]

@[rocq_alias iriswasm.module_inst_build_table_map]
def moduleInstBuildTableMap (m : Module) (inst : Instance) : List Tableinst :=
  m.tables.mapIdx fun j mt => moduleInstBuildTable m inst (j + getImportTableCount m) mt

@[rocq_alias iriswasm.imap_id]
theorem imap_id {A : Type} (acc : List A) : acc.mapIdx (fun _ a => a) = acc := by
  apply List.ext_getElem?
  intro i
  simp only [List.getElem?_mapIdx]
  cases acc[i]? <;> rfl

/-- One step of `moduleInstBuildTables` (the function folded over `m.elem`). -/
private def tabsStep (m : Module) (inst : Instance) (tabs : List Tableinst) (e : ModuleElement) :
    List Tableinst :=
  match e.table with
  | .tableidx k =>
    if k < getImportTableCount m then tabs else
      match tabs[k - getImportTableCount m]? with
      | some t => tabs.set (k - getImportTableCount m)
          (tableInitReplaceSingle t (assertConst1I32ToNat e.offset) (lookupFuncaddr inst e.init))
      | none => tabs

/-- One step of `moduleInstBuildTable m inst n`. -/
private def tabStep (m : Module) (inst : Instance) (n : Nat) (t : Tableinst) (me : ModuleElement) :
    Tableinst :=
  match me.table with
  | .tableidx k =>
    if k < getImportTableCount m then t else
      if k = n then
        tableInitReplaceSingle t (assertConst1I32ToNat me.offset) (lookupFuncaddr inst me.init)
      else t

private theorem buildTables_eq (m : Module) (inst : Instance) :
    moduleInstBuildTables m inst = m.elem.foldl (tabsStep m inst) (moduleInstTableBase m.tables) :=
  rfl

private theorem buildTable_eq (m : Module) (inst : Instance) (n : Nat) (mt : ModuleTable) :
    moduleInstBuildTable m inst n mt = m.elem.foldl (tabStep m inst n) (moduleInstTableBaseCreate mt) :=
  rfl

/-- Folding a list-updating step that acts pointwise is the pointwise fold. -/
private theorem foldl_mapIdx_comm {α β : Type} (l : List β) (step : List α → β → List α)
    (stepT : Nat → α → β → α) (hstep : ∀ ts e, step ts e = ts.mapIdx (fun j t => stepT j t e))
    (ts : List α) : l.foldl step ts = ts.mapIdx (fun j t => l.foldl (stepT j) t) := by
  induction l generalizing ts with
  | nil => exact (imap_id ts).symm
  | cons e l ih => rw [List.foldl_cons, ih, hstep, List.mapIdx_mapIdx]; rfl

private theorem tabsStep_eq (m : Module) (inst : Instance) (ts : List Tableinst)
    (e : ModuleElement) :
    tabsStep m inst ts e = ts.mapIdx (fun j t => tabStep m inst (j + getImportTableCount m) t e) := by
  rcases e with ⟨⟨k⟩, off, init⟩
  simp only [tabsStep, tabStep]
  by_cases hk : k < getImportTableCount m
  · simp only [hk, ite_true]; exact (imap_id ts).symm
  · simp only [hk, ite_false]
    apply List.ext_getElem?
    intro j
    simp only [List.getElem?_mapIdx]
    split
    · rename_i t0 ht0
      rw [List.getElem?_set]
      by_cases hj : k - getImportTableCount m = j
      · subst hj
        obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp ht0
        simp [hlt, heq, show k - getImportTableCount m + getImportTableCount m = k by omega]
      · simp only [hj, ite_false]
        cases ts[j]? <;> simp [show k ≠ j + getImportTableCount m by omega]
    · rename_i ht0
      cases hj : ts[j]? with
      | none => rfl
      | some t =>
        have : k ≠ j + getImportTableCount m := by
          rintro rfl; simp [hj] at ht0
        simp [this]

private theorem tables_eq_map (m : Module) (inst : Instance) :
    moduleInstBuildTables m inst = moduleInstBuildTableMap m inst := by
  rw [buildTables_eq, foldl_mapIdx_comm _ _ _ (tabsStep_eq m inst)]
  unfold moduleInstBuildTableMap moduleInstTableBase
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_mapIdx, List.getElem?_map, Option.map_map]
  rfl

@[rocq_alias iriswasm.module_inst_build_tables_lookup]
theorem module_inst_build_tables_lookup (m : Module) (i : Instance) (j : Nat) (a : ModuleTable)
    (x : Tableinst) :
    m.tables[j]? = some a → (moduleInstBuildTables m i)[j]? = some x →
    x = moduleInstBuildTable m i (j + getImportTableCount m) a := by
  intro ha hx
  rw [tables_eq_map] at hx
  simp [moduleInstBuildTableMap, ha] at hx
  exact hx.symm

@[rocq_alias iriswasm.module_inst_build_tables_lookup_None]
theorem module_inst_build_tables_lookup_None (m : Module) (i : Instance) (j : Nat) :
    m.tables[j]? = none → (moduleInstBuildTables m i)[j]? = none := by
  intro ha
  rw [tables_eq_map]
  simp [moduleInstBuildTableMap, ha]

@[rocq_alias iriswasm.module_inst_build_tables_lookup_is_Some]
theorem module_inst_build_tables_lookup_is_Some (m : Module) (i : Instance) (j : Nat)
    (a : ModuleTable) :
    m.tables[j]? = some a → ((moduleInstBuildTables m i)[j]?).isSome = true := by
  intro ha
  rw [tables_eq_map]
  simp [moduleInstBuildTableMap, ha]

@[rocq_alias iriswasm.module_inst_build_table_map_lookup]
theorem module_inst_build_table_map_lookup (m : Module) (inst : Instance) (i : Nat)
    (m0 : ModuleTable) :
    m.tables[i]? = some m0 →
    (moduleInstBuildTableMap m inst)[i]? =
      some (moduleInstBuildTable m inst (i + getImportTableCount m) m0) := by
  intro ha
  simp [moduleInstBuildTableMap, ha]

@[rocq_alias iriswasm.module_inst_build_table_map_lookup_None]
theorem module_inst_build_table_map_lookup_None (m : Module) (inst : Instance) (i : Nat) :
    m.tables[i]? = none → (moduleInstBuildTableMap m inst)[i]? = none := by
  intro ha
  simp [moduleInstBuildTableMap, ha]

@[rocq_alias iriswasm.module_inst_build_table_map_eq]
theorem module_inst_build_table_map_eq (m : Module) (inst : Instance) :
    moduleInstBuildTableMap m inst = moduleInstBuildTables m inst := by
  exact (tables_eq_map m inst).symm

@[rocq_alias iriswasm.module_inst_built_table_max_opt_eq]
theorem module_inst_built_table_max_opt_eq (m : Module) (i : Instance) (n : Nat)
    (m0 : ModuleTable) :
    (moduleInstBuildTable m i n m0).maxOpt = m0.type.limits.max := by
  rw [buildTable_eq]
  refine fold_left_preserve (fun t : Tableinst => t.maxOpt = m0.type.limits.max) _ _ _ ?_ ?_
  · simp [moduleInstTableBaseCreate]
  · intro t me ht
    rcases me with ⟨⟨k⟩, off, init⟩
    simp only [tabStep]
    split
    · exact ht
    · split
      · simp [tableInitReplaceSingle, ht]
      · exact ht

@[rocq_alias iriswasm.module_inst_build_table_length]
theorem module_inst_build_table_length (m : Module) (i : Instance) (n : Nat) (m0 : ModuleTable) :
    (moduleInstBuildTable m i n m0).data.length = m0.type.limits.min := by
  rw [buildTable_eq]
  refine fold_left_preserve (fun t : Tableinst => t.data.length = m0.type.limits.min) _ _ _ ?_ ?_
  · simp [moduleInstTableBaseCreate, Tableinst.data]
  · intro t me ht
    rcases me with ⟨⟨k⟩, off, init⟩
    simp only [tabStep]
    split
    · exact ht
    · split
      · exact (table_init_replace_single_preserve_len _ _ _ _ rfl).symm.trans ht
      · exact ht

@[rocq_alias iriswasm.module_inst_build_table_lt_is_Some]
theorem module_inst_build_table_lt_is_Some (m : Module) (i : Instance) (n : Nat)
    (m0 : ModuleTable) (j : Nat) :
    j < m0.type.limits.min → ((moduleInstBuildTable m i n m0).data[j]?).isSome = true := by
  intro hj
  rw [← module_inst_build_table_length m i n m0] at hj
  rw [List.getElem?_eq_getElem hj]; rfl

@[rocq_alias iriswasm.repeat_lookup_eq]
theorem repeat_lookup_eq (T : Type) (x y : T) (n i : Nat) :
    (List.replicate n x)[i]? = some y → x = y := by
  intro h
  simp only [List.getElem?_replicate] at h
  split at h <;> simp_all

private theorem replace_lookup (t : Tableinst) (fns : List Funcelem) (o j : Nat) (x : Funcelem)
    (h : (tableInitReplaceSingle t o fns).data[j]? = some x) :
    t.data[j]? = some x ∨ ∃ e : Nat, fns[e]? = some x := by
  have hj := (List.getElem?_eq_some_iff.1 h).1
  rw [← table_init_replace_single_preserve_len t o fns _ rfl] at hj
  rw [data_tableInitReplaceSingle, List.append_assoc, List.getElem?_append] at h
  split at h
  · left; rw [List.getElem?_take] at h; split at h <;> simp_all
  · rw [List.getElem?_append] at h
    split at h
    · right
      rw [List.getElem?_take] at h
      split at h
      · exact ⟨_, h⟩
      · cases h
    · left; rw [List.getElem?_drop] at h; rw [← h]; congr 1; simp at *; omega

private theorem isSome_insert_of_some {V : Type} {w : NatMap V} {a n : Nat} {t0 v : V}
    (h : get? w a = some t0) : (get? (insert w a v) n).isSome = (get? w n).isSome := by
  rw [LawfulPartialMap.get?_insert]; split <;> simp_all

@[rocq_alias iriswasm.module_inst_build_table_lookup_Some]
theorem module_inst_build_table_lookup_Some (m : Module) (i : Instance) (n : Nat)
    (m0 : ModuleTable) (j : Nat) (x : Funcelem) :
    (moduleInstBuildTable m i n m0).data[j]? = some x →
    x = none ∨ ∃ (k : Nat) (moff : Wasm.Expr) (minit : List Funcidx) (idx f : Nat),
      i.funcs[idx]? = some f ∧ x = some f ∧
      m.elem[k]? = some ⟨.tableidx n, moff, minit⟩ ∧
      decide (n < getImportTableCount m) = false ∧
      ∃ ei : Nat, minit[ei]? = some (.funcidx idx) := by
  rw [buildTable_eq]
  revert j x
  refine fold_left_preserve_index (fun t : Tableinst => ∀ j x, t.data[j]? = some x →
    x = none ∨ ∃ (k : Nat) (moff : Wasm.Expr) (minit : List Funcidx) (idx f : Nat),
      i.funcs[idx]? = some f ∧ x = some f ∧
      m.elem[k]? = some ⟨.tableidx n, moff, minit⟩ ∧
      decide (n < getImportTableCount m) = false ∧
      ∃ ei : Nat, minit[ei]? = some (.funcidx idx)) _ _ _ ?_ ?_
  · intro j x h
    simp only [moduleInstTableBaseCreate, Tableinst.data, RunTable.toList_uniform] at h
    exact .inl (repeat_lookup_eq _ _ _ _ _ h).symm
  · intro t me ht ⟨ki, hki⟩ j x h
    rcases me with ⟨⟨k⟩, off, init⟩
    simp only [tabStep] at h
    split at h
    · exact ht _ _ h
    · split at h
      · rename_i h1 h2
        subst h2
        rcases replace_lookup _ _ _ _ _ h with h | ⟨e, he⟩
        · exact ht _ _ h
        · simp only [lookupFuncaddr, List.getElem?_map, Option.map_eq_some_iff] at he
          obtain ⟨⟨idx⟩, ha, rfl⟩ := he
          cases hf : i.funcs[idx]? with
          | none => exact .inl rfl
          | some f => exact .inr ⟨ki, off, init, idx, f, hf, rfl, hki, by simp [h1], e, ha⟩
      · exact ht _ _ h

/-! ### Re-initialising imported tables -/

@[rocq_alias iriswasm.module_import_init_tab]
def moduleImportInitTab (m : Module) (inst : Instance) (n : Nat) (mt : Tableinst) : Tableinst :=
  m.elem.foldl (fun t me =>
    let itc := getImportTableCount m
    match me.table with
    | .tableidx k =>
      if k < itc then
        match inst.tab[k]? with
        | some tAddr =>
          if tAddr = n then
            tableInitReplaceSingle t (assertConst1I32ToNat me.offset) (lookupFuncaddr inst me.init)
          else t
        | none => t
      else t) mt

@[rocq_alias iriswasm.module_import_init_tabs_lookup]
theorem module_import_init_tabs_lookup (m : Module) (i : Instance) (wts : NatMap Tableinst)
    (n : Nat) (tab tab' : Tableinst) :
    get? wts n = some tab → get? (moduleImportInitTabs m i wts) n = some tab' →
    tab' = moduleImportInitTab m i n tab := by
  intro h1 h2
  unfold moduleImportInitTabs at h2
  unfold moduleImportInitTab
  refine Option.some.inj (h2.symm.trans ?_)
  refine fold_left_preserve_twice (fun (w : NatMap Tableinst) t => get? w n = some t) _ _ _ _ _
    h1 ?_
  intro w t me hw
  rcases me with ⟨⟨k⟩, off, init⟩
  dsimp only
  by_cases hk : k < getImportTableCount m
  · simp only [hk, ite_true]
    cases htab : i.tab[k]? with
    | none => exact hw
    | some tAddr =>
      dsimp only
      cases h0 : get? w tAddr with
      | none =>
        have hn : tAddr ≠ n := by rintro rfl; simp [hw] at h0
        simp [hn, hw]
      | some t0 =>
        by_cases hn : tAddr = n
        · subst hn; rw [hw] at h0; cases h0; simp [LawfulPartialMap.get?_insert]
        · simp [LawfulPartialMap.get?_insert, hn, hw]
  · simp only [hk, ite_false]; exact hw

@[rocq_alias iriswasm.module_import_init_tab_lookup_length]
theorem module_import_init_tab_lookup_length (m : Module) (i : Instance) (n : Nat)
    (tab : Tableinst) : (moduleImportInitTab m i n tab).data.length = tab.data.length := by
  unfold moduleImportInitTab
  refine fold_left_preserve (fun t : Tableinst => t.data.length = tab.data.length) _ _ _ rfl ?_
  intro t me ht
  rcases me with ⟨⟨k⟩, off, init⟩
  dsimp only
  split
  · split
    · split
      · exact (table_init_replace_single_preserve_len _ _ _ _ rfl).symm.trans ht
      · exact ht
    · exact ht
  · exact ht

private theorem importInitTabs_isSome (m : Module) (i : Instance) (wts : NatMap Tableinst)
    (n : Nat) : (get? (moduleImportInitTabs m i wts) n).isSome = (get? wts n).isSome := by
  unfold moduleImportInitTabs
  refine fold_left_preserve (fun w : NatMap Tableinst => (get? w n).isSome = (get? wts n).isSome)
    _ _ _ rfl ?_
  intro w me hw
  rcases me with ⟨⟨k⟩, off, init⟩
  dsimp only
  split
  · split
    · split
      · rw [isSome_insert_of_some ‹_›]; exact hw
      · exact hw
    · exact hw
  · exact hw

@[rocq_alias iriswasm.module_import_init_tabs_is_Some]
theorem module_import_init_tabs_is_Some (m : Module) (i : Instance) (wts : NatMap Tableinst)
    (n : Nat) :
    (get? wts n).isSome = true ↔ (get? (moduleImportInitTabs m i wts) n).isSome = true := by
  rw [importInitTabs_isSome]

@[rocq_alias iriswasm.module_import_init_tabs_Some]
theorem module_import_init_tabs_Some (m : Module) (i : Instance) (wts : NatMap Tableinst)
    (n : Nat) (x : Tableinst) :
    get? (moduleImportInitTabs m i wts) n = some x → (get? wts n).isSome = true := by
  intro h
  rw [← importInitTabs_isSome m i, h]; rfl

@[rocq_alias iriswasm.module_import_init_tab_lookup_Some]
theorem module_import_init_tab_lookup_Some (m : Module) (i : Instance) (n : Nat)
    (tab : Tableinst) (j : Nat) (x : Funcelem) :
    (moduleImportInitTab m i n tab).data[j]? = some x →
    tab.data[j]? = some x ∨
      ∃ (k : Nat) (moff : Wasm.Expr) (minit : List Funcidx) (idx n1 : Nat),
        i.tab[idx]? = some n ∧ x = i.funcs[n1]? ∧
        m.elem[k]? = some ⟨.tableidx idx, moff, minit⟩ ∧
        decide (idx < getImportTableCount m) = true ∧
        ∃ ei : Nat, minit[ei]? = some (.funcidx n1) := by
  unfold moduleImportInitTab
  revert j x
  refine fold_left_preserve_index (fun t : Tableinst => ∀ j x, t.data[j]? = some x →
    tab.data[j]? = some x ∨
      ∃ (k : Nat) (moff : Wasm.Expr) (minit : List Funcidx) (idx n1 : Nat),
        i.tab[idx]? = some n ∧ x = i.funcs[n1]? ∧
        m.elem[k]? = some ⟨.tableidx idx, moff, minit⟩ ∧
        decide (idx < getImportTableCount m) = true ∧
        ∃ ei : Nat, minit[ei]? = some (.funcidx n1)) _ _ _ (fun _ _ h => .inl h) ?_
  intro t me ht ⟨ki, hki⟩ j x h
  rcases me with ⟨⟨k⟩, off, init⟩
  dsimp only at h
  split at h
  · rename_i h1
    split at h
    · rename_i tAddr htab
      split at h
      · rename_i h2
        subst h2
        rcases replace_lookup _ _ _ _ _ h with h | ⟨e, he⟩
        · exact ht _ _ h
        · simp only [lookupFuncaddr, List.getElem?_map, Option.map_eq_some_iff] at he
          obtain ⟨⟨idx⟩, ha, rfl⟩ := he
          exact .inr ⟨ki, off, init, k, idx, htab, rfl, hki, by simp [h1], e, ha⟩
      · exact ht _ _ h
    · exact ht _ _ h
  · exact ht _ _ h

@[rocq_alias iriswasm.module_import_init_tab_table_max_opt_eq]
theorem module_import_init_tab_table_max_opt_eq (m : Module) (i : Instance) (n : Nat)
    (x : Tableinst) : (moduleImportInitTab m i n x).maxOpt = x.maxOpt := by
  unfold moduleImportInitTab
  refine fold_left_preserve (fun t : Tableinst => t.maxOpt = x.maxOpt) _ _ _ rfl ?_
  intro t me ht
  rcases me with ⟨⟨k⟩, off, init⟩
  dsimp only
  split
  · split
    · split
      · exact ht
      · exact ht
    · exact ht
  · exact ht

/-! ### Memories -/

@[rocq_alias iriswasm.module_inst_build_mems_length]
theorem module_inst_build_mems_length (m : Module) (i : Instance) :
    (moduleInstBuildMems m i).length = m.mems.length := by
  unfold moduleInstBuildMems
  refine fold_left_preserve (fun l : List Memory => l.length = m.mems.length) _ _ _
    (by simp [moduleInstMemBase]) ?_
  intro l d hl
  rcases d with ⟨⟨k⟩, off, init⟩
  dsimp only
  split <;> try exact hl
  split <;> try exact hl
  split <;> simpa using hl

private def memStep (m : Module) (n : Nat) (mem : Memory) (d : ModuleData) : Memory :=
  match d.data with
  | .memidx k =>
    if k < getImportMemCount m then mem else
      if n = k then
        match literalDataOffset d.offset with
        | some off => memInitReplaceSingle mem off d.init
        | none => mem
      else mem

#rocq_ignore iriswasm.module_inst_build_mem "active data uses the literal memory32 or memory64 offset"
def moduleInstBuildMem (m : Module) (_inst : Instance) (n : Nat) (mmem : Memory) : Memory :=
  m.data.foldl (memStep m n) mmem

/-- One step of `moduleInstBuildMems` (the function folded over `m.data`). -/
private def memsStep (m : Module) (mems : List Memory) (d : ModuleData) : List Memory :=
  match d.data with
  | .memidx k =>
    if k < getImportMemCount m then mems else
      match mems[k - getImportMemCount m]? with
      | some mem =>
        match literalDataOffset d.offset with
        | some off => mems.set (k - getImportMemCount m) (memInitReplaceSingle mem off d.init)
        | none => mems
      | none => mems

private theorem memsStep_eq (m : Module) (ms : List Memory) (d : ModuleData) :
    memsStep m ms d = ms.mapIdx (fun j t => memStep m (j + getImportMemCount m) t d) := by
  rcases d with ⟨⟨k⟩, off, init⟩
  simp only [memsStep, memStep]
  by_cases hk : k < getImportMemCount m
  · simp only [hk, ite_true]; exact (imap_id ms).symm
  · simp only [hk, ite_false]
    apply List.ext_getElem?
    intro j
    simp only [List.getElem?_mapIdx]
    split
    · rename_i t0 ht0
      cases literalDataOffset off
      · simp
      rw [List.getElem?_set]
      by_cases hj : k - getImportMemCount m = j
      · subst hj
        obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp ht0
        simp [hlt, heq, show k - getImportMemCount m + getImportMemCount m = k by omega]
      · simp only [hj, ite_false]
        cases ms[j]? <;> simp [show j + getImportMemCount m ≠ k by omega]
    · rename_i ht0
      cases hj : ms[j]? with
      | none => rfl
      | some t =>
        have : j + getImportMemCount m ≠ k := by
          rintro rfl; simp [hj] at ht0
        simp [this]

private theorem mems_eq_map (m : Module) (inst : Instance) :
    moduleInstBuildMems m inst = m.mems.mapIdx fun j mt =>
      moduleInstBuildMem m inst (j + getImportMemCount m) (moduleInstMemBaseFunc mt) := by
  change m.data.foldl (memsStep m) (moduleInstMemBase m.mems) = _
  rw [foldl_mapIdx_comm _ _ _ (memsStep_eq m)]
  unfold moduleInstMemBase
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_mapIdx, List.getElem?_map, Option.map_map]
  rfl

@[rocq_alias iriswasm.module_inst_build_mems_lookup]
theorem module_inst_build_mems_lookup (m : Module) (i : Instance) (n : Nat) (mmem : MemoryType)
    (x : Memory) :
    (moduleInstBuildMems m i)[n]? = some x → m.mems[n]? = some mmem →
    x = moduleInstBuildMem m i (n + getImportMemCount m) (moduleInstMemBaseFunc mmem) := by
  intro hx hm
  simp [mems_eq_map, hm] at hx
  exact hx.symm

@[rocq_alias iriswasm.module_inst_build_mems_is_Some]
theorem module_inst_build_mems_is_Some (m : Module) (i : Instance) (n : Nat) :
    ((moduleInstBuildMems m i)[n]?).isSome = true ↔ (m.mems[n]?).isSome = true := by
  simp [mems_eq_map]

#rocq_ignore iriswasm.module_inst_build_mem_max_opt "data initialization preserves the whole memory type"
theorem module_inst_build_mem_type (m : Module) (i : Instance) (n : Nat) (mm : Memory) :
    (moduleInstBuildMem m i n mm).type = mm.type := by
  change (m.data.foldl (memStep m n) mm).type = _
  refine fold_left_preserve (fun t : Memory => t.type = mm.type) _ _ _ rfl ?_
  intro t d ht
  rcases d with ⟨⟨k⟩, off, init⟩
  simp only [memStep]
  split <;> try exact ht
  split <;> try exact ht
  split <;> exact ht

#rocq_ignore iriswasm.module_inst_mem_base_func_max_opt "the allocated memory stores the complete descriptor"

#rocq_ignore iriswasm.module_import_init_mem "active data resolves the store address and both widths"
def moduleImportInitMem (m : Module) (inst : Instance) (n : Nat) (ms : Memory) : Memory :=
  m.data.foldl (fun ms d =>
    let imc := getImportMemCount m
    match d.data with
    | .memidx k =>
      if k < imc then
        match inst.memory[k]? with
        | some addr =>
          if n = addr then
            match literalDataOffset d.offset with
            | some off => memInitReplaceSingle ms off d.init
            | none => ms
          else ms
        | none => ms
      else ms) ms

@[rocq_alias iriswasm.mem_init_replace_single_preserve_len]
theorem mem_init_replace_single_preserve_len (mem : Memory) (offset : Nat) (bs : List Byte) :
    (memInitReplaceSingle mem offset bs).data.data.length = mem.data.data.length := by
  simp only [memInitReplaceSingle, MemoryList.data_splice, lengthMem_eq_data_length,
    List.length_take, List.length_append, List.length_drop]
  omega

@[rocq_alias iriswasm.module_import_init_mem_lookup_length]
theorem module_import_init_mem_lookup_length (m : Module) (i : Instance) (n : Nat)
    (mem : Memory) :
    (moduleImportInitMem m i n mem).data.data.length = mem.data.data.length := by
  unfold moduleImportInitMem
  refine fold_left_preserve (fun t : Memory => t.data.data.length = mem.data.data.length) _ _ _
    rfl ?_
  intro t d ht
  rcases d with ⟨⟨k⟩, off, init⟩
  dsimp only
  split <;> try exact ht
  split <;> try exact ht
  split <;> try exact ht
  split
  · exact (mem_init_replace_single_preserve_len _ _ _).trans ht
  · exact ht

private theorem importInitMems_type (m : Module) (i : Instance) (wms : NatMap Memory) (n : Nat) :
    (get? (moduleImportInitMems m i wms) n).map Memory.type = (get? wms n).map Memory.type := by
  unfold moduleImportInitMems
  refine fold_left_preserve (fun w : NatMap Memory =>
    (get? w n).map Memory.type = (get? wms n).map Memory.type) _ _ _ rfl ?_
  intro w d hw
  rcases d with ⟨⟨k⟩, off, init⟩
  dsimp only
  rw [← hw]
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  rw [LawfulPartialMap.get?_insert]; split <;> simp_all [memInitReplaceSingle]

private theorem importInitMems_isSome (m : Module) (i : Instance) (wms : NatMap Memory)
    (n : Nat) : (get? (moduleImportInitMems m i wms) n).isSome = (get? wms n).isSome := by
  simpa only [Option.isSome_map] using congrArg Option.isSome (importInitMems_type m i wms n)

@[rocq_alias iriswasm.module_import_init_mems_is_Some]
theorem module_import_init_mems_is_Some (m : Module) (i : Instance) (wts : NatMap Memory)
    (n : Nat) :
    (get? wts n).isSome = true ↔ (get? (moduleImportInitMems m i wts) n).isSome = true := by
  rw [importInitMems_isSome]

@[rocq_alias iriswasm.module_inst_global_init_length]
theorem module_inst_global_init_length (mglobs : List Global) (vs : List Value) :
    (moduleInstGlobalInit mglobs vs).length = mglobs.length := by
  induction mglobs generalizing vs with
  | nil => rfl
  | cons g gs ih => cases vs <;> simp [moduleInstGlobalInit, ih]

@[rocq_alias iriswasm.module_import_init_tabs_dom]
theorem module_import_init_tabs_dom (m : Module) (i : Instance) (wts : NatMap Tableinst) :
    ∀ k, PartialMap.dom (moduleImportInitTabs m i wts) k ↔ PartialMap.dom wts k := by
  intro k
  simp only [PartialMap.dom, importInitTabs_isSome]

@[rocq_alias iriswasm.module_import_init_mems_dom]
theorem module_import_init_mems_dom (m : Module) (i : Instance) (wts : NatMap Memory) :
    ∀ k, PartialMap.dom (moduleImportInitMems m i wts) k ↔ PartialMap.dom wts k := by
  intro k
  simp only [PartialMap.dom, importInitMems_isSome]

/-! ### Host functions -/

@[rocq_alias iriswasm.map_host_func]
def mapHostFunc (v : FunctionClosure) : Option (FunctionType × Hostfuncidx) :=
  match v with
  | .funcHost tf h => some (tf, h)
  | _ => none

@[rocq_alias iriswasm.filter_Some]
def FilterSome (a : Option (FunctionType × Hostfuncidx)) : Prop :=
  match a with
  | none => False
  | some _ => True

@[rocq_alias iriswasm.filter_Some_dec]
instance filterSomeDec (x : Option (FunctionType × Hostfuncidx)) : Decidable (FilterSome x) :=
  match x with
  | none => isFalse id
  | some _ => isTrue trivial

@[rocq_alias iriswasm.host_funcs]
def hostFuncs (wfs : NatMap FunctionClosure) : List (Option (FunctionType × Hostfuncidx)) :=
  (((toList wfs).map Prod.snd).map mapHostFunc).filter (decide <| FilterSome ·)

/-! ### The instance relation for a freshly allocated module -/

instance moduleInstResourcesFuncInvs_persistent (mfuncs : List ModuleFunc) (inst : Instance)
    (inst_f : List Funcaddr) :
    Persistent (moduleInstResourcesFuncInvs (GF := GF) mfuncs inst inst_f) := by
  unfold moduleInstResourcesFuncInvs; infer_instance

instance moduleInstResourcesTabInvs_persistent (mtabs : List Tableinst) (inst_t : List Tableaddr) :
    Persistent (moduleInstResourcesTabInvs (GF := GF) mtabs inst_t) := by
  unfold moduleInstResourcesTabInvs; infer_instance

instance moduleInstResourcesMemInvs_persistent (mmems : List Memory) (inst_m : List Memaddr) :
    Persistent (moduleInstResourcesMemInvs (GF := GF) mmems inst_m) := by
  unfold moduleInstResourcesMemInvs; infer_instance

/-- The typing context of `interp_instance_alloc`. -/
private abbrev allocCtx (m : Module) (t_imps : List ExternT) (fts : List FunctionType)
    (gts : List GlobalType) : TContext :=
  { typesT := m.types, funcT := extTFuncs t_imps ++ fts, global := extTGlobs t_imps ++ gts
    table := extTTabs t_imps ++ m.tables.map (·.type), memory := extTMems t_imps ++ m.mems
    local_ := [], label := [], return_ := none }

private theorem body_parts {m : Module} {t_imps t_exps : List ExternT} {fts : List FunctionType}
    {gts : List GlobalType} (h : ModuleTypingBody m t_imps t_exps fts gts) :
    Wasm.List.Forall₂ (ModuleFuncTyping (allocCtx m t_imps fts gts)) m.funcs fts ∧
    ModuleGlobalsTyping (globalInitContext t_imps) m.globals gts ∧
    Wasm.List.Forall₂ (fun (imp : ModuleImport) e =>
      moduleImportTyping (allocCtx m t_imps fts gts) imp.desc e = true) m.imports t_imps := by
  rcases m with ⟨tfs, fs, ts, ms, gs, els, ds, iOpt, imps, exps⟩
  exact ⟨h.1, h.2.2.2.1, h.2.2.2.2.2.2.2.1⟩

/-- Every function address of the new instance satisfies the pre-instance closure relation at
its declared type. -/
private theorem func_entry (m : Module) (t_imps : List ExternT) (v_imps : List ModuleExport)
    (wfs : NatMap FunctionClosure) (wts : NatMap Tableinst) (wms : NatMap Memory)
    (wgs : NatMap Global) (inst : Instance) (fts : List FunctionType) (gts : List GlobalType)
    (hl : List (Hostfuncidx × FunctionType)) (rest : List Funcaddr)
    (hfuncs : Wasm.List.Forall₂ (ModuleFuncTyping (allocCtx m t_imps fts gts)) m.funcs fts)
    (hcnt : getImportFuncCount m = (extTFuncs t_imps).length) (htypes : inst.types = m.types)
    (hpre : extFuncAddrs (v_imps.map (·.desc)) ++ rest = inst.funcs)
    (hlen : (extFuncAddrs (v_imps.map (·.desc))).length = (extTFuncs t_imps).length)
    (hdisj : ∀ (i fa : Nat), (inst.funcs.drop (getImportFuncCount m))[i]? = some fa →
      get? wfs fa = none)
    (hftc : funcTypecheck v_imps t_imps wfs) (httc : tabTypecheck v_imps t_imps wts)
    (hmtc : memTypecheck v_imps t_imps wms) (hgtc : globTypecheck v_imps t_imps wgs)
    (idx f : Nat) (ft : FunctionType) (hf : inst.funcs[idx]? = some f)
    (hft : (extTFuncs t_imps ++ fts)[idx]? = some ft) :
    ⊢ (□ [∗map] _k ↦ cl ∈ wfs, interpClosure (GF := GF) hl (clType cl) cl) -∗
      □ importFuncNainv wfs -∗
      □ moduleInstResourcesFuncInvs m.funcs inst (inst.funcs.drop (getImportFuncCount m)) -∗
      interpFunction ft (interpClosurePre (allocCtx m t_imps fts gts) wfs inst hl) f := by
  have hdrop : inst.funcs.drop (getImportFuncCount m) = rest := by
    rw [hcnt, ← hpre, ← hlen]; simp
  rw [← hpre] at hf
  unfold interpFunction
  by_cases hi : idx < (extTFuncs t_imps).length
  · -- an imported function: its closure is valid by assumption
    rw [List.getElem?_append_left hi] at hft
    rw [List.getElem?_append_left (by omega)] at hf
    obtain ⟨k', ht, fm, hv, hd⟩ :=
      import_funcs_lookup t_imps v_imps idx ft f wfs wts wms wgs hft hf hftc httc hmtc hgtc
    obtain ⟨b, hb, hR⟩ := forall2_lookup_l hftc hv
    rw [ht] at hb; cases hb
    simp only [hd] at hR
    obtain ⟨cl, hcl, heq⟩ := hR
    cases heq
    unfold importFuncNainv
    iintro #Hval #Hfinv #-
    iexists cl
    isplitr
    · iapply BigSepM.bigSepM_lookup hcl $$ Hfinv
    ihave Hc := BigSepM.bigSepM_lookup hcl $$ Hval
    rcases cl with ⟨j, τ', tLocs, bEs⟩ | ⟨tf, h⟩
    · simp only [interpClosurePre, hcl]
      isplitr
      · ipureintro; trivial
      iexact Hc
    · simp only [interpClosurePre]; iexact Hc
  · -- a function declared by the module: syntactically well-typed
    rw [List.getElem?_append_right (by omega)] at hft
    rw [List.getElem?_append_right (by omega), hlen] at hf
    have hnone := hdisj _ _ (hdrop ▸ hf)
    obtain ⟨mf, hmf, htyp⟩ := forall2_lookup_r hfuncs hft
    rcases mf with ⟨⟨ti⟩, locs, body⟩
    rcases ft with ⟨tn, tm⟩
    obtain ⟨hdec, hbe⟩ := htyp
    change m.types[ti]? = some (.tf tn tm) at hdec
    have hty : inst.types.getD ti (.tf [] []) = .tf tn tm := by
      simp [htypes, List.getD_eq_getElem?_getD, hdec]
    rw [hdrop]
    unfold moduleInstResourcesFuncInvs
    iintro #- #- #Hfr
    ihave Hi := BigSepL2.bigSepL2_lookup hmf hf $$ Hfr
    iexists (.funcNative inst (inst.types.getD ti (.tf [] [])) locs body)
    isplitr
    · iexact Hi
    simp only [interpClosurePre, hnone]
    ipureintro
    refine ⟨trivial, hty.symm, ?_⟩
    simpa [updLocalLabelReturn] using hbe

private theorem funcs_part (m : Module) (t_imps : List ExternT) (v_imps : List ModuleExport)
    (wfs : NatMap FunctionClosure) (wts : NatMap Tableinst) (wms : NatMap Memory)
    (wgs : NatMap Global) (inst : Instance) (fts : List FunctionType) (gts : List GlobalType)
    (hl : List (Hostfuncidx × FunctionType)) (rest : List Funcaddr)
    (hfuncs : Wasm.List.Forall₂ (ModuleFuncTyping (allocCtx m t_imps fts gts)) m.funcs fts)
    (hcnt : getImportFuncCount m = (extTFuncs t_imps).length) (htypes : inst.types = m.types)
    (hpre : extFuncAddrs (v_imps.map (·.desc)) ++ rest = inst.funcs)
    (hlen : (extFuncAddrs (v_imps.map (·.desc))).length = (extTFuncs t_imps).length)
    (hdisj : ∀ (i fa : Nat), (inst.funcs.drop (getImportFuncCount m))[i]? = some fa →
      get? wfs fa = none)
    (hftc : funcTypecheck v_imps t_imps wfs) (httc : tabTypecheck v_imps t_imps wts)
    (hmtc : memTypecheck v_imps t_imps wms) (hgtc : globTypecheck v_imps t_imps wgs) :
    ⊢ (□ [∗map] _k ↦ cl ∈ wfs, interpClosure (GF := GF) hl (clType cl) cl) -∗
      □ importFuncNainv wfs -∗
      □ moduleInstResourcesFuncInvs m.funcs inst (inst.funcs.drop (getImportFuncCount m)) -∗
      [∗list] kf;tf ∈ inst.funcs;(extTFuncs t_imps ++ fts),
        interpFunction tf (interpClosurePre (allocCtx m t_imps fts gts) wfs inst hl) kf := by
  iintro #Hval #Hfinv #Hfr
  ihave %Hlenfr : ⌜m.funcs.length = (inst.funcs.drop (getImportFuncCount m)).length⌝ $$ []
  · unfold moduleInstResourcesFuncInvs; iapply BigSepL2.bigSepL2_length $$ Hfr
  have hflen := Wasm.List.Forall₂.length_eq hfuncs
  iapply (BigSepL2.bigSepL2_forall fun _ _ _ => inferInstance).2
  isplit
  · ipureintro
    rw [← hpre] at Hlenfr ⊢
    simp only [List.length_append, List.length_drop] at Hlenfr ⊢
    omega
  iintro %k %f %ft %hf %hft
  iapply func_entry m t_imps v_imps wfs wts wms wgs inst fts gts hl rest hfuncs hcnt htypes hpre
    hlen hdisj hftc httc hmtc hgtc k f ft hf hft $$ Hval Hfinv Hfr

private instance interpTableEntry_persistent' (τf : FunctionType) (n k : Nat)
    (icl : Nat → FunctionType → FunctionClosure → IProp GF)
    [∀ n τf cl, Persistent (icl n τf cl)] : Persistent (interpTableEntry τf icl n k) := by
  unfold interpTableEntry
  refine @exists_persistent _ _ _ _ fun fe => ?_
  cases fe <;> dsimp only <;> infer_instance

private instance interpTable_persistent (sz n : Nat)
    (icl : Nat → FunctionType → FunctionClosure → IProp GF)
    [∀ n τf cl, Persistent (icl n τf cl)] : Persistent (interpTable sz icl n) := by
  unfold interpTable; infer_instance

private theorem interpInstance'_intro (τctx : TContext)
    (icl icl' : Nat → FunctionType → FunctionClosure → IProp GF) (i : Instance) :
    iprop(⌜i.types = τctx.typesT⌝ ∗
      ([∗list] kf;tf ∈ i.funcs;τctx.funcT, interpFunction tf icl kf) ∗
      ([∗list] a;tt ∈ i.tab;τctx.table, interpTableAt tt icl' a) ∗
      ([∗list] a;mt ∈ i.memory;τctx.memory, interpMemLimit a mt.limits.max ∗ interpMem mt.address a) ∗
      ([∗list] kg;gt ∈ i.globs;τctx.global, interpGlobal gt kg)) ⊢
    interpInstance' τctx icl icl' i := .rfl

/-- The table conjunct of the pre-instance relation. -/
private theorem tabs_part (m : Module) (t_imps : List ExternT) (v_imps : List ModuleExport)
    (wfs : NatMap FunctionClosure) (wts : NatMap Tableinst) (wms : NatMap Memory)
    (wgs : NatMap Global) (inst : Instance) (fts : List FunctionType) (gts : List GlobalType)
    (hl : List (Hostfuncidx × FunctionType)) (restF restT : List Nat)
    (hfuncs : Wasm.List.Forall₂ (ModuleFuncTyping (allocCtx m t_imps fts gts)) m.funcs fts)
    (hcF : getImportFuncCount m = (extTFuncs t_imps).length)
    (hcT : getImportTableCount m = (extTTabs t_imps).length) (htypes : inst.types = m.types)
    (hpreF : extFuncAddrs (v_imps.map (·.desc)) ++ restF = inst.funcs)
    (hlenF : (extFuncAddrs (v_imps.map (·.desc))).length = (extTFuncs t_imps).length)
    (hpreT : extTabAddrs (v_imps.map (·.desc)) ++ restT = inst.tab)
    (hlenT : (extTabAddrs (v_imps.map (·.desc))).length = (extTTabs t_imps).length)
    (hdisj : ∀ (i fa : Nat), (inst.funcs.drop (getImportFuncCount m))[i]? = some fa →
      get? wfs fa = none)
    (hftc : funcTypecheck v_imps t_imps wfs)
    (httc : tabTypecheck v_imps t_imps (moduleImportInitTabs m inst wts))
    (hmtc : memTypecheck v_imps t_imps wms) (hgtc : globTypecheck v_imps t_imps wgs) :
    ⊢ (□ [∗map] _k ↦ cl ∈ wfs, interpClosure (GF := GF) hl (clType cl) cl) -∗
      (□ [∗map] n ↦ t ∈ wts,
        interpTable (tabSize t) (interpClosurePre (allocCtx m t_imps fts gts) wfs inst hl) n) -∗
      □ importFuncNainv wfs -∗
      □ importTabNainv (moduleImportInitTabs m inst wts) -∗
      □ moduleInstResourcesFuncInvs m.funcs inst (inst.funcs.drop (getImportFuncCount m)) -∗
      □ moduleInstResourcesTabInvs (moduleInstBuildTables m inst)
        (inst.tab.drop (getImportTableCount m)) -∗
      [∗list] a;tt ∈ inst.tab;(allocCtx m t_imps fts gts).table,
        interpTableAt tt (interpClosurePre (allocCtx m t_imps fts gts) wfs inst hl) a := by
  have hdropT : inst.tab.drop (getImportTableCount m) = restT := by
    rw [hcT, ← hpreT, ← hlenT]; simp
  rw [hdropT, ← hpreT]
  unfold moduleInstResourcesTabInvs importTabNainv
  iintro #Hval #Htabs #Hfinv #Htinv #Hfr #Htr
  ihave %Hlen := BigSepL2.bigSepL2_length $$ Htr
  rw [module_inst_build_tables_length] at Hlen
  iapply BigSepL2.bigSepL2_app_wand
  · iapply (BigSepL2.bigSepL2_forall fun _ _ _ => inferInstance).2
    isplit
    · ipureintro; exact hlenT
    iintro %j %a %tt %ha %htt
    unfold interpTableAt
    obtain ⟨k', ht, fm, hv, hd⟩ :=
      import_tabs_lookup t_imps v_imps j tt a wfs _ wms wgs htt ha hftc httc hmtc hgtc
    obtain ⟨b, hb, hR⟩ := forall2_lookup_l httc hv
    rw [ht] at hb; cases hb
    simp only [hd] at hR
    obtain ⟨tab, tt', hwts, heq, hty⟩ := hR
    cases heq
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp
      (module_import_init_tabs_Some m inst wts a tab hwts)
    have htab := module_import_init_tabs_lookup m inst wts a x tab hx hwts
    ihave Hk := BigSepM.bigSepM_lookup hwts $$ Htinv
    icases Hk with ⟨Hsize, Hlim, -⟩
    ihave Hv := BigSepM.bigSepM_lookup hx $$ Htabs
    iexists tabSize tab, tab.maxOpt
    isplitr
    · ipureintro
      simp only [tabTyping, Limits.matches, Bool.and_eq_true] at hty
      exact hty.2
    isplitr
    · iexact Hlim
    isplitr
    · iexact Hsize
    have hsz : tabSize tab = tabSize x := by
      rw [htab]
      simpa only [tabSize, Tableinst.length_data] using module_import_init_tab_lookup_length m inst a x
    rw [hsz]
    iexact Hv
  · iapply (BigSepL2.bigSepL2_forall fun _ _ _ => inferInstance).2
    isplit
    · ipureintro; simpa only [List.length_map] using Hlen.symm
    iintro %j %a %tt %ha %htt
    simp only [List.getElem?_map, Option.map_eq_some_iff] at htt
    obtain ⟨mt, hmt, rfl⟩ := htt
    unfold interpTableAt
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp
      (module_inst_build_tables_lookup_is_Some m inst j mt hmt)
    have hxeq := module_inst_build_tables_lookup m inst j mt x hmt hx
    ihave Hk := BigSepL2.bigSepL2_lookup hx ha $$ Htr
    icases Hk with ⟨Hsize, Hlim, Hel⟩
    -- the instance's functions line up with the context's function types
    ihave %HlenFr : ⌜m.funcs.length = (inst.funcs.drop (getImportFuncCount m)).length⌝ $$ []
    · unfold moduleInstResourcesFuncInvs; iapply BigSepL2.bigSepL2_length $$ Hfr
    have hflen : inst.funcs.length = (extTFuncs t_imps ++ fts).length := by
      have := Wasm.List.Forall₂.length_eq hfuncs
      rw [← hpreF] at HlenFr ⊢
      simp only [List.length_append, List.length_drop] at HlenFr ⊢
      omega
    iexists tabSize x, x.maxOpt
    isplitr
    · ipureintro
      rw [hxeq, module_inst_built_table_max_opt_eq]
      exact Limits.maxMatches_self _
    isplitr
    · iexact Hlim
    isplitr
    · iexact Hsize
    unfold interpTable
    iapply BigSepL.bigSepL_forall_elim
    iintro %k %z %hk
    obtain ⟨fe, hfe⟩ : ∃ fe, x.data[k]? = some fe := by
      have := (List.getElem?_eq_some_iff.mp hk).1
      rw [List.length_replicate, tabSize, ← Tableinst.length_data] at this
      exact ⟨_, List.getElem?_eq_getElem this⟩
    ihave Hinv := BigSepL.bigSepL_lookup hfe $$ Hel
    unfold interpTableEntry
    rw [hxeq] at hfe
    rcases module_inst_build_table_lookup_Some m inst _ mt k fe hfe with
      rfl | ⟨_, _, _, idx, f, hf, rfl, _⟩
    · iexists (.tf [] []), none
      isplitr
      · iexact Hinv
      ipureintro; trivial
    obtain ⟨ft, hft⟩ : ∃ ft, (extTFuncs t_imps ++ fts)[idx]? = some ft := by
      have := (List.getElem?_eq_some_iff.mp hf).1
      exact ⟨_, List.getElem?_eq_getElem (hflen ▸ this)⟩
    iexists ft, some f
    isplitr
    · iexact Hinv
    iapply func_entry m t_imps v_imps wfs (moduleImportInitTabs m inst wts) wms wgs inst fts gts hl
      restF hfuncs hcF htypes hpreF hlenF hdisj hftc httc hmtc hgtc idx f ft hf hft
      $$ Hval Hfinv Hfr

/-- The memory conjunct of the pre-instance relation. -/
private theorem mems_part (m : Module) (t_imps : List ExternT) (v_imps : List ModuleExport)
    (wfs : NatMap FunctionClosure) (wts : NatMap Tableinst) (wms : NatMap Memory)
    (wgs : NatMap Global) (inst : Instance) (fts : List FunctionType) (gts : List GlobalType)
    (restM : List Nat) (hcM : getImportMemCount m = (extTMems t_imps).length)
    (hpreM : extMemAddrs (v_imps.map (·.desc)) ++ restM = inst.memory)
    (hlenM : (extMemAddrs (v_imps.map (·.desc))).length = (extTMems t_imps).length)
    (hftc : funcTypecheck v_imps t_imps wfs) (httc : tabTypecheck v_imps t_imps wts)
    (hmtc : memTypecheck v_imps t_imps (moduleImportInitMems m inst wms))
    (hgtc : globTypecheck v_imps t_imps wgs) :
    ⊢ (□ [∗map] n ↦ mem ∈ wms, interpMem (GF := GF) mem.type.address n) -∗
      □ importMemNainv (moduleImportInitMems m inst wms) -∗
      □ moduleInstResourcesMemInvs (moduleInstBuildMems m inst)
        (inst.memory.drop (getImportMemCount m)) -∗
      [∗list] a;mt ∈ inst.memory;(allocCtx m t_imps fts gts).memory,
        interpMemLimit a mt.limits.max ∗ interpMem mt.address a := by
  have hdrop : inst.memory.drop (getImportMemCount m) = restM := by
    rw [hcM, ← hpreM, ← hlenM]; simp
  rw [hdrop, ← hpreM]
  unfold moduleInstResourcesMemInvs importMemNainv
  iintro #Hmems #Hminv #Hmr
  ihave %Hlen := BigSepL2.bigSepL2_length $$ Hmr
  rw [module_inst_build_mems_length] at Hlen
  iapply BigSepL2.bigSepL2_app_wand
  · iapply (BigSepL2.bigSepL2_forall fun _ _ _ => inferInstance).2
    isplit
    · ipureintro; exact hlenM
    iintro %k %a %mt %ha %hmt
    obtain ⟨k', ht, fm, hv, hd⟩ := import_mems_lookup t_imps v_imps k mt a wfs wts _ wgs
      hmt ha hftc httc hmtc hgtc
    obtain ⟨b, hb, hR⟩ := forall2_lookup_l hmtc hv
    rw [ht] at hb; cases hb
    simp only [hd] at hR
    obtain ⟨mem, mt', hmem, heq, hty⟩ := hR
    cases heq
    simp only [memTyping, Limits.matches, Bool.and_eq_true, beq_iff_eq] at hty
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp
      ((module_import_init_mems_is_Some m inst wms a).2 (by rw [hmem]; rfl))
    ihave Hk := BigSepM.bigSepM_lookup hmem $$ Hminv
    icases Hk with ⟨-, Hlim⟩
    isplitr
    · iexists mem.type.limits.max
      isplitr
      · ipureintro; exact hty.2.2
      iexact Hlim
    have htype := importInitMems_type m inst wms a
    simp only [hmem, hx, Option.map_some, Option.some.injEq] at htype
    rw [← hty.1, htype]
    iapply BigSepM.bigSepM_lookup hx $$ Hmems
  · iapply (BigSepL2.bigSepL2_forall fun _ _ _ => inferInstance).2
    isplit
    · ipureintro; exact Hlen.symm
    iintro %k %a %mt %ha %hmt
    obtain ⟨mem, hm⟩ := Option.isSome_iff_exists.mp
      ((module_inst_build_mems_is_Some m inst k).2 (by rw [hmt]; rfl))
    have htype : mem.type = mt := by
      rw [module_inst_build_mems_lookup m inst k mt mem hm hmt, module_inst_build_mem_type]
      rfl
    ihave Hk := BigSepL2.bigSepL2_lookup hm ha $$ Hmr
    icases Hk with ⟨Hinv, Hlim⟩
    isplitr
    · iexists mem.type.limits.max
      isplitr
      · ipureintro; rw [htype]; exact Limits.maxMatches_self _
      iexact Hlim
    rw [← htype]; iexact Hinv

/-- The globals conjunct of the pre-instance relation. -/
private theorem globs_part (m : Module) (t_imps : List ExternT) (v_imps : List ModuleExport)
    (wfs : NatMap FunctionClosure) (wts : NatMap Tableinst) (wms : NatMap Memory)
    (wgs : NatMap Global) (inst : Instance) (fts : List FunctionType) (gts : List GlobalType)
    (g_inits : List Value) (restG : List Nat)
    (hglobals : ModuleGlobalsTyping (globalInitContext t_imps) m.globals gts)
    (hcG : getImportGlobalCount m = (extTGlobs t_imps).length)
    (hpreG : extGlobAddrs (v_imps.map (·.desc)) ++ restG = inst.globs)
    (hlenG : (extGlobAddrs (v_imps.map (·.desc))).length = (extTGlobs t_imps).length)
    (hftc : funcTypecheck v_imps t_imps wfs) (httc : tabTypecheck v_imps t_imps wts)
    (hmtc : memTypecheck v_imps t_imps wms) (hgtc : globTypecheck v_imps t_imps wgs) :
    ⊢ □ importGlobNainv (GF := GF) wgs -∗
      □ moduleInstResourcesGlobInvs
        (moduleInstGlobalInit (moduleInstBuildGlobals m.globals) g_inits)
        (inst.globs.drop (getImportGlobalCount m)) gts -∗
      [∗list] kg;gt ∈ inst.globs;(allocCtx m t_imps fts gts).global, interpGlobal gt kg := by
  have hdrop : inst.globs.drop (getImportGlobalCount m) = restG := by
    rw [hcG, ← hpreG, ← hlenG]; simp
  have hglen : gts.length = m.globals.length := by simp [hglobals.types_eq]
  rw [hdrop, ← hpreG]
  unfold moduleInstResourcesGlobInvs importGlobNainv
  iintro #Hginv #Hgr
  ihave %Hlen := BigSepL2.bigSepL2_length $$ Hgr
  simp only [module_inst_global_init_length, moduleInstBuildGlobals, List.length_map] at Hlen
  iapply BigSepL2.bigSepL2_app_wand
  · -- imported globals: typed by the import check
    iapply (BigSepL2.bigSepL2_forall fun _ _ _ => inferInstance).2
    isplit
    · ipureintro; exact hlenG
    iintro %k %a %gt %ha %hgt
    obtain ⟨k', ht, fm, hv, hd⟩ :=
      import_globs_lookup t_imps v_imps k gt a wfs wts wms wgs hgt ha hftc httc hmtc hgtc
    obtain ⟨b, hb, hR⟩ := forall2_lookup_l hgtc hv
    rw [ht] at hb; cases hb
    simp only [hd] at hR
    obtain ⟨⟨mu, v⟩, gt0, hg, heq, hag⟩ := hR
    cases heq
    rcases gt with ⟨gm, gtt⟩
    simp only [globalAgree, Bool.and_eq_true, beq_iff_eq] at hag
    obtain ⟨rfl, rfl⟩ := hag
    ihave Hi := BigSepM.bigSepM_lookup hg $$ Hginv
    unfold interpGlobal
    cases gm
    · dsimp only
      iexists interpValue
      isplitr
      · imodintro; iintro %w H; iexact H
      iexact Hi
    · iexact Hi
  · -- declared globals: their invariants were just allocated
    iapply (BigSepL2.bigSepL2_forall fun _ _ _ => inferInstance).2
    isplit
    · ipureintro; omega
    iintro %k %a %gt %ha %hgt
    obtain ⟨g, hg⟩ : ∃ g,
        (moduleInstGlobalInit (moduleInstBuildGlobals m.globals) g_inits)[k]? = some g := by
      have := (List.getElem?_eq_some_iff.mp ha).1
      refine ⟨_, List.getElem?_eq_getElem ?_⟩
      simp only [module_inst_global_init_length, moduleInstBuildGlobals, List.length_map]
      omega
    ihave Hk := BigSepL2.bigSepL2_lookup hg ha $$ Hgr
    icases Hk with ⟨%τg, %hτ, Hk⟩
    rw [hgt] at hτ; cases hτ
    unfold interpGlobal
    rcases gt with ⟨gm, gtt⟩
    cases gm
    · dsimp only
      iexists interpValue
      isplitr
      · imodintro; iintro %w H; iexact H
      iexact Hk
    · iexact Hk

private theorem res_disj (v_imps : List ModuleExport) (t_imps : List ExternT)
    (wfs : NatMap FunctionClosure) (wts : NatMap Tableinst) (wms : NatMap Memory)
    (wgs : NatMap Global) (m : Module) (inst : Instance) (tab_inits : List Tableinst)
    (mem_inits : List Memory) (glob_inits : List Global) :
    ⊢ importResourcesWasmTypecheck (GF := GF) v_imps t_imps wfs wts wms wgs -∗
      moduleInstResourcesWasm m inst tab_inits mem_inits glob_inits -∗
      ⌜∀ (i fa : Nat), (inst.funcs.drop (getImportFuncCount m))[i]? = some fa →
        get? wfs fa = none⌝ := by
  unfold importResourcesWasmTypecheck moduleInstResourcesWasm
  iintro ⟨Hf, -⟩ ⟨Hm, -⟩
  iapply module_res_imports_disj v_imps t_imps wfs m inst $$ Hf Hm

#rocq_ignore iriswasm.interp_instance_alloc "imported and newly allocated memory invariants are width-indexed"
/-- Since host functions can only be imported, the host function is already accounted for and
determined by the validity of imports; the list `hl` the imports are valid against suffices to
determine the validity of the instance. -/
theorem interp_instance_alloc (hl : List (Hostfuncidx × FunctionType)) (E : CoPset) (m : Module)
    (t_imps t_exps : List ExternT) (v_imps : List ModuleExport) (wfs : NatMap FunctionClosure)
    (wts : NatMap Tableinst) (wms : NatMap Memory) (wgs : NatMap Global) (inst : Instance)
    (fts : List FunctionType) (gts : List GlobalType) (g_inits : List Value) :
    let C : TContext :=
      { typesT := m.types, funcT := extTFuncs t_imps ++ fts, global := extTGlobs t_imps ++ gts
        table := extTTabs t_imps ++ m.tables.map (·.type), memory := extTMems t_imps ++ m.mems
        local_ := [], label := [], return_ := none }
    let tab_inits := moduleInstBuildTables m inst
    let wts' := moduleImportInitTabs m inst wts
    let mem_inits := moduleInstBuildMems m inst
    let wms' := moduleImportInitMems m inst wms
    let glob_inits := moduleInstGlobalInit (moduleInstBuildGlobals m.globals) g_inits
    ModuleTypingBody m t_imps t_exps fts gts →
    (inst.types = m.types ∧
      let v_imp_descs := v_imps.map (·.desc)
      extFuncAddrs v_imp_descs <+: inst.funcs ∧
        extTabAddrs v_imp_descs <+: inst.tab ∧
        extMemAddrs v_imp_descs <+: inst.memory ∧
        extGlobAddrs v_imp_descs <+: inst.globs) →
    g_inits.map typeof = m.globals.map (·.type.t) →
    ⊢ ([∗map] _k ↦ cl ∈ wfs, interpClosure (GF := GF) hl (clType cl) cl) -∗
      ([∗map] n ↦ t ∈ wts, interpTable (tabSize t) (interpClosurePre C wfs inst hl) n) -∗
      ([∗map] n ↦ mem ∈ wms, interpMem mem.type.address n) -∗
      importResourcesWasmTypecheck v_imps t_imps wfs wts' wms' wgs -∗
      moduleInstResourcesWasm m inst tab_inits mem_inits glob_inits ={E}=∗
      interpInstance C hl inst ∗
        moduleInstResourcesWasmInvs m inst gts tab_inits mem_inits glob_inits ∗
        importResourcesWasmTypecheckInvs v_imps t_imps wfs wts' wms' wgs := by
  intro C tab_inits wts' mem_inits wms' glob_inits Hmod Hinst Hinit
  obtain ⟨Htypes, ⟨restF, hpreF⟩, ⟨restT, hpreT⟩, ⟨restM, hpreM⟩, ⟨restG, hpreG⟩⟩ := Hinst
  obtain ⟨hfuncs, hglobals, himps⟩ := body_parts Hmod
  obtain ⟨hcF, hcT, hcM, hcG⟩ := get_import_count_length m t_imps _ himps
  iintro #Hval #Htabs #Hmems Hir Hmr
  ihave %Hdisj := res_disj v_imps t_imps wfs wts' wms' wgs m inst _ _ _ $$ Hir Hmr
  ihave %⟨hlF, hlT, hlM, hlG⟩ :=
    import_resources_wasm_typecheck_lengths v_imps t_imps wfs wts' wms' wgs $$ Hir
  unfold moduleInstResourcesWasm
  icases Hmr with ⟨Hfr, Htr, Hmr, Hgr⟩
  imod import_resources_wasm_typecheck_alloc E v_imps t_imps wfs wts' wms' wgs $$ Hir with #Hir
  imod module_inst_resources_func_invs_alloc E _ _ _ $$ Hfr with #Hfr
  imod module_inst_resources_tab_invs_alloc E _ _ $$ Htr with #Htr
  imod module_inst_resources_mem_invs_alloc E _ _ $$ Hmr with #Hmr
  imod module_inst_resources_glob_invs_alloc E glob_inits m.globals g_inits _ t_imps gts hglobals
    Hinit rfl $$ Hgr with #Hgr
  unfold importResourcesWasmTypecheckInvs importFuncWasmCheckInvs importTabWasmCheckInvs
    importMemWasmCheckInvs importGlobWasmCheckInvs
  icases Hir with ⟨⟨#Hfinv, %⟨Hfdom, Hftc⟩⟩, ⟨#Htinv, %⟨Htdom, Httc⟩⟩, ⟨#Hminv, %⟨Hmdom, Hmtc⟩⟩,
    ⟨#Hginv, %⟨Hgdom, Hgtc⟩⟩⟩
  imodintro
  isplitr
  · iapply interp_instance_pre_create C inst wfs hl ⟨rfl, rfl⟩
    unfold interpInstancePre
    iapply interpInstance'_intro
    isplitr
    · ipureintro; exact Htypes
    isplitr
    · iapply funcs_part m t_imps v_imps wfs wts' wms' wgs inst fts gts hl restF hfuncs hcF Htypes
        hpreF hlF Hdisj Hftc Httc Hmtc Hgtc $$ Hval Hfinv Hfr
    isplitr
    · iapply tabs_part m t_imps v_imps wfs wts wms' wgs inst fts gts hl restF restT hfuncs hcF
        hcT Htypes hpreF hlF hpreT hlT Hdisj Hftc Httc Hmtc Hgtc $$ Hval Htabs Hfinv Htinv Hfr Htr
    isplitr
    · iapply mems_part m t_imps v_imps wfs wts' wms wgs inst fts gts restM hcM hpreM hlM Hftc
        Httc Hmtc Hgtc $$ Hmems Hminv Hmr
    iapply globs_part m t_imps v_imps wfs wts' wms' wgs inst fts gts g_inits restG hglobals hcG
      hpreG hlG Hftc Httc Hmtc Hgtc $$ Hginv Hgr
  unfold moduleInstResourcesWasmInvs
  isplitr
  · isplitr; · iexact Hfr
    isplitr; · iexact Htr
    isplitr; · iexact Hmr
    iexact Hgr
  isplitr
  · isplitr; · iexact Hfinv
    ipureintro; exact ⟨Hfdom, Hftc⟩
  isplitr
  · isplitr; · iexact Htinv
    ipureintro; exact ⟨Htdom, Httc⟩
  isplitr
  · isplitr; · iexact Hminv
    ipureintro; exact ⟨Hmdom, Hmtc⟩
  isplitr; · iexact Hginv
  ipureintro; exact ⟨Hgdom, Hgtc⟩

end IrisWasm
