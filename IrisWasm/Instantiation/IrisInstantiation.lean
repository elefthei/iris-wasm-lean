/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Rules.IrisRulesResources
import IrisWasm.Instantiation.InstantiationProperties
import Wasm.TypePreservation
import Wasm.StdppAux

/-! Port of `theories/iris/instantiation/iris_instantiation.v`, lines 1–3716: every definition and
lemma except the final theorem `instantiation_wasm_spec`, which lives in
`IrisWasm/Instantiation/IrisInstantiationSpec.lean` (importing this module).

Coq `gmap N T` is `NatMap T`; `dom m ≡ list_to_set l` is stated pointwise as
`∀ k, PartialMap.dom m k ↔ k ∈ l`; `list_to_map` is `PartialMap.ofList`; Coq `≡` on `iProp` is
`⊣⊢`. -/

namespace IrisWasm

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm
open scoped Iris.Std.PartialMap

/-! ### Constant-expression helpers and bound checks (no ghost state) -/

@[rocq_alias iriswasm.assert_const1]
def assertConst1 (es : Wasm.Expr) : Option Value :=
  match es with
  | [.const v] => some v
  | _ => none

@[rocq_alias iriswasm.assert_const1_i32]
def assertConst1I32 (es : Wasm.Expr) : Option I32 :=
  match es with
  | [.const (.int32 v)] => some v
  | _ => none

@[rocq_alias iriswasm.assert_const1_i32_to_nat]
def assertConst1I32ToNat (es : Wasm.Expr) : Nat :=
  match assertConst1I32 es with
  | some v => natOfInt v
  | none => 0

def assertConst1Address (es : Wasm.Expr) : Option AddressOperand :=
  (assertConst1 es).bind AddressOperand.ofValue?

@[simp] theorem assertConst1Address_value (a : AddressOperand) :
    assertConst1Address [.const a.value] = some a :=
  AddressOperand.ofValue?_value a

def literalDataOffset (es : Wasm.Expr) : Option Nat :=
  (assertConst1Address es).map AddressOperand.unsigned

@[rocq_alias iriswasm.module_elem_bound_check_gmap]
def ModuleElemBoundCheckGmap (wts : NatMap Tableinst) (impDescs : List ModuleExportDesc)
    (m : Module) : Prop :=
  ∀ e ∈ m.elem,
    match e.table with
    | .tableidx n =>
      match assertConst1I32 e.offset with
      | some eoffi =>
        match (extTabs impDescs)[n]? with
        | some (.tableidx k) =>
          match get? wts k with
          | some ti => natOfInt eoffi + e.init.length ≤ ti.entries.size
          | none => False
        | none =>
          match m.tables[n - (extTabs impDescs).length]? with
          | some modtab => natOfInt eoffi + e.init.length ≤ modtab.type.limits.min
          | none => False
      | none => False

#rocq_ignore iriswasm.module_data_bound_check_gmap "active data offsets can have either address type"
def ModuleDataBoundCheckGmap (wms : NatMap Memory) (impDescs : List ModuleExportDesc)
    (m : Module) : Prop :=
  ∀ d ∈ m.data,
    match d.data with
    | .memidx n =>
      match literalDataOffset d.offset with
      | some off =>
        match (extMems impDescs)[n]? with
        | some (.memidx k) =>
          match get? wms k with
          | some mi => off + d.init.length ≤ lengthMem mi
          | none => False
        | none =>
          match m.mems[n - (extMems impDescs).length]? with
          | some modmem => off + d.init.length ≤ pageSize * modmem.limits.min
          | none => False
      | none => False

variable {hlc : HasLC} {GF : BundledGFunctors}

section Iris_instantiation
variable [WasmG hlc GF]

/-! ### Big operators over `list_to_map (zip l1 l2)` -/

@[rocq_alias iriswasm.big_sepL2_big_sepM]
theorem big_sepL2_big_sepM {X Y : Type} {M : Type → Type} [DecidableEq X] [LawfulFiniteMap M X]
    (l1 : List X) (l2 : List Y) (Φ : X → Y → IProp GF) (m : M Y)
    (hnd : l1.Nodup) (hlen : l1.length = l2.length) (hm : m = PartialMap.ofList (l1.zip l2)) :
    ⊢ ([∗map] k ↦ v ∈ m, Φ k v) -∗ [∗list] x;y ∈ l1;l2, Φ x y := by
  subst hm
  have hk : NoDupKeys (l1.zip l2) := by
    unfold NoDupKeys; rwa [List.map_fst_zip (by omega)]
  exact entails_wand ((BigSepM.bigSepM_ofList hk).1.trans
    ((and_intro (pure_intro hlen) .rfl).trans BigSepL2.bigSepL2_alt.2))

@[rocq_alias iriswasm.big_sepM_l2m_zip_f]
theorem big_sepM_l2m_zip_f {X Y Z : Type} {MX MZ : Type → Type} [DecidableEq X] [DecidableEq Z]
    [LawfulFiniteMap MX X] [LawfulFiniteMap MZ Z]
    (l1 : List X) (l2 : List Y) (Φ : Z → Y → IProp GF) (f : X → Z)
    (hlen : l1.length = l2.length) (hnd : l1.Nodup) (hinj : ∀ a b, f a = f b → a = b) :
    ([∗map] k ↦ v ∈ (PartialMap.ofList (l1.zip l2) : MX Y), Φ (f k) v) ⊣⊢
      [∗map] k ↦ v ∈ (PartialMap.ofList ((l1.map f).zip l2) : MZ Y), Φ k v := by
  have hk1 : NoDupKeys (l1.zip l2) := by
    unfold NoDupKeys; rwa [List.map_fst_zip (by omega)]
  have hk2 : NoDupKeys ((l1.map f).zip l2) := by
    unfold NoDupKeys; rw [List.map_fst_zip (by simp; omega)]
    exact List.Pairwise.map f (fun a b h e => h (hinj a b e)) hnd
  refine (BigSepM.bigSepM_ofList hk1).trans
    (BiEntails.trans ?_ (BigSepM.bigSepM_ofList hk2).symm)
  rw [List.zip_map_left]
  exact BiEntails.of_eq
    (BigSepL.bigSepL_map (Prod.map f id) (Φ := fun _ kv => Φ kv.1 kv.2)).symm

/-! ### Import resources -/

@[rocq_alias iriswasm.import_resources_wasm_domcheck]
def importResourcesWasmDomcheck (v_imps : List ModuleExport) (wfs : NatMap FunctionClosure)
    (wts : NatMap Tableinst) (wms : NatMap Memory) (wgs : NatMap Global) : IProp GF :=
  iprop(⌜(∀ k, PartialMap.dom wfs k ↔ k ∈ extFuncAddrs (v_imps.map (·.desc))) ∧
    (∀ k, PartialMap.dom wts k ↔ k ∈ extTabAddrs (v_imps.map (·.desc))) ∧
    (∀ k, PartialMap.dom wms k ↔ k ∈ extMemAddrs (v_imps.map (·.desc))) ∧
    (∀ k, PartialMap.dom wgs k ↔ k ∈ extGlobAddrs (v_imps.map (·.desc)))⌝)

@[rocq_alias iriswasm.import_func_resources]
def importFuncResources (wfs : NatMap FunctionClosure) : IProp GF :=
  iprop([∗map] n ↦ v ∈ wfs, n ↦[wf] v)

@[rocq_alias iriswasm.import_tab_resources]
def importTabResources (wts : NatMap Tableinst) : IProp GF :=
  iprop([∗map] n ↦ v ∈ wts, n ↦[wtblock] v)

@[rocq_alias iriswasm.import_mem_resources]
def importMemResources (wms : NatMap Memory) : IProp GF :=
  iprop([∗map] n ↦ v ∈ wms, n ↦[wmblock] v)

@[rocq_alias iriswasm.import_glob_resources]
def importGlobResources (wgs : NatMap Global) : IProp GF :=
  iprop([∗map] n ↦ v ∈ wgs, n ↦[wg] v)

end Iris_instantiation

@[rocq_alias iriswasm.func_domcheck]
def funcDomcheck (v_imps : List ModuleExport) (wfs : NatMap FunctionClosure) : Prop :=
  ∀ k, PartialMap.dom wfs k ↔ k ∈ extFuncAddrs (v_imps.map (·.desc))

@[rocq_alias iriswasm.tab_domcheck]
def tabDomcheck (v_imps : List ModuleExport) (wts : NatMap Tableinst) : Prop :=
  ∀ k, PartialMap.dom wts k ↔ k ∈ extTabAddrs (v_imps.map (·.desc))

@[rocq_alias iriswasm.mem_domcheck]
def memDomcheck (v_imps : List ModuleExport) (wms : NatMap Memory) : Prop :=
  ∀ k, PartialMap.dom wms k ↔ k ∈ extMemAddrs (v_imps.map (·.desc))

@[rocq_alias iriswasm.glob_domcheck]
def globDomcheck (v_imps : List ModuleExport) (wgs : NatMap Global) : Prop :=
  ∀ k, PartialMap.dom wgs k ↔ k ∈ extGlobAddrs (v_imps.map (·.desc))

@[rocq_alias iriswasm.func_typecheck]
def funcTypecheck (v_imps : List ModuleExport) (t_imps : List ExternT)
    (wfs : NatMap FunctionClosure) : Prop :=
  Wasm.List.Forall₂ (fun (v : ModuleExport) (t : ExternT) =>
    match v.desc with
    | .func (.funcidx i) => ∃ cl, get? wfs i = some cl ∧ t = .func (clType cl)
    | _ => True) v_imps t_imps

@[rocq_alias iriswasm.tab_typecheck]
def tabTypecheck (v_imps : List ModuleExport) (t_imps : List ExternT)
    (wts : NatMap Tableinst) : Prop :=
  Wasm.List.Forall₂ (fun (v : ModuleExport) (t : ExternT) =>
    match v.desc with
    | .table (.tableidx i) =>
      ∃ tab tt, get? wts i = some tab ∧ t = .tab tt ∧ tabTyping tab tt = true
    | _ => True) v_imps t_imps

@[rocq_alias iriswasm.mem_typecheck]
def memTypecheck (v_imps : List ModuleExport) (t_imps : List ExternT)
    (wms : NatMap Memory) : Prop :=
  Wasm.List.Forall₂ (fun (v : ModuleExport) (t : ExternT) =>
    match v.desc with
    | .mem (.memidx i) =>
      ∃ mem mt, get? wms i = some mem ∧ t = .mem mt ∧ memTyping mem mt = true
    | _ => True) v_imps t_imps

@[rocq_alias iriswasm.glob_typecheck]
def globTypecheck (v_imps : List ModuleExport) (t_imps : List ExternT)
    (wgs : NatMap Global) : Prop :=
  Wasm.List.Forall₂ (fun (v : ModuleExport) (t : ExternT) =>
    match v.desc with
    | .global (.globalidx i) =>
      ∃ g gt, get? wgs i = some g ∧ t = .glob gt ∧ globalAgree g gt = true
    | _ => True) v_imps t_imps

section Iris_instantiation
variable [WasmG hlc GF]

@[rocq_alias iriswasm.import_func_wasm_check]
def importFuncWasmCheck (v_imps : List ModuleExport) (t_imps : List ExternT)
    (wfs : NatMap FunctionClosure) : IProp GF :=
  iprop(importFuncResources wfs ∗ ⌜funcTypecheck v_imps t_imps wfs ∧ funcDomcheck v_imps wfs⌝)

@[rocq_alias iriswasm.import_tab_wasm_check]
def importTabWasmCheck (v_imps : List ModuleExport) (t_imps : List ExternT)
    (wts : NatMap Tableinst) : IProp GF :=
  iprop(importTabResources wts ∗ ⌜tabTypecheck v_imps t_imps wts ∧ tabDomcheck v_imps wts⌝)

@[rocq_alias iriswasm.import_mem_wasm_check]
def importMemWasmCheck (v_imps : List ModuleExport) (t_imps : List ExternT)
    (wms : NatMap Memory) : IProp GF :=
  iprop(importMemResources wms ∗ ⌜memTypecheck v_imps t_imps wms ∧ memDomcheck v_imps wms⌝)

@[rocq_alias iriswasm.import_glob_wasm_check]
def importGlobWasmCheck (v_imps : List ModuleExport) (t_imps : List ExternT)
    (wgs : NatMap Global) : IProp GF :=
  iprop(importGlobResources wgs ∗ ⌜globTypecheck v_imps t_imps wgs ∧ globDomcheck v_imps wgs⌝)

@[rocq_alias iriswasm.import_resources_wasm_typecheck]
def importResourcesWasmTypecheck (v_imps : List ModuleExport) (t_imps : List ExternT)
    (wfs : NatMap FunctionClosure) (wts : NatMap Tableinst) (wms : NatMap Memory)
    (wgs : NatMap Global) : IProp GF :=
  iprop(importFuncWasmCheck v_imps t_imps wfs ∗ importTabWasmCheck v_imps t_imps wts ∗
    importMemWasmCheck v_imps t_imps wms ∗ importGlobWasmCheck v_imps t_imps wgs)

/-- Coq Ltac `unfold_irwt_all`. -/
macro "unfold_irwt_all" : tactic => `(tactic| unfold importFuncWasmCheck importTabWasmCheck
  importMemWasmCheck importGlobWasmCheck importFuncResources importTabResources importMemResources
  importGlobResources funcTypecheck tabTypecheck memTypecheck globTypecheck funcDomcheck
  tabDomcheck memDomcheck globDomcheck)

@[rocq_alias iriswasm.import_resources_wasm_typecheck_sepL2]
def importResourcesWasmTypecheckSepL2 (v_imps : List ModuleExport) (t_imps : List ExternT)
    (wfs : NatMap FunctionClosure) (wts : NatMap Tableinst) (wms : NatMap Memory)
    (wgs : NatMap Global) : IProp GF :=
  iprop(importResourcesWasmDomcheck v_imps wfs wts wms wgs ∗
    [∗list] v;t ∈ v_imps;t_imps,
      match v.desc with
      | .func (.funcidx i) =>
        ∃ cl, i ↦[wf] cl ∗ ⌜get? wfs i = some cl ∧ t = .func (clType cl)⌝
      | .table (.tableidx i) =>
        ∃ tab tt, i ↦[wtblock] tab ∗
          ⌜get? wts i = some tab ∧ t = .tab tt ∧ tabTyping tab tt = true⌝
      | .mem (.memidx i) =>
        ∃ mem mt, i ↦[wmblock] mem ∗
          ⌜get? wms i = some mem ∧ t = .mem mt ∧ memTyping mem mt = true⌝
      | .global (.globalidx i) =>
        ∃ g gt, i ↦[wg] g ∗ ⌜get? wgs i = some g ∧ t = .glob gt ∧ globalAgree g gt = true⌝)

@[rocq_alias iriswasm.ifwc_cons_ne]
theorem ifwc_cons_ne (v_imps : List ModuleExport) (t_imps : List ExternT)
    (wfs : NatMap FunctionClosure) (v : ModuleExport) (t : ExternT)
    (hnv : ∀ idx, v.desc ≠ .func idx) (_hnt : ∀ tt, t ≠ .func tt) :
    ⊢ importFuncWasmCheck (GF := GF) v_imps t_imps wfs -∗
      importFuncWasmCheck (v :: v_imps) (t :: t_imps) wfs := by
  unfold importFuncWasmCheck funcTypecheck funcDomcheck
  iintro ⟨Hm, %Ht, %Hc⟩
  isplitl [Hm]
  · iexact Hm
  ipureintro
  rcases v with ⟨nm, d⟩
  cases d <;> first
    | exact absurd rfl (hnv _)
    | exact ⟨.cons trivial Ht, by simpa [extFuncAddrs, extFuncs] using Hc⟩

@[rocq_alias iriswasm.itwc_cons_ne]
theorem itwc_cons_ne (v_imps : List ModuleExport) (t_imps : List ExternT)
    (wts : NatMap Tableinst) (v : ModuleExport) (t : ExternT)
    (hnv : ∀ idx, v.desc ≠ .table idx) (_hnt : ∀ tt, t ≠ .tab tt) :
    ⊢ importTabWasmCheck (GF := GF) v_imps t_imps wts -∗
      importTabWasmCheck (v :: v_imps) (t :: t_imps) wts := by
  unfold importTabWasmCheck tabTypecheck tabDomcheck
  iintro ⟨Hm, %Ht, %Hc⟩
  isplitl [Hm]
  · iexact Hm
  ipureintro
  rcases v with ⟨nm, d⟩
  cases d <;> first
    | exact absurd rfl (hnv _)
    | exact ⟨.cons trivial Ht, by simpa [extTabAddrs, extTabs] using Hc⟩

@[rocq_alias iriswasm.imwc_cons_ne]
theorem imwc_cons_ne (v_imps : List ModuleExport) (t_imps : List ExternT)
    (wms : NatMap Memory) (v : ModuleExport) (t : ExternT)
    (hnv : ∀ idx, v.desc ≠ .mem idx) (_hnt : ∀ tt, t ≠ .mem tt) :
    ⊢ importMemWasmCheck (GF := GF) v_imps t_imps wms -∗
      importMemWasmCheck (v :: v_imps) (t :: t_imps) wms := by
  unfold importMemWasmCheck memTypecheck memDomcheck
  iintro ⟨Hm, %Ht, %Hc⟩
  isplitl [Hm]
  · iexact Hm
  ipureintro
  rcases v with ⟨nm, d⟩
  cases d <;> first
    | exact absurd rfl (hnv _)
    | exact ⟨.cons trivial Ht, by simpa [extMemAddrs, extMems] using Hc⟩

@[rocq_alias iriswasm.igwc_cons_ne]
theorem igwc_cons_ne (v_imps : List ModuleExport) (t_imps : List ExternT)
    (wgs : NatMap Global) (v : ModuleExport) (t : ExternT)
    (hnv : ∀ idx, v.desc ≠ .global idx) (_hnt : ∀ tt, t ≠ .glob tt) :
    ⊢ importGlobWasmCheck (GF := GF) v_imps t_imps wgs -∗
      importGlobWasmCheck (v :: v_imps) (t :: t_imps) wgs := by
  unfold importGlobWasmCheck globTypecheck globDomcheck
  iintro ⟨Hm, %Ht, %Hc⟩
  isplitl [Hm]
  · iexact Hm
  ipureintro
  rcases v with ⟨nm, d⟩
  cases d <;> first
    | exact absurd rfl (hnv _)
    | exact ⟨.cons trivial Ht, by simpa [extGlobAddrs, extGlobs] using Hc⟩

/-! Generic form of the per-kind argument of `irwt_nodup_equiv` (the Coq proof repeats it four
times): a map whose domain is the list of addresses selected by `sel` splits into a `[∗list]`. -/

private def kindR {A B V : Type} (sel : A → Option Nat) (m0 : NatMap V) (P : V → B → Prop)
    (v : A) (t : B) : Prop :=
  match sel v with
  | some i => ∃ x, get? m0 i = some x ∧ P x t
  | none => True

private def kindE {A B V : Type} (sel : A → Option Nat) (m0 : NatMap V) (Φ : Nat → V → IProp GF)
    (P : V → B → Prop) (v : A) (t : B) : IProp GF :=
  match sel v with
  | some i => iprop(∃ x, Φ i x ∗ ⌜get? m0 i = some x ∧ P x t⌝)
  | none => iprop(emp)

private theorem sepM_sepL2_kind {A B V : Type} (sel : A → Option Nat) (m0 : NatMap V)
    (Φ : Nat → V → IProp GF) (P : V → B → Prop) :
    ∀ (vs : List A) (ts : List B) (m : NatMap V),
    (vs.filterMap sel).Nodup →
    (∀ k, PartialMap.dom m k ↔ k ∈ vs.filterMap sel) →
    (∀ k ∈ vs.filterMap sel, get? m k = get? m0 k) →
    (iprop(([∗map] k ↦ x ∈ m, Φ k x) ∗ ⌜Wasm.List.Forall₂ (kindR sel m0 P) vs ts⌝) ⊣⊢
     [∗list] v;t ∈ vs;ts, kindE sel m0 Φ P v t)
  | [], [], m, _, hdom, _ => by
    have hm : m = ∅ := LawfulPartialMap.eq_empty_iff.2 fun k => by
      cases h : get? m k with
      | none => rfl
      | some _ => exact absurd ((hdom k).1 (by simp [PartialMap.dom, h])) (by simp)
    subst hm
    exact ⟨Affine.affine, emp_sep.2.trans (sep_mono BigSepM.bigSepM_empty_intro (pure_intro .nil))⟩
  | [], _ :: _, _, _, _, _ => ⟨(by iintro ⟨-, %h⟩; cases h), false_elim⟩
  | _ :: _, [], _, _, _, _ => ⟨(by iintro ⟨-, %h⟩; cases h), false_elim⟩
  | v :: vs, t :: ts, m, hnd, hdom, hlk => by
    cases hs : sel v with
    | none =>
      have hk : (v :: vs).filterMap sel = vs.filterMap sel := by simp [hs]
      rw [hk] at hnd hdom hlk
      have ih := sepM_sepL2_kind sel m0 Φ P vs ts m hnd hdom hlk
      have hF : Wasm.List.Forall₂ (kindR sel m0 P) (v :: vs) (t :: ts) ↔
          Wasm.List.Forall₂ (kindR sel m0 P) vs ts :=
        ⟨fun h => by cases h; assumption, fun h => .cons (by simp [kindR, hs]) h⟩
      rw [hF]
      refine ih.trans (emp_sep.symm.trans (sep_congr ?_ .rfl))
      simp only [kindE, hs]; exact .rfl
    | some i =>
      have hk : (v :: vs).filterMap sel = i :: vs.filterMap sel := by simp [hs]
      rw [hk] at hnd hdom hlk
      obtain ⟨hni, hnd⟩ := List.nodup_cons.1 hnd
      have ih := sepM_sepL2_kind sel m0 Φ P vs ts (delete m i) hnd
        (fun k => by
          rw [PartialMap.dom, LawfulPartialMap.get?_delete]
          by_cases hik : i = k
          · subst hik; simp [hni]
          · simp only [hik, ↓reduceIte]
            exact (hdom k).trans (by simp [Ne.symm hik]))
        (fun k hk => by
          have hik : ¬ i = k := fun h => hni (by subst h; exact hk)
          rw [LawfulPartialMap.get?_delete]; simp only [hik, ↓reduceIte]
          exact hlk k (List.mem_cons_of_mem _ hk))
      have hmi := hlk i List.mem_cons_self
      constructor
      · iintro ⟨Hm, %hF⟩
        rcases hF with _ | ⟨hR, hF'⟩
        obtain ⟨x, hx, hP⟩ : ∃ x, get? m0 i = some x ∧ P x t := by simpa [kindR, hs] using hR
        icases (BigSepM.bigSepM_delete (hmi.trans hx)).1 $$ Hm with ⟨Hi, Hm⟩
        isplitl [Hi]
        · simp only [kindE, hs]
          iexists x
          isplitl [Hi]
          · iexact Hi
          · ipureintro; exact ⟨hx, hP⟩
        · iapply ih.1
          isplitl [Hm]
          · iexact Hm
          · ipureintro; exact hF'
      · iintro ⟨He, Hr⟩
        icases ih.2 $$ Hr with ⟨Hm, %hF'⟩
        simp only [kindE, hs]
        icases He with ⟨%x, Hi, %hx, %hP⟩
        isplitl [Hi Hm]
        · iapply (BigSepM.bigSepM_delete (hmi.trans hx)).2
          isplitl [Hi]
          · iexact Hi
          · iexact Hm
        · ipureintro; exact .cons (by simp only [kindR, hs]; exact ⟨x, hx, hP⟩) hF'

private theorem forall₂_congr {A B : Type} {R S : A → B → Prop} (h : ∀ a b, R a b ↔ S a b) :
    ∀ {l1 : List A} {l2 : List B}, Wasm.List.Forall₂ R l1 l2 ↔ Wasm.List.Forall₂ S l1 l2
  | [], [] => ⟨fun _ => .nil, fun _ => .nil⟩
  | [], _ :: _ => ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | _ :: _, [] => ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | a :: _, b :: _ =>
    ⟨fun hh => by cases hh with | cons h1 h2 => exact .cons ((h a b).1 h1) (forall₂_congr h |>.1 h2),
     fun hh => by cases hh with | cons h1 h2 => exact .cons ((h a b).2 h1) (forall₂_congr h |>.2 h2)⟩

/-- One kind of import check (`import_*_wasm_check`) as a `[∗list]` over the imports. -/
private theorem check_kind {V : Type} (v_imps : List ModuleExport) (t_imps : List ExternT)
    (sel : ModuleExportDesc → Option Nat) (m : NatMap V) (Φ : Nat → V → IProp GF)
    (P : V → ExternT → Prop) (Rt : ModuleExport → ExternT → Prop)
    (hRt : ∀ v t, Rt v t ↔ kindR (fun v : ModuleExport => sel v.desc) m P v t)
    (addrs : List Nat) (haddrs : addrs = v_imps.filterMap fun v => sel v.desc)
    (hinj : ∀ a a' b, sel a = some b → sel a' = some b → a = a')
    (hnd : (v_imps.map (·.desc)).Nodup) :
    iprop(([∗map] k ↦ x ∈ m, Φ k x) ∗
        ⌜Wasm.List.Forall₂ Rt v_imps t_imps ∧ ∀ k, PartialMap.dom m k ↔ k ∈ addrs⌝) ⊣⊢
      iprop(⌜∀ k, PartialMap.dom m k ↔ k ∈ addrs⌝ ∗
        [∗list] v;t ∈ v_imps;t_imps, kindE (fun v : ModuleExport => sel v.desc) m Φ P v t) := by
  subst haddrs
  have hnd' : (v_imps.filterMap fun v => sel v.desc).Nodup := by
    have e : (v_imps.filterMap fun v => sel v.desc) = (v_imps.map (·.desc)).filterMap sel :=
      List.filterMap_map.symm
    rw [e]
    exact List.Pairwise.filterMap sel
      (fun a a' hne b hb b' hb' (heq : b = b') => hne (hinj a a' b hb (heq ▸ hb'))) hnd
  rw [forall₂_congr hRt]
  constructor
  · iintro ⟨Hm, %hF, %hd⟩
    isplitr
    · ipureintro; exact hd
    · iapply (sepM_sepL2_kind _ m Φ P v_imps t_imps m hnd' hd (fun _ _ => rfl)).1
      isplitl [Hm]
      · iexact Hm
      · ipureintro; exact hF
  · iintro ⟨%hd, Hl⟩
    icases (sepM_sepL2_kind _ m Φ P v_imps t_imps m hnd' hd (fun _ _ => rfl)).2 $$ Hl
      with ⟨Hm, %hF⟩
    isplitl [Hm]
    · iexact Hm
    · ipureintro; exact ⟨hF, hd⟩

private def selFunc : ModuleExportDesc → Option Nat
  | .func (.funcidx i) => some i
  | _ => none

private def selTab : ModuleExportDesc → Option Nat
  | .table (.tableidx i) => some i
  | _ => none

private def selMem : ModuleExportDesc → Option Nat
  | .mem (.memidx i) => some i
  | _ => none

private def selGlob : ModuleExportDesc → Option Nat
  | .global (.globalidx i) => some i
  | _ => none

private theorem ext_addrs_sel (l : List ModuleExportDesc) :
    extFuncAddrs l = l.filterMap selFunc ∧ extTabAddrs l = l.filterMap selTab ∧
    extMemAddrs l = l.filterMap selMem ∧ extGlobAddrs l = l.filterMap selGlob := by
  induction l with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons d l ih =>
    rcases d with (⟨⟨i⟩⟩ | ⟨⟨i⟩⟩ | ⟨⟨i⟩⟩ | ⟨⟨i⟩⟩) <;>
      simp_all [extFuncAddrs, extTabAddrs, extMemAddrs, extGlobAddrs, extFuncs, extTabs, extMems,
        extGlobs, selFunc, selTab, selMem, selGlob, List.filterMap_cons]

macro "sel_inj" : tactic => `(tactic| (
  intro a a' b h1 h2
  rcases a with (⟨⟨_⟩⟩ | ⟨⟨_⟩⟩ | ⟨⟨_⟩⟩ | ⟨⟨_⟩⟩) <;>
    rcases a' with (⟨⟨_⟩⟩ | ⟨⟨_⟩⟩ | ⟨⟨_⟩⟩ | ⟨⟨_⟩⟩) <;>
    simp_all [selFunc, selTab, selMem, selGlob]))

/-- If `v_imps` has no duplicated imports, the two versions are equivalent. -/
@[rocq_alias iriswasm.irwt_nodup_equiv]
theorem irwt_nodup_equiv (v_imps : List ModuleExport) (t_imps : List ExternT)
    (wfs : NatMap FunctionClosure) (wts : NatMap Tableinst) (wms : NatMap Memory)
    (wgs : NatMap Global) (hnd : (v_imps.map (·.desc)).Nodup) :
    importResourcesWasmTypecheck (GF := GF) v_imps t_imps wfs wts wms wgs ⊣⊢
      importResourcesWasmTypecheckSepL2 v_imps t_imps wfs wts wms wgs := by
  have hl := ext_addrs_sel (v_imps.map (·.desc))
  have hF := check_kind (GF := GF) v_imps t_imps selFunc wfs (fun i cl => iprop(i ↦[wf] cl))
    (fun cl t => t = .func (clType cl))
    (fun (v : ModuleExport) (t : ExternT) => match v.desc with
      | .func (.funcidx i) => ∃ cl, get? wfs i = some cl ∧ t = .func (clType cl)
      | _ => True)
    (fun v t => by rcases v with ⟨_, (⟨⟨_⟩⟩ | ⟨⟨_⟩⟩ | ⟨⟨_⟩⟩ | ⟨⟨_⟩⟩)⟩ <;> simp [kindR, selFunc])
    _ (hl.1.trans List.filterMap_map) (by sel_inj) hnd
  have hT := check_kind (GF := GF) v_imps t_imps selTab wts (fun i tab => iprop(i ↦[wtblock] tab))
    (fun tab t => ∃ tt, t = .tab tt ∧ tabTyping tab tt = true)
    (fun (v : ModuleExport) (t : ExternT) => match v.desc with
      | .table (.tableidx i) =>
        ∃ tab tt, get? wts i = some tab ∧ t = .tab tt ∧ tabTyping tab tt = true
      | _ => True)
    (fun v t => by rcases v with ⟨_, (⟨⟨_⟩⟩ | ⟨⟨_⟩⟩ | ⟨⟨_⟩⟩ | ⟨⟨_⟩⟩)⟩ <;> simp [kindR, selTab])
    _ (hl.2.1.trans List.filterMap_map) (by sel_inj) hnd
  have hM := check_kind (GF := GF) v_imps t_imps selMem wms (fun i mem => iprop(i ↦[wmblock] mem))
    (fun mem t => ∃ mt, t = .mem mt ∧ memTyping mem mt = true)
    (fun (v : ModuleExport) (t : ExternT) => match v.desc with
      | .mem (.memidx i) =>
        ∃ mem mt, get? wms i = some mem ∧ t = .mem mt ∧ memTyping mem mt = true
      | _ => True)
    (fun v t => by rcases v with ⟨_, (⟨⟨_⟩⟩ | ⟨⟨_⟩⟩ | ⟨⟨_⟩⟩ | ⟨⟨_⟩⟩)⟩ <;> simp [kindR, selMem])
    _ (hl.2.2.1.trans List.filterMap_map) (by sel_inj) hnd
  have hG := check_kind (GF := GF) v_imps t_imps selGlob wgs (fun i g => iprop(i ↦[wg] g))
    (fun g t => ∃ gt, t = .glob gt ∧ globalAgree g gt = true)
    (fun (v : ModuleExport) (t : ExternT) => match v.desc with
      | .global (.globalidx i) =>
        ∃ g gt, get? wgs i = some g ∧ t = .glob gt ∧ globalAgree g gt = true
      | _ => True)
    (fun v t => by rcases v with ⟨_, (⟨⟨_⟩⟩ | ⟨⟨_⟩⟩ | ⟨⟨_⟩⟩ | ⟨⟨_⟩⟩)⟩ <;> simp [kindR, selGlob])
    _ (hl.2.2.2.trans List.filterMap_map) (by sel_inj) hnd
  -- the combined per-import body is the `∗` of the four per-kind bodies
  have hpt : ∀ (v : ModuleExport) (t : ExternT),
      (match v.desc with
        | .func (.funcidx i) =>
          iprop(∃ cl, i ↦[wf] cl ∗ ⌜get? wfs i = some cl ∧ t = .func (clType cl)⌝)
        | .table (.tableidx i) =>
          iprop(∃ tab tt, i ↦[wtblock] tab ∗
            ⌜get? wts i = some tab ∧ t = .tab tt ∧ tabTyping tab tt = true⌝)
        | .mem (.memidx i) =>
          iprop(∃ mem mt, i ↦[wmblock] mem ∗
            ⌜get? wms i = some mem ∧ t = .mem mt ∧ memTyping mem mt = true⌝)
        | .global (.globalidx i) =>
          iprop(∃ g gt, i ↦[wg] g ∗
            ⌜get? wgs i = some g ∧ t = .glob gt ∧ globalAgree g gt = true⌝) : IProp GF) ⊣⊢
      kindE (fun v : ModuleExport => selFunc v.desc) wfs (fun i cl => iprop(i ↦[wf] cl))
          (fun cl t => t = .func (clType cl)) v t ∗
        kindE (fun v : ModuleExport => selTab v.desc) wts (fun i tab => iprop(i ↦[wtblock] tab))
          (fun tab t => ∃ tt, t = .tab tt ∧ tabTyping tab tt = true) v t ∗
        kindE (fun v : ModuleExport => selMem v.desc) wms (fun i mem => iprop(i ↦[wmblock] mem))
          (fun mem t => ∃ mt, t = .mem mt ∧ memTyping mem mt = true) v t ∗
        kindE (fun v : ModuleExport => selGlob v.desc) wgs (fun i g => iprop(i ↦[wg] g))
          (fun g t => ∃ gt, t = .glob gt ∧ globalAgree g gt = true) v t := by
    intro v t
    rcases v with ⟨_, (⟨⟨i⟩⟩ | ⟨⟨i⟩⟩ | ⟨⟨i⟩⟩ | ⟨⟨i⟩⟩)⟩ <;>
      simp only [kindE, selFunc, selTab, selMem, selGlob] <;> constructor
    · iintro ⟨%x, H, %h⟩
      isplitl [H]
      · iexists x; isplitl [H]; iexact H; ipureintro; exact h
      · isplitl []; iempintro; isplitl []; iempintro; iempintro
    · iintro ⟨⟨%x, H, %h⟩, -, -, -⟩
      iexists x; isplitl [H]; iexact H; ipureintro; exact h
    · iintro ⟨%x, %tt, H, %h1, %h2⟩
      isplitl []; iempintro
      isplitl [H]
      · iexists x; isplitl [H]; iexact H; ipureintro; exact ⟨h1, tt, h2⟩
      · isplitl []; iempintro; iempintro
    · iintro ⟨-, ⟨%x, H, %h1, %tt, %h2⟩, -, -⟩
      iexists x, tt; isplitl [H]; iexact H; ipureintro; exact ⟨h1, h2⟩
    · iintro ⟨%x, %tt, H, %h1, %h2⟩
      isplitl []; iempintro
      isplitl []; iempintro
      isplitl [H]
      · iexists x; isplitl [H]; iexact H; ipureintro; exact ⟨h1, tt, h2⟩
      · iempintro
    · iintro ⟨-, -, ⟨%x, H, %h1, %tt, %h2⟩, -⟩
      iexists x, tt; isplitl [H]; iexact H; ipureintro; exact ⟨h1, h2⟩
    · iintro ⟨%x, %tt, H, %h1, %h2⟩
      isplitl []; iempintro
      isplitl []; iempintro
      isplitl []; iempintro
      iexists x; isplitl [H]; iexact H; ipureintro; exact ⟨h1, tt, h2⟩
    · iintro ⟨-, -, -, %x, H, %h1, %tt, %h2⟩
      iexists x, tt; isplitl [H]; iexact H; ipureintro; exact ⟨h1, h2⟩
  unfold importResourcesWasmTypecheck importResourcesWasmTypecheckSepL2
    importResourcesWasmDomcheck importFuncWasmCheck importTabWasmCheck importMemWasmCheck
    importGlobWasmCheck importFuncResources importTabResources importMemResources
    importGlobResources funcDomcheck tabDomcheck memDomcheck globDomcheck
  refine (sep_congr hF (sep_congr hT (sep_congr hM hG))).trans ?_
  refine BiEntails.trans ?_ (sep_congr .rfl (BigSepL2.bigSepL2_eqv_of_forall_eqv
    (fun {_ v t} => (hpt v t).symm)))
  refine BiEntails.trans ?_ (sep_congr .rfl
    ((sep_congr .rfl ((sep_congr .rfl BigSepL2.bigSepL2_sep_eqv.symm).trans
      BigSepL2.bigSepL2_sep_eqv.symm)).trans BigSepL2.bigSepL2_sep_eqv.symm))
  constructor
  · iintro ⟨⟨%h1, H1⟩, ⟨%h2, H2⟩, ⟨%h3, H3⟩, ⟨%h4, H4⟩⟩
    isplitr
    · ipureintro; exact ⟨h1, h2, h3, h4⟩
    · isplitl [H1]; iexact H1; isplitl [H2]; iexact H2; isplitl [H3]; iexact H3; iexact H4
  · iintro ⟨%⟨h1, h2, h3, h4⟩, H1, H2, H3, H4⟩
    isplitl [H1]
    · isplitr; ipureintro; exact h1; iexact H1
    isplitl [H2]
    · isplitr; ipureintro; exact h2; iexact H2
    isplitl [H3]
    · isplitr; ipureintro; exact h3; iexact H3
    · isplitr; ipureintro; exact h4; iexact H4

private theorem forall₂_getElem? {A B : Type} {R : A → B → Prop} :
    ∀ {l1 : List A} {l2 : List B} {k : Nat} {a : A} {b : B}, Wasm.List.Forall₂ R l1 l2 →
    l1[k]? = some a → l2[k]? = some b → R a b
  | _ :: _, _ :: _, 0, _, _, .cons h _, h1, h2 => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h1 h2; subst h1 h2; exact h
  | _ :: _, _ :: _, _ + 1, _, _, .cons _ h, h1, h2 => forall₂_getElem? h h1 h2

/-- `genHeap_valid` without the update modality (and without consuming the resources). -/
private theorem heap_lookup_i {L V : Type _} {H : Type _ → Type _} [LawfulFiniteMap H L]
    {G : genHeapGS L V GF H} {σ : H V} {l : L} {dq : DFrac} {v : V} :
    ⊢ (genHeapInterp (G := G) σ -∗ pointsTo (G := G) l dq v -∗ ⌜get? σ l = some v⌝ : IProp GF) := by
  unfold genHeapInterp pointsTo
  iintro ⟨%m, -, Hσ, -⟩ Hl
  iapply ghost_map_lookup $$ Hσ Hl

/-- Every entry of a `[∗map]` satisfies the pure consequence `ψ` of its resource. -/
private theorem sepM_pure_all {V : Type} {m : NatMap V} {Q : IProp GF} {Φ : Nat → V → IProp GF}
    {ψ : Nat → V → Prop} (h : ∀ k x, ⊢ Q -∗ Φ k x -∗ ⌜ψ k x⌝) :
    ⊢ Q -∗ ([∗map] k ↦ x ∈ m, Φ k x) -∗ ⌜∀ k x, get? m k = some x → ψ k x⌝ := by
  iintro HQ Hm
  iapply pure_forall.2; iintro %k
  iapply pure_forall.2; iintro %x
  iapply pure_wand.1; iintro %hx
  ihave Hx := BigSepM.bigSepM_lookup hx $$ Hm
  iapply h k x $$ HQ Hx

@[rocq_alias iriswasm.import_func_wasm_lookup]
theorem import_func_wasm_lookup (v_imps : List ModuleExport) (t_imps : List ExternT)
    (wfs : NatMap FunctionClosure) (ws : StoreRecord) :
    ⊢ genHeapInterp (G := WasmG.funcHs) (gmapOfList ws.funcs) -∗
      importFuncWasmCheck (GF := GF) v_imps t_imps wfs -∗
      ⌜v_imps.length = t_imps.length ∧ ∀ (k : Nat) (v : ModuleExport) (t : ExternT),
        v_imps[k]? = some v → t_imps[k]? = some t →
        match v.desc with
        | .func (.funcidx i) =>
          ∃ cl, ws.funcs[i]? = some cl ∧ get? wfs i = some cl ∧ t = .func (clType cl)
        | _ => True⌝ := by
  unfold importFuncWasmCheck importFuncResources funcTypecheck
  iintro Hw ⟨Hm, %Htype, -⟩
  ihave %hv := sepM_pure_all (ψ := fun k x => ws.funcs[k]? = some x)
    (fun k x => by
      iintro Hw Hx
      ihave %h := heap_lookup_i $$ Hw Hx
      ipureintro; rwa [gmap_of_list_lookup] at h) $$ Hw Hm
  ipureintro
  refine ⟨Htype.length_eq, fun k v t hv' ht => ?_⟩
  have hR := forall₂_getElem? Htype hv' ht
  rcases v with ⟨_, (⟨⟨i⟩⟩ | ⟨⟨i⟩⟩ | ⟨⟨i⟩⟩ | ⟨⟨i⟩⟩)⟩ <;> try trivial
  obtain ⟨cl, h1, h2⟩ := hR
  exact ⟨cl, hv i cl h1, h1, h2⟩

@[rocq_alias iriswasm.import_tab_wasm_lookup]
theorem import_tab_wasm_lookup (v_imps : List ModuleExport) (t_imps : List ExternT)
    (wts : NatMap Tableinst) (ws : StoreRecord) :
    ⊢ genHeapInterp (G := WasmG.tabHs) (gmapOfTable ws.tables) -∗
      genHeapInterp (G := WasmG.tabsizeHs) (gmapOfList (ws.tables.map tabSize)) -∗
      genHeapInterp (G := WasmG.tablimitHs) (gmapOfList (ws.tables.map (·.maxOpt))) -∗
      importTabWasmCheck (GF := GF) v_imps t_imps wts -∗
      ⌜v_imps.length = t_imps.length ∧ ∀ (k : Nat) (v : ModuleExport) (t : ExternT),
        v_imps[k]? = some v → t_imps[k]? = some t →
        match v.desc with
        | .table (.tableidx i) => ∃ tab tt, ws.tables[i]? = some tab ∧ get? wts i = some tab ∧
            t = .tab tt ∧ tabTyping tab tt = true
        | _ => True⌝ := by
  unfold importTabWasmCheck importTabResources tabTypecheck
  iintro Hw Hws Hwl ⟨Hm, %Htype, -⟩
  ihave %hv := sepM_pure_all (Q := iprop(genHeapInterp (G := WasmG.tabHs) (gmapOfTable ws.tables) ∗
      genHeapInterp (G := WasmG.tabsizeHs) (gmapOfList (ws.tables.map tabSize)) ∗
      genHeapInterp (G := WasmG.tablimitHs) (gmapOfList (ws.tables.map (·.maxOpt)))))
    (ψ := fun k x => ws.tables[k]? = some x)
    (fun k x => by
      iintro ⟨Hw, Hws, Hwl⟩ Hx
      iapply tab_block_lookup $$ Hw Hws Hwl Hx) $$ [Hw Hws Hwl] Hm
  · isplitl [Hw]; iexact Hw; isplitl [Hws]; iexact Hws; iexact Hwl
  ipureintro
  refine ⟨Htype.length_eq, fun k v t hv' ht => ?_⟩
  have hR := forall₂_getElem? Htype hv' ht
  rcases v with ⟨_, (⟨⟨i⟩⟩ | ⟨⟨i⟩⟩ | ⟨⟨i⟩⟩ | ⟨⟨i⟩⟩)⟩ <;> try trivial
  obtain ⟨tab, tt, h1, h2⟩ := hR
  exact ⟨tab, tt, hv i tab h1, h1, h2⟩

@[rocq_alias iriswasm.import_mem_wasm_lookup]
theorem import_mem_wasm_lookup (v_imps : List ModuleExport) (t_imps : List ExternT)
    (wms : NatMap Memory) (ws : StoreRecord) :
    ⊢ genHeapInterp (G := WasmG.memHs) (gmapOfMemory ws.mems) -∗
      genHeapInterp (G := WasmG.memsizeHs) (gmapOfList (ws.mems.map memLengthMeta)) -∗
      genHeapInterp (G := WasmG.memlimitHs) (gmapOfList (ws.mems.map (·.type.limits.max))) -∗
      importMemWasmCheck (GF := GF) v_imps t_imps wms -∗
      ⌜v_imps.length = t_imps.length ∧ ∀ (k : Nat) (v : ModuleExport) (t : ExternT),
        v_imps[k]? = some v → t_imps[k]? = some t →
        match v.desc with
        | .mem (.memidx i) => ∃ mem mt,
            ws.mems[i]? = some mem ∧
            get? wms i = some mem ∧ t = .mem mt ∧ memTyping mem mt = true
        | _ => True⌝ := by
  unfold importMemWasmCheck importMemResources memTypecheck
  iintro Hw Hws Hwl ⟨Hm, %Htype, -⟩
  ihave %hv := sepM_pure_all (Q := iprop(genHeapInterp (G := WasmG.memHs) (gmapOfMemory ws.mems) ∗
      genHeapInterp (G := WasmG.memsizeHs) (gmapOfList (ws.mems.map memLengthMeta)) ∗
      genHeapInterp (G := WasmG.memlimitHs) (gmapOfList (ws.mems.map (·.type.limits.max)))))
    (ψ := fun k x => ∃ m, ws.mems[k]? = some m ∧ m.data.data = x.data.data ∧ m.type = x.type)
    (fun k x => by
      iintro ⟨Hw, Hws, Hwl⟩ Hx
      iapply mem_block_lookup $$ Hw Hws Hwl Hx) $$ [Hw Hws Hwl] Hm
  · isplitl [Hw]; iexact Hw; isplitl [Hws]; iexact Hws; iexact Hwl
  ipureintro
  refine ⟨Htype.length_eq, fun k v t hv' ht => ?_⟩
  have hR := forall₂_getElem? Htype hv' ht
  rcases v with ⟨_, (⟨⟨i⟩⟩ | ⟨⟨i⟩⟩ | ⟨⟨i⟩⟩ | ⟨⟨i⟩⟩)⟩ <;> try trivial
  obtain ⟨mem, mt, h1, h2⟩ := hR
  obtain ⟨m, hm, hd, ho⟩ := hv i mem h1
  exact ⟨mem, mt, MemEquiv.eq (m₁ := m) (m₂ := mem) ⟨ho, hd⟩ ▸ hm, h1, h2⟩

@[rocq_alias iriswasm.import_glob_wasm_lookup]
theorem import_glob_wasm_lookup (v_imps : List ModuleExport) (t_imps : List ExternT)
    (wgs : NatMap Global) (ws : StoreRecord) :
    ⊢ genHeapInterp (G := WasmG.globHs) (gmapOfList ws.globals) -∗
      importGlobWasmCheck (GF := GF) v_imps t_imps wgs -∗
      ⌜v_imps.length = t_imps.length ∧ ∀ (k : Nat) (v : ModuleExport) (t : ExternT),
        v_imps[k]? = some v → t_imps[k]? = some t →
        match v.desc with
        | .global (.globalidx i) => ∃ g gt, ws.globals[i]? = some g ∧ get? wgs i = some g ∧
            t = .glob gt ∧ globalAgree g gt = true
        | _ => True⌝ := by
  unfold importGlobWasmCheck importGlobResources globTypecheck
  iintro Hw ⟨Hm, %Htype, -⟩
  ihave %hv := sepM_pure_all (ψ := fun k x => ws.globals[k]? = some x)
    (fun k x => by
      iintro Hw Hx
      ihave %h := heap_lookup_i $$ Hw Hx
      ipureintro; rwa [gmap_of_list_lookup] at h) $$ Hw Hm
  ipureintro
  refine ⟨Htype.length_eq, fun k v t hv' ht => ?_⟩
  have hR := forall₂_getElem? Htype hv' ht
  rcases v with ⟨_, (⟨⟨i⟩⟩ | ⟨⟨i⟩⟩ | ⟨⟨i⟩⟩ | ⟨⟨i⟩⟩)⟩ <;> try trivial
  obtain ⟨g, gt, h1, h2⟩ := hR
  exact ⟨g, gt, hv i g h1, h1, h2⟩

@[rocq_alias iriswasm.import_resources_wasm_lookup]
theorem import_resources_wasm_lookup (v_imps : List ModuleExport) (t_imps : List ExternT)
    (wfs : NatMap FunctionClosure) (wts : NatMap Tableinst) (wms : NatMap Memory)
    (wgs : NatMap Global) (ws : StoreRecord) :
    ⊢ genHeapInterp (G := WasmG.funcHs) (gmapOfList ws.funcs) -∗
      genHeapInterp (G := WasmG.tabHs) (gmapOfTable ws.tables) -∗
      genHeapInterp (G := WasmG.memHs) (gmapOfMemory ws.mems) -∗
      genHeapInterp (G := WasmG.globHs) (gmapOfList ws.globals) -∗
      genHeapInterp (G := WasmG.tabsizeHs) (gmapOfList (ws.tables.map tabSize)) -∗
      genHeapInterp (G := WasmG.tablimitHs) (gmapOfList (ws.tables.map (·.maxOpt))) -∗
      genHeapInterp (G := WasmG.memsizeHs) (gmapOfList (ws.mems.map memLengthMeta)) -∗
      genHeapInterp (G := WasmG.memlimitHs) (gmapOfList (ws.mems.map (·.type.limits.max))) -∗
      importResourcesWasmTypecheck (GF := GF) v_imps t_imps wfs wts wms wgs -∗
      ⌜v_imps.length = t_imps.length ∧ ∀ (k : Nat) (v : ModuleExport) (t : ExternT),
        v_imps[k]? = some v → t_imps[k]? = some t →
        match v.desc with
        | .func (.funcidx i) =>
          ∃ cl, ws.funcs[i]? = some cl ∧ get? wfs i = some cl ∧ t = .func (clType cl)
        | .table (.tableidx i) => ∃ tab tt, ws.tables[i]? = some tab ∧ get? wts i = some tab ∧
            t = .tab tt ∧ tabTyping tab tt = true
        | .mem (.memidx i) => ∃ mem mt,
            ws.mems[i]? = some mem ∧
            get? wms i = some mem ∧ t = .mem mt ∧ memTyping mem mt = true
        | .global (.globalidx i) => ∃ g gt, ws.globals[i]? = some g ∧ get? wgs i = some g ∧
            t = .glob gt ∧ globalAgree g gt = true⌝ := by
  unfold importResourcesWasmTypecheck
  iintro Hwf Hwt Hwm Hwg Hwts Hwtl Hwml Hwmll ⟨Hf, Ht, Hm, Hg⟩
  ihave %⟨hl, hf⟩ := import_func_wasm_lookup v_imps t_imps wfs ws $$ Hwf Hf
  ihave %⟨-, ht⟩ := import_tab_wasm_lookup v_imps t_imps wts ws $$ Hwt Hwts Hwtl Ht
  ihave %⟨-, hm⟩ := import_mem_wasm_lookup v_imps t_imps wms ws $$ Hwm Hwml Hwmll Hm
  ihave %⟨-, hg⟩ := import_glob_wasm_lookup v_imps t_imps wgs ws $$ Hwg Hg
  ipureintro
  refine ⟨hl, fun k v t hv ht' => ?_⟩
  specialize hf k v t hv ht'
  specialize ht k v t hv ht'
  specialize hm k v t hv ht'
  specialize hg k v t hv ht'
  rcases v with ⟨_, (⟨⟨i⟩⟩ | ⟨⟨i⟩⟩ | ⟨⟨i⟩⟩ | ⟨⟨i⟩⟩)⟩ <;> assumption

@[rocq_alias iriswasm.import_resources_wts_subset]
theorem import_resources_wts_subset (v_imps : List ModuleExport) (t_imps : List ExternT)
    (wts : NatMap Tableinst) (ws : StoreRecord) :
    ⊢ genHeapInterp (G := WasmG.tabHs) (gmapOfTable ws.tables) -∗
      genHeapInterp (G := WasmG.tabsizeHs) (gmapOfList (ws.tables.map tabSize)) -∗
      genHeapInterp (G := WasmG.tablimitHs) (gmapOfList (ws.tables.map (·.maxOpt))) -∗
      importTabWasmCheck (GF := GF) v_imps t_imps wts -∗
      ⌜v_imps.length = t_imps.length⌝ -∗
      ⌜wts ⊆ gmapOfList ws.tables⌝ := by
  unfold importTabWasmCheck importTabResources
  iintro Hw Hws Hwl ⟨Hm, -, -⟩ -
  ihave %hv := sepM_pure_all (Q := iprop(genHeapInterp (G := WasmG.tabHs) (gmapOfTable ws.tables) ∗
      genHeapInterp (G := WasmG.tabsizeHs) (gmapOfList (ws.tables.map tabSize)) ∗
      genHeapInterp (G := WasmG.tablimitHs) (gmapOfList (ws.tables.map (·.maxOpt)))))
    (ψ := fun k x => ws.tables[k]? = some x)
    (fun k x => by
      iintro ⟨Hw, Hws, Hwl⟩ Hx
      iapply tab_block_lookup $$ Hw Hws Hwl Hx) $$ [Hw Hws Hwl] Hm
  · isplitl [Hw]; iexact Hw; isplitl [Hws]; iexact Hws; iexact Hwl
  ipureintro
  intro k x hx
  rw [gmap_of_list_lookup]; exact hv k x hx

@[rocq_alias iriswasm.import_resources_wms_subset]
theorem import_resources_wms_subset (v_imps : List ModuleExport) (t_imps : List ExternT)
    (wms : NatMap Memory) (ws : StoreRecord) :
    ⊢ genHeapInterp (G := WasmG.memHs) (gmapOfMemory ws.mems) -∗
      genHeapInterp (G := WasmG.memsizeHs) (gmapOfList (ws.mems.map memLengthMeta)) -∗
      genHeapInterp (G := WasmG.memlimitHs) (gmapOfList (ws.mems.map (·.type.limits.max))) -∗
      importMemWasmCheck (GF := GF) v_imps t_imps wms -∗
      ⌜v_imps.length = t_imps.length⌝ -∗
      ⌜mapRelated MemEquiv wms (gmapOfList ws.mems)⌝ := by
  unfold importMemWasmCheck importMemResources
  iintro Hw Hws Hwl ⟨Hm, -, -⟩ -
  ihave %hv := sepM_pure_all (Q := iprop(genHeapInterp (G := WasmG.memHs) (gmapOfMemory ws.mems) ∗
      genHeapInterp (G := WasmG.memsizeHs) (gmapOfList (ws.mems.map memLengthMeta)) ∗
      genHeapInterp (G := WasmG.memlimitHs) (gmapOfList (ws.mems.map (·.type.limits.max)))))
    (ψ := fun k x => ∃ m, ws.mems[k]? = some m ∧ m.data.data = x.data.data ∧ m.type = x.type)
    (fun k x => by
      iintro ⟨Hw, Hws, Hwl⟩ Hx
      iapply mem_block_lookup $$ Hw Hws Hwl Hx) $$ [Hw Hws Hwl] Hm
  · isplitl [Hw]; iexact Hw; isplitl [Hws]; iexact Hws; iexact Hwl
  ipureintro
  intro k x hx
  obtain ⟨m, hm, hd, ho⟩ := hv k x hx
  exact ⟨m, by rw [gmap_of_list_lookup]; exact hm, ho.symm, hd.symm⟩

end Iris_instantiation

@[rocq_alias iriswasm.module_elem_bound_check_gmap_extend]
theorem module_elem_bound_check_gmap_extend (wts1 wts2 : NatMap Tableinst)
    (impDescs : List ModuleExportDesc) (m : Module)
    (h : ModuleElemBoundCheckGmap wts1 impDescs m) (hsub : wts1 ⊆ wts2) :
    ModuleElemBoundCheckGmap wts2 impDescs m := by
  intro e he
  have := h e he
  rcases e with ⟨⟨n⟩, o, ini⟩
  dsimp only at this ⊢
  split at this <;> try exact this
  split at this <;> try exact this
  split at this
  · exact hsub _ _ ‹_› ▸ this
  · exact this.elim

@[rocq_alias iriswasm.module_data_bound_check_gmap_extend]
theorem module_data_bound_check_gmap_extend (wms1 wms2 : NatMap Memory)
    (impDescs : List ModuleExportDesc) (m : Module)
    (h : ModuleDataBoundCheckGmap wms1 impDescs m) (hrel : mapRelated MemEquiv wms1 wms2) :
    ModuleDataBoundCheckGmap wms2 impDescs m := by
  intro d hd
  have := h d hd
  rcases d with ⟨⟨n⟩, o, ini⟩
  dsimp only at this ⊢
  split at this <;> try exact this
  split at this <;> try exact this
  split at this
  · obtain ⟨mi', hmi', hmax, hdata⟩ := hrel _ _ ‹_›
    rw [hmi']
    simpa only [lengthMem_eq_data_length, hdata] using this
  · exact this.elim

@[rocq_alias iriswasm.module_glob_init_value]
def moduleGlobInitValue (modglobs : List ModuleGlob) : Option (List Value) :=
  those (modglobs.map (assertConst1 ∘ (·.init)))

section Iris_instantiation
variable [WasmG hlc GF]

@[rocq_alias iriswasm.instantiation_resources_pre_wasm]
def instantiationResourcesPreWasm (m : Module) (v_imps : List ModuleExport)
    (t_imps : List ExternT) (wfs : NatMap FunctionClosure) (wts : NatMap Tableinst)
    (wms : NatMap Memory) (wgs : NatMap Global) : IProp GF :=
  iprop(importResourcesWasmTypecheck v_imps t_imps wfs wts wms wgs ∗
    ⌜ModuleElemBoundCheckGmap wts (v_imps.map (·.desc)) m⌝ ∗
    ⌜ModuleDataBoundCheckGmap wms (v_imps.map (·.desc)) m⌝)

end Iris_instantiation

/-! ### Initial values of the allocated resources -/

/-- A map from (instance table id, index) to the funcelem dictated by one elem segment. -/
@[rocq_alias iriswasm.build_tab_initialiser]
def buildTabInitialiser (instfuncs : List Funcaddr) (elem : ModuleElement) (tabid offset : Nat) :
    NatPairMap Funcelem :=
  (elem.init.mapIdx fun j eInit => match eInit with
    | .funcidx fid => fun (acc : NatPairMap Funcelem) =>
      insert acc (tabid, j + offset) instfuncs[fid]?).foldl (fun acc actor => actor acc) ∅

@[rocq_alias iriswasm.module_tab_init_values]
def moduleTabInitValues (m : Module) (inst : Instance) :
    List ModuleElement → NatPairMap Funcelem
  | [] => ∅
  | eInit :: eInits' =>
    match eInit.table with
    | .tableidx i => moduleTabInitValues m inst eInits' ∪
        buildTabInitialiser inst.funcs eInit i (assertConst1I32ToNat eInit.offset)

@[rocq_alias iriswasm.build_mem_initialiser]
def buildMemInitialiser (datum : ModuleData) (memid offset : Nat) : NatPairMap Byte :=
  (datum.init.mapIdx fun j b => fun (acc : NatPairMap Byte) =>
    insert acc (memid, j + offset) b).foldl (fun acc actor => actor acc) ∅

#rocq_ignore iriswasm.module_mem_init_values "literal offsets use their unsigned address type"
def moduleMemInitValues (m : Module) : List ModuleData → NatPairMap Byte
  | [] => ∅
  | dInit :: dInits' =>
    match dInit.data with
    | .memidx i =>
      let rest := moduleMemInitValues m dInits'
      match literalDataOffset dInit.offset with
      | some off => rest ∪ buildMemInitialiser dInit i off
      | none => rest

@[rocq_alias iriswasm.module_glob_init_values]
def ModuleGlobInitValues (m : Module) (g_inits : List Value) : Prop :=
  g_inits.map typeof = m.globals.map (·.type.t) ∧ moduleGlobInitValue m.globals = some g_inits

@[rocq_alias iriswasm.module_inst_table_base_create]
def moduleInstTableBaseCreate (mt : ModuleTable) : Tableinst :=
  { entries := RunTable.uniform mt.type.limits.min none, maxOpt := mt.type.limits.max }

@[rocq_alias iriswasm.module_inst_table_base]
def moduleInstTableBase (mtabs : List ModuleTable) : List Tableinst :=
  mtabs.map moduleInstTableBaseCreate

@[rocq_alias iriswasm.table_init_replace_single]
def tableInitReplaceSingle (t : Tableinst) (offset : Nat) (fns : List Funcelem) : Tableinst :=
  { t with entries := t.entries.overwrite offset (fns.take (t.entries.size - offset)) }

theorem data_tableInitReplaceSingle (t : Tableinst) (off : Nat) (fns : List Funcelem) :
    (tableInitReplaceSingle t off fns).data =
      let pay := fns.take (t.data.length - off)
      t.data.take off ++ pay ++ t.data.drop (off + pay.length) := by
  simp only [tableInitReplaceSingle, Tableinst.data, RunTable.toList_overwrite, RunTable.length_toList]

@[rocq_alias iriswasm.table_init_replace_single_preserve_len]
theorem table_init_replace_single_preserve_len (t : Tableinst) (offset : Nat)
    (fns : List Funcelem) (t' : Tableinst) (h : tableInitReplaceSingle t offset fns = t') :
    t.data.length = t'.data.length := by
  subst h
  simp only [data_tableInitReplaceSingle, List.length_take, List.length_append, List.length_drop]
  omega

@[rocq_alias iriswasm.lookup_funcaddr]
def lookupFuncaddr (inst : Instance) (meInit : List Funcidx) : List Funcelem :=
  meInit.map fun | .funcidx fidx => inst.funcs[fidx]?

/-- For each elem segment targeting a non-imported table, update the table built from the base. -/
@[rocq_alias iriswasm.module_inst_build_tables]
def moduleInstBuildTables (m : Module) (inst : Instance) : List Tableinst :=
  m.elem.foldl (fun tabs e =>
    let itc := getImportTableCount m
    match e.table with
    | .tableidx k =>
      if k < itc then tabs else
        match tabs[k - itc]? with
        | some t => tabs.set (k - itc)
            (tableInitReplaceSingle t (assertConst1I32ToNat e.offset) (lookupFuncaddr inst e.init))
        | none => tabs) (moduleInstTableBase m.tables)

@[rocq_alias iriswasm.module_import_init_tabs]
def moduleImportInitTabs (m : Module) (inst : Instance) (wts : NatMap Tableinst) :
    NatMap Tableinst :=
  m.elem.foldl (fun wts e =>
    let itc := getImportTableCount m
    match e.table with
    | .tableidx k =>
      if k < itc then
        match inst.tab[k]? with
        | some tAddr =>
          match get? wts tAddr with
          | some t => insert wts tAddr
              (tableInitReplaceSingle t (assertConst1I32ToNat e.offset)
                (lookupFuncaddr inst e.init))
          | none => wts
        | none => wts
      else wts) wts

#rocq_ignore iriswasm.module_inst_mem_base_func "fresh memories retain their full descriptor"
def moduleInstMemBaseFunc (mt : MemoryType) : Memory := memMk mt

@[rocq_alias iriswasm.module_inst_mem_base]
def moduleInstMemBase (mmemtypes : List MemoryType) : List Memory :=
  mmemtypes.map moduleInstMemBaseFunc

theorem moduleInstMemBase_agree {mts : List MemoryType}
    (ht : ∀ mt ∈ mts, moduleMemTyping mt = true) :
    ∀ mem ∈ moduleInstMemBase mts, MemAgree mem := by
  intro mem hm
  obtain ⟨mt, hmt, rfl⟩ := List.mem_map.1 hm
  exact ⟨ht mt hmt, by simp [moduleInstMemBaseFunc, memMk, lengthMem, Nat.mul_comm]⟩

@[rocq_alias iriswasm.mem_init_replace_single]
def memInitReplaceSingle (mem : Memory) (offset : Nat) (bs : List Byte) : Memory :=
  { mem with data := mem.data.splice offset (bs.take (lengthMem mem - offset)) }

#rocq_ignore iriswasm.module_inst_build_mems "only actual literal offsets select a byte address"
def moduleInstBuildMems (m : Module) (_inst : Instance) : List Memory :=
  m.data.foldl (fun mems d =>
    let imc := getImportMemCount m
    match d.data with
    | .memidx k =>
      if k < imc then mems else
        match mems[k - imc]? with
        | some mem =>
          match literalDataOffset d.offset with
          | some off => mems.set (k - imc) (memInitReplaceSingle mem off d.init)
          | none => mems
        | none => mems) (moduleInstMemBase m.mems)

#rocq_ignore iriswasm.module_import_init_mems "only actual literal offsets select a byte address"
def moduleImportInitMems (m : Module) (inst : Instance) (wms : NatMap Memory) : NatMap Memory :=
  m.data.foldl (fun wms d =>
    let imc := getImportMemCount m
    match d.data with
    | .memidx k =>
      if k < imc then
        match inst.memory[k]? with
        | some mAddr =>
          match get? wms mAddr with
          | some mem =>
            match literalDataOffset d.offset with
            | some off => insert wms mAddr (memInitReplaceSingle mem off d.init)
            | none => wms
          | none => wms
        | none => wms
      else wms) wms

/-- The allocated globals, with a dummy initial value. -/
@[rocq_alias iriswasm.module_inst_build_globals]
def moduleInstBuildGlobals (mglobs : List ModuleGlob) : List Global :=
  mglobs.map fun mg => { mut_ := mg.type.mut_, val := bitzero mg.type.t }

@[rocq_alias iriswasm.global_init_replace_single]
def globalInitReplaceSingle (g : Global) (v : Value) : Global :=
  { mut_ := g.mut_, val := v }

@[rocq_alias iriswasm.module_inst_global_init]
def moduleInstGlobalInit : List Global → List Value → List Global
  | [], _ => []
  | g :: gs', [] => g :: gs'
  | g :: gs', gi :: gInits' => globalInitReplaceSingle g gi :: moduleInstGlobalInit gs' gInits'

@[rocq_alias iriswasm.module_inst_global_init_cat]
theorem module_inst_global_init_cat (gs1 gs2 : List Global) (gi1 gi2 : List Value)
    (h : gs1.length = gi1.length) :
    moduleInstGlobalInit (gs1 ++ gs2) (gi1 ++ gi2) =
      moduleInstGlobalInit gs1 gi1 ++ moduleInstGlobalInit gs2 gi2 := by
  induction gs1 generalizing gi1 with
  | nil => cases gi1 <;> simp_all [moduleInstGlobalInit]
  | cons g gs ih =>
    cases gi1 with
    | nil => simp at h
    | cons v gi => simp [moduleInstGlobalInit, ih gi (by simpa using h)]

section Iris_instantiation
variable [WasmG hlc GF]

@[rocq_alias iriswasm.module_inst_resources_func]
def moduleInstResourcesFunc (mfuncs : List ModuleFunc) (inst : Instance)
    (instF : List Funcaddr) : IProp GF :=
  iprop([∗list] f;addr ∈ mfuncs;instF,
    addr ↦[wf] (.funcNative inst
      (inst.types.getD (match f.type with | .typeidx k => k) (.tf [] [])) f.locals f.body))

@[rocq_alias iriswasm.module_inst_resources_tab]
def moduleInstResourcesTab (tabs : List Tableinst) (instT : List Tableaddr) : IProp GF :=
  iprop([∗list] tab;addr ∈ tabs;instT, addr ↦[wtblock] tab)

@[rocq_alias iriswasm.module_inst_resources_mem]
def moduleInstResourcesMem (mems : List Memory) (instM : List Memaddr) : IProp GF :=
  iprop([∗list] mem;addr ∈ mems;instM, addr ↦[wmblock] mem)

@[rocq_alias iriswasm.module_inst_resources_glob]
def moduleInstResourcesGlob (globs : List Global) (instG : List Globaladdr) : IProp GF :=
  iprop([∗list] g;addr ∈ globs;instG, addr ↦[wg] g)

/-- The four kinds of newly allocated resources. -/
@[rocq_alias iriswasm.module_inst_resources_wasm]
def moduleInstResourcesWasm (m : Module) (inst : Instance) (tabInits : List Tableinst)
    (memInits : List Memory) (globInits : List Global) : IProp GF :=
  iprop(moduleInstResourcesFunc m.funcs inst (inst.funcs.drop (getImportFuncCount m)) ∗
    moduleInstResourcesTab tabInits (inst.tab.drop (getImportTableCount m)) ∗
    moduleInstResourcesMem memInits (inst.memory.drop (getImportMemCount m)) ∗
    moduleInstResourcesGlob globInits (inst.globs.drop (getImportGlobalCount m)))

end Iris_instantiation

#rocq_ignore iriswasm.module_restrictions "literal data offsets may be i32 or i64"
/-- Offsets and global initialisers are restricted to constants. -/
def ModuleRestrictions (m : Module) : Prop :=
  (∃ vs : List Value, m.globals.map (·.init) = vs.map fun v => [BasicInstruction.const v]) ∧
  (∃ vi32s : List I32,
    m.elem.map (·.offset) = vi32s.map fun v => [BasicInstruction.const (.int32 v)]) ∧
  (∃ offsets : List AddressOperand,
    m.data.map (·.offset) = offsets.map fun a => [BasicInstruction.const a.value])

section Iris_instantiation
variable [WasmG hlc GF]

@[rocq_alias iriswasm.instantiation_resources_post_wasm]
def instantiationResourcesPostWasm (m : Module) (v_imps : List ModuleExport)
    (t_imps : List ExternT) (wfs : NatMap FunctionClosure) (wts : NatMap Tableinst)
    (wms : NatMap Memory) (wgs : NatMap Global) (idfstart : Option Nat) (inst : Instance) :
    IProp GF :=
  iprop(∃ (g_inits : List Value) (tabAllocs : List Tableinst) (memAllocs : List Memory)
      (globAllocs : List Global) (wts' : NatMap Tableinst) (wms' : NatMap Memory),
    importResourcesWasmTypecheck v_imps t_imps wfs wts' wms' wgs ∗
    ⌜inst.types = m.types ∧
      extFuncAddrs (v_imps.map (·.desc)) <+: inst.funcs ∧
      extTabAddrs (v_imps.map (·.desc)) <+: inst.tab ∧
      extMemAddrs (v_imps.map (·.desc)) <+: inst.memory ∧
      extGlobAddrs (v_imps.map (·.desc)) <+: inst.globs ∧
      checkStart m inst idfstart = true⌝ ∗
    ⌜tabAllocs = moduleInstBuildTables m inst⌝ ∗
    ⌜wts' = moduleImportInitTabs m inst wts⌝ ∗
    ⌜ModuleElemBoundCheckGmap wts (v_imps.map (·.desc)) m⌝ ∗
    ⌜memAllocs = moduleInstBuildMems m inst⌝ ∗
    ⌜wms' = moduleImportInitMems m inst wms⌝ ∗
    ⌜ModuleDataBoundCheckGmap wms (v_imps.map (·.desc)) m⌝ ∗
    ⌜ModuleGlobInitValues m g_inits⌝ ∗
    ⌜globAllocs = moduleInstGlobalInit (moduleInstBuildGlobals m.globals) g_inits⌝ ∗
    moduleInstResourcesWasm m inst tabAllocs memAllocs globAllocs)

end Iris_instantiation

@[rocq_alias iriswasm.BI_const_assert_const1_i32]
theorem BI_const_assert_const1_i32 (es : List Wasm.Expr) (vs : List I32)
    (h : es = vs.map fun v => [BasicInstruction.const (.int32 v)]) :
    those (es.map assertConst1I32) = some vs := by
  subst h
  induction vs with
  | nil => rfl
  | cons v vs ih => exact those_app [some v] _ [v] vs rfl ih

@[rocq_alias iriswasm.module_inst_build_tables_length]
theorem module_inst_build_tables_length (m : Module) (i : Instance) :
    (moduleInstBuildTables m i).length = m.tables.length := by
  unfold moduleInstBuildTables
  refine fold_left_preserve (fun tabs : List Tableinst => tabs.length = m.tables.length) _ _ _
    (by simp [moduleInstTableBase]) ?_
  rintro x ⟨⟨k⟩, o, i⟩ hx
  dsimp only
  split
  · exact hx
  · split <;> simp [hx]

/-! ### Allocation of fresh resources -/

private theorem alloc_list {V : Type} {G : genHeapGS Nat V GF NatMap} (dq : DFrac)
    (hp : ∀ (l : Nat) (v : V), ⊢ (pointsTo (G := G) l (DFrac.own 1) v ==∗
      pointsTo (G := G) l dq v : IProp GF)) :
    ∀ (nl l : List V), ⊢ (genHeapInterp (G := G) (gmapOfList l) ==∗
      genHeapInterp (G := G) (gmapOfList (l ++ nl)) ∗
        [∗list] i ↦ v ∈ nl, pointsTo (G := G) (l.length + i) dq v : IProp GF)
  | [], l => by
    simp only [List.append_nil]
    iintro Hσ
    imodintro
    isplitl [Hσ]
    · iexact Hσ
    · iapply BigSepL.bigSepL_nil.2; iempintro
  | v :: nl, l => by
    have key := alloc_list (G := G) dq hp nl (l ++ [v])
    rw [List.append_assoc, List.singleton_append, List.length_append, List.length_singleton] at key
    simp only [Nat.add_assoc, Nat.add_comm 1 _] at key
    iintro Hσ
    imod @genHeap_alloc _ _ _ _ _ G _ _ l.length v (by rw [gmap_of_list_lookup]; simp)
      $$ Hσ with ⟨Hσ, Hv, -⟩
    rw [← gmap_of_list_append]
    imod key $$ Hσ with ⟨Hσ, Hl⟩
    imod hp l.length v $$ Hv with Hv
    imodintro
    isplitl [Hσ]
    · iexact Hσ
    · iapply BigSepL.bigSepL_cons.2
      isplitl [Hv]
      · iexact Hv
      · iexact Hl

private theorem gmapOfList2d_snoc {V : Type} (ll : List (List V)) (r : List V) (b : V) :
    insert (gmapOfList2d (ll ++ [r])) (ll.length, r.length) b = gmapOfList2d (ll ++ [r ++ [b]]) := by
  apply LawfulPartialMap.equiv_iff_eq.1
  rintro ⟨i, j⟩
  rw [LawfulPartialMap.get?_insert, gmap_of_list_2d_lookup, gmap_of_list_2d_lookup]
  by_cases hi : i = ll.length
  · subst hi
    by_cases hj : j = r.length
    · subst hj; simp
    · simp [Ne.symm hj, List.getElem?_append]
      grind
  · simp only [Prod.mk.injEq, Ne.symm hi, false_and, ↓reduceIte, List.getElem?_append]
    grind

private theorem gmapOfList2d_nil_row {V : Type} (ll : List (List V)) :
    gmapOfList2d (ll ++ [[]]) = gmapOfList2d ll := by
  apply LawfulPartialMap.equiv_iff_eq.1
  rintro ⟨i, j⟩
  rw [gmap_of_list_2d_lookup, gmap_of_list_2d_lookup, List.getElem?_append]
  grind

private theorem alloc_row {V : Type} {G : genHeapGS (Nat × Nat) V GF NatPairMap}
    (ll : List (List V)) : ∀ (r pre : List V), ⊢ (genHeapInterp (G := G) (gmapOfList2d (ll ++ [pre])) ==∗
      genHeapInterp (G := G) (gmapOfList2d (ll ++ [pre ++ r])) ∗
        [∗list] j ↦ e ∈ r, pointsTo (G := G) (ll.length, pre.length + j) (DFrac.own 1) e : IProp GF)
  | [], pre => by
    simp only [List.append_nil]
    iintro Hσ
    imodintro
    isplitl [Hσ]
    · iexact Hσ
    · iapply BigSepL.bigSepL_nil.2; iempintro
  | b :: r, pre => by
    have key := alloc_row (G := G) ll r (pre ++ [b])
    rw [List.append_assoc pre, List.singleton_append, List.length_append, List.length_singleton] at key
    simp only [Nat.add_assoc, Nat.add_comm 1 _] at key
    iintro Hσ
    imod @genHeap_alloc _ _ _ _ _ G _ _ (ll.length, pre.length) b
      (by rw [gmap_of_list_2d_lookup]; simp) $$ Hσ with ⟨Hσ, Hv, -⟩
    rw [gmapOfList2d_snoc]
    imod key $$ Hσ with ⟨Hσ, Hl⟩
    imodintro
    isplitl [Hσ]
    · iexact Hσ
    · iapply BigSepL.bigSepL_cons.2
      isplitl [Hv]
      · iexact Hv
      · iexact Hl

private theorem alloc_rows {V : Type} {G : genHeapGS (Nat × Nat) V GF NatPairMap} :
    ∀ (nl ll : List (List V)), ⊢ (genHeapInterp (G := G) (gmapOfList2d ll) ==∗
      genHeapInterp (G := G) (gmapOfList2d (ll ++ nl)) ∗
        [∗list] i ↦ r ∈ nl, [∗list] j ↦ e ∈ r,
          pointsTo (G := G) (ll.length + i, j) (DFrac.own 1) e : IProp GF)
  | [], ll => by
    simp only [List.append_nil]
    iintro Hσ
    imodintro
    isplitl [Hσ]
    · iexact Hσ
    · iapply BigSepL.bigSepL_nil.2; iempintro
  | r :: nl, ll => by
    have hrow := alloc_row (G := G) ll r []
    rw [gmapOfList2d_nil_row, List.nil_append] at hrow
    simp only [List.length_nil, Nat.zero_add] at hrow
    have key := alloc_rows (G := G) nl (ll ++ [r])
    rw [List.append_assoc, List.singleton_append, List.length_append, List.length_singleton] at key
    simp only [Nat.add_assoc, Nat.add_comm 1 _] at key
    iintro Hσ
    imod hrow $$ Hσ with ⟨Hσ, Hr⟩
    imod key $$ Hσ with ⟨Hσ, Hl⟩
    imodintro
    isplitl [Hσ]
    · iexact Hσ
    · iapply BigSepL.bigSepL_cons.2
      isplitl [Hr]
      · iexact Hr
      · iexact Hl

section Iris_instantiation
variable [WasmG hlc GF]

@[rocq_alias iriswasm.alloc_func_state_update]
theorem alloc_func_state_update (funcs funcs' nf : List FunctionClosure)
    (h : funcs' = funcs ++ nf) :
    ⊢ genHeapInterp (G := WasmG.funcHs) (gmapOfList funcs) -∗ |==>
      (genHeapInterp (G := WasmG.funcHs) (gmapOfList funcs') ∗
        [∗list] i ↦ v ∈ nf, (funcs.length + i) ↦[wf] v : IProp GF) := by
  subst h
  exact alloc_list (DFrac.own 1) (fun _ _ => by iintro H; imodintro; iexact H) nf funcs

@[rocq_alias iriswasm.alloc_tab_state_update]
theorem alloc_tab_state_update (tabs tabs' nt : List Tableinst) (h : tabs' = tabs ++ nt) :
    ⊢ genHeapInterp (G := WasmG.tabHs) (gmapOfTable tabs) -∗
      genHeapInterp (G := WasmG.tabsizeHs) (gmapOfList (tabs.map tabSize)) -∗
      genHeapInterp (G := WasmG.tablimitHs) (gmapOfList (tabs.map (·.maxOpt))) -∗ |==>
      (genHeapInterp (G := WasmG.tabHs) (gmapOfTable tabs') ∗
        genHeapInterp (G := WasmG.tabsizeHs) (gmapOfList (tabs'.map tabSize)) ∗
        genHeapInterp (G := WasmG.tablimitHs) (gmapOfList (tabs'.map (·.maxOpt))) ∗
        [∗list] i ↦ v ∈ nt, (tabs.length + i) ↦[wtblock] v : IProp GF) := by
  subst h
  have h1 := alloc_rows (GF := GF) (G := WasmG.tabHs) (nt.map tableToList) (tabs.map tableToList)
  have h2 := alloc_list (GF := GF) (G := WasmG.tabsizeHs) DFrac.discard (fun _ _ => @pointsTo_persist _ _ _ _ _ WasmG.tabsizeHs _ _ _)
    (nt.map tabSize) (tabs.map tabSize)
  have h3 := alloc_list (GF := GF) (G := WasmG.tablimitHs) DFrac.discard (fun _ _ => @pointsTo_persist _ _ _ _ _ WasmG.tablimitHs _ _ _)
    (nt.map (·.maxOpt)) (tabs.map (·.maxOpt))
  simp only [List.length_map, BigSepL.bigSepL_map, tableToList] at h1 h2 h3
  unfold gmapOfTable tabBlock
  simp only [List.map_append]
  iintro Ht Hts Htl
  imod h1 $$ Ht with ⟨Ht, Hb⟩
  imod h2 $$ Hts with ⟨Hts, Hbs⟩
  imod h3 $$ Htl with ⟨Htl, Hbl⟩
  imodintro
  iframe
  iapply BigSepL.bigSepL_sep_eqv.2
  isplitl [Hb]
  · iexact Hb
  · iapply BigSepL.bigSepL_sep_eqv.2
    isplitl [Hbs]
    · iexact Hbs
    · iexact Hbl

#rocq_ignore iriswasm.alloc_mem_state_update "new memory blocks require valid descriptors and extents"
theorem alloc_mem_state_update (mems mems' nm : List Memory) (h : mems' = mems ++ nm)
    (hagree : ∀ mem ∈ nm, MemAgree mem) :
    ⊢ genHeapInterp (G := WasmG.memHs) (gmapOfMemory mems) -∗
      genHeapInterp (G := WasmG.memsizeHs) (gmapOfList (mems.map memLengthMeta)) -∗
      genHeapInterp (G := WasmG.memlimitHs) (gmapOfList (mems.map (·.type.limits.max))) -∗ |==>
      (genHeapInterp (G := WasmG.memHs) (gmapOfMemory mems') ∗
        genHeapInterp (G := WasmG.memsizeHs) (gmapOfList (mems'.map memLengthMeta)) ∗
        genHeapInterp (G := WasmG.memlimitHs) (gmapOfList (mems'.map (·.type.limits.max))) ∗
        [∗list] i ↦ v ∈ nm, (mems.length + i) ↦[wmblock] v : IProp GF) := by
  subst h
  have h1 := alloc_rows (GF := GF) (G := WasmG.memHs) (nm.map memoryToList) (mems.map memoryToList)
  have h2 := alloc_list (GF := GF) (G := WasmG.memsizeHs) (DFrac.own 1)
    (fun _ _ => by iintro H; imodintro; iexact H) (nm.map memLengthMeta) (mems.map memLengthMeta)
  have h3 := alloc_list (GF := GF) (G := WasmG.memlimitHs) DFrac.discard (fun _ _ => @pointsTo_persist _ _ _ _ _ WasmG.memlimitHs _ _ _)
    (nm.map (·.type.limits.max)) (mems.map (·.type.limits.max))
  simp only [List.length_map, BigSepL.bigSepL_map, memoryToList] at h1 h2 h3
  unfold gmapOfMemory memBlock
  simp only [List.map_append]
  iintro Ht Hts Htl
  imod h1 $$ Ht with ⟨Ht, Hb⟩
  imod h2 $$ Hts with ⟨Hts, Hbs⟩
  imod h3 $$ Htl with ⟨Htl, Hbl⟩
  imodintro
  iframe
  iapply BigSepL.bigSepL_sep_eqv.2
  isplitr
  · iapply BigSepL.bigSepL_pure.2
    ipureintro; exact fun _ _ hv => hagree _ (List.mem_of_getElem? hv)
  iapply BigSepL.bigSepL_sep_eqv.2
  isplitl [Hb]
  · iexact Hb
  · iapply BigSepL.bigSepL_sep_eqv.2
    isplitl [Hbs]
    · iapply (BigSepL.bigSepL_mono (l := nm) ?_) $$ Hbs
      intro k mem hm
      have hmin := (hagree mem (List.mem_of_getElem? hm)).min_eq
      simp only [memLengthMeta, hmin, memSize, memLengthToken] <;> exact .rfl
    · iexact Hbl

@[rocq_alias iriswasm.alloc_glob_state_update]
theorem alloc_glob_state_update (globs globs' ng : List Global) (h : globs' = globs ++ ng) :
    ⊢ genHeapInterp (G := WasmG.globHs) (gmapOfList globs) -∗ |==>
      (genHeapInterp (G := WasmG.globHs) (gmapOfList globs') ∗
        [∗list] i ↦ v ∈ ng, (globs.length + i) ↦[wg] v : IProp GF) := by
  subst h
  exact alloc_list (DFrac.own 1) (fun _ _ => by iintro H; imodintro; iexact H) ng globs

end Iris_instantiation

/-! ### Table initialisation -/

/-- Splitting a one-element overwrite off a block overwrite (shared by tables and memories). -/
private theorem take_drop_shift {α : Type} (L td : List α) (t : α) (off : Nat)
    (h : off + 1 + td.length ≤ L.length) :
    (L.take off ++ [t] ++ L.drop (off + 1)).take (off + 1) ++ td ++
      (L.take off ++ [t] ++ L.drop (off + 1)).drop (off + 1 + td.length) =
    L.take off ++ t :: td ++ L.drop (off + (td.length + 1)) := by
  have hl : (L.take off ++ [t]).length = off + 1 := by simp; omega
  rw [List.take_append, List.drop_append, hl,
    List.take_of_length_le (l := L.take off ++ [t]) (by rw [hl]; omega),
    List.drop_of_length_le (l := L.take off ++ [t]) (by rw [hl]; omega)]
  simp [List.drop_drop]; omega

@[rocq_alias iriswasm.update_tab]
def updateTab (tab : Tableinst) (off : Nat) (td' : List Funcelem) : Option Tableinst :=
  if off + td'.length ≤ tab.entries.size then
    some { tab with entries := tab.entries.overwrite off td' }
  else none

@[rocq_alias iriswasm.update_tabs]
def updateTabs (tabs : List Tableinst) (off n : Nat) (td' : List Funcelem) :
    Option (List Tableinst) :=
  match tabs[n]? with
  | some tab =>
    match updateTab tab off td' with
    | some tab' => some (tabs.set n tab')
    | none => none
  | none => none

@[rocq_alias iriswasm.update_tab_length]
theorem update_tab_length (tab : Tableinst) (off : Nat) (td' : List Funcelem) (tab' : Tableinst)
    (h : updateTab tab off td' = some tab') : tab.data.length = tab'.data.length := by
  unfold updateTab at h
  split at h
  · cases h
    simpa only [Tableinst.length_data] using
      (RunTable.size_overwrite_of_le tab.entries off td' ‹_›).symm
  · cases h

@[rocq_alias iriswasm.update_tab_nil_id]
theorem update_tab_nil_id (tab : Tableinst) (off : Nat) (tab' : Tableinst)
    (h : updateTab tab off [] = some tab') : tab = tab' := by
  unfold updateTab at h
  split at h
  · cases h; rfl
  · cases h

@[rocq_alias iriswasm.update_tabs_nil_id]
theorem update_tabs_nil_id (tabs : List Tableinst) (n off : Nat) (tabs' : List Tableinst)
    (h : updateTabs tabs off n [] = some tabs') : tabs = tabs' := by
  unfold updateTabs at h
  split at h
  · split at h
    · rename_i tab _ tab' htab
      cases h
      cases update_tab_nil_id _ _ _ htab
      obtain ⟨hn, rfl⟩ := List.getElem?_eq_some_iff.1 tab
      simp
    · cases h
  · cases h

@[rocq_alias iriswasm.update_tab_shift]
theorem update_tab_shift (tab tab' : Tableinst) (off : Nat) (t : Funcelem) (td' : List Funcelem)
    (h : updateTab tab off (t :: td') = some tab') :
    ∃ tab0, updateTab tab off [t] = some tab0 ∧ updateTab tab0 (off + 1) td' = some tab' := by
  unfold updateTab at h ⊢
  split at h
  · cases h
    rename_i hle
    simp only [List.length_cons] at hle
    have hb : off + [t].length ≤ tab.entries.size := by simp only [List.length_singleton]; omega
    have hs := RunTable.size_overwrite_of_le tab.entries off [t] hb
    have ht : off + 1 + td'.length ≤ (tab.entries.overwrite off [t]).size := by omega
    refine ⟨_, ite_eq_left hb, ?_⟩
    rw [ite_eq_left ht]
    congr 2
    apply RunTable.ext_toList
    simpa only [RunTable.toList_overwrite, List.length_cons, List.length_nil, Nat.zero_add] using
      take_drop_shift tab.entries.toList td' t off (by simpa only [RunTable.length_toList] using
        (show off + 1 + td'.length ≤ tab.entries.size by omega))
  · cases h

@[rocq_alias iriswasm.update_tabs_shift]
theorem update_tabs_shift (tabs tabs' : List Tableinst) (off n : Nat) (t : Funcelem)
    (td' : List Funcelem) (h : updateTabs tabs off n (t :: td') = some tabs') :
    ∃ tabs0, updateTabs tabs off n [t] = some tabs0 ∧
      updateTabs tabs0 (off + 1) n td' = some tabs' := by
  unfold updateTabs at h ⊢
  split at h
  · rename_i tab htab
    split at h
    · rename_i tab' htab'
      cases h
      obtain ⟨tab0, h0, h1⟩ := update_tab_shift _ _ _ _ _ htab'
      have hn : n < tabs.length := (List.getElem?_eq_some_iff.1 htab).1
      refine ⟨tabs.set n tab0, by simp only [h0], ?_⟩
      simp [List.getElem?_set_self hn, h1]
    · cases h
  · cases h

section Iris_instantiation
variable [WasmG hlc GF]

@[rocq_alias iriswasm.tab_block_update_aux]
theorem tab_block_update_aux (off : Nat) (td td' : List Funcelem) (n : Nat)
    (tabs tabs' : List Tableinst) (hlen : td.length = td'.length)
    (h : updateTabs tabs off n td' = some tabs') :
    ⊢ ([∗list] i ↦ telem ∈ td, n ↦[wt][ off + i ] telem) -∗
      genHeapInterp (G := WasmG.tabHs) (gmapOfTable tabs) -∗ |==>
      (([∗list] i ↦ telem ∈ td', n ↦[wt][ off + i ] telem) ∗
        genHeapInterp (G := WasmG.tabHs) (gmapOfTable tabs') : IProp GF) := by
  induction td generalizing tabs tabs' td' off with
  | nil =>
    cases td' with
    | cons => simp at hlen
    | nil =>
      cases update_tabs_nil_id _ _ _ _ h
      iintro Htm Ht
      imodintro
      isplitl [Htm]
      · iexact Htm
      · iexact Ht
  | cons a td ih =>
    cases td' with
    | nil => simp at hlen
    | cons b td' =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      obtain ⟨tabs0, h1, h2⟩ := update_tabs_shift _ _ _ _ _ _ h
      have key := ih (off + 1) td' tabs0 tabs' hlen h2
      simp only [show ∀ k, off + 1 + k = off + (k + 1) from fun k => by omega] at key
      have hins : insert (gmapOfTable tabs) (n, off + 0) b = gmapOfTable tabs0 := by
        rcases htab : tabs[n]? with _ | tab
        · simp [updateTabs, htab] at h1
        · simp only [updateTabs, htab, updateTab] at h1
          by_cases hle : off + 1 ≤ tab.entries.size
          · simp only [List.length_singleton, hle, ite_true, Option.some.injEq] at h1
            subst h1
            have ho : off < tab.data.length := by rw [Tableinst.length_data]; omega
            apply gmap_of_table_insert n off b tabs tab htab ho
            simp only [Tableinst.data, RunTable.toList_overwrite, List.length_singleton]
            exact (insert_take_drop off tab.data b ho).symm
          · simp [hle] at h1
      iintro Htm Ht
      icases Htm with ⟨H0, Htm⟩
      imod @genHeap_update _ _ _ _ _ WasmG.tabHs _ _ _ _ b $$ [$Ht $H0] with ⟨Ht, H0⟩
      rw [hins]
      imod key $$ Htm Ht with ⟨Htm, Ht⟩
      imodintro
      isplitl [H0 Htm]
      · isplitl [H0]
        · iexact H0
        · iexact Htm
      · iexact Ht

@[rocq_alias iriswasm.tab_block_update]
theorem tab_block_update (tab tab' : Tableinst) (n : Nat) (ws ws' : StoreRecord)
    (hsize : tabSize tab = tabSize tab') (hmax : tab.maxOpt = tab'.maxOpt)
    (hws : ws'.tables = ws.tables.set n tab') :
    ⊢ n ↦[wtblock] tab -∗
      genHeapInterp (G := WasmG.tabHs) (gmapOfTable ws.tables) -∗
      genHeapInterp (G := WasmG.tabsizeHs) (gmapOfList (ws.tables.map tabSize)) -∗
      genHeapInterp (G := WasmG.tablimitHs) (gmapOfList (ws.tables.map (·.maxOpt))) -∗ |==>
      (n ↦[wtblock] tab' ∗
        genHeapInterp (G := WasmG.tabHs) (gmapOfTable ws'.tables) ∗
        genHeapInterp (G := WasmG.tabsizeHs) (gmapOfList (ws'.tables.map tabSize)) ∗
        genHeapInterp (G := WasmG.tablimitHs) (gmapOfList (ws'.tables.map (·.maxOpt))) :
        IProp GF) := by
  iintro Hb Ht Hts Htl
  ihave %htab := tab_block_lookup ws.tables n tab $$ Ht Hts Htl Hb
  have hn := (List.getElem?_eq_some_iff.1 htab).1
  have e1 : ws'.tables.map tabSize = ws.tables.map tabSize := by
    rw [hws, List.map_set, ← hsize]
    apply List.ext_getElem?; intro i
    rw [List.getElem?_set]; split <;> simp_all
  have e2 : ws'.tables.map (·.maxOpt) = ws.tables.map (·.maxOpt) := by
    rw [hws, List.map_set, ← hmax]
    apply List.ext_getElem?; intro i
    rw [List.getElem?_set]; split <;> simp_all
  have hlen : tab.data.length = tab'.data.length := by simpa [tabSize] using hsize
  have hreplace : tab.entries.overwrite 0 tab'.data = tab'.entries := by
    apply RunTable.ext_toList
    rw [RunTable.toList_overwrite]
    change tab.data.take 0 ++ tab'.data ++ tab.data.drop (0 + tab'.data.length) = tab'.data
    simp only [Nat.zero_add, ← hlen, List.take_zero, List.nil_append, List.drop_length,
      List.append_nil]
  have key := tab_block_update_aux (GF := GF) 0 tab.data tab'.data n ws.tables ws'.tables hlen
    (by
      obtain ⟨d', o'⟩ := tab'
      change tab.entries.size = d'.size at hsize
      change tab.maxOpt = o' at hmax
      simp [updateTabs, htab, updateTab, hreplace, hsize, hws, hmax])
  simp only [Nat.zero_add] at key
  rw [e1, e2]
  unfold tabBlock
  rw [← hsize, ← hmax]
  icases Hb with ⟨Htm, Hsz, Hlim⟩
  imod key $$ Htm Ht with ⟨Htm, Ht⟩
  imodintro
  iframe

@[rocq_alias iriswasm.init_tab_state_update]
theorem init_tab_state_update (ws ws' : StoreRecord) (inst : Instance) (e_off : Nat)
    (e : ModuleElement) (t_ind : Nat) (tab : Tableinst) (e_pay : List Funcelem)
    (hinit : initTab ws inst e_off e = ws')
    (hind : t_ind = inst.tab.getD (match e.table with | .tableidx i => i) 0)
    (hpay : e_pay = e.init.map fun | .funcidx j => inst.funcs[j]?)
    (hbound : e_off + e.init.length ≤ tab.entries.size) :
    ⊢ t_ind ↦[wtblock] tab -∗
      genHeapInterp (G := WasmG.tabHs) (gmapOfTable ws.tables) -∗
      genHeapInterp (G := WasmG.tabsizeHs) (gmapOfList (ws.tables.map tabSize)) -∗
      genHeapInterp (G := WasmG.tablimitHs) (gmapOfList (ws.tables.map (·.maxOpt))) -∗ |==>
      (t_ind ↦[wtblock] { tab with entries := tab.entries.overwrite e_off e_pay } ∗
        genHeapInterp (G := WasmG.tabHs) (gmapOfTable ws'.tables) ∗
        genHeapInterp (G := WasmG.tabsizeHs) (gmapOfList (ws'.tables.map tabSize)) ∗
        genHeapInterp (G := WasmG.tablimitHs) (gmapOfList (ws'.tables.map (·.maxOpt))) :
        IProp GF) := by
  iintro Hb Ht Hts Htl
  ihave %htab := tab_block_lookup ws.tables t_ind tab $$ Ht Hts Htl Hb
  have hn := (List.getElem?_eq_some_iff.1 htab).1
  have hb := tab_block_update (GF := GF) tab { tab with entries := tab.entries.overwrite e_off e_pay }
    t_ind ws ws' (RunTable.size_overwrite_of_le tab.entries e_off e_pay
      (by simpa [hpay] using hbound)).symm rfl
    (by
      subst hinit hpay
      obtain ⟨⟨k⟩, eo, ei⟩ := e
      simp only [List.getD_eq_getElem?_getD] at hind
      subst hind
      obtain ⟨d, o⟩ := tab
      simp only [initTab, List.getD_eq_getElem?_getD, htab, Option.getD_some]
      rw [insert_at_insert _ _ _ hn])
  iapply hb $$ Hb Ht Hts Htl

end Iris_instantiation

@[rocq_alias iriswasm.update_wts]
def updateWts (wts : NatMap Tableinst) (inst : Instance) :
    List Nat → List ModuleElement → Option (NatMap Tableinst)
  | _, [] => some wts
  | off :: eOffs', e :: elems' =>
    match e.table with
    | .tableidx n =>
      match inst.tab[n]? with
      | some i =>
        match get? wts i with
        | some tab =>
          match updateTab tab off (e.init.map fun | .funcidx j => inst.funcs[j]?) with
          | some tab' => updateWts (insert wts i tab') inst eOffs' elems'
          | none => none
        | none => none
      | none => none
  | [], _ :: _ => none

@[rocq_alias iriswasm.update_wts_partial]
def updateWtsPartial (wts : NatMap Tableinst) (inst : Instance) :
    List Nat → List ModuleElement → Option (NatMap Tableinst)
  | _, [] => some wts
  | off :: eOffs', e :: elems' =>
    match e.table with
    | .tableidx n =>
      match inst.tab[n]? with
      | some i =>
        match get? wts i with
        | some tab =>
          match updateTab tab off (e.init.map fun | .funcidx j => inst.funcs[j]?) with
          | some tab' => updateWtsPartial (insert wts i tab') inst eOffs' elems'
          | none => none
        | none => updateWtsPartial wts inst eOffs' elems'
      | none => none
  | [], _ :: _ => none

private theorem dom_insert_some {V : Type} {m : NatMap V} {i : Nat} {x y : V}
    (h : get? m i = some x) (k : Nat) :
    PartialMap.dom (insert m i y) k ↔ PartialMap.dom m k := by
  rw [LawfulPartialMap.dom_insert_iff]
  refine ⟨?_, Or.inr⟩
  rintro (rfl | h')
  · simp [PartialMap.dom, h]
  · exact h'

/-- Inserting at a key of `m₂` commutes with a left-biased union whose left side misses it. -/
private theorem insert_union_right {V : Type} {m₁ m₂ : NatMap V} {i : Nat} {x : V}
    (h : get? m₁ i = none) : insert (m₁ ∪ m₂) i x = m₁ ∪ insert m₂ i x := by
  apply LawfulPartialMap.equiv_iff_eq.mp
  intro k
  simp only [LawfulPartialMap.get?_union, LawfulPartialMap.get?_insert]
  split
  · subst_vars; simp [h, Option.orElse]
  · rfl

private theorem updateTab_maxOpt {tab tab' : Tableinst} {off : Nat} {td : List Funcelem}
    (h : updateTab tab off td = some tab') : tab'.maxOpt = tab.maxOpt := by
  unfold updateTab at h
  split at h
  · cases h; rfl
  · cases h

@[rocq_alias iriswasm.update_wts_dom_preserve]
theorem update_wts_dom_preserve (wts wts' : NatMap Tableinst) (inst : Instance)
    (e_offs : List Nat) (elems : List ModuleElement)
    (h : updateWts wts inst e_offs elems = some wts') :
    ∀ k, PartialMap.dom wts k ↔ PartialMap.dom wts' k := by
  induction elems generalizing wts e_offs with
  | nil =>
    cases e_offs <;> (simp only [updateWts, Option.some.injEq] at h; subst h; exact fun _ => .rfl)
  | cons e elems ih =>
    cases e_offs with
    | nil => simp [updateWts] at h
    | cons off offs =>
      rcases e with ⟨⟨n⟩, o, ini⟩
      simp only [updateWts] at h
      rcases hi : inst.tab[n]? with _ | i <;> rw [hi] at h <;> simp only [reduceCtorEq] at h
      rcases hw : get? wts i with _ | tab <;> rw [hw] at h <;> simp only [reduceCtorEq] at h
      rcases hu : updateTab tab off _ with _ | tab' <;> rw [hu] at h <;>
        simp only [reduceCtorEq] at h
      intro k
      rw [← ih _ _ h k, dom_insert_some hw]

@[rocq_alias iriswasm.update_wts_partial_dom_preserve]
theorem update_wts_partial_dom_preserve (wts wts' : NatMap Tableinst) (inst : Instance)
    (e_offs : List Nat) (elems : List ModuleElement)
    (h : updateWtsPartial wts inst e_offs elems = some wts') :
    ∀ k, PartialMap.dom wts k ↔ PartialMap.dom wts' k := by
  induction elems generalizing wts e_offs with
  | nil =>
    cases e_offs <;>
      (simp only [updateWtsPartial, Option.some.injEq] at h; subst h; exact fun _ => .rfl)
  | cons e elems ih =>
    cases e_offs with
    | nil => simp [updateWtsPartial] at h
    | cons off offs =>
      rcases e with ⟨⟨n⟩, o, ini⟩
      simp only [updateWtsPartial] at h
      rcases hi : inst.tab[n]? with _ | i <;> rw [hi] at h <;> simp only [reduceCtorEq] at h
      rcases hw : get? wts i with _ | tab <;> rw [hw] at h <;> simp only at h
      · exact ih _ _ h
      rcases hu : updateTab tab off _ with _ | tab' <;> rw [hu] at h <;>
        simp only [reduceCtorEq] at h
      intro k
      rw [← ih _ _ h k, dom_insert_some hw]

@[rocq_alias iriswasm.update_wts_split]
theorem update_wts_split (wts' wts1 wts2 : NatMap Tableinst) (inst : Instance)
    (e_offs : List Nat) (elems : List ModuleElement) (hdisj : wts1 ##ₘ wts2)
    (h : updateWts (wts1 ∪ wts2) inst e_offs elems = some wts') :
    match updateWtsPartial wts1 inst e_offs elems with
    | some wts1' =>
      match updateWtsPartial wts2 inst e_offs elems with
      | some wts2' => wts' = wts1' ∪ wts2'
      | none => False
    | none => False := by
  induction elems generalizing wts1 wts2 e_offs with
  | nil =>
    cases e_offs <;>
      (simp only [updateWts, Option.some.injEq] at h; simp only [updateWtsPartial, h])
  | cons e elems ih =>
    cases e_offs with
    | nil => simp [updateWts] at h
    | cons off offs =>
      rcases e with ⟨⟨n⟩, o, ini⟩
      simp only [updateWts] at h
      simp only [updateWtsPartial]
      rcases hi : inst.tab[n]? with _ | i <;> rw [hi] at h <;> simp only [reduceCtorEq] at h ⊢
      rcases hw : get? (wts1 ∪ wts2) i with _ | tab <;> rw [hw] at h <;>
        simp only [reduceCtorEq] at h
      rcases hu : updateTab tab off _ with _ | tab' <;> rw [hu] at h <;>
        simp only [reduceCtorEq] at h
      rw [LawfulPartialMap.get?_union] at hw
      rcases h1 : get? wts1 i with _ | tab1 <;> rw [h1] at hw <;> simp only [Option.orElse] at hw
      · simp only [hw, hu]
        rw [insert_union_right h1] at h
        exact ih _ _ _ (LawfulPartialMap.disjoint_insert_right h1 hdisj) h
      · cases hw
        have h2 : get? wts2 i = none :=
          ((PartialMap.disjoint_iff _ _).1 hdisj i).resolve_left (by simp [h1])
        simp only [hu, h2]
        rw [LawfulPartialMap.union_insert_left] at h
        exact ih _ _ _ (LawfulPartialMap.disjoint_insert_left h2 hdisj) h

@[rocq_alias iriswasm.update_wts_partial_lookup_type]
theorem update_wts_partial_lookup_type (wts wts' : NatMap Tableinst) (inst : Instance)
    (e_offs : List Nat) (elems : List ModuleElement) (n : Nat) (tab : Tableinst) (tt : TableType)
    (h : updateWtsPartial wts inst e_offs elems = some wts') (hn : get? wts n = some tab)
    (htt : tabTyping tab tt = true) :
    ∃ tab', get? wts' n = some tab' ∧ tabTyping tab' tt = true := by
  induction elems generalizing wts tab e_offs with
  | nil =>
    cases e_offs <;>
      (simp only [updateWtsPartial, Option.some.injEq] at h; subst h; exact ⟨tab, hn, htt⟩)
  | cons e elems ih =>
    cases e_offs with
    | nil => simp [updateWtsPartial] at h
    | cons off offs =>
      rcases e with ⟨⟨k⟩, o, ini⟩
      simp only [updateWtsPartial] at h
      rcases hi : inst.tab[k]? with _ | i <;> rw [hi] at h <;> simp only [reduceCtorEq] at h
      rcases hw : get? wts i with _ | tab0 <;> rw [hw] at h <;> simp only at h
      · exact ih _ _ _ h hn htt
      rcases hu : updateTab tab0 off _ with _ | tab' <;> rw [hu] at h <;>
        simp only [reduceCtorEq] at h
      by_cases hin : i = n
      · subst hin
        rw [hn] at hw; cases hw
        refine ih _ _ tab' h (by simp [LawfulPartialMap.get?_insert]) ?_
        have hl := update_tab_length _ _ _ _ hu
        simp only [Tableinst.length_data] at hl
        simp only [tabTyping, tabSize] at htt ⊢
        simp only [← hl, updateTab_maxOpt hu]
        exact htt
      · exact ih _ _ _ h (by simp [LawfulPartialMap.get?_insert, hin, hn]) htt

@[rocq_alias iriswasm.wts_bound_check]
def wtsBoundCheck (wts : NatMap Tableinst) (inst : Instance) (e_offs : List Nat)
    (elems : List ModuleElement) : Bool :=
  List.all2 (fun off e =>
    match inst.tab[match e.table with | .tableidx i => i]? with
    | some i =>
      match get? wts i with
      | some ti => decide (off + e.init.length ≤ ti.entries.size)
      | none => false
    | none => false) e_offs elems

@[rocq_alias iriswasm.update_wts_Some]
theorem update_wts_Some (wts : NatMap Tableinst) (inst : Instance) (e_offs : List Nat)
    (elems : List ModuleElement) (h : wtsBoundCheck wts inst e_offs elems = true) :
    ∃ wts', updateWts wts inst e_offs elems = some wts' := by
  induction elems generalizing wts e_offs with
  | nil => cases e_offs <;> simp [updateWts]
  | cons e elems ih =>
    cases e_offs with
    | nil => simp [wtsBoundCheck] at h
    | cons off offs =>
      rcases e with ⟨⟨n⟩, o, ini⟩
      simp only [wtsBoundCheck, List.all2, Bool.and_eq_true] at h
      obtain ⟨h0, hrest⟩ := h
      simp only [updateWts]
      rcases hi : inst.tab[n]? with _ | i <;> rw [hi] at h0 <;> simp only [reduceCtorEq] at h0 ⊢
      rcases hw : get? wts i with _ | tab <;> rw [hw] at h0 <;> simp only [reduceCtorEq] at h0 ⊢
      have hle : off + (ini.map fun | .funcidx j => inst.funcs[j]?).length ≤ tab.entries.size := by
        simpa using h0
      have hu : updateTab tab off (ini.map fun | .funcidx j => inst.funcs[j]?) =
          some { tab with entries := tab.entries.overwrite off (ini.map fun | .funcidx j => inst.funcs[j]?) } := by
        simp only [updateTab, hle, ↓reduceIte]
      rw [hu]
      refine ih _ _ ?_
      have hl := update_tab_length _ _ _ _ hu
      simp only [Tableinst.length_data] at hl
      refine (congrArg (fun f => List.all2 f offs elems)
        (funext fun off' => funext fun e' => ?_)).trans hrest
      rcases e' with ⟨⟨n'⟩, o', ini'⟩
      dsimp only
      cases inst.tab[n']? with
      | none => rfl
      | some i' =>
        dsimp only
        rw [LawfulPartialMap.get?_insert]
        by_cases hii : i = i'
        · subst hii; simp only [↓reduceIte, hw, hl]
        · simp only [hii, ↓reduceIte]

section Iris_instantiation
variable [WasmG hlc GF]

@[rocq_alias iriswasm.init_tabs_state_update]
theorem init_tabs_state_update (ws ws' : StoreRecord) (inst : Instance) (e_offs : List Nat)
    (elems : List ModuleElement) (wts wts' : NatMap Tableinst)
    (hinit : initTabs ws inst e_offs elems = ws')
    (hbound : wtsBoundCheck wts inst e_offs elems = true)
    (hupd : updateWts wts inst e_offs elems = some wts') :
    ⊢ genHeapInterp (G := WasmG.tabHs) (gmapOfTable ws.tables) -∗
      genHeapInterp (G := WasmG.tabsizeHs) (gmapOfList (ws.tables.map tabSize)) -∗
      genHeapInterp (G := WasmG.tablimitHs) (gmapOfList (ws.tables.map (·.maxOpt))) -∗
      ([∗map] n ↦ tabinst ∈ wts, n ↦[wtblock] tabinst) -∗ |==>
      (genHeapInterp (G := WasmG.tabHs) (gmapOfTable ws'.tables) ∗
        genHeapInterp (G := WasmG.tabsizeHs) (gmapOfList (ws'.tables.map tabSize)) ∗
        genHeapInterp (G := WasmG.tablimitHs) (gmapOfList (ws'.tables.map (·.maxOpt))) ∗
        [∗map] n ↦ tabinst ∈ wts', n ↦[wtblock] tabinst : IProp GF) := by
  induction elems generalizing ws e_offs wts with
  | nil =>
    simp only [updateWts, Option.some.injEq] at hupd
    have : ws' = ws := by subst hinit; simp [initTabs]
    subst hupd this
    iintro Ht Hts Htl Hm
    imodintro
    iframe
  | cons e elems ih =>
    cases e_offs with
    | nil => simp [updateWts] at hupd
    | cons off offs =>
      rcases e with ⟨⟨k⟩, o, ini⟩
      simp only [wtsBoundCheck, List.all2, Bool.and_eq_true] at hbound
      obtain ⟨h0, hrest⟩ := hbound
      simp only [updateWts] at hupd
      rcases hi : inst.tab[k]? with _ | i <;> rw [hi] at h0 hupd <;>
        simp only [reduceCtorEq] at h0 hupd
      rcases hw : get? wts i with _ | tab <;> rw [hw] at h0 hupd <;>
        simp only [reduceCtorEq] at h0 hupd
      have hle : off + ini.length ≤ tab.entries.size := by simpa using h0
      let pay := ini.map fun | .funcidx j => inst.funcs[j]?
      let tab' := { tab with entries := tab.entries.overwrite off pay }
      have hu : updateTab tab off pay = some tab' := by
        simp only [pay, tab', updateTab, List.length_map, hle, ↓reduceIte]
      rw [hu] at hupd
      have hl := update_tab_length _ _ _ _ hu
      simp only [Tableinst.length_data] at hl
      have hb' : wtsBoundCheck (insert wts i tab') inst offs elems = true := by
        refine (congrArg (fun f => List.all2 f offs elems)
          (funext fun off' => funext fun e' => ?_)).trans hrest
        rcases e' with ⟨⟨n'⟩, o', ini'⟩
        dsimp only
        cases inst.tab[n']? with
        | none => rfl
        | some i' =>
          dsimp only
          rw [LawfulPartialMap.get?_insert]
          by_cases hii : i = i'
          · subst hii; simp only [↓reduceIte, hw, hl]
          · simp only [hii, ↓reduceIte]
      have key := ih _ offs _ (by rw [← hinit]; rfl) hb' hupd
      have hstep := init_tab_state_update (GF := GF) ws _ inst off ⟨⟨k⟩, o, ini⟩ i tab _ rfl
        (by simp [List.getD_eq_getElem?_getD, hi]) rfl hle
      iintro Ht Hts Htl Hm
      icases (BigSepM.bigSepM_delete hw).1 $$ Hm with ⟨Hb, Hm⟩
      imod hstep $$ Hb Ht Hts Htl with ⟨Hb, Ht, Hts, Htl⟩
      iapply key $$ Ht Hts Htl
      iapply BigSepM.bigSepM_insert_delete.2
      isplitl [Hb]
      · iexact Hb
      · iexact Hm

end Iris_instantiation

/-! ### Memory initialisation -/

@[rocq_alias iriswasm.update_mem]
def updateMem (mem : Memory) (off : Nat) (md : List Byte) : Option Memory :=
  if off + md.length ≤ lengthMem mem then some { mem with data := mem.data.splice off md }
  else none

private theorem updateMem_store (mem : Memory) (off : Nat) (md : List Byte) :
    updateMem mem off md = store mem 0 off md md.length := by
  rw [updateMem, store_eq]
  simp only [Nat.zero_add, bytesTakefill_of_length]
  split
  · congr 1
    exact MemEquiv.eq ⟨rfl, by simp only [MemoryList.data_splice, MemoryList.data_ofBytes]⟩
  · rfl

@[rocq_alias iriswasm.update_mems]
def updateMems (mems : List Memory) (off n : Nat) (md : List Byte) : Option (List Memory) :=
  match mems[n]? with
  | some mem =>
    match updateMem mem off md with
    | some mem' => some (mems.set n mem')
    | none => none
  | none => none

@[rocq_alias iriswasm.update_mem_length]
theorem update_mem_length (mem : Memory) (off : Nat) (md : List Byte) (mem' : Memory)
    (h : updateMem mem off md = some mem') : mem.data.data.length = mem'.data.data.length := by
  rw [updateMem_store] at h
  exact length_store _ _ _ _ _ h

@[rocq_alias iriswasm.update_mem_nil_id]
theorem update_mem_nil_id (mem : Memory) (off : Nat) (mem' : Memory)
    (h : updateMem mem off [] = some mem') : mem = mem' := by
  unfold updateMem at h
  split at h
  · cases h
    exact MemEquiv.eq ⟨rfl, by simp [MemoryList.data_splice]⟩
  · cases h

@[rocq_alias iriswasm.update_mems_nil_id]
theorem update_mems_nil_id (mems : List Memory) (n off : Nat) (mems' : List Memory)
    (h : updateMems mems off n [] = some mems') : mems = mems' := by
  unfold updateMems at h
  split at h
  · split at h
    · rename_i mem _ mem' hmem
      cases h
      cases update_mem_nil_id _ _ _ hmem
      obtain ⟨hn, rfl⟩ := List.getElem?_eq_some_iff.1 mem
      simp
    · cases h
  · cases h

@[rocq_alias iriswasm.update_mem_shift]
theorem update_mem_shift (mem mem' : Memory) (off : Nat) (t : Byte) (td' : List Byte)
    (h : updateMem mem off (t :: td') = some mem') :
    ∃ mem0, updateMem mem off [t] = some mem0 ∧ updateMem mem0 (off + 1) td' = some mem' := by
  simp only [updateMem_store] at h ⊢
  obtain ⟨m, hrest, hfirst⟩ := store_append1 _ _ _ _ _ _ h
  exact ⟨m, hfirst, hrest⟩

@[rocq_alias iriswasm.update_mems_shift]
theorem update_mems_shift (mems mems' : List Memory) (off n : Nat) (t : Byte) (td' : List Byte)
    (h : updateMems mems off n (t :: td') = some mems') :
    ∃ mems0, updateMems mems off n [t] = some mems0 ∧
      updateMems mems0 (off + 1) n td' = some mems' := by
  unfold updateMems at h ⊢
  split at h
  · rename_i mem hmem
    split at h
    · rename_i mem' hmem'
      cases h
      obtain ⟨mem0, h0, h1⟩ := update_mem_shift _ _ _ _ _ hmem'
      have hn : n < mems.length := (List.getElem?_eq_some_iff.1 hmem).1
      refine ⟨mems.set n mem0, by simp only [h0], ?_⟩
      simp [List.getElem?_set_self hn, h1]
    · cases h
  · cases h

section Iris_instantiation
variable [WasmG hlc GF]

@[rocq_alias iriswasm.mem_block_update_aux]
theorem mem_block_update_aux (off : Nat) (md md' : List Byte) (n : Nat)
    (mems mems' : List Memory) (hlen : md.length = md'.length)
    (h : updateMems mems off n md' = some mems') :
    ⊢ ([∗list] i ↦ mdata ∈ md, n ↦[wm][ off + i ] mdata) -∗
      genHeapInterp (G := WasmG.memHs) (gmapOfMemory mems) -∗ |==>
      (([∗list] i ↦ mdata ∈ md', n ↦[wm][ off + i ] mdata) ∗
        genHeapInterp (G := WasmG.memHs) (gmapOfMemory mems') : IProp GF) := by
  induction md generalizing mems mems' md' off with
  | nil =>
    cases md' with
    | cons => simp at hlen
    | nil =>
      cases update_mems_nil_id _ _ _ _ h
      iintro Htm Ht
      imodintro
      isplitl [Htm]
      · iexact Htm
      · iexact Ht
  | cons a md ih =>
    cases md' with
    | nil => simp at hlen
    | cons b md' =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      obtain ⟨mems0, h1, h2⟩ := update_mems_shift _ _ _ _ _ _ h
      have key := ih (off + 1) md' mems0 mems' hlen h2
      simp only [show ∀ k, off + 1 + k = off + (k + 1) from fun k => by omega] at key
      have hins : insert (gmapOfMemory mems) (n, off + 0) b = gmapOfMemory mems0 := by
        rcases hmem : mems[n]? with _ | mem
        · simp [updateMems, hmem] at h1
        · simp only [updateMems, hmem, updateMem] at h1
          by_cases hle : off + 1 ≤ lengthMem mem
          · simp only [List.length_singleton, hle, ite_true, Option.some.injEq] at h1
            subst h1
            have hi : off < mem.data.data.length := by rw [lengthMem_eq_data_length] at hle; omega
            rw [Nat.add_zero, gmap_of_memory_insert n off b mems mem (mem.data.splice off [b]) hmem hi]
            rw [MemoryList.update_eq, if_pos (by simpa only [MemoryList.length_data] using hi),
              ← MemoryList.ofBytes_data (mem.data.splice off [b]), MemoryList.data_splice,
              insert_take_drop _ _ _ hi, List.length_singleton]
          · simp [hle] at h1
      iintro Htm Ht
      icases Htm with ⟨H0, Htm⟩
      imod @genHeap_update _ _ _ _ _ WasmG.memHs _ _ _ _ b $$ [$Ht $H0] with ⟨Ht, H0⟩
      rw [hins]
      imod key $$ Htm Ht with ⟨Htm, Ht⟩
      imodintro
      isplitl [H0 Htm]
      · isplitl [H0]
        · iexact H0
        · iexact Htm
      · iexact Ht

#rocq_ignore iriswasm.mem_block_update "updating bytes preserves the entire memory descriptor"
theorem mem_block_update (mem mem' : Memory) (n : Nat) (ws ws' : StoreRecord)
    (hlen : lengthMem mem = lengthMem mem') (htype : mem.type = mem'.type)
    (hws : ws'.mems = ws.mems.set n mem') :
    ⊢ n ↦[wmblock] mem -∗
      genHeapInterp (G := WasmG.memHs) (gmapOfMemory ws.mems) -∗
      genHeapInterp (G := WasmG.memsizeHs) (gmapOfList (ws.mems.map memLengthMeta)) -∗
      genHeapInterp (G := WasmG.memlimitHs) (gmapOfList (ws.mems.map (·.type.limits.max))) -∗ |==>
      (n ↦[wmblock] mem' ∗
        genHeapInterp (G := WasmG.memHs) (gmapOfMemory ws'.mems) ∗
        genHeapInterp (G := WasmG.memsizeHs) (gmapOfList (ws'.mems.map memLengthMeta)) ∗
        genHeapInterp (G := WasmG.memlimitHs) (gmapOfList (ws'.mems.map (·.type.limits.max))) :
        IProp GF) := by
  iintro Hb Ht Hts Htl
  ihave %hm := mem_block_lookup ws.mems n mem $$ Ht Hts Htl Hb
  obtain ⟨m0, hm0, hd, ho⟩ := hm
  have hmem : ws.mems[n]? = some mem := by
    exact MemEquiv.eq (m₁ := m0) (m₂ := mem) ⟨ho, hd⟩ ▸ hm0
  have hn := (List.getElem?_eq_some_iff.1 hmem).1
  have hmeta : memLengthMeta mem = memLengthMeta mem' := by simp [memLengthMeta, hlen, htype]
  have e1 : ws'.mems.map memLengthMeta = ws.mems.map memLengthMeta := by
    rw [hws, List.map_set, ← hmeta]
    apply List.ext_getElem?; intro i
    rw [List.getElem?_set]; split <;> simp_all
  have e2 : ws'.mems.map (·.type.limits.max) = ws.mems.map (·.type.limits.max) := by
    rw [hws, List.map_set]
    simp only [← htype]
    apply List.ext_getElem?; intro i
    rw [List.getElem?_set]; split <;> simp_all
  have hlen' : mem.data.data.length = mem'.data.data.length := by
    simpa only [lengthMem_eq_data_length] using hlen
  have key := mem_block_update_aux (GF := GF) 0 mem.data.data mem'.data.data n ws.mems ws'.mems hlen'
    (by
      have hb : 0 + mem'.data.data.length ≤ lengthMem mem := by rw [lengthMem_eq_data_length]; omega
      have hm' : ({ mem with data := mem.data.splice 0 mem'.data.data } : Memory) = mem' :=
        MemEquiv.eq ⟨htype, by simp only [MemoryList.data_splice, Nat.zero_add, List.take_zero,
          List.nil_append, List.drop_eq_nil_of_le (Nat.le_of_eq hlen'), List.append_nil]⟩
      simp only [updateMems, hmem, updateMem, hb, ↓reduceIte, hm', hws])
  simp only [Nat.zero_add] at key
  rw [e1, e2]
  unfold memBlock
  rw [← hlen, ← htype]
  icases Hb with ⟨%hag, Htm, Hsz, Hlim⟩
  have hag' : MemAgree mem' := by simpa only [MemAgree, ← htype, ← hlen] using hag
  imod key $$ Htm Ht with ⟨Htm, Ht⟩
  imodintro
  iframe
  ipureintro; exact hag'

#rocq_ignore iriswasm.init_mem_state_update "write only to the successfully resolved memory"
theorem init_mem_state_update (ws ws' : StoreRecord) (inst : Instance) (d_off : Nat)
    (d : ModuleData) (m_ind : Nat) (mem : Memory) (d_pay : List Byte) (mem' : Memory)
    (hinit : initMem ws inst d_off d = .ok ws')
    (hind : inst.memory[match d.data with | .memidx i => i]? = some m_ind)
    (heqv : MemEquiv mem'
      { mem with data := mem.data.splice d_off d_pay })
    (hpay : d_pay = d.init)
    (hbound : d_off + d.init.length ≤ lengthMem mem) :
    ⊢ m_ind ↦[wmblock] mem -∗
      genHeapInterp (G := WasmG.memHs) (gmapOfMemory ws.mems) -∗
      genHeapInterp (G := WasmG.memsizeHs) (gmapOfList (ws.mems.map memLengthMeta)) -∗
      genHeapInterp (G := WasmG.memlimitHs) (gmapOfList (ws.mems.map (·.type.limits.max))) -∗ |==>
      (m_ind ↦[wmblock] mem' ∗
        genHeapInterp (G := WasmG.memHs) (gmapOfMemory ws'.mems) ∗
        genHeapInterp (G := WasmG.memsizeHs) (gmapOfList (ws'.mems.map memLengthMeta)) ∗
        genHeapInterp (G := WasmG.memlimitHs) (gmapOfList (ws'.mems.map (·.type.limits.max))) :
        IProp GF) := by
  iintro Hb Ht Hts Htl
  ihave %hm := mem_block_lookup ws.mems m_ind mem $$ Ht Hts Htl Hb
  obtain ⟨m0, hm0, hd, ho⟩ := hm
  have hmem : ws.mems[m_ind]? = some mem := by
    exact MemEquiv.eq (m₁ := m0) (m₂ := mem) ⟨ho, hd⟩ ▸ hm0
  have hb := mem_block_update (GF := GF) mem { mem with data := mem.data.splice d_off d_pay }
    m_ind ws ws' (by
      simp only [lengthMem_eq_data_length, MemoryList.data_splice, List.length_append,
        List.length_take, List.length_drop, hpay] at hbound ⊢; omega) rfl
    (by
      obtain ⟨i, m, hi, hm, -, rfl⟩ := initMem_ok_iff.mp hinit
      rw [hind] at hi; cases hi
      rw [hmem] at hm; cases hm
      subst hpay
      rfl)
  have e := mem_equiv_wmblock_rewrite (GF := GF) (n := m_ind) heqv
  imod hb $$ Hb Ht Hts Htl with ⟨Hb, Hrest⟩
  imodintro
  isplitl [Hb]
  · iapply e.2; iexact Hb
  · iexact Hrest

end Iris_instantiation

@[rocq_alias iriswasm.update_wms]
def updateWms (wms : NatMap Memory) (inst : Instance) :
    List Nat → List ModuleData → Option (NatMap Memory)
  | _, [] => some wms
  | off :: dOffs', d :: datas' =>
    match d.data with
    | .memidx n =>
      match inst.memory[n]? with
      | some i =>
        match get? wms i with
        | some mem =>
          match updateMem mem off d.init with
          | some mem' => updateWms (insert wms i mem') inst dOffs' datas'
          | none => none
        | none => none
      | none => none
  | [], _ :: _ => none

@[rocq_alias iriswasm.update_wms_partial]
def updateWmsPartial (wms : NatMap Memory) (inst : Instance) :
    List Nat → List ModuleData → Option (NatMap Memory)
  | _, [] => some wms
  | off :: dOffs', d :: datas' =>
    match d.data with
    | .memidx n =>
      match inst.memory[n]? with
      | some i =>
        match get? wms i with
        | some mem =>
          match updateMem mem off d.init with
          | some mem' => updateWmsPartial (insert wms i mem') inst dOffs' datas'
          | none => none
        | none => updateWmsPartial wms inst dOffs' datas'
      | none => none
  | [], _ :: _ => none

private theorem updateMem_type {mem mem' : Memory} {off : Nat} {md : List Byte}
    (h : updateMem mem off md = some mem') : mem'.type = mem.type := by
  unfold updateMem at h
  split at h
  · cases h; rfl
  · cases h

@[rocq_alias iriswasm.update_wms_dom_preserve]
theorem update_wms_dom_preserve (wms wms' : NatMap Memory) (inst : Instance)
    (d_offs : List Nat) (datas : List ModuleData)
    (h : updateWms wms inst d_offs datas = some wms') :
    ∀ k, PartialMap.dom wms k ↔ PartialMap.dom wms' k := by
  induction datas generalizing wms d_offs with
  | nil =>
    cases d_offs <;> (simp only [updateWms, Option.some.injEq] at h; subst h; exact fun _ => .rfl)
  | cons d datas ih =>
    cases d_offs with
    | nil => simp [updateWms] at h
    | cons off offs =>
      rcases d with ⟨⟨n⟩, o, ini⟩
      simp only [updateWms] at h
      rcases hi : inst.memory[n]? with _ | i <;> rw [hi] at h <;> simp only [reduceCtorEq] at h
      rcases hw : get? wms i with _ | mem <;> rw [hw] at h <;> simp only [reduceCtorEq] at h
      rcases hu : updateMem mem off _ with _ | mem' <;> rw [hu] at h <;>
        simp only [reduceCtorEq] at h
      intro k
      rw [← ih _ _ h k, dom_insert_some hw]

@[rocq_alias iriswasm.update_wms_partial_dom_preserve]
theorem update_wms_partial_dom_preserve (wms wms' : NatMap Memory) (inst : Instance)
    (d_offs : List Nat) (datas : List ModuleData)
    (h : updateWmsPartial wms inst d_offs datas = some wms') :
    ∀ k, PartialMap.dom wms k ↔ PartialMap.dom wms' k := by
  induction datas generalizing wms d_offs with
  | nil =>
    cases d_offs <;>
      (simp only [updateWmsPartial, Option.some.injEq] at h; subst h; exact fun _ => .rfl)
  | cons d datas ih =>
    cases d_offs with
    | nil => simp [updateWmsPartial] at h
    | cons off offs =>
      rcases d with ⟨⟨n⟩, o, ini⟩
      simp only [updateWmsPartial] at h
      rcases hi : inst.memory[n]? with _ | i <;> rw [hi] at h <;> simp only [reduceCtorEq] at h
      rcases hw : get? wms i with _ | mem <;> rw [hw] at h <;> simp only at h
      · exact ih _ _ h
      rcases hu : updateMem mem off _ with _ | mem' <;> rw [hu] at h <;>
        simp only [reduceCtorEq] at h
      intro k
      rw [← ih _ _ h k, dom_insert_some hw]

@[rocq_alias iriswasm.update_wms_split]
theorem update_wms_split (wms' wms1 wms2 : NatMap Memory) (inst : Instance)
    (d_offs : List Nat) (datas : List ModuleData) (hdisj : wms1 ##ₘ wms2)
    (h : updateWms (wms1 ∪ wms2) inst d_offs datas = some wms') :
    match updateWmsPartial wms1 inst d_offs datas with
    | some wms1' =>
      match updateWmsPartial wms2 inst d_offs datas with
      | some wms2' => wms' = wms1' ∪ wms2'
      | none => False
    | none => False := by
  induction datas generalizing wms1 wms2 d_offs with
  | nil =>
    cases d_offs <;>
      (simp only [updateWms, Option.some.injEq] at h; simp only [updateWmsPartial, h])
  | cons d datas ih =>
    cases d_offs with
    | nil => simp [updateWms] at h
    | cons off offs =>
      rcases d with ⟨⟨n⟩, o, ini⟩
      simp only [updateWms] at h
      simp only [updateWmsPartial]
      rcases hi : inst.memory[n]? with _ | i <;> rw [hi] at h <;> simp only [reduceCtorEq] at h ⊢
      rcases hw : get? (wms1 ∪ wms2) i with _ | mem <;> rw [hw] at h <;>
        simp only [reduceCtorEq] at h
      rcases hu : updateMem mem off _ with _ | mem' <;> rw [hu] at h <;>
        simp only [reduceCtorEq] at h
      rw [LawfulPartialMap.get?_union] at hw
      rcases h1 : get? wms1 i with _ | mem1 <;> rw [h1] at hw <;> simp only [Option.orElse] at hw
      · simp only [hw, hu]
        rw [insert_union_right h1] at h
        exact ih _ _ _ (LawfulPartialMap.disjoint_insert_right h1 hdisj) h
      · cases hw
        have h2 : get? wms2 i = none :=
          ((PartialMap.disjoint_iff _ _).1 hdisj i).resolve_left (by simp [h1])
        simp only [hu, h2]
        rw [LawfulPartialMap.union_insert_left] at h
        exact ih _ _ _ (LawfulPartialMap.disjoint_insert_left h2 hdisj) h

@[rocq_alias iriswasm.update_wms_partial_lookup_type]
theorem update_wms_partial_lookup_type (wms wms' : NatMap Memory) (inst : Instance)
    (d_offs : List Nat) (datas : List ModuleData) (n : Nat) (mem : Memory) (mt : MemoryType)
    (h : updateWmsPartial wms inst d_offs datas = some wms') (hn : get? wms n = some mem)
    (hmt : memTyping mem mt = true) :
    ∃ mem', get? wms' n = some mem' ∧ memTyping mem' mt = true := by
  induction datas generalizing wms mem d_offs with
  | nil =>
    cases d_offs <;>
      (simp only [updateWmsPartial, Option.some.injEq] at h; subst h; exact ⟨mem, hn, hmt⟩)
  | cons d datas ih =>
    cases d_offs with
    | nil => simp [updateWmsPartial] at h
    | cons off offs =>
      rcases d with ⟨⟨k⟩, o, ini⟩
      simp only [updateWmsPartial] at h
      rcases hi : inst.memory[k]? with _ | i <;> rw [hi] at h <;> simp only [reduceCtorEq] at h
      rcases hw : get? wms i with _ | mem0 <;> rw [hw] at h <;> simp only at h
      · exact ih _ _ _ h hn hmt
      rcases hu : updateMem mem0 off _ with _ | mem' <;> rw [hu] at h <;>
        simp only [reduceCtorEq] at h
      by_cases hin : i = n
      · subst hin
        rw [hn] at hw; cases hw
        refine ih _ _ mem' h (by simp [LawfulPartialMap.get?_insert]) ?_
        simpa only [memTyping, updateMem_type hu] using hmt
      · exact ih _ _ _ h (by simp [LawfulPartialMap.get?_insert, hin, hn]) hmt

@[rocq_alias iriswasm.wms_bound_check]
def wmsBoundCheck (wms : NatMap Memory) (inst : Instance) (d_offs : List Nat)
    (datas : List ModuleData) : Bool :=
  List.all2 (fun off e =>
    match inst.memory[match e.data with | .memidx i => i]? with
    | some i =>
      match get? wms i with
      | some mi => decide (off + e.init.length ≤ lengthMem mi)
      | none => false
    | none => false) d_offs datas

@[rocq_alias iriswasm.update_wms_Some]
theorem update_wms_Some (wms : NatMap Memory) (inst : Instance) (d_offs : List Nat)
    (datas : List ModuleData) (h : wmsBoundCheck wms inst d_offs datas = true) :
    ∃ wms', updateWms wms inst d_offs datas = some wms' := by
  induction datas generalizing wms d_offs with
  | nil => cases d_offs <;> simp [updateWms]
  | cons d datas ih =>
    cases d_offs with
    | nil => simp [wmsBoundCheck] at h
    | cons off offs =>
      rcases d with ⟨⟨n⟩, o, ini⟩
      simp only [wmsBoundCheck, List.all2, Bool.and_eq_true] at h
      obtain ⟨h0, hrest⟩ := h
      simp only [updateWms]
      rcases hi : inst.memory[n]? with _ | i <;> rw [hi] at h0 <;>
        simp only [reduceCtorEq] at h0 ⊢
      rcases hw : get? wms i with _ | mem <;> rw [hw] at h0 <;> simp only [reduceCtorEq] at h0 ⊢
      have hle : off + ini.length ≤ lengthMem mem := of_decide_eq_true h0
      have hu : updateMem mem off ini = some { mem with data := mem.data.splice off ini } := by
        simp only [updateMem, hle, ↓reduceIte]
      rw [hu]
      refine ih _ _ ?_
      have hl := update_mem_length _ _ _ _ hu
      refine (congrArg (fun f => List.all2 f offs datas)
        (funext fun off' => funext fun d' => ?_)).trans hrest
      rcases d' with ⟨⟨n'⟩, o', ini'⟩
      dsimp only
      cases inst.memory[n']? with
      | none => rfl
      | some i' =>
        dsimp only
        rw [LawfulPartialMap.get?_insert]
        by_cases hii : i = i'
        · subst hii
          simp only [↓reduceIte, hw, lengthMem_eq_data_length, ← hl]
        · simp only [hii, ↓reduceIte]

section Iris_instantiation
variable [WasmG hlc GF]

/-- Coq's `d_offnats = fmap N.to_nat d_offs` becomes `d_offnats = d_offs` (`N` is `Nat`). -/
@[rocq_alias iriswasm.init_mems_state_update]
theorem init_mems_state_update (ws ws' : StoreRecord) (inst : Instance)
    (d_offs d_offnats : List Nat) (datas : List ModuleData) (wms wms' : NatMap Memory)
    (hoffs : d_offnats = d_offs)
    (hinit : initMems ws inst d_offs datas = .ok ws')
    (hbound : wmsBoundCheck wms inst d_offs datas = true)
    (hupd : updateWms wms inst d_offnats datas = some wms') :
    ⊢ genHeapInterp (G := WasmG.memHs) (gmapOfMemory ws.mems) -∗
      genHeapInterp (G := WasmG.memsizeHs) (gmapOfList (ws.mems.map memLengthMeta)) -∗
      genHeapInterp (G := WasmG.memlimitHs) (gmapOfList (ws.mems.map (·.type.limits.max))) -∗
      ([∗map] n ↦ meminst ∈ wms, n ↦[wmblock] meminst) -∗ |==>
      (genHeapInterp (G := WasmG.memHs) (gmapOfMemory ws'.mems) ∗
        genHeapInterp (G := WasmG.memsizeHs) (gmapOfList (ws'.mems.map memLengthMeta)) ∗
        genHeapInterp (G := WasmG.memlimitHs) (gmapOfList (ws'.mems.map (·.type.limits.max))) ∗
        [∗map] n ↦ meminst ∈ wms', n ↦[wmblock] meminst : IProp GF) := by
  subst hoffs
  induction datas generalizing ws d_offnats wms with
  | nil =>
    simp only [updateWms, Option.some.injEq] at hupd
    have : ws = ws' := by cases d_offnats <;> cases hinit <;> rfl
    subst hupd this
    iintro Ht Hts Htl Hm
    imodintro
    iframe
  | cons d datas ih =>
    cases d_offnats with
    | nil => simp [updateWms] at hupd
    | cons off offs =>
      rcases d with ⟨⟨k⟩, o, ini⟩
      simp only [wmsBoundCheck, List.all2, Bool.and_eq_true] at hbound
      obtain ⟨h0, hrest⟩ := hbound
      simp only [updateWms] at hupd
      rcases hi : inst.memory[k]? with _ | i <;> rw [hi] at h0 hupd <;>
        simp only [reduceCtorEq] at h0 hupd
      rcases hw : get? wms i with _ | mem <;> rw [hw] at h0 hupd <;>
        simp only [reduceCtorEq] at h0 hupd
      have hle0 : off + ini.length ≤ lengthMem mem := of_decide_eq_true h0
      have hu : updateMem mem off ini = some { mem with data := mem.data.splice off ini } := by
        simp only [updateMem, hle0, ↓reduceIte]
      rw [hu] at hupd
      have hl := update_mem_length _ _ _ _ hu
      have hb' : wmsBoundCheck (insert wms i { mem with data := mem.data.splice off ini })
          inst offs datas = true := by
        refine (congrArg (fun f => List.all2 f offs datas)
          (funext fun off' => funext fun d' => ?_)).trans hrest
        rcases d' with ⟨⟨n'⟩, o', ini'⟩
        dsimp only
        cases inst.memory[n']? with
        | none => rfl
        | some i' =>
          dsimp only
          rw [LawfulPartialMap.get?_insert]
          by_cases hii : i = i'
          · subst hii
            simp only [↓reduceIte, hw, lengthMem_eq_data_length, ← hl]
          · simp only [hii, ↓reduceIte]
      obtain ⟨mid, hhead, htail⟩ := initMems_cons.mp hinit
      have key := ih mid offs _ hupd htail hb'
      have hstep := init_mem_state_update (GF := GF) ws mid inst off ⟨⟨k⟩, o, ini⟩ i mem ini _ hhead
        hi ⟨rfl, rfl⟩ rfl hle0
      iintro Ht Hts Htl Hm
      icases (BigSepM.bigSepM_delete hw).1 $$ Hm with ⟨Hb, Hm⟩
      imod hstep $$ Hb Ht Hts Htl with ⟨Hb, Ht, Hts, Htl⟩
      iapply key $$ Ht Hts Htl
      iapply BigSepM.bigSepM_insert_delete.2
      isplitl [Hb]
      · iexact Hb
      · iexact Hm

end Iris_instantiation

@[rocq_alias iriswasm.module_inst_build_tables_nil]
theorem module_inst_build_tables_nil (m : Module) (inst : Instance) (h : m.tables = []) :
    moduleInstBuildTables m inst = [] := by
  unfold moduleInstBuildTables
  refine fold_left_preserve (fun tabs => tabs = []) _ _ _ (by simp [moduleInstTableBase, h]) ?_
  rintro x ⟨⟨k⟩, o, i⟩ rfl
  dsimp only
  split
  · rfl
  · simp

end IrisWasm
