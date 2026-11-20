/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Instantiation.IrisInstantiation

/-! Port of `theories/iris/instantiation/iris_instantiation.v`, lines 3717–6185:
the final theorem `instantiation_wasm_spec`. -/

namespace IrisWasm
open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm
open scoped Iris.Std.PartialMap
open BigSepL BigSepL2 BigSepM

private theorem map_seq_set {V : Type} (N j : Nat) (l : List V) (v : V) (hj : j < l.length) :
    (FiniteMap.map_seq N (l.set j v) : NatMap V) = insert (FiniteMap.map_seq N l) (N + j) v := by
  apply LawfulPartialMap.equiv_iff_eq.1; intro i
  rw [LawfulFiniteMap.get?_map_seq, LawfulPartialMap.get?_insert, LawfulFiniteMap.get?_map_seq,
    List.getElem?_set]
  by_cases h1 : N + j = i
  · subst h1; simp [hj]
  · simp only [h1, ↓reduceIte]; split <;> simp_all <;> omega

private theorem updateTab_eq {t t' : Tableinst} {off : Nat} {pay : List Funcelem}
    (h : updateTab t off pay = some t') : t' = tableInitReplaceSingle t off pay := by
  unfold updateTab at h
  by_cases hle : off + pay.length ≤ t.data.length
  · simp only [hle, ↓reduceIte, Option.some.injEq] at h; subst h
    simp only [tableInitReplaceSingle, Tableinst.mk.injEq, and_true]
    exact (List.take_of_length_le (by simp; omega)).symm
  · simp [hle] at h

private theorem updateMem_eq {t t' : Memory} {off : Nat} {pay : List Byte}
    (h : updateMem t off pay = some t') : t' = memInitReplaceSingle t off pay := by
  unfold updateMem at h; dsimp only at h
  by_cases hle : off + pay.length ≤ t.data.data.length
  · simp only [hle, ↓reduceIte, Option.some.injEq] at h; subst h
    simp only [memInitReplaceSingle, Memory.mk.injEq, MemoryList.mk.injEq, and_true]
    exact (List.take_of_length_le (by simp; omega)).symm
  · simp [hle] at h

private def buildTabsStep (m : Module) (inst : Instance) (tabs : List Tableinst)
    (e : ModuleElement) : List Tableinst :=
  let itc := getImportTableCount m
  match e.table with
  | .tableidx k =>
    if k < itc then tabs else
      match tabs[k - itc]? with
      | some t => tabs.set (k - itc)
          (tableInitReplaceSingle t (assertConst1I32ToNat e.offset) (lookupFuncaddr inst e.init))
      | none => tabs

private theorem buildTables_eq (m : Module) (inst : Instance) :
    moduleInstBuildTables m inst = m.elem.foldl (buildTabsStep m inst) (moduleInstTableBase m.tables) :=
  rfl

private theorem upd_alloc_tabs (m : Module) (inst : Instance) (N : Nat)
    (hinst : ∀ k a, inst.tab[k]? = some a →
      if k < getImportTableCount m then a < N else a = N + (k - getImportTableCount m))
    (offs : List Nat) (elems : List ModuleElement)
    (hoff : Wasm.List.Forall₂ (fun off (e : ModuleElement) => assertConst1I32ToNat e.offset = off)
      offs elems) :
    ∀ (tabs : List Tableinst) (w : NatMap Tableinst),
    updateWtsPartial (FiniteMap.map_seq N tabs) inst offs elems = some w →
    w = FiniteMap.map_seq N (elems.foldl (buildTabsStep m inst) tabs) := by
  induction hoff with
  | nil => intro tabs w h; simp [updateWtsPartial] at h; simp [h]
  | @cons off e offs elems hoe _ ih =>
    intro tabs w h
    rcases e with ⟨⟨k⟩, o, ini⟩
    simp only [updateWtsPartial] at h
    rcases hi : inst.tab[k]? with _ | a <;> rw [hi] at h <;> simp only [reduceCtorEq] at h
    have ha := hinst k a hi
    simp only [List.foldl_cons]
    by_cases hk : k < getImportTableCount m
    · simp only [hk, ↓reduceIte] at ha
      rw [LawfulFiniteMap.get?_map_seq] at h
      simp only [show ¬ N ≤ a by omega, ↓reduceIte] at h
      have : buildTabsStep m inst tabs ⟨.tableidx k, o, ini⟩ = tabs := by
        simp [buildTabsStep, hk]
      rw [this]; exact ih _ _ h
    · simp only [hk, ↓reduceIte] at ha
      subst ha
      rw [LawfulFiniteMap.get?_map_seq] at h
      simp only [Nat.le_add_right, ↓reduceIte, Nat.add_sub_cancel_left] at h
      rcases ht : tabs[k - getImportTableCount m]? with _ | t <;> rw [ht] at h <;>
        simp only at h
      · have : buildTabsStep m inst tabs ⟨.tableidx k, o, ini⟩ = tabs := by
          simp [buildTabsStep, hk, ht]
        rw [this]; exact ih _ _ h
      · rcases hu : updateTab t off _ with _ | t' <;> rw [hu] at h <;>
          simp only [reduceCtorEq] at h
        have hlt : k - getImportTableCount m < tabs.length := by
          rcases (List.getElem?_eq_some_iff.1 ht) with ⟨h1, _⟩; exact h1
        rw [← map_seq_set _ _ _ _ hlt] at h
        have : buildTabsStep m inst tabs ⟨.tableidx k, o, ini⟩ =
            tabs.set (k - getImportTableCount m) t' := by
          simp only [buildTabsStep, hk, ht, ↓reduceIte, updateTab_eq hu]
          dsimp only at hoe; rw [hoe]; rfl
        rw [this]; exact ih _ _ h

private def importTabsStep (m : Module) (inst : Instance) (wts : NatMap Tableinst)
    (e : ModuleElement) : NatMap Tableinst :=
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
    else wts

private theorem importTabs_eq (m : Module) (inst : Instance) (wts : NatMap Tableinst) :
    moduleImportInitTabs m inst wts = m.elem.foldl (importTabsStep m inst) wts := rfl

private theorem upd_imp_tabs (m : Module) (inst : Instance) (N : Nat)
    (hinst : ∀ k a, inst.tab[k]? = some a →
      if k < getImportTableCount m then a < N else a = N + (k - getImportTableCount m))
    (offs : List Nat) (elems : List ModuleElement)
    (hoff : Wasm.List.Forall₂ (fun off (e : ModuleElement) => assertConst1I32ToNat e.offset = off)
      offs elems) :
    ∀ (wts w : NatMap Tableinst), (∀ a, (get? wts a).isSome → a < N) →
    updateWtsPartial wts inst offs elems = some w →
    w = elems.foldl (importTabsStep m inst) wts := by
  induction hoff with
  | nil => intro wts w _ h; simp [updateWtsPartial] at h; simp [h]
  | @cons off e offs elems hoe _ ih =>
    intro wts w hdom h
    rcases e with ⟨⟨k⟩, o, ini⟩
    simp only [updateWtsPartial] at h
    rcases hi : inst.tab[k]? with _ | a <;> rw [hi] at h <;> simp only [reduceCtorEq] at h
    have ha := hinst k a hi
    simp only [List.foldl_cons]
    by_cases hk : k < getImportTableCount m
    · simp only [hk, ↓reduceIte] at ha
      rcases hw : get? wts a with _ | t <;> rw [hw] at h <;> simp only at h
      · have : importTabsStep m inst wts ⟨.tableidx k, o, ini⟩ = wts := by
          simp [importTabsStep, hk, hi, hw]
        rw [this]; exact ih _ _ hdom h
      · rcases hu : updateTab t off _ with _ | t' <;> rw [hu] at h <;>
          simp only [reduceCtorEq] at h
        have : importTabsStep m inst wts ⟨.tableidx k, o, ini⟩ = insert wts a t' := by
          simp only [importTabsStep, hk, hi, hw, ↓reduceIte, updateTab_eq hu]
          dsimp only at hoe; rw [hoe]; rfl
        rw [this]
        refine ih _ _ (fun b hb => ?_) h
        rw [LawfulPartialMap.get?_insert] at hb
        split at hb
        · omega
        · exact hdom b hb
    · simp only [hk, ↓reduceIte] at ha
      have hw : get? wts a = none := by
        rcases hw : get? wts a with _ | t
        · rfl
        · have := hdom a (by simp [hw]); omega
      rw [hw] at h; simp only at h
      have : importTabsStep m inst wts ⟨.tableidx k, o, ini⟩ = wts := by
        simp [importTabsStep, hk]
      rw [this]; exact ih _ _ hdom h

private theorem disj_map_seq {V : Type} (N : Nat) (w : NatMap V) (l : List V)
    (hdom : ∀ a, (get? w a).isSome → a < N) : w ##ₘ (FiniteMap.map_seq N l : NatMap V) := by
  intro k ⟨h1, h2⟩
  have := hdom k h1
  rw [LawfulFiniteMap.get?_map_seq] at h2
  split at h2
  · omega
  · simp at h2

private theorem tabs_split (m : Module) (inst : Instance) (N : Nat)
    (hinst : ∀ k a, inst.tab[k]? = some a →
      if k < getImportTableCount m then a < N else a = N + (k - getImportTableCount m))
    (offs : List Nat) (elems : List ModuleElement)
    (hoff : Wasm.List.Forall₂ (fun off (e : ModuleElement) => assertConst1I32ToNat e.offset = off)
      offs elems)
    (wts : NatMap Tableinst) (nt : List Tableinst) (hdom : ∀ a, (get? wts a).isSome → a < N)
    (wts' : NatMap Tableinst)
    (h : updateWts (wts ∪ FiniteMap.map_seq N nt) inst offs elems = some wts') :
    updateWtsPartial wts inst offs elems = some (elems.foldl (importTabsStep m inst) wts) ∧
    wts' = elems.foldl (importTabsStep m inst) wts ∪
      FiniteMap.map_seq N (elems.foldl (buildTabsStep m inst) nt) ∧
    elems.foldl (importTabsStep m inst) wts ##ₘ
      (FiniteMap.map_seq N (elems.foldl (buildTabsStep m inst) nt) : NatMap Tableinst) := by
  have hs := update_wts_split wts' wts (FiniteMap.map_seq N nt) inst offs elems
    (disj_map_seq N wts nt hdom) h
  rcases h1 : updateWtsPartial wts inst offs elems with _ | w1 <;> rw [h1] at hs
  · exact hs.elim
  rcases h2 : updateWtsPartial (FiniteMap.map_seq N nt) inst offs elems with _ | w2 <;>
    rw [h2] at hs
  · exact hs.elim
  have d1 := update_wts_partial_dom_preserve _ _ _ _ _ h1
  have e1 := upd_imp_tabs m inst N hinst offs elems hoff wts w1 hdom h1
  have e2 := upd_alloc_tabs m inst N hinst offs elems hoff nt w2 h2
  subst e1 e2
  refine ⟨rfl, hs, disj_map_seq N _ _ fun a ha => hdom a ((d1 a).2 ha)⟩

private def buildMemsStep (m : Module) (_inst : Instance) (mems : List Memory)
    (e : ModuleData) : List Memory :=
  let itc := getImportMemCount m
  match e.data with
  | .memidx k =>
    if k < itc then mems else
      match mems[k - itc]? with
      | some t => mems.set (k - itc)
          (memInitReplaceSingle t (assertConst1I32ToNat e.offset) e.init)
      | none => mems

private theorem buildMems_eq (m : Module) (inst : Instance) :
    moduleInstBuildMems m inst = m.data.foldl (buildMemsStep m inst) (moduleInstMemBase m.mems) :=
  rfl

private theorem upd_alloc_mems (m : Module) (inst : Instance) (N : Nat)
    (hinst : ∀ k a, inst.memory[k]? = some a →
      if k < getImportMemCount m then a < N else a = N + (k - getImportMemCount m))
    (offs : List Nat) (elems : List ModuleData)
    (hoff : Wasm.List.Forall₂ (fun off (e : ModuleData) => assertConst1I32ToNat e.offset = off)
      offs elems) :
    ∀ (mems : List Memory) (w : NatMap Memory),
    updateWmsPartial (FiniteMap.map_seq N mems) inst offs elems = some w →
    w = FiniteMap.map_seq N (elems.foldl (buildMemsStep m inst) mems) := by
  induction hoff with
  | nil => intro mems w h; simp [updateWmsPartial] at h; simp [h]
  | @cons off e offs elems hoe _ ih =>
    intro mems w h
    rcases e with ⟨⟨k⟩, o, ini⟩
    simp only [updateWmsPartial] at h
    rcases hi : inst.memory[k]? with _ | a <;> rw [hi] at h <;> simp only [reduceCtorEq] at h
    have ha := hinst k a hi
    simp only [List.foldl_cons]
    by_cases hk : k < getImportMemCount m
    · simp only [hk, ↓reduceIte] at ha
      rw [LawfulFiniteMap.get?_map_seq] at h
      simp only [show ¬ N ≤ a by omega, ↓reduceIte] at h
      have : buildMemsStep m inst mems ⟨.memidx k, o, ini⟩ = mems := by
        simp [buildMemsStep, hk]
      rw [this]; exact ih _ _ h
    · simp only [hk, ↓reduceIte] at ha
      subst ha
      rw [LawfulFiniteMap.get?_map_seq] at h
      simp only [Nat.le_add_right, ↓reduceIte, Nat.add_sub_cancel_left] at h
      rcases ht : mems[k - getImportMemCount m]? with _ | t <;> rw [ht] at h <;>
        simp only at h
      · have : buildMemsStep m inst mems ⟨.memidx k, o, ini⟩ = mems := by
          simp [buildMemsStep, hk, ht]
        rw [this]; exact ih _ _ h
      · rcases hu : updateMem t off _ with _ | t' <;> rw [hu] at h <;>
          simp only [reduceCtorEq] at h
        have hlt : k - getImportMemCount m < mems.length := by
          rcases (List.getElem?_eq_some_iff.1 ht) with ⟨h1, _⟩; exact h1
        rw [← map_seq_set _ _ _ _ hlt] at h
        have : buildMemsStep m inst mems ⟨.memidx k, o, ini⟩ =
            mems.set (k - getImportMemCount m) t' := by
          simp only [buildMemsStep, hk, ht, ↓reduceIte, updateMem_eq hu]
          dsimp only at hoe; rw [hoe]
        rw [this]; exact ih _ _ h

private def importMemsStep (m : Module) (inst : Instance) (wms : NatMap Memory)
    (e : ModuleData) : NatMap Memory :=
  let itc := getImportMemCount m
  match e.data with
  | .memidx k =>
    if k < itc then
      match inst.memory[k]? with
      | some mAddr =>
        match get? wms mAddr with
        | some t => insert wms mAddr
            (memInitReplaceSingle t (assertConst1I32ToNat e.offset)
              e.init)
        | none => wms
      | none => wms
    else wms

private theorem importMems_eq (m : Module) (inst : Instance) (wms : NatMap Memory) :
    moduleImportInitMems m inst wms = m.data.foldl (importMemsStep m inst) wms := rfl

private theorem upd_imp_mems (m : Module) (inst : Instance) (N : Nat)
    (hinst : ∀ k a, inst.memory[k]? = some a →
      if k < getImportMemCount m then a < N else a = N + (k - getImportMemCount m))
    (offs : List Nat) (elems : List ModuleData)
    (hoff : Wasm.List.Forall₂ (fun off (e : ModuleData) => assertConst1I32ToNat e.offset = off)
      offs elems) :
    ∀ (wms w : NatMap Memory), (∀ a, (get? wms a).isSome → a < N) →
    updateWmsPartial wms inst offs elems = some w →
    w = elems.foldl (importMemsStep m inst) wms := by
  induction hoff with
  | nil => intro wms w _ h; simp [updateWmsPartial] at h; simp [h]
  | @cons off e offs elems hoe _ ih =>
    intro wms w hdom h
    rcases e with ⟨⟨k⟩, o, ini⟩
    simp only [updateWmsPartial] at h
    rcases hi : inst.memory[k]? with _ | a <;> rw [hi] at h <;> simp only [reduceCtorEq] at h
    have ha := hinst k a hi
    simp only [List.foldl_cons]
    by_cases hk : k < getImportMemCount m
    · simp only [hk, ↓reduceIte] at ha
      rcases hw : get? wms a with _ | t <;> rw [hw] at h <;> simp only at h
      · have : importMemsStep m inst wms ⟨.memidx k, o, ini⟩ = wms := by
          simp [importMemsStep, hk, hi, hw]
        rw [this]; exact ih _ _ hdom h
      · rcases hu : updateMem t off _ with _ | t' <;> rw [hu] at h <;>
          simp only [reduceCtorEq] at h
        have : importMemsStep m inst wms ⟨.memidx k, o, ini⟩ = insert wms a t' := by
          simp only [importMemsStep, hk, hi, hw, ↓reduceIte, updateMem_eq hu]
          dsimp only at hoe; rw [hoe]
        rw [this]
        refine ih _ _ (fun b hb => ?_) h
        rw [LawfulPartialMap.get?_insert] at hb
        split at hb
        · omega
        · exact hdom b hb
    · simp only [hk, ↓reduceIte] at ha
      have hw : get? wms a = none := by
        rcases hw : get? wms a with _ | t
        · rfl
        · have := hdom a (by simp [hw]); omega
      rw [hw] at h; simp only at h
      have : importMemsStep m inst wms ⟨.memidx k, o, ini⟩ = wms := by
        simp [importMemsStep, hk]
      rw [this]; exact ih _ _ hdom h

private theorem mems_split (m : Module) (inst : Instance) (N : Nat)
    (hinst : ∀ k a, inst.memory[k]? = some a →
      if k < getImportMemCount m then a < N else a = N + (k - getImportMemCount m))
    (offs : List Nat) (elems : List ModuleData)
    (hoff : Wasm.List.Forall₂ (fun off (e : ModuleData) => assertConst1I32ToNat e.offset = off)
      offs elems)
    (wms : NatMap Memory) (nt : List Memory) (hdom : ∀ a, (get? wms a).isSome → a < N)
    (wms' : NatMap Memory)
    (h : updateWms (wms ∪ FiniteMap.map_seq N nt) inst offs elems = some wms') :
    updateWmsPartial wms inst offs elems = some (elems.foldl (importMemsStep m inst) wms) ∧
    wms' = elems.foldl (importMemsStep m inst) wms ∪
      FiniteMap.map_seq N (elems.foldl (buildMemsStep m inst) nt) ∧
    elems.foldl (importMemsStep m inst) wms ##ₘ
      (FiniteMap.map_seq N (elems.foldl (buildMemsStep m inst) nt) : NatMap Memory) := by
  have hs := update_wms_split wms' wms (FiniteMap.map_seq N nt) inst offs elems
    (disj_map_seq N wms nt hdom) h
  rcases h1 : updateWmsPartial wms inst offs elems with _ | w1 <;> rw [h1] at hs
  · exact hs.elim
  rcases h2 : updateWmsPartial (FiniteMap.map_seq N nt) inst offs elems with _ | w2 <;>
    rw [h2] at hs
  · exact hs.elim
  have d1 := update_wms_partial_dom_preserve _ _ _ _ _ h1
  have e1 := upd_imp_mems m inst N hinst offs elems hoff wms w1 hdom h1
  have e2 := upd_alloc_mems m inst N hinst offs elems hoff nt w2 h2
  subst e1 e2
  refine ⟨rfl, hs, disj_map_seq N _ _ fun a ha => hdom a ((d1 a).2 ha)⟩

private theorem offs_of_restr {X : Type} (get : X → Wasm.Expr) (s : StoreRecord) (inst : Instance) :
    ∀ (xs : List X) (cs vs : List I32),
    xs.map get = vs.map (fun v => [BasicInstruction.const (.int32 v)]) →
    Wasm.List.Forall₂ (fun x c => ReduceTrans (s, ⟨[], inst⟩, toEList (get x))
      (s, ⟨[], inst⟩, [.basic (.const (.int32 c))])) xs cs →
    Wasm.List.Forall₂ (fun off x => assertConst1I32ToNat (get x) = off) (cs.map (·.toNat)) xs
  | [], [], _, _, _ => .nil
  | x :: xs, c :: cs, v :: vs, hr, .cons h1 h2 => by
    simp only [List.map_cons, List.cons.injEq] at hr
    refine .cons ?_ (offs_of_restr get s inst xs cs vs hr.2 h2)
    rw [hr.1] at h1 ⊢
    cases reduce_trans_const h1
    rfl
  | _ :: _, _ :: _, [], hr, _ => by simp at hr
  | [], _ :: _, _, _, h => by cases h
  | _ :: _, [], _, _, h => by cases h

private theorem globs_of_restr (s : StoreRecord) (inst : Instance) :
    ∀ (gs : List ModuleGlob) (cs vs : List Value),
    gs.map (·.init) = vs.map (fun v => [BasicInstruction.const v]) →
    Wasm.List.Forall₂ (fun (g : ModuleGlob) v => ReduceTrans (s, ⟨[], inst⟩, toEList g.init)
      (s, ⟨[], inst⟩, [.basic (.const v)])) gs cs →
    Wasm.List.Forall₂ (fun (g : ModuleGlob) v => g.init = [BasicInstruction.const v]) gs cs
  | [], [], _, _, _ => .nil
  | x :: xs, c :: cs, v :: vs, hr, .cons h1 h2 => by
    simp only [List.map_cons, List.cons.injEq] at hr
    refine .cons ?_ (globs_of_restr s inst xs cs vs hr.2 h2)
    rw [hr.1] at h1 ⊢
    cases reduce_trans_const h1
    rfl
  | _ :: _, _ :: _, [], hr, _ => by simp at hr
  | [], _ :: _, _, _, h => by cases h
  | _ :: _, [], _, _, h => by cases h

private theorem glob_init_value {gs : List ModuleGlob} {vs : List Value}
    (h : Wasm.List.Forall₂ (fun (g : ModuleGlob) v => g.init = [BasicInstruction.const v]) gs vs) :
    moduleGlobInitValue gs = some vs := by
  unfold moduleGlobInitValue
  induction h with
  | nil => rfl
  | cons h1 _ ih =>
    rw [List.map_cons]
    exact those_app [_] _ [_] _ (by simp [assertConst1, h1]; rfl) ih

private theorem glob_init_types {c : TContext} {gs : List ModuleGlob} {gts : List GlobalType}
    (ht : Wasm.List.Forall₂ (ModuleGlobTyping c) gs gts) :
    ∀ {vs : List Value},
    Wasm.List.Forall₂ (fun (g : ModuleGlob) v => g.init = [BasicInstruction.const v]) gs vs →
    vs.map typeof = gs.map (·.type.t) := by
  induction ht with
  | nil => intro vs h; cases h; rfl
  | cons h1 _ ih =>
    intro vs h
    cases h with
    | cons h2 h3 =>
      obtain ⟨_, rfl, hbt⟩ := h1
      rw [h2] at hbt
      have := BI_const_typing hbt
      simp only [List.nil_append, List.cons.injEq, and_true] at this
      simp [this, ih h3]

private theorem global_init_eq :
    ∀ (gs : List ModuleGlob) (vs : List Value), vs.length = gs.length →
    moduleInstGlobalInit (moduleInstBuildGlobals gs) vs =
      (gs.zip vs).map (fun (mg, v) => ({ mut_ := mg.type.mut_, val := v } : Global))
  | [], [], _ => rfl
  | g :: gs, v :: vs, h => by
    simp only [moduleInstBuildGlobals, List.map_cons, moduleInstGlobalInit, List.zip_cons_cons]
    have := global_init_eq gs vs (by simpa using h)
    simp only [moduleInstBuildGlobals] at this
    rw [this]; rfl
  | [], _ :: _, h | _ :: _, [], h => by simp at h

private theorem all2_map_mono {A A' B : Type} (f : A → A') (F : A → B → Bool) (G : A' → B → Bool)
    (h : ∀ a b, F a b = true → G (f a) b = true) :
    ∀ (l : List A) (l' : List B), Wasm.List.all2 F l l' = true →
      Wasm.List.all2 G (l.map f) l' = true
  | [], [], _ => rfl
  | a :: l, b :: l', hh => by
    simp only [Wasm.List.all2_cons, Bool.and_eq_true, List.map_cons] at hh ⊢
    exact ⟨h _ _ hh.1, all2_map_mono f F G h l l' hh.2⟩
  | [], _ :: _, hh | _ :: _, [], hh => by simp at hh

private theorem tabs_bound (inst : Instance) (stabs nt : List Tableinst) (wts : NatMap Tableinst)
    (hsub : ∀ a t, get? wts a = some t → stabs[a]? = some t)
    (hcover : ∀ (k a : Nat), inst.tab[k]? = some a → (get? wts a).isSome ∨ stabs.length ≤ a)
    (eOffs : List I32) (elems : List ModuleElement)
    (hcb : Wasm.List.all2 (fun eOff (e : ModuleElement) =>
      match inst.tab[match e.table with | .tableidx i => i]? with
      | none => false
      | some i => match (stabs ++ nt)[i]? with
        | none => false
        | some ti => decide (nOfInt eOff + e.init.length ≤ ti.data.length)) eOffs elems = true) :
    wtsBoundCheck (wts ∪ FiniteMap.map_seq stabs.length nt) inst (eOffs.map (·.toNat)) elems =
      true := by
  unfold wtsBoundCheck
  refine all2_map_mono (·.toNat) _ _ ?_ _ _ hcb
  intro eOff e h
  rcases e with ⟨⟨k⟩, o, ini⟩
  dsimp only at h ⊢
  rcases hi : inst.tab[k]? with _ | i <;> rw [hi] at h
  · simp at h
  dsimp only at h ⊢
  rcases hs : (stabs ++ nt)[i]? with _ | ti <;> rw [hs] at h
  · simp at h
  dsimp only at h
  have key : get? (wts ∪ FiniteMap.map_seq stabs.length nt) i = some ti := by
    rw [LawfulPartialMap.get?_union]
    rcases hw : get? wts i with _ | t
    · rcases hcover k i hi with hc | hc
      · simp [hw] at hc
      rw [List.getElem?_append_right hc] at hs
      simp [LawfulFiniteMap.get?_map_seq, hc, hs, Option.orElse]
    · have h1 := hsub i t hw
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h1).1, h1] at hs
      cases hs; rfl
  rw [key]
  simpa [nOfInt] using of_decide_eq_true h

private theorem mems_bound (inst : Instance) (smems nm : List Memory) (wms : NatMap Memory)
    (hsub : ∀ a t, get? wms a = some t → smems[a]? = some t)
    (hcover : ∀ (k a : Nat), inst.memory[k]? = some a → (get? wms a).isSome ∨ smems.length ≤ a)
    (dOffs : List I32) (datas : List ModuleData)
    (hcb : Wasm.List.all2 (fun dOff (d : ModuleData) =>
      match inst.memory[match d.data with | .memidx i => i]? with
      | none => false
      | some i => match (smems ++ nm)[i]? with
        | none => false
        | some mem => decide (nOfInt dOff + d.init.length ≤ lengthMem mem)) dOffs datas = true) :
    wmsBoundCheck (wms ∪ FiniteMap.map_seq smems.length nm) inst (dOffs.map (·.toNat)) datas =
      true := by
  unfold wmsBoundCheck
  refine all2_map_mono (·.toNat) _ _ ?_ _ _ hcb
  intro dOff d h
  rcases d with ⟨⟨k⟩, o, ini⟩
  dsimp only at h ⊢
  rcases hi : inst.memory[k]? with _ | i <;> rw [hi] at h
  · simp at h
  dsimp only at h ⊢
  rcases hs : (smems ++ nm)[i]? with _ | ti <;> rw [hs] at h
  · simp at h
  dsimp only at h
  have key : get? (wms ∪ FiniteMap.map_seq smems.length nm) i = some ti := by
    rw [LawfulPartialMap.get?_union]
    rcases hw : get? wms i with _ | t
    · rcases hcover k i hi with hc | hc
      · simp [hw] at hc
      rw [List.getElem?_append_right hc] at hs
      simp [LawfulFiniteMap.get?_map_seq, hc, hs, Option.orElse]
    · have h1 := hsub i t hw
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h1).1, h1] at hs
      cases hs; rfl
  rw [key]
  simpa [nOfInt] using of_decide_eq_true h

private theorem layout {l ext : List Nat} {N len : Nat} (hl : l = ext ++ genIndex N len)
    (hext : ∀ a ∈ ext, a < N) :
    ∀ k a, l[k]? = some a →
      if k < ext.length then a ∈ ext ∧ a < N else a = N + (k - ext.length) := by
  intro k a h
  subst hl
  split
  · rw [List.getElem?_append_left ‹_›] at h
    have := List.mem_of_getElem? h
    exact ⟨this, hext a this⟩
  · rw [List.getElem?_append_right (by omega)] at h
    exact (gen_index_lookup_Some h).1

private theorem mem_extTabAddrs {vs : List ModuleExport} {a : Nat}
    (h : a ∈ extTabAddrs (vs.map (·.desc))) :
    ∃ (j : Nat) (v : ModuleExport), vs[j]? = some v ∧ v.desc = .table (.tableidx a) := by
  simp only [extTabAddrs, extTabs, Function.comp, List.mem_map, List.mem_filterMap] at h
  obtain ⟨⟨i⟩, ⟨d, hd, hdi⟩, rfl⟩ := h
  cases d <;> simp at hdi
  subst hdi
  obtain ⟨v, hv, hvd⟩ := hd
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hv
  exact ⟨j, v, hj, hvd⟩

private theorem mem_extMemAddrs {vs : List ModuleExport} {a : Nat}
    (h : a ∈ extMemAddrs (vs.map (·.desc))) :
    ∃ (j : Nat) (v : ModuleExport), vs[j]? = some v ∧ v.desc = .mem (.memidx a) := by
  simp only [extMemAddrs, extMems, Function.comp, List.mem_map, List.mem_filterMap] at h
  obtain ⟨⟨i⟩, ⟨d, hd, hdi⟩, rfl⟩ := h
  cases d <;> simp at hdi
  subst hdi
  obtain ⟨v, hv, hvd⟩ := hd
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hv
  exact ⟨j, v, hj, hvd⟩

variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF]

private theorem bigSepL_range_L2 {A B : Type} (l : List A) (f : A → B)
    (Φ : Nat → B → IProp GF) (N : Nat) :
    ([∗list] i ↦ v ∈ l.map f, Φ (N + i) v) ⊢
      [∗list] x;a ∈ l; List.range' N l.length, Φ a (f x) := by
  induction l generalizing N with
  | nil => exact bigSepL2_nil.2
  | cons x l ih =>
    rw [List.length_cons, List.range'_succ]
    refine (bigSepL_cons.1).trans (.trans (sep_mono (by rw [Nat.add_zero]) ?_)
      bigSepL2_cons.2)
    refine .trans ?_ (ih (N + 1))
    exact bigSepL_mono_of_forall fun {k _} => by rw [Nat.add_assoc, Nat.add_comm k 1]

private theorem genIndex_eq_range (n l : Nat) : genIndex n l = List.range' n l := by
  apply List.ext_getElem <;> simp [genIndex]; intros; omega

private theorem res_of_list {B : Type} (l : List B) (Φ : Nat → B → IProp GF) (N : Nat) :
    ([∗list] i ↦ v ∈ l, Φ (N + i) v) ⊢ [∗list] v;a ∈ l; genIndex N l.length, Φ a v := by
  rw [genIndex_eq_range]
  simpa using bigSepL_range_L2 l id Φ N

private theorem func_res (mfuncs : List ModuleFunc) (inst : Instance) (N : Nat) :
    ([∗list] i ↦ v ∈ mfuncs.map (fun mf => genFuncInstance mf inst), (N + i) ↦[wf] v) ⊢
      moduleInstResourcesFunc (GF := GF) mfuncs inst (genIndex N mfuncs.length) := by
  rw [genIndex_eq_range]
  exact bigSepL_range_L2 mfuncs (fun mf => genFuncInstance mf inst) (fun a v => iprop(a ↦[wf] v)) N

private theorem forall2_imp {A B : Type} {R S : A → B → Prop} (h : ∀ a b, R a b → S a b) :
    ∀ {l₁ : List A} {l₂ : List B}, Wasm.List.Forall₂ R l₁ l₂ → Wasm.List.Forall₂ S l₁ l₂
  | _, _, .nil => .nil
  | _, _, .cons h1 h2 => .cons (h _ _ h1) (forall2_imp h h2)

private theorem buildMems_length (m : Module) (inst : Instance) :
    (moduleInstBuildMems m inst).length = m.mems.length := by
  unfold moduleInstBuildMems
  refine fold_left_preserve (fun mems : List Memory => mems.length = m.mems.length) _ _ _
    (by simp [moduleInstMemBase]) ?_
  rintro x ⟨⟨k⟩, o, i⟩ hx
  dsimp only
  split
  · exact hx
  · split <;> simp [hx]

private theorem keep4 {P1 P2 P3 P4 : IProp GF} {φ : Prop} (h : ⊢ P1 -∗ P2 -∗ P3 -∗ P4 -∗ ⌜φ⌝) :
    ⊢ P1 -∗ P2 -∗ P3 -∗ P4 -∗ ⌜φ⌝ ∗ P1 ∗ P2 ∗ P3 ∗ P4 := by
  iintro H1 H2 H3 H4
  ihave %hφ : ⌜φ⌝ $$ [H1 H2 H3 H4]
  · iapply h $$ H1 H2 H3 H4
  isplitr
  · ipureintro; exact hφ
  · iframe

private theorem tab_imports {v_imps : List ModuleExport} {t_imps : List ExternT}
    {wts : NatMap Tableinst} {stabs : List Tableinst}
    (hl : v_imps.length = t_imps.length ∧ ∀ (k : Nat) (v : ModuleExport) (t : ExternT),
      v_imps[k]? = some v → t_imps[k]? = some t →
      match v.desc with
      | .table (.tableidx i) => ∃ tab tt, stabs[i]? = some tab ∧ get? wts i = some tab ∧
          t = .tab tt ∧ tabTyping tab tt = true
      | _ => True)
    (hdc : tabDomcheck v_imps wts) :
    (∀ a t, get? wts a = some t → stabs[a]? = some t) ∧
    (∀ a ∈ extTabAddrs (v_imps.map (·.desc)), a < stabs.length) ∧
    (∀ a, (get? wts a).isSome → a < stabs.length) := by
  have key : ∀ a ∈ extTabAddrs (v_imps.map (·.desc)),
      ∃ tab, stabs[a]? = some tab ∧ get? wts a = some tab := by
    intro a ha
    obtain ⟨j, v, hj, hd⟩ := mem_extTabAddrs ha
    have hjl := (List.getElem?_eq_some_iff.1 hj).1
    have := hl.2 j v _ hj (List.getElem?_eq_getElem (by omega))
    rw [hd] at this
    obtain ⟨tab, _, h1, h2, -⟩ := this
    exact ⟨tab, h1, h2⟩
  refine ⟨fun a t h => ?_, fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨tab, h1, h2⟩ := key a ((hdc a).1 (by simp [PartialMap.dom, h]))
    rw [h] at h2; cases h2; exact h1
  · obtain ⟨tab, h1, -⟩ := key a ha; exact (List.getElem?_eq_some_iff.1 h1).1
  · obtain ⟨tab, h1, -⟩ := key a ((hdc a).1 ha); exact (List.getElem?_eq_some_iff.1 h1).1

private theorem mem_imports {v_imps : List ModuleExport} {t_imps : List ExternT}
    {wms : NatMap Memory} {smems : List Memory}
    (hl : v_imps.length = t_imps.length ∧ ∀ (k : Nat) (v : ModuleExport) (t : ExternT),
      v_imps[k]? = some v → t_imps[k]? = some t →
      match v.desc with
      | .mem (.memidx i) => ∃ mem mt,
          smems[i]? = some { data := { data := mem.data.data }, maxOpt := mem.maxOpt } ∧
          get? wms i = some mem ∧ t = .mem mt ∧ memTyping mem mt = true
      | _ => True)
    (hdc : memDomcheck v_imps wms) :
    (∀ a t, get? wms a = some t → smems[a]? = some t) ∧
    (∀ a ∈ extMemAddrs (v_imps.map (·.desc)), a < smems.length) ∧
    (∀ a, (get? wms a).isSome → a < smems.length) := by
  have key : ∀ a ∈ extMemAddrs (v_imps.map (·.desc)),
      ∃ mem, smems[a]? = some mem ∧ get? wms a = some mem := by
    intro a ha
    obtain ⟨j, v, hj, hd⟩ := mem_extMemAddrs ha
    have hjl := (List.getElem?_eq_some_iff.1 hj).1
    have := hl.2 j v _ hj (List.getElem?_eq_getElem (by omega))
    rw [hd] at this
    obtain ⟨mem, _, h1, h2, -⟩ := this
    exact ⟨mem, h1, h2⟩
  refine ⟨fun a t h => ?_, fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨tab, h1, h2⟩ := key a ((hdc a).1 (by simp [PartialMap.dom, h]))
    rw [h] at h2; cases h2; exact h1
  · obtain ⟨tab, h1, -⟩ := key a ha; exact (List.getElem?_eq_some_iff.1 h1).1
  · obtain ⟨tab, h1, -⟩ := key a ((hdc a).1 ha); exact (List.getElem?_eq_some_iff.1 h1).1

@[rocq_alias iriswasm.instantiation_wasm_spec]
theorem instantiation_wasm_spec (v_imps : List ModuleExport) (m : Module) (t_imps t_exps : List ExternT)
    (wfs : NatMap FunctionClosure) (wts : NatMap Tableinst) (wms : NatMap Memory)
    (wgs : NatMap Global) (s s' : StoreRecord) (inst : Instance) (v_exps : List ModuleExport)
    (start : Option Nat) (hmt : ModuleTyping m t_imps t_exps) (hmr : ModuleRestrictions m)
    (hinst : Instantiate s m (v_imps.map (·.desc)) ((s', inst, v_exps), start)) :
    ⊢ instantiationResourcesPreWasm (GF := GF) m v_imps t_imps wfs wts wms wgs -∗
      genHeapWasmStore s -∗
      |==> (instantiationResourcesPostWasm m v_imps t_imps wfs wts wms wgs start inst ∗
        genHeapWasmStore s') := by
  obtain ⟨t_imps', t_exps', s1, g_inits, e_offs, d_offs, hmt', hext, halloc, hglob, helem, hdata,
    hecb, hdcb, hstart, hs'⟩ := hinst
  cases module_typing_det hmt hmt'
  obtain ⟨⟨gvs, hrg⟩, ⟨evs, hre⟩, ⟨dvs, hrd⟩⟩ := hmr
  have hglen : g_inits.length = m.globals.length := (Wasm.List.Forall₂.length_eq hglob).symm
  have hginit := globs_of_restr _ _ _ _ _ hrg hglob
  have heoff := offs_of_restr (fun e : ModuleElement => e.offset) _ _ _ _ _ hre helem
  have hdoff := offs_of_restr (fun d : ModuleData => d.offset) _ _ _ _ _ hrd hdata
  have hgval : ModuleGlobInitValues m g_inits := by
    refine ⟨?_, glob_init_value hginit⟩
    obtain ⟨fts, gts, hmt⟩ := hmt
    rcases m with ⟨tfs, fs, ts, ms, gs, els, ds, iOpt, imps, exps⟩
    exact glob_init_types hmt.2.2.2.1 hginit
  obtain ⟨hifc, hitc, himc, higc⟩ := mod_imps_len_t hmt
  obtain ⟨hvfc, hvtc, hvmc, hvgc⟩ := vt_imps_comp_len hext
  simp only [allocModule] at halloc
  generalize hf : allocFuncs s m.funcs inst = rf at halloc
  rcases rf with ⟨sF, idf⟩
  generalize ht : allocTabs sF (m.tables.map (·.type)) = rt at halloc
  rcases rt with ⟨sT, idt⟩
  generalize hm : allocMems sT m.mems = rm at halloc
  rcases rm with ⟨sM, idm⟩
  generalize hg : allocGlobs sM m.globals g_inits = rg at halloc
  rcases rg with ⟨sG, idg⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq] at halloc hs'
  obtain ⟨⟨⟨⟨⟨⟨rfl, hty⟩, hfu⟩, hta⟩, hme⟩, hgl⟩, hex⟩ := halloc
  obtain ⟨af1, af2, af3, af4, af5⟩ := alloc_func_gen_index hf
  obtain ⟨at1, at2, at3, at4, at5⟩ := alloc_tab_gen_index ht
  obtain ⟨am1, am2, am3, am4, am5⟩ := alloc_mem_gen_index hm
  obtain ⟨ag1, ag2, ag3, ag4, ag5⟩ := alloc_glob_gen_index hglen hg
  -- the store after allocation, in terms of `s`
  have hfuncs : s1.funcs = s.funcs ++ m.funcs.map (fun mf => genFuncInstance mf inst) := by
    rw [← ag3, ← am3, ← at3, af2]
  have htabs : s1.tables = s.tables ++ moduleInstTableBase m.tables := by
    rw [← ag4, ← am4, at2, ← af3, List.map_map]; rfl
  have hmems : s1.mems = s.mems ++ moduleInstMemBase m.mems := by
    rw [← ag5, am2, ← at4, ← af4]; rfl
  have hglobs : s1.globals =
      s.globals ++ moduleInstGlobalInit (moduleInstBuildGlobals m.globals) g_inits := by
    rw [ag2, ← am5, ← at5, ← af5, global_init_eq _ _ hglen]
  have hinstF : inst.funcs = extFuncAddrs (v_imps.map (·.desc)) ++
      genIndex s.funcs.length m.funcs.length := by
    rw [hfu, List.map_append]; exact congrArg _ af1
  have hinstT : inst.tab = extTabAddrs (v_imps.map (·.desc)) ++
      genIndex s.tables.length m.tables.length := by
    rw [hta, List.map_append, af3]; exact congrArg _ (at1.trans (by simp))
  have hinstM : inst.memory = extMemAddrs (v_imps.map (·.desc)) ++
      genIndex s.mems.length m.mems.length := by
    rw [hme, List.map_append, af4, at4]; exact congrArg _ am1
  have hinstG : inst.globs = extGlobAddrs (v_imps.map (·.desc)) ++
      genIndex s.globals.length m.globals.length := by
    rw [hgl, List.map_append, af5, at5, am5]; exact congrArg _ ag1
  have hFc : getImportFuncCount m = (extFuncAddrs (v_imps.map (·.desc))).length := by
    simp [extFuncAddrs, hifc, hvfc]
  have hTc : getImportTableCount m = (extTabAddrs (v_imps.map (·.desc))).length := by
    simp [extTabAddrs, hitc, hvtc]
  have hMc : getImportMemCount m = (extMemAddrs (v_imps.map (·.desc))).length := by
    simp [extMemAddrs, himc, hvmc]
  have hGc : getImportGlobalCount m = (extGlobAddrs (v_imps.map (·.desc))).length := by
    simp [extGlobAddrs, higc, hvgc]
  generalize hs'' : initTabs s1 inst (e_offs.map (·.toNat)) m.elem = s'' at hs'
  obtain ⟨hp1, hp2, hp3⟩ := init_tabs_preserve hs''
  obtain ⟨hq1, hq2, hq3⟩ := init_mems_preserve hs'.symm
  unfold instantiationResourcesPreWasm importResourcesWasmTypecheck genHeapWasmStore
  iintro ⟨Himp, %Hebound, %Hdbound⟩ Hσ
  icases Hσ with ⟨Hwf, Hwt, Hwm, Hwg, Hmsize, Htsize, Hmlimit, Htlimit⟩
  icases Himp with ⟨Hfc, Htc, Hmc, Hgc⟩
  ihave ⟨%Htl, Hwt, Htsize, Htlimit, Htc⟩ :=
    keep4 (import_tab_wasm_lookup v_imps t_imps wts s) $$ Hwt Htsize Htlimit Htc
  ihave ⟨%Hml, Hwm, Hmsize, Hmlimit, Hmc⟩ :=
    keep4 (import_mem_wasm_lookup v_imps t_imps wms s) $$ Hwm Hmsize Hmlimit Hmc
  iunfold importTabWasmCheck, importTabResources at Htc
  iunfold importMemWasmCheck, importMemResources at Hmc
  icases Htc with ⟨Hwts, %htc⟩
  icases Hmc with ⟨Hwms, %hmc⟩
  -- allocation
  imod alloc_func_state_update _ _ _ hfuncs $$ Hwf with ⟨Hwf, Hfm⟩
  imod alloc_tab_state_update _ _ _ htabs $$ Hwt Htsize Htlimit with ⟨Hwt, Htsize, Htlimit, Htm⟩
  imod alloc_mem_state_update _ _ _ hmems $$ Hwm Hmsize Hmlimit with ⟨Hwm, Hmsize, Hmlimit, Hmm⟩
  imod alloc_glob_state_update _ _ _ hglobs $$ Hwg with ⟨Hwg, Hgm⟩
  -- tables
  obtain ⟨hsubT, hextT, hdomT⟩ := tab_imports Htl htc.2
  have hlayT := layout hinstT hextT
  rw [← hTc] at hlayT
  have hinstT' : ∀ k a, inst.tab[k]? = some a → if k < getImportTableCount m
      then a < s.tables.length else a = s.tables.length + (k - getImportTableCount m) := by
    intro k a h; have := hlayT k a h
    by_cases hk : k < getImportTableCount m
    · simp only [hk, ↓reduceIte] at this ⊢; exact this.2
    · simp only [hk, ↓reduceIte] at this ⊢; exact this
  have hcoverT : ∀ (k a : Nat), inst.tab[k]? = some a →
      (get? wts a).isSome ∨ s.tables.length ≤ a := by
    intro k a h; have := hlayT k a h
    split at this
    · exact .inl ((htc.2 a).2 this.1)
    · exact .inr (by omega)
  have hboundT := tabs_bound inst s.tables (moduleInstTableBase m.tables) wts hsubT hcoverT
    e_offs m.elem (by unfold checkBoundsElem at hecb; rwa [htabs] at hecb)
  obtain ⟨wts', hupdT⟩ := update_wts_Some _ _ _ _ hboundT
  obtain ⟨hpT, hwts', hdisjT⟩ := tabs_split m inst _ hinstT' _ _ heoff wts _ hdomT wts' hupdT
  ihave Hall : ([∗map] n ↦ tabinst ∈ wts ∪ FiniteMap.map_seq s.tables.length
      (moduleInstTableBase m.tables), n ↦[wtblock] tabinst) $$ [Hwts Htm]
  · iapply (bigSepM_union (disj_map_seq _ _ _ hdomT)).2
    isplitl [Hwts]
    · iexact Hwts
    · iapply bigSepM_map_seq.2; iexact Htm
  imod init_tabs_state_update s1 s'' inst _ _ _ _ hs'' hboundT hupdT $$ Hwt Htsize Htlimit Hall
    with ⟨Hwt, Htsize, Htlimit, Hall⟩
  subst hwts'
  ihave ⟨Hw1, Hw2⟩ := (bigSepM_union hdisjT).1 $$ Hall
  -- memories
  obtain ⟨hsubM, hextM, hdomM⟩ := mem_imports Hml hmc.2
  have hlayM := layout hinstM hextM
  rw [← hMc] at hlayM
  have hinstM' : ∀ k a, inst.memory[k]? = some a → if k < getImportMemCount m
      then a < s.mems.length else a = s.mems.length + (k - getImportMemCount m) := by
    intro k a h; have := hlayM k a h
    by_cases hk : k < getImportMemCount m
    · simp only [hk, ↓reduceIte] at this ⊢; exact this.2
    · simp only [hk, ↓reduceIte] at this ⊢; exact this
  have hcoverM : ∀ (k a : Nat), inst.memory[k]? = some a →
      (get? wms a).isSome ∨ s.mems.length ≤ a := by
    intro k a h; have := hlayM k a h
    split at this
    · exact .inl ((hmc.2 a).2 this.1)
    · exact .inr (by omega)
  have hboundM := mems_bound inst s.mems (moduleInstMemBase m.mems) wms hsubM hcoverM
    d_offs m.data (by unfold checkBoundsData at hdcb; rwa [hmems] at hdcb)
  obtain ⟨wms', hupdM⟩ := update_wms_Some _ _ _ _ hboundM
  obtain ⟨hpM, hwms', hdisjM⟩ := mems_split m inst _ hinstM' _ _ hdoff wms _ hdomM wms' hupdM
  ihave Hallm : ([∗map] n ↦ meminst ∈ wms ∪ FiniteMap.map_seq s.mems.length
      (moduleInstMemBase m.mems), n ↦[wmblock] meminst) $$ [Hwms Hmm]
  · iapply (bigSepM_union (disj_map_seq _ _ _ hdomM)).2
    isplitl [Hwms]
    · iexact Hwms
    · iapply bigSepM_map_seq.2; iexact Hmm
  have L := init_mems_state_update (GF := GF) s'' s' inst _ _ _ _ _ rfl hs'.symm hboundM hupdM
  rw [← hp2] at L
  imod L $$ Hwm Hmsize Hmlimit Hallm with ⟨Hwm, Hmsize, Hmlimit, Hallm⟩
  subst hwms'
  ihave ⟨Hm1, Hm2⟩ := (bigSepM_union hdisjM).1 $$ Hallm
  -- final assembly
  have hdF : inst.funcs.drop (getImportFuncCount m) = genIndex s.funcs.length m.funcs.length := by
    rw [hinstF, hFc, List.drop_left]
  have hdT : inst.tab.drop (getImportTableCount m) =
      genIndex s.tables.length (moduleInstBuildTables m inst).length := by
    rw [hinstT, hTc, List.drop_left, module_inst_build_tables_length]
  have hdM : inst.memory.drop (getImportMemCount m) =
      genIndex s.mems.length (moduleInstBuildMems m inst).length := by
    rw [hinstM, hMc, List.drop_left, buildMems_length]
  have hdG : inst.globs.drop (getImportGlobalCount m) = genIndex s.globals.length
      (moduleInstGlobalInit (moduleInstBuildGlobals m.globals) g_inits).length := by
    rw [hinstG, hGc, List.drop_left, global_init_eq _ _ hglen]; simp [hglen]
  have htc' : tabTypecheck v_imps t_imps (moduleImportInitTabs m inst wts) ∧
      tabDomcheck v_imps (moduleImportInitTabs m inst wts) := by
    refine ⟨forall2_imp (fun v t h => ?_) htc.1, fun k =>
      (update_wts_partial_dom_preserve _ _ _ _ _ hpT k).symm.trans (htc.2 k)⟩
    rcases v with ⟨nm, d⟩
    dsimp only at h ⊢
    cases d with
    | table ti =>
      rcases ti with ⟨i⟩
      obtain ⟨tab, tt, h1, h2, h3⟩ := h
      obtain ⟨tab', h4, h5⟩ := update_wts_partial_lookup_type _ _ _ _ _ i tab tt hpT h1 h3
      exact ⟨tab', tt, h4, h2, h5⟩
    | _ => trivial
  have hmc' : memTypecheck v_imps t_imps (moduleImportInitMems m inst wms) ∧
      memDomcheck v_imps (moduleImportInitMems m inst wms) := by
    refine ⟨forall2_imp (fun v t h => ?_) hmc.1, fun k =>
      (update_wms_partial_dom_preserve _ _ _ _ _ hpM k).symm.trans (hmc.2 k)⟩
    rcases v with ⟨nm, d⟩
    dsimp only at h ⊢
    cases d with
    | mem mi =>
      rcases mi with ⟨i⟩
      obtain ⟨mem, mt, h1, h2, h3⟩ := h
      obtain ⟨mem', h4, h5⟩ := update_wms_partial_lookup_type _ _ _ _ _ i mem mt hpM h1 h3
      exact ⟨mem', mt, h4, h2, h5⟩
    | _ => trivial
  rw [show List.foldl (buildTabsStep m inst) (moduleInstTableBase m.tables) m.elem = moduleInstBuildTables m inst from rfl,
    show List.foldl (buildMemsStep m inst) (moduleInstMemBase m.mems) m.data = moduleInstBuildMems m inst from rfl] at *
  rw [← hq1, ← hp1, ← hq2, ← hq3, ← hp3]
  imodintro
  isplitr [Hwf Hwt Hwm Hwg Hmsize Htsize Hmlimit Htlimit]
  · unfold instantiationResourcesPostWasm importResourcesWasmTypecheck importTabWasmCheck
      importMemWasmCheck importTabResources importMemResources moduleInstResourcesWasm
      moduleInstResourcesTab moduleInstResourcesMem moduleInstResourcesGlob
    iexists g_inits, moduleInstBuildTables m inst, moduleInstBuildMems m inst,
      moduleInstGlobalInit (moduleInstBuildGlobals m.globals) g_inits,
      moduleImportInitTabs m inst wts, moduleImportInitMems m inst wms
    isplitl [Hfc Hgc Hw1 Hm1]
    · isplitl [Hfc]
      · iexact Hfc
      isplitl [Hw1]
      · isplitl [Hw1]
        · rw [show moduleImportInitTabs m inst wts = List.foldl (importTabsStep m inst) wts m.elem from rfl]; iexact Hw1
        · ipureintro; exact htc'
      isplitl [Hm1]
      · isplitl [Hm1]
        · rw [show moduleImportInitMems m inst wms = List.foldl (importMemsStep m inst) wms m.data from rfl]; iexact Hm1
        · ipureintro; exact hmc'
      · iexact Hgc
    isplitr
    · ipureintro
      refine ⟨hty, ?_, ?_, ?_, ?_, hstart⟩
      · rw [hinstF]; exact List.prefix_append _ _
      · rw [hinstT]; exact List.prefix_append _ _
      · rw [hinstM]; exact List.prefix_append _ _
      · rw [hinstG]; exact List.prefix_append _ _
    isplitr; · ipureintro; rfl
    isplitr; · ipureintro; rfl
    isplitr; · ipureintro; exact Hebound
    isplitr; · ipureintro; rfl
    isplitr; · ipureintro; rfl
    isplitr; · ipureintro; exact Hdbound
    isplitr; · ipureintro; exact hgval
    isplitr; · ipureintro; rfl
    rw [hdF, hdT, hdM, hdG]
    isplitl [Hfm]
    · iapply func_res; iexact Hfm
    isplitl [Hw2]
    · iapply res_of_list (moduleInstBuildTables m inst) (fun a v => iprop(a ↦[wtblock] v))
      iapply bigSepM_map_seq.1; iexact Hw2
    isplitl [Hm2]
    · iapply res_of_list (moduleInstBuildMems m inst) (fun a v => iprop(a ↦[wmblock] v))
      iapply bigSepM_map_seq.1; iexact Hm2
    · iapply res_of_list _ (fun a v => iprop(a ↦[wg] v)); iexact Hgm
  · iframe

end IrisWasm
