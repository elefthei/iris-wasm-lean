import IrisWasm.Denotational.Observation
import IrisWasm.Logrel.IrisFundamentalHelpers

/-! Every simple reduction remains observable under any operand stack and instruction tail. -/

namespace IrisWasm.Denotational

open Wasm

private theorem converted_depth {lh : Lholed} {i : Nat} {vh : ValidHoled i}
    (h : vhOfLh lh i = some vh) : lhDepth (lhOfVh vh) = lhDepth lh := by
  induction lh generalizing i with
  | base bef aft =>
    simp only [vhOfLh, Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h
    rfl
  | rec_ bef n es lh aft ih =>
    cases i with
    | zero => simp [vhOfLh] at h
    | succ i =>
      simp only [vhOfLh] at h
      split at h
      · simp only [Option.map_eq_some_iff] at h
        obtain ⟨_, hx, rfl⟩ := h
        simp [lhOfVh, lhDepth, ih hx]
      · contradiction

/-- Move the branch operands into the innermost constant prefix, preserving label depth. -/
private theorem branch_payload {i : Nat} (vh : ValidHoled i) (ws : List Value) (e : Expr) :
    ∃ vh' : ValidHoled i, vfill vh' e = vfill vh (vToEList ws ++ e) ∧
      getBaseL vh' = getBaseL vh ++ ws ∧ lhDepth (lhOfVh vh') = lhDepth (lhOfVh vh) := by
  induction vh with
  | base bef aft =>
    exact ⟨.base (bef ++ ws) aft, by simp [vfill, vToEList, List.append_assoc], rfl, rfl⟩
  | rec_ bef n cont vh aft ih =>
    obtain ⟨vh', hf, hb, hd⟩ := ih
    exact ⟨.rec_ bef n cont vh' aft, by simp [vfill, hf], hb, by simp [lhOfVh, lhDepth, hd]⟩

private theorem return_payload (sh : SimpleValidHoled) (ws : List Value) :
    simpleGetBaseL (shPullConstR sh ws) = simpleGetBaseL sh ++ ws := by
  induction sh with
  | base => rfl
  | rec_ _ _ _ _ _ ih => exact ih

private theorem decrease_caught {i : Nat} (vh : ValidHoled i) (bef : List Value) (n : Nat)
    (cont aft : Expr) (hd : lhDepth (lhOfVh vh) = i) :
    vhDecrease (.rec_ bef n cont vh aft) = none := by
  cases he : vhDecrease (.rec_ bef n cont vh aft) with
  | none => rfl
  | some w =>
    have h := lh_depth_vh_decrease_eq _ w he
    have hle := (vfill_to_lfilled w []).1
    simp only [lhOfVh, lhDepth, hd] at h
    omega

private theorem local_done {v : Val} {body : Expr} {s : StoreRecord} (caller inner : Frame)
    (h : Runs (layer body) (stateOf s inner) (.done v) (stateOf s inner))
    {n : Nat} {vs : List Value} {tail : Expr} {k : List Value → Layer} {r : Front}
    (hr : Runs (localFront n inner inner vs tail (.done v)) (stateOf s caller) r
      (stateOf s caller)) :
    Runs (frag [.local n inner body] vs tail k) (stateOf s caller) r (stateOf s caller) := by
  rw [frag, runs_vis]
  refine ⟨caller, stateOf s inner, ?_, runs_bind.mpr ⟨_, _, h, runs_vis.mpr ?_⟩⟩
  · simp [handle, stateOf]
  · exact ⟨inner, stateOf s caller, by simp [handle, stateOf], by simpa using hr⟩

private theorem trim_outer {ws : List Value} {aft : Expr}
    (h : vToEList ws ++ [.trap] ++ aft ≠ [.trap]) (s : StoreRecord) (f : Frame) :
    Covers s f (vToEList ws ++ [.trap] ++ aft) s f [.trap] := by
  intro vs tail k
  have hpos : 0 < ws.length + aft.length := by
    cases ws <;> cases aft <;> simp_all [vToEList]
    omega
  rw [List.append_assoc, frag_consts]
  simp only [List.singleton_append, frag, remaining_eq]
  have hn : ¬ (ws.reverse ++ vs = [] ∧ aft ++ tail = []) := by
    simp only [List.append_eq_nil_iff, List.reverse_eq_nil_iff]
    rintro ⟨⟨rfl, _⟩, rfl, _⟩; contradiction
  rw [trapLayer, ite_eq_right hn, runs_br]
  refine ⟨⟨(vs.length, tail.length), ?_, ?_, ?_⟩, ?_⟩
  · simp
  · simp
  · simp only [List.length_append, List.length_reverse]; omega
  · simp [List.reverse_append]

theorem simple_covers (values : ∀ (v : Val) (σ : State), Runs (layer (ofVal v)) σ (.done v) σ)
    {es es' : Expr} (h : ReduceSimple es es') (s : StoreRecord) (f : Frame) :
    Covers s f es s f es' := by
  intro vs tail k
  cases h with
  | labelConst hc =>
    obtain ⟨ws, rfl⟩ := Wasm.const_es_exists hc
    rw [frag, runs_bind]
    exact ⟨_, _, values (.immV ws) _, by simp [labelFront, emit]⟩
  | labelTrap =>
    rw [frag, runs_bind]
    exact ⟨_, _, values .trapV _, by simp [labelFront, emit]⟩
  | @br n _ cont i body lh hc hn hf =>
    obtain ⟨ws, rfl⟩ := Wasm.const_es_exists hc
    obtain ⟨vh, hconv, hbody⟩ := lfilled_to_vfill hf (Nat.le_refl i)
    obtain ⟨w, hfill, hb, hd⟩ := branch_payload vh ws [.basic (.br i)]
    have hval : ofVal (.brV w) = body := hfill.trans hbody
    have hdepth := hd.trans ((converted_depth hconv).trans (lfilled_depth _ _ _ _ hf))
    simp only [vToEList, List.length_map] at hn
    subst n
    rw [frag, runs_bind]
    refine ⟨.done (.brV w), _, hval ▸ values _ _, ?_⟩
    simp [labelFront, decrease_caught _ _ _ _ _ hdepth, catchValues, hb, emit]
  | brTable _ hj =>
    simp only [frag, basicLayer, hj]
    simp [emit]
  | brTableLength hlen =>
    simp [frag, basicLayer, emit, List.getElem?_eq_none hlen]
  | localConst hc hn =>
    obtain ⟨ws, rfl⟩ := Wasm.const_es_exists hc
    apply local_done _ _ (values (.immV ws) _)
    simp [localFront, emit, show ws.length = _ by simpa [vToEList] using hn]
  | localTrap =>
    apply local_done _ _ (values .trapV _)
    simp [localFront, emit]
  | @return_ n i _ body lh inner hc hn hf =>
    obtain ⟨ws, rfl⟩ := Wasm.const_es_exists hc
    obtain ⟨sh, rfl⟩ := lfilled_to_sfill _ _ _ _ hf
    rw [← sfill_sh_pull_const_r]
    apply local_done _ _ (values (.retV (shPullConstR sh ws)) _)
    simp only [vToEList, List.length_map] at hn
    subst n
    simp [localFront, catchValues, return_payload, emit]
  | @teeLocal i v hc =>
    match v, hc with
    | .basic (.const _), _ => simp [frag, basicLayer, emit]
  | trap lh hne hf =>
    rw [lfilled_Ind_Equivalent] at hf
    cases hf with
    | lfilledBase bef _ aft hc =>
      obtain ⟨ws, rfl⟩ := Wasm.const_es_exists hc
      exact trim_outer hne s f vs tail k
  | _ => simp [frag, basicLayer, resultCode, emit, *]

end IrisWasm.Denotational
