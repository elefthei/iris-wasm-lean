import IrisWasm.Denotational.Observation

namespace IrisWasm.Denotational

open Wasm

private theorem br_runs {i : Nat} (vh : ValidHoled i) (σ : State) :
    Runs (layer (vfill vh [.basic (.br i)])) σ (.done (.brV vh)) σ := by
  cases vh with
  | base bef aft =>
    simp [layer, vfill, List.append_assoc, frag_consts, frag, basicLayer]
  | @rec_ m bef n cont vh aft =>
    simp only [vfill, layer, frag_consts, List.append_nil, frag, remaining, runs_bind]
    refine ⟨.done (.brV (vhIncrease vh)), σ, ?_, ?_⟩
    · simpa only [layer, vfill_increase] using br_runs (vhIncrease vh) σ
    · simp [labelFront, vhDecrease, vh_decrease_increase]
termination_by lengthRec (vfill vh [])
decreasing_by
  simp only [vfill_increase, vfill, lengthRec, List.map_append, List.sum_append,
    List.map_cons, List.sum_cons, sizeOfInstruction]
  omega

/-- Each Iris value is observable at its original syntax without changing the store or frame. -/
theorem ofVal_runs (v : Val) (σ : State) : Runs (layer (ofVal v)) σ (.done v) σ := by
  cases v with
  | immV ws =>
    rw [ofVal, layer, ← List.append_nil (vToEList ws), frag_consts]
    simp [frag, finish]
  | trapV => simp [layer, ofVal, frag, trapLayer]
  | brV vh => exact br_runs vh σ
  | retV sh =>
    induction sh with
    | base bef aft =>
      simp [ofVal, sfill, layer, List.append_assoc, frag_consts, frag, basicLayer]
    | rec_ bef n cont sh aft ih =>
      simp only [ofVal, sfill, layer, frag_consts, List.append_nil, frag, remaining, runs_bind]
      exact ⟨_, σ, ih, by simp [labelFront]⟩
  | callHostV tf h args lh =>
    induction lh generalizing σ with
    | base bef aft =>
      simp [ofVal, llfill, layer, List.append_assoc, frag_consts, frag]
    | label bef n cont lh aft ih =>
      simp only [ofVal, llfill, layer, frag_consts, List.append_nil, frag, remaining, runs_bind]
      exact ⟨_, σ, ih σ, by simp [labelFront]⟩
    | «local» bef n f lh aft ih =>
      obtain ⟨s, locs, inst⟩ := σ
      simp only [ofVal, llfill, layer, frag_consts, List.append_nil, frag, remaining, runs_vis]
      refine ⟨⟨locs, inst⟩, stateOf s f, by simp [handle], runs_bind.mpr ⟨_, _, ih _, ?_⟩⟩
      exact runs_vis.mpr ⟨f, (s, locs, inst), by simp [handle], by simp [localFront]⟩

end IrisWasm.Denotational
