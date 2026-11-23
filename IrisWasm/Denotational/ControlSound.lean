import IrisWasm.Denotational.Observation
import IrisWasm.Logrel.IrisFundamentalHelpers

namespace IrisWasm.Denotational

open Wasm

private theorem emit_simple {vs : List Value} {tail rhs : Expr} {a : AdministrativeInstruction}
    {σ σ' : State} {r : Front} (red : ReduceSimple [a] rhs) (h : Runs (emit vs rhs tail) σ r σ') :
    Represents (vToEList vs.reverse ++ a :: tail) σ r σ' := by
  obtain ⟨rfl, rfl⟩ := runs_ret.mp h
  exact wrap_reduce vs.reverse tail (.simple red)

/-- A completed label body either propagates its value context or takes one label reduction. -/
theorem label_done_sound {n : Nat} {cont : Expr} {vs : List Value} {tail : Expr} {v : Val}
    {σ : State} {r : Front} {σ' : State} (h : Runs (labelFront n cont vs tail (.done v)) σ r σ') :
    Represents (vToEList vs.reverse ++ .label n cont (ofVal v) :: tail) σ r σ' := by
  cases v with
  | immV ws => exact emit_simple (.labelConst (v_to_e_is_const_list ws)) h
  | trapV => exact emit_simple .labelTrap h
  | @brV i vh =>
    simp only [labelFront] at h
    split at h
    next vh' hd =>
      obtain ⟨rfl, rfl⟩ := runs_ret.mp h
      exact ⟨(vfill_decrease _ _ [.basic (.br i)] hd).symm, rfl⟩
    next hd =>
      simp only [catchValues] at h
      split at h
      next hn =>
        obtain ⟨hle, hf⟩ := vfill_to_lfilled vh [.basic (.br i)]
        have he : lhDepth (lhOfVh vh) = i := by
          apply Nat.le_antisymm hle
          apply Classical.byContradiction
          intro hlt
          obtain ⟨_, hs⟩ := lh_depth_le_vh_decrease (.rec_ vs.reverse n cont vh tail)
            (by simp only [lhOfVh, lhDepth]; omega)
          rw [hd] at hs
          contradiction
        rw [he] at hf
        let ws := getBaseL vh
        obtain ⟨lh, hfill⟩ := lfilled_get_base_pull i vh _ _ (ws.take (ws.length - n))
          (ws.drop (ws.length - n)) (List.take_append_drop ..).symm hf
        apply emit_simple _ h
        exact .br i lh (v_to_e_is_const_list _) (by simp [vToEList]; omega) hfill
      next => exact (runs_stuck h).elim
  | retV sh =>
    obtain ⟨rfl, rfl⟩ := runs_ret.mp h
    exact ⟨rfl, rfl⟩
  | callHostV tf a args lh =>
    obtain ⟨rfl, rfl⟩ := runs_ret.mp h
    exact ⟨rfl, rfl⟩

/-- A completed local body is interpreted after restoring the caller's frame. -/
theorem local_done_sound {n : Nat} {f : Frame} {vs : List Value} {tail : Expr} {v : Val}
    {σ : State} {r : Front} {σ' : State} (h : Runs (localFront n f f vs tail (.done v)) σ r σ') :
    Represents (vToEList vs.reverse ++ .local n f (ofVal v) :: tail) σ r σ' := by
  cases v with
  | immV ws =>
    simp only [localFront] at h
    split at h
    next hn =>
      exact emit_simple (.localConst (v_to_e_is_const_list _) (by simpa [ofVal, vToEList] using hn)) h
    next => exact (runs_stuck h).elim
  | trapV => exact emit_simple .localTrap h
  | brV vh => exact (runs_stuck h).elim
  | retV sh =>
    simp only [localFront, catchValues] at h
    split at h
    next hn =>
      let ws := simpleGetBaseL sh
      obtain ⟨lh, hfill⟩ := lfilled_simple_get_base_pull _ sh _ _ (ws.take (ws.length - n))
        (ws.drop (ws.length - n)) (List.take_append_drop ..).symm (sfill_to_lfilled sh [.basic .return_])
      simp only [List.append_nil] at h
      exact emit_simple (.return_ _ lh (v_to_e_is_const_list _) (by simp [vToEList, ws]; omega) hfill) h
    next => exact (runs_stuck h).elim
  | callHostV tf a args lh =>
    obtain ⟨rfl, rfl⟩ := runs_ret.mp h
    exact ⟨rfl, rfl⟩

end IrisWasm.Denotational
