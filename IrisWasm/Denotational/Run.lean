import IrisWasm.Denotational.Correspondence

namespace IrisWasm.Denotational

/-- Follow exactly `n` internal steps of the computable chooser. A value is not a padding step. -/
def runCut : Nat → Cfg → Option Cfg
  | 0, c => some c
  | n+1, c => match runRound c with
    | some (.next es, σ) => runCut n (es, σ)
    | _ => none

theorem runCut_next {n : Nat} {c d : Cfg} (h : runCut n c = some d) :
    Relation.Iterate Next n c d := by
  induction n generalizing c with
  | zero => cases h; exact .rfl _
  | succ n ih =>
    cases hr : runRound c with
    | none => simp [runCut, hr] at h
    | some p =>
      rcases p with ⟨r, σ⟩
      cases r with
      | done => simp [runCut, hr] at h
      | next es =>
        exact .head (b := (es, σ)) (runRound_sound c hr) (ih (by simpa [runCut, hr] using h))

/-- The raw endpoint is shared by the chosen execution, the native cut and the Iris singleton pool. -/
theorem runCut_sound {n : Nat} {c d : Cfg} (h : runCut n c = some d) :
    (∃ t : Tree Cfg, Relation.Iterate (CTree.trans .tau) n (cutAfter n c) t ∧ Yields t d) ∧
    Iris.ProgramLogic.Language.NSteps (Λ := wasmLanguage) n ([c.1], c.2) [] ([d.1], d.2) :=
  ⟨(exact_cut_next_iff ..).2 (runCut_next h), (iterate_next_iff_nsteps ..).1 (runCut_next h)⟩

/-- Count down the embedding limit on the active evaluation path only. Do not enter suspended code. -/
def framesFit : Expr → Nat → Bool
  | .basic (.const _) :: rest, room => framesFit rest room
  | .label _ _ body :: _, room => framesFit body room
  | .local .. :: _, 0 => false
  | .local _ _ body :: _, room+1 => framesFit body room
  | _, _ => true
termination_by es _ => sizeOf es
decreasing_by all_goals simp_wf; omega

inductive StopReason where
  | boundary (value : Val)
  | noLeaf
  | frameLimit
  | budget

private def inspect (c : Cfg) : Sum StopReason Cfg :=
  if !framesFit c.1 1024 then .inl .frameLimit else
  match runRound c with
  | none => .inl .noLeaf
  | some (.done v, _) => .inl (.boundary v)
  | some (.next es, σ) => .inr (es, σ)

/-- Tail-recursive execution to the first boundary. A watchdog cut retains the redex for resumption;
    it is neither a Wasm trap nor call-stack exhaustion. -/
def runUntil (budget : Nat) (c : Cfg) : Cfg × StopReason :=
  match inspect c with
  | .inl why => (c, why)
  | .inr d => match budget with
    | 0 => (c, .budget)
    | n+1 => runUntil n d

private theorem inspect_next {c d : Cfg} (h : inspect c = .inr d) :
    runRound c = some (.next d.1, d.2) := by
  unfold inspect at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  cases h; assumption

/-- Even on timeout, exhaustion, or a host boundary, the saved configuration is a real exact cut. -/
theorem runUntil_path (c : Cfg) (fuel : Nat) :
    ∃ n ≤ fuel, runCut n c = some (runUntil fuel c).1 := by
  induction fuel generalizing c with
  | zero =>
    refine ⟨0, Nat.le_refl _, ?_⟩
    rw [runUntil]; split <;> rfl
  | succ fuel ih =>
    rw [runUntil]; split
    · exact ⟨0, Nat.zero_le _, rfl⟩
    · rename_i d hd
      obtain ⟨n, hn, hp⟩ := ih d
      exact ⟨n+1, by omega, by simpa [runCut, inspect_next hd] using hp⟩

theorem runUntil_boundary {fuel : Nat} {c d : Cfg} {v : Val}
    (h : runUntil fuel c = (d, .boundary v)) : toVal d.1 = some v := by
  induction fuel generalizing c with
  | zero =>
    rw [runUntil] at h
    split at h
    · rename_i why hi
      cases h
      unfold inspect at hi
      split at hi
      · cases hi
      · split at hi
        · cases hi
        · cases hi; exact (runRound_done (by assumption)).1
        · cases hi
    · cases h
  | succ n ih =>
    rw [runUntil] at h
    split at h
    · rename_i why hi
      apply ih (c := c)
      simpa only [runUntil, hi] using h
    · exact ih h

end IrisWasm.Denotational
