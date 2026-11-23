import IrisWasm.Denotational.LayerCorrect
import Iris.Std.Relation

namespace IrisWasm.Denotational
open Iris.ProgramLogic.Language

private theorem singleton_step {c : Cfg} {ρ : List Expr × State} {obs : List Observation}
    (h : Step (Λ := wasmLanguage) ([c.1], c.2) obs ρ) :
    ∃ b : Cfg, ρ = ([b.1], b.2) ∧ obs = [] ∧ Next c b := by
  rcases c with ⟨es, σ⟩
  generalize hp : ([es], σ) = p at h
  cases h with
  | @atomic e s obs e' s' forks hprim left right =>
    obtain ⟨hl, rfl⟩ := Prod.mk.inj hp.symm
    rcases List.append_eq_singleton_iff.mp hl with ⟨rfl, he⟩ | ⟨_, he⟩
    · cases he
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (prim_step_obs_efs_empty hprim)
      exact ⟨(e', s'), rfl, rfl, round_next_iff.2 hprim⟩
    · cases he

/-- Exactly `i` handled next layers coincide with exactly `i` Iris singleton-pool steps. -/
theorem iterate_next_iff_nsteps (i : Nat) (c d : Cfg) :
    Relation.Iterate Next i c d ↔ NSteps (Λ := wasmLanguage) i ([c.1], c.2) [] ([d.1], d.2) := by
  constructor
  · intro h
    induction h using Relation.Iterate.head_induction_on with
    | rfl => exact .refl _
    | head b hnext _ ih =>
      exact .cons (Step.atomic (Λ := wasmLanguage) (round_next_iff.1 hnext) [] []) ih
  · intro h
    induction i generalizing c with
    | zero =>
      rcases c with ⟨es, σ⟩
      rcases d with ⟨es', σ'⟩
      cases h
      exact .rfl _
    | succ i ih =>
      generalize ho : ([] : List Observation) = obs at h
      cases h with
      | cons hs ht =>
        obtain ⟨b, rfl, rfl, hn⟩ := singleton_step hs
        cases ho
        exact .head hn (ih b ht)

end IrisWasm.Denotational
