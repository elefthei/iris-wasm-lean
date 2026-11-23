import IrisWasm.Denotational.Transitions
import IrisWasm.Denotational.PoolSteps

/-! Exact configurations and results on the native choice-tree transition system. -/

namespace IrisWasm.Denotational

open Wasm CTree Relation Iris.ProgramLogic
noncomputable section

/-- Return the raw residual after exactly `i` Wasm steps. A value is not a padding step. -/
def cutAfter : Nat → Cfg → Tree Cfg
  | 0, c => pure c
  | n + 1, c => round c >>= fun
    | (.next es, σ) => .step (cutAfter n (es, σ))
    | (.done _, _) => .stuck

theorem cutAfter_tau_iff {n : Nat} {c : Cfg} {t : Tree Cfg} :
    trans .tau (cutAfter (n+1) c) t ↔ ∃ d, Next c d ∧ t = cutAfter n d := by
  rw [cutAfter]
  constructor
  · intro h
    obtain ⟨⟨r, σ⟩, hr, ht⟩ := trans_bind_pure (pure_pure_finite (round_finite c)) h
    cases r with
    | next es => exact ⟨(es, σ), hr, (trans_step_inv ht).1⟩
    | done => exact (trans_stuck_inv ht).elim
  · rintro ⟨d, hr, rfl⟩
    exact trans_bind_r hr (trans_step _)

theorem iterate_zero_iff {α : Type} {R : α → α → Prop} {a b : α} :
    Iterate R 0 a b ↔ a = b := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .rfl _

theorem iterate_succ_iff {α : Type} {R : α → α → Prop} {a b : α} {n : Nat} :
    Iterate R (n+1) a b ↔ ∃ c, R a c ∧ Iterate R n c b := by
  constructor
  · exact Iterate.head_induction_on (r := R) (b := b)
      (motive := fun i a _ ↦ match i with | 0 => True | k+1 => ∃ c, R a c ∧ Iterate R k c b)
      trivial (fun c hac hcb _ ↦ ⟨c, hac, hcb⟩)
  · exact fun ⟨_, hac, hcb⟩ ↦ Iterate.head hac hcb

/-- Both the unbounded driver and the cut follow exactly the same `Next` choices. -/
private theorem path_image {α : Type} (F : Nat → Cfg → Tree α)
    (one : ∀ n c t, trans .tau (F (n+1) c) t ↔ ∃ d, Next c d ∧ t = F n d)
    (i : Nat) (c : Cfg) (t : Tree α) :
    Iterate (trans .tau) i (F i c) t ↔ ∃ d, Iterate Next i c d ∧ t = F 0 d := by
  induction i generalizing c with
  | zero => simp [iterate_zero_iff, eq_comm]
  | succ i ih =>
    constructor
    · intro h
      obtain ⟨u, hu, ht⟩ := iterate_succ_iff.1 h
      obtain ⟨b, hb, rfl⟩ := (one i c u).1 hu
      obtain ⟨d, hd, rfl⟩ := (ih b).1 ht
      exact ⟨d, .head hb hd, rfl⟩
    · rintro ⟨d, hd, he⟩
      obtain ⟨b, hb, hd⟩ := iterate_succ_iff.1 hd
      exact .head ((one i c _).2 ⟨b, hb, rfl⟩) ((ih b).2 ⟨d, hd, he⟩)

theorem denote_steps_next_iff (i : Nat) (c : Cfg) (t : Tree (Val × State)) :
    Iterate (trans .tau) i (denote c) t ↔ ∃ d, Iterate Next i c d ∧ t = denote d :=
  path_image (fun _ ↦ denote) (fun _ _ _ ↦ denote_tau_next_iff) i c t

theorem exact_cut_next_iff (i : Nat) (c d : Cfg) :
    (∃ t : Tree Cfg, Iterate (trans .tau) i (cutAfter i c) t ∧ Yields t d) ↔ Iterate Next i c d := by
  constructor
  · rintro ⟨t, ht, hd⟩
    obtain ⟨b, hb, rfl⟩ := (path_image cutAfter (fun _ _ _ ↦ cutAfter_tau_iff) i c t).1 ht
    exact (yields_ret.1 hd : d = b) ▸ hb
  · intro h
    exact ⟨pure d, (path_image cutAfter (fun _ _ _ ↦ cutAfter_tau_iff) i c _).2 ⟨d, h, rfl⟩,
      trans_ret d⟩

theorem denote_steps_iff (i : Nat) (c : Cfg) (t : Tree (Val × State)) :
    Iterate (trans .tau) i (denote c) t ↔ ∃ d : Cfg,
      Language.NSteps (Λ := wasmLanguage) i ([c.1], c.2) [] ([d.1], d.2) ∧ t = denote d := by
  simpa only [iterate_next_iff_nsteps] using denote_steps_next_iff i c t

/-- Unlike equality of denotations, this observes the actual expression, store and frame. -/
theorem exact_config_iff (i : Nat) (c d : Cfg) :
    (∃ t : Tree Cfg, Iterate (trans .tau) i (cutAfter i c) t ∧ Yields t d) ↔
      Language.NSteps (Λ := wasmLanguage) i ([c.1], c.2) [] ([d.1], d.2) :=
  (exact_cut_next_iff i c d).trans (iterate_next_iff_nsteps i c d)

/-- The final layer readout includes pending host calls and takes no Wasm step. -/
theorem exact_result_iff (i : Nat) (c : Cfg) (v : Val) (σ' : State) :
    (∃ (t : Tree Cfg) (d : Cfg), Iterate (trans .tau) i (cutAfter i c) t ∧
      Yields t d ∧ Yields (round d) (.done v, σ')) ↔
      Language.NSteps (Λ := wasmLanguage) i ([c.1], c.2) [] ([ofVal v], σ') := by
  constructor
  · rintro ⟨t, ⟨es, σ⟩, ht, hd, hv⟩
    obtain ⟨he, hs⟩ := round_done_iff.1 hv
    simpa only [of_to_val es v he, hs] using (exact_config_iff i c (es, σ)).1 ⟨t, ht, hd⟩
  · intro h
    obtain ⟨t, ht, hd⟩ := (exact_config_iff i c (ofVal v, σ')).2 h
    exact ⟨t, (ofVal v, σ'), ht, hd, round_done_iff.2 ⟨to_of_val v, rfl⟩⟩

end
end IrisWasm.Denotational
