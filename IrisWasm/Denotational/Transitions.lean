import IrisWasm.Denotational.LayerCorrect

/-! Native transitions of the Wasm resumption, including its visible host requests. -/

namespace IrisWasm.Denotational
open Wasm CTree

private theorem trans_denote {c : Cfg} {l : Label HostCallE} {t : Tree (Val × State)} :
    trans l (denote c) t ↔ ∃ p, Yields (round c) p ∧ trans l (match p with
      | (.next es, σ) => .step (denote (es, σ))
      | (.done (.callHostV tf h args lh), (_, locs, inst)) =>
        .vis (tf, h, args) fun (s', res) ↦ denote (llfill lh res, s', locs, inst)
      | (.done v, σ) => pure (v, σ)) t := by
  conv => lhs; rw [denote.eq_1]
  constructor
  · exact trans_bind_pure (pure_pure_finite (round_finite c))
  · rintro ⟨p, hp, ht⟩; exact trans_bind_r hp ht

/-- A native silent transition always follows one residual of the handled layer. -/
theorem denote_tau_next_iff {c : Cfg} {t : Tree (Val × State)} :
    trans .tau (denote c) t ↔ ∃ d : Cfg, Next c d ∧ t = denote d := by
  rw [trans_denote]
  constructor
  · rintro ⟨⟨es | v, σ⟩, hp, ht⟩
    · exact ⟨(es, σ), hp, (trans_step_inv ht).1⟩
    · cases v <;> first | cases (trans_ret_inv ht).2 | obtain ⟨_, _, he⟩ := trans_vis_inv ht; cases he
  · rintro ⟨⟨es, σ⟩, hp, rfl⟩; exact ⟨(.next es, σ), hp, trans_step _⟩

theorem denote_tau_iff {c : Cfg} {t : Tree (Val × State)} :
    trans .tau (denote c) t ↔ ∃ d : Cfg, primStep c [] (d.1, d.2, []) ∧ t = denote d := by
  rcases c with ⟨es, σ⟩
  simp only [denote_tau_next_iff, Next, round_next_iff]

/-- A host request is an Iris value, but not a native return from the resumption. -/
def NonHost : Val → Prop
  | .callHostV .. => False
  | _ => True

theorem denote_val_iff {c : Cfg} {v : Val} {σ' : State} {t : Tree (Val × State)} :
    trans (.val (v, σ')) (denote c) t ↔
      toVal c.1 = some v ∧ NonHost v ∧ σ' = c.2 ∧ t = .stuck := by
  rw [trans_denote]
  constructor
  · rintro ⟨⟨es | w, σ⟩, hp, ht⟩
    · cases (trans_step_inv ht).2
    · obtain ⟨hv, rfl⟩ := round_done_iff.1 hp
      cases w <;> first
        | obtain ⟨hs, he⟩ := trans_ret_inv ht; cases he; exact ⟨hv, trivial, rfl, hs⟩
        | obtain ⟨_, _, he⟩ := trans_vis_inv ht; cases he
  · rintro ⟨hv, hn, rfl, rfl⟩
    refine ⟨(.done v, c.2), round_done_iff.2 ⟨hv, rfl⟩, ?_⟩
    cases v <;> first | exact trans_ret _ | exact False.elim hn

theorem denote_host_iff {es : Expr} {s s' : StoreRecord} {locs : List Value} {inst : Instance}
    {tf : FunctionType} {h : Hostfuncidx} {args : List Value} {res : Expr} {t : Tree (Val × State)} :
    trans (.obs (tf, h, args) (s', res)) (denote (es, s, locs, inst)) t ↔
      ∃ lh, toVal es = some (.callHostV tf h args lh) ∧ t = denote (llfill lh res, s', locs, inst) := by
  rw [trans_denote]
  constructor
  · rintro ⟨⟨es' | v, σ⟩, hp, ht⟩
    · cases (trans_step_inv ht).2
    · obtain ⟨hv, rfl⟩ := round_done_iff.1 hp
      cases v <;> first
        | cases (trans_ret_inv ht).2
        | obtain ⟨_, hs, he⟩ := trans_vis_inv ht; cases he; exact ⟨_, hv, hs⟩
  · rintro ⟨lh, hv, rfl⟩
    refine ⟨(_, _), round_done_iff.2 ⟨hv, rfl⟩, ?_⟩
    exact trans_vis (E := HostCallE) (e := (tf, h, args)) (s', res)
      (fun reply ↦ denote (llfill lh reply.2, reply.1, locs, inst))

end IrisWasm.Denotational
