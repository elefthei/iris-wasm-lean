import IrisWasm.Denotational.BasicSound
import IrisWasm.Denotational.ControlSound
import IrisWasm.Denotational.ReduceComplete
import IrisWasm.Denotational.SimpleComplete
import IrisWasm.Denotational.ValueComplete

/-! The native returns of a handled layer are exactly the Wasm reductions and Iris values. -/

namespace IrisWasm.Denotational
open Wasm

private theorem trap_trim_reduce (P : List Value) (T : Expr) (a b : Nat)
    (ha : a ≤ P.length) (hb : b ≤ T.length) (hlt : a + b < P.length + T.length)
    (s : StoreRecord) (f : Frame) :
    Reduce s f (vToEList P ++ .trap :: T) s f
      (vToEList (P.take a) ++ .trap :: T.drop (T.length - b)) := by
  let dead := vToEList (P.drop a) ++ [.trap] ++ T.take (T.length - b)
  have ne : dead ≠ [.trap] := by
    intro h
    have hl := congrArg List.length h
    simp [dead, vToEList] at hl
    omega
  have red : Reduce s f dead s f [.trap] := .simple (.trap (.base (vToEList (P.drop a)) _) ne
    ((lfilled_Ind_Equivalent ..).2 (.lfilledBase _ _ _ (v_to_e_is_const_list _))))
  have hw := wrap_reduce (P.take a) (T.drop (T.length - b)) red
  have he : vToEList (P.take a) ++ (dead ++ T.drop (T.length - b)) = vToEList P ++ .trap :: T := by
    simp only [dead, List.append_assoc, List.cons_append, List.nil_append, List.take_append_drop]
    rw [← List.append_assoc, v_to_e_cat, List.take_append_drop]
  rwa [he] at hw

private theorem trap_sound {vs : List Value} {tail : Expr} {σ σ' : State} {r : Front}
    (h : Runs (trapLayer vs tail) σ r σ') : Represents (vToEList vs.reverse ++ .trap :: tail) σ r σ' := by
  unfold trapLayer at h
  split at h
  · rename_i he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨rfl, rfl⟩ := runs_ret.1 h
    exact ⟨rfl, rfl⟩
  · obtain ⟨⟨⟨a,b⟩, ha, hb, hlt⟩, h⟩ := runs_br.1 h
    obtain ⟨rfl, rfl⟩ := runs_ret.1 h
    exact trap_trim_reduce _ _ _ _ (by simpa using ha) hb (by simpa using hlt) _ _

private theorem label_step {s s' : StoreRecord} {f f' : Frame} {body b : Expr} (n : Nat)
    (cont : Expr) (h : Reduce s f body s' f' b) : Reduce s f [.label n cont body] s' f' [.label n cont b] :=
  .label body b 1 (.rec_ [] n cont (.base [] []) []) h
    (by simp [lfilled, lfill, constList]) (by simp [lfilled, lfill, constList])

private theorem runs_swap {α : Type} {f : Frame} {k : Frame → WasmProg α} {σ σ' : State} {a : α} :
    Runs (.vis (.swapFrame f) k) σ a σ' ↔ Runs (k ⟨σ.2.1, σ.2.2⟩) (stateOf σ.1 f) a σ' := by
  rcases σ with ⟨s, locs, inst⟩
  simp [handle, and_assoc]

private theorem frag_sound (es : Expr) (vs : List Value) {σ σ' : State} {r : Front}
    (h : Runs (frag es vs [] finish) σ r σ') : Represents (vToEList vs.reverse ++ es) σ r σ' := by
  match es with
  | [] =>
    rw [frag] at h
    obtain ⟨rfl, rfl⟩ := runs_ret.1 h
    simp [Represents, ofVal]
  | .basic b :: es =>
    rw [frag] at h
    by_cases hb : ∃ v, b = .const v
    · obtain ⟨v, rfl⟩ := hb
      rw [basicLayer] at h
      simpa [vToEList] using frag_sound es (v :: vs) h
    · exact basic_sound (fun v he ↦ hb ⟨v, he⟩) h
  | .trap :: es => rw [frag] at h; exact trap_sound h
  | .invoke a :: es => rw [frag] at h; exact invoke_sound h
  | .callHost tf hf args :: es =>
    rw [frag] at h
    obtain ⟨rfl, rfl⟩ := runs_ret.1 h
    simp [Represents, ofVal, llfill]
  | .label n cont body :: es =>
    rw [frag] at h
    obtain ⟨r₀, σ₀, inner, outer⟩ := runs_bind.1 h
    have ih : Represents body σ r₀ σ₀ := frag_sound body [] inner
    cases r₀ with
    | next b =>
      obtain ⟨rfl, rfl⟩ := runs_ret.1 outer
      exact wrap_reduce _ es (label_step n cont ih)
    | done v =>
      obtain ⟨he, rfl⟩ := ih
      rw [← he]; exact label_done_sound outer
  | .local n f body :: es =>
    obtain ⟨s, locs, inst⟩ := σ
    rw [frag] at h
    obtain ⟨r₀, ⟨s₀, locs₀, inst₀⟩, inner, outer⟩ := runs_bind.1 (runs_swap.1 h)
    have outer := runs_swap.1 outer
    have ih : Represents body (stateOf s f) r₀ (s₀, locs₀, inst₀) := frag_sound body [] inner
    cases r₀ with
    | next b =>
      obtain ⟨rfl, rfl⟩ := runs_ret.1 outer
      exact wrap_reduce _ es (.local ih)
    | done v =>
      obtain ⟨he, hs⟩ := ih
      cases f; cases hs
      rw [← he]; exact local_done_sound outer
termination_by sizeOf es
decreasing_by all_goals simp_wf; omega

theorem round_done_iff {es : Expr} {σ σ' : State} {v : Val} :
    Yields (round (es, σ)) (.done v, σ') ↔ toVal es = some v ∧ σ' = σ := by
  constructor
  · intro h
    obtain ⟨he, hs⟩ := frag_sound es [] h
    change ofVal v = es at he
    exact ⟨he ▸ to_of_val v, hs⟩
  · rintro ⟨hv, hs⟩
    subst σ'
    rw [← of_to_val es v hv]
    exact ofVal_runs v σ

private theorem round_next_of_covers {s s' : StoreRecord} {f f' : Frame} {es es' : Expr}
    (h : Covers s f es s' f' es') :
    Yields (round (es, stateOf s f)) (.next es', stateOf s' f') := by
  simpa [vToEList, round, roundProg, layer, Runs] using h [] [] finish

theorem round_next_iff {es es' : Expr} {σ σ' : State} :
    Yields (round (es, σ)) (.next es', σ') ↔ primStep (es, σ) [] (es', σ', []) := by
  obtain ⟨s, locs, inst⟩ := σ
  obtain ⟨s', locs', inst'⟩ := σ'
  constructor
  · intro h
    exact ⟨frag_sound es [] h, rfl, rfl⟩
  · rintro ⟨h, _, _⟩
    exact round_next_of_covers (reduce_covers (simple_covers ofVal_runs) h)

def Next (c d : Cfg) : Prop := Yields (round c) (.next d.1, d.2)

/-- The executable chooser selects an actual primitive step, not just a possible return value. -/
theorem runRound_next {c d : Cfg} (h : runRound c = some (.next d.1, d.2)) :
    primStep c [] (d.1, d.2, []) :=
  round_next_iff.mp (runRound_sound c h)

theorem runRound_done {c : Cfg} {v : Val} {σ : State}
    (h : runRound c = some (.done v, σ)) : toVal c.1 = some v ∧ σ = c.2 :=
  round_done_iff.mp (runRound_sound c h)

end IrisWasm.Denotational
