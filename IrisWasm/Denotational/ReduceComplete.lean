import IrisWasm.Denotational.Observation

/-! Every operational step is available in the interpreted layer, in every outer sequence. -/

namespace IrisWasm.Denotational

open Wasm

private theorem covers_seq {s f es s' f' es'} (h : Covers s f es s' f' es')
    (pre : List Value) (post : Expr) :
    Covers s f (vToEList pre ++ es ++ post) s' f' (vToEList pre ++ es' ++ post) := by
  intro vs tail k
  rw [List.append_assoc, frag_consts, frag_append]
  simpa [vToEList, List.append_assoc] using
    h (pre.reverse ++ vs) (post ++ tail) (fun ws ↦ frag post ws tail k)

private theorem covers_label {s f es s' f' es'} (h : Covers s f es s' f' es') (n : Nat)
    (cont : Expr) : Covers s f [.label n cont es] s' f' [.label n cont es'] := by
  intro vs tail k
  rw [frag, runs_bind]
  refine ⟨.next es', stateOf s' f', ?_, ?_⟩
  · simpa [vToEList] using h [] [] finish
  · simp [labelFront, emit]

private theorem covers_fill {s f s' f' i lh es les} (src : LfilledInd i lh es les)
    {es' les'} (dst : LfilledInd i lh es' les') (h : Covers s f es s' f' es') :
    Covers s f les s' f' les' := by
  induction src generalizing es' les' with
  | lfilledBase pre es post hc =>
    cases dst
    obtain ⟨pre, rfl⟩ := const_es_exists hc
    exact covers_seq h pre post
  | lfilledRec depth pre n cont inside post es body hc hb ih =>
    cases dst with
    | lfilledRec _ _ _ _ _ _ _ body' _ hb' =>
      obtain ⟨pre, rfl⟩ := const_es_exists hc
      exact covers_seq (covers_label (ih hb' h) n cont) pre post

private theorem covers_local {s f es s' f' es'} (h : Covers s f es s' f' es') (n : Nat)
    (caller : Frame) : Covers s caller [.local n f es] s' caller [.local n f' es'] := by
  intro vs tail k
  rw [frag, runs_vis]
  refine ⟨caller, stateOf s f, ?_, runs_bind.mpr ⟨.next es', stateOf s' f', ?_, ?_⟩⟩
  · simp [handle, stateOf]
  · simpa [vToEList] using h [] [] finish
  · exact runs_vis.mpr ⟨f', stateOf s' caller, by simp [handle, stateOf], by simp [localFront, emit]⟩

private theorem withArgs_exact (args vs : List Value) (k : List Value → List Value → Layer) :
    withArgs args.length (args.reverse ++ vs) k = k vs args := by
  have ht := List.take_left (l₁ := args.reverse) (l₂ := vs)
  have hd := List.drop_left (l₁ := args.reverse) (l₂ := vs)
  simp only [List.length_reverse] at ht hd
  simp [withArgs, ht, hd]

private theorem runs_answer {o : WasmE.I} {k : WasmE.O o → Layer} {σ σ₁ σ' x r}
    (answer : handle o σ = pure (x, σ₁)) (rest : Runs (k x) σ₁ r σ') : Runs (.vis o k) σ r σ' :=
  runs_vis.mpr ⟨x, σ₁, answer ▸ yields_ret.mpr rfl, rest⟩

/-- Expose a primitive instruction and perform the state requests justified by its premises. -/
local macro "state_redex" : tactic => `(tactic|
  (intro vs tail k
   simp only [frag, basicLayer, remaining_eq, List.nil_append, Option.all, AddressOperand.ofValue?_value, *]
   repeat' (apply runs_answer; · simp only [handle, stateOf, withMemory, *] <;> rfl)
   simp [emit, resultCode, stateOf, *]))

theorem reduce_covers
    (simple : ∀ {es es' : Expr}, ReduceSimple es es' → ∀ (s : StoreRecord) (f : Frame),
      Covers s f es s f es') {s f es s' f' es'} (h : Reduce s f es s' f' es') :
    Covers s f es s' f' es' := by
  induction h with
  | simple h => exact simple h _ _
  | block hb hc hn | loop hb hc hn =>
    obtain ⟨args, rfl⟩ := Wasm.const_es_exists hc
    simp only [vToEList, List.length_map] at hn
    intro vs tail k
    rw [frag_consts, frag, basicLayer, runs_withBlockType]
    exact ⟨_, hb, by simp [← hn, withArgs_exact, emit, stateOf]⟩
  | label _ _ _ _ _ src dst ih =>
    exact covers_fill ((lfilled_Ind_Equivalent ..).1 src) ((lfilled_Ind_Equivalent ..).1 dst) ih
  | «local» _ ih => exact covers_local ih _ _
  | invokeNative cl ins ts args n k zeros inst hcl hc he ha _ hi ho hz hinst hlocs =>
    subst cl; subst_vars
    intro vs tail k
    rw [frag_consts, frag, invokeLayer]
    apply runs_answer
    · simp only [handle, stateOf, hcl]; rfl
    · simp [hi, withArgs_exact, emit, ← hlocs]
  | invokeHost cl m n hcl hc he ha hi ho =>
    subst cl; subst_vars
    intro vs tail k
    rw [frag_consts, frag, invokeLayer]
    apply runs_answer
    · simp only [handle, stateOf, hcl]; rfl
    · simp [hi, withArgs_exact, emit]
  | @currentMemory i f m n x s hi hm hlen hfit =>
    have hn : memSize m = n := by simp [memSize, hlen, pageSize]
    intro vs tail k
    simp only [frag, basicLayer, remaining_eq, List.nil_append]
    apply runs_answer (x := m.type.address.natValue n) (σ₁ := stateOf s f)
    · simp [handle, stateOf, withMemory, hi, hm, hn, hlen, hfit]
    simp [emit]
  | @growMemorySuccess s i f m n mem x c hind hmem hsize hfit hg =>
    intro vs tail k
    simp only [frag, basicLayer, AddressOperand.ofValue?_value, remaining_eq, List.nil_append, runs_vis]
    refine ⟨c.result n, stateOf (updSMem s (updateListAt s.mems i mem)) f, ?_, ?_⟩
    · simp only [handle, stateOf, withMemory, hind, hmem, hsize, hfit, ite_true, hg,
        ClosedProg.toTree_br, yields_br]
      exact ⟨true, by simp⟩
    · simp [emit]
  | @growMemoryFailure f s x c =>
    intro vs tail k
    simp only [frag, basicLayer, AddressOperand.ofValue?_value, remaining_eq, List.nil_append, runs_vis]
    refine ⟨c.failure, stateOf s f, ?_, ?_⟩
    · simp only [handle, stateOf, withMemory]
      repeat' (split <;> try simp)
    · simp [emit]
  | _ => state_redex

end IrisWasm.Denotational
