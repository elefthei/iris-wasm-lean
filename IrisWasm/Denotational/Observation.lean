import IrisWasm.Denotational.Semantics

/-! Equations for finite observations. They eliminate a request or hidden choice without a τ. -/

namespace IrisWasm.Denotational

open Wasm CTree

variable {α β : Type}

def Yields (t : Tree α) (x : α) : Prop := trans (.val x) t .stuck

def Runs (p : WasmProg α) (σ : State) (x : α) (σ' : State) : Prop :=
  Yields (ClosedProg.toTree (close p σ)) (x, σ')

@[simp] theorem yields_ret {a b : α} : Yields (pure a) b ↔ b = a :=
  ⟨fun h ↦ val_eq_inv (trans_ret_inv h).2, fun h ↦ h ▸ trans_ret a⟩

@[simp] theorem yields_stuck {x : α} : ¬ Yields .stuck x := trans_stuck_inv

@[simp] theorem yields_guard {t : Tree α} {x : α} : Yields (.guard t) x ↔ Yields t x :=
  ⟨trans_guard_inv, trans_guard⟩

@[simp] theorem yields_br {c : ChoiceE.I} {k : ChoiceE.O c → Tree α} {x : α} :
    Yields (.br c k) x ↔ ∃ y, Yields (k y) x := ⟨trans_br_inv, fun ⟨y, h⟩ ↦ trans_br y h⟩

@[simp] theorem yields_bind {t : Tree α} {k : α → Tree β} {x : β} :
    Yields (t >>= k) x ↔ ∃ y, Yields t y ∧ Yields (k y) x := by
  constructor
  · intro h
    exact (trans_bind_inv h).resolve_left fun hn ↦ hn.1 (.val x)
  · exact fun ⟨_, h, h'⟩ ↦ trans_bind_r h h'

/-- Native observations are exactly finite, occurrence-by-occurrence choice witnesses. -/
theorem ClosedProg.yields_iff_path (p : ClosedProg α) (x : α) :
    Yields (toTree p) x ↔ ∃ path : Path p, path.result = x := by
  induction p with
  | ret a =>
    constructor
    · intro h
      exact ⟨.ret a, (yields_ret.mp h).symm⟩
    · rintro ⟨path, h⟩
      cases path
      exact yields_ret.mpr h.symm
  | stuck =>
    constructor
    · intro h; exact (yields_stuck h).elim
    · rintro ⟨path, _⟩; cases path
  | vis o => exact nomatch o
  | br b k ih =>
    constructor
    · intro h
      obtain ⟨y, hy⟩ := yields_br.mp h
      obtain ⟨path, hp⟩ := (ih y).mp hy
      exact ⟨.br y path, hp⟩
    · rintro ⟨path, hp⟩
      cases path with
      | br y rest => exact yields_br.mpr ⟨y, (ih y).mpr ⟨rest, hp⟩⟩

theorem ClosedProg.run_sound (p : ClosedProg α) {x : α} :
    run p = some x → Yields (toTree p) x := by
  induction p with
  | ret => simp [run, toTree, eq_comm]
  | stuck => simp [run]
  | vis o => exact nomatch o
  | br b k ih =>
    intro h
    obtain ⟨y, _, hy⟩ := Option.bind_eq_some_iff.mp h
    exact yields_br.mpr ⟨y, ih y hy⟩

theorem runRound_sound (c : Cfg) {p : Front × State} :
    runRound c = some p → Yields (round c) p := ClosedProg.run_sound _

-- The second occurrence of grow can fail on a native path even if the first succeeded.
example :
    let twice : ClosedProg (Bool × Bool) :=
      .br .grow fun a ↦ .br .grow fun b ↦ .ret (a, b)
    ClosedProg.run twice = some (true, true) ∧
      Yields (ClosedProg.toTree twice) (true, false) := by
  refine ⟨rfl, (ClosedProg.yields_iff_path _ _).2 ⟨.br true (.br false (.ret _)), rfl⟩⟩

@[simp] theorem runs_ret {a b : α} {σ σ' : State} : Runs (pure a) σ b σ' ↔ b = a ∧ σ' = σ := by
  change Yields (pure (a, σ)) (b, σ') ↔ _
  simp

@[simp] theorem runs_stuck {σ σ' : State} {a : α} : ¬ Runs .stuck σ a σ' :=
  yields_stuck

@[simp] theorem runs_vis {o : WasmE.I} {k : WasmE.O o → WasmProg α} {σ σ' : State} {a : α} :
    Runs (.vis o k) σ a σ' ↔
      ∃ x σ₁, Yields (ClosedProg.toTree (handle o σ)) (x, σ₁) ∧ Runs (k x) σ₁ a σ' := by
  simp [Runs, close, ClosedProg.toTree_bind]

@[simp] theorem runs_br {c : ChoiceE.I} {k : ChoiceE.O c → WasmProg α} {a : α} {σ σ' : State} :
    Runs (.br c k) σ a σ' ↔ ∃ x, Runs (k x) σ a σ' := yields_br

@[simp] theorem runs_bind {t : WasmProg α} {k : α → WasmProg β} {σ σ' : State} {b : β} :
    Runs (t >>= k) σ b σ' ↔ ∃ a σ₁, Runs t σ a σ₁ ∧ Runs (k a) σ₁ b σ' := by
  simp [Runs, close_bind, ClosedProg.toTree_bind]

theorem runs_withBlockType {bt : Wasm.BlockType} {k : FunctionType → WasmProg α} {σ σ' : State}
    {x : α} : Runs (withBlockType bt k) σ x σ' ↔
    ∃ tf, expandBlockType σ.2.2.types bt = some tf ∧ Runs (k tf) σ x σ' := by
  rcases σ with ⟨s, locs, inst⟩
  cases bt with
  | result t => simp [withBlockType, expandBlockType]
  | index i =>
    rw [withBlockType, runs_vis]
    constructor
    · rintro ⟨answer, st, ha, hr⟩
      have e : (answer, st) = (inst.types[i]?, (s, locs, inst)) := yields_ret.mp ha
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
      cases h : inst.types[i]? with
      | none => rw [h] at hr; exact False.elim (runs_stuck hr)
      | some tf => exact ⟨tf, h, by simpa only [h] using hr⟩
    · rintro ⟨tf, ht, hr⟩
      refine ⟨some tf, (s, locs, inst), ?_, hr⟩
      apply yields_ret.mpr
      exact Prod.ext ht.symm rfl

abbrev stateOf (s : StoreRecord) (f : Frame) : State := (s, f.locs, f.inst)

/-- The inversion invariant for any leaf, including ones inside structured instructions. -/
def Represents (es : Expr) (σ : State) (r : Front) (σ' : State) : Prop :=
  match r with
  | .next es' => Reduce σ.1 ⟨σ.2.1, σ.2.2⟩ es σ'.1 ⟨σ'.2.1, σ'.2.2⟩ es'
  | .done v => ofVal v = es ∧ σ' = σ

/-- A redex still takes its step under every outer constant prefix and syntax suffix. -/
def Covers (s : StoreRecord) (f : Frame) (es : Expr) (s' : StoreRecord) (f' : Frame) (es' : Expr) : Prop :=
  ∀ (vs : List Value) (tail : Expr) (k : List Value → Layer),
    Runs (frag es vs tail k) (stateOf s f) (.next (vToEList vs.reverse ++ (es' ++ tail))) (stateOf s' f')

theorem wrap_reduce {s s' : StoreRecord} {f f' : Frame} {es es' : Expr} (pre : List Value)
    (tail : Expr) (h : Reduce s f es s' f' es') :
    Reduce s f (vToEList pre ++ (es ++ tail)) s' f' (vToEList pre ++ (es' ++ tail)) := by
  apply Reduce.label es es' 0 (.base (vToEList pre) tail) h <;>
    simpa [← List.append_assoc] using (lfilled_Ind_Equivalent ..).2
      (LfilledInd.lfilledBase (vToEList pre) _ tail (v_to_e_is_const_list pre))

end IrisWasm.Denotational
