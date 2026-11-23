import IrisWasm.Denotational.Layer

/-! State interpretation ends before the visible Wasm step or host request. -/

namespace IrisWasm.Denotational

open Wasm CTree

/-- The sole input to both the executable chooser and the native round. -/
def roundProg (c : Cfg) : ClosedProg (Front × State) := close (layer c.1) c.2

def runRound (c : Cfg) : Option (Front × State) := ClosedProg.run (roundProg c)

noncomputable def round (c : Cfg) : Tree (Front × State) := ClosedProg.toTree (roundProg c)

/-- A pending host call resumes in its saved context, with the store supplied by the host. -/
noncomputable def denote (c : Cfg) : Tree (Val × State) :=
  round c >>= fun
    | (.next es, σ) => .step (denote (es, σ))
    | (.done (.callHostV tf h args lh), (_, locs, inst)) =>
      .vis (tf, h, args) fun (s', res) ↦ denote (llfill lh res, s', locs, inst)
    | (.done v, σ) => pure (v, σ)
partial_fixpoint

/-- Hidden branches and state requests cannot diverge or contribute a native τ. -/
theorem round_finite (c : Cfg) : PureFinite (round c) :=
  ClosedProg.finite _

end IrisWasm.Denotational
