import IrisWasm.Denotational.Run

namespace WasmTest.RelopDomain

open Wasm IrisWasm IrisWasm.Denotational

private def redex (a b : Value) (t : ValueType) (op : Relop) : IrisWasm.Expr :=
  [.basic (.const a), .basic (.const b), .basic (.relop t op)]

/-- An ill-shaped comparison has no primitive successor, including a trap. -/
theorem relop_stuck {a b t op} (h : (typesAgree t a && typesAgree t b && relopTypeOK t op) = false)
    (σ σ' : State) (out : IrisWasm.Expr) : ¬ primStep (redex a b t op, σ) [] (out, σ', []) := by
  intro hs
  have hr := round_next_iff.2 hs
  change Runs (layer (redex a b t op)) σ (.next out) σ' at hr
  simp [redex, layer, frag, basicLayer, h] at hr

private abbrev σ₀ : State := (⟨[], [], [], []⟩, [], ⟨[], [], [], [], []⟩)

private def cut (a b : Value) (t : ValueType) (op : Relop) := runCut 1 (redex a b t op, σ₀)

/-- Both operand positions and the opcode family are checked before evaluating the comparison. -/
theorem relop_domain :
    cut (.int32 2) (.int32 7) .i32 (.i (.lt .u)) = some ([.basic (.const (.int32 1))], σ₀) ∧
    cut (.float32 ⟨0x7fc00000⟩) (.float32 ⟨0x7fc00000⟩) .f32 (.f .eq) =
      some ([.basic (.const (.int32 0))], σ₀) ∧
    cut (.int64 1) (.int64 1) .i32 (.i .eq) = none ∧
    cut (.int64 1) (.int32 1) .i32 (.i .eq) = none ∧
    cut (.int32 1) (.int64 1) .i32 (.i .eq) = none ∧
    cut (.int32 1) (.int32 1) .i32 (.f .eq) = none := by decide +kernel

end WasmTest.RelopDomain
