import IrisWasm.Denotational.Run

namespace WasmTest.BinopDomain

open Wasm IrisWasm IrisWasm.Denotational

private def redex (t : ValueType) (op : Binop) (a b : Value) : IrisWasm.Expr :=
  [.basic (.const a), .basic (.const b), .basic (.binop t op)]

/-- A mismatched binary redex has no primitive successor, not even a trap. -/
theorem binop_stuck {t op a b} (h : (typesAgree t a && typesAgree t b && binopTypeOK t op) = false)
    (σ σ' : State) (out : IrisWasm.Expr) : ¬ primStep (redex t op a b, σ) [] (out, σ', []) := by
  intro hs
  have hr := round_next_iff.2 hs
  change Runs (layer (redex t op a b)) σ (.next out) σ' at hr
  simp [redex, layer, frag, basicLayer, h] at hr

private abbrev σ₀ : State := (⟨[], [], [], []⟩, [], ⟨[], [], [], [], []⟩)

private def cut (t : ValueType) (op : Binop) (a b : Value) := runCut 1 (redex t op a b, σ₀)

/-- Operand width and operator family are checked before classifying arithmetic failures. -/
theorem binop_domain :
    cut .i32 (.i .add) (.int32 3) (.int32 4) = some ([.basic (.const (.int32 7))], σ₀) ∧
    cut .i32 (.i (.div .s)) (.int32 4) (.int32 0) = some ([.trap], σ₀) ∧
    cut .i32 (.i (.div .s)) (.int32 0x80000000) (.int32 0xffffffff) = some ([.trap], σ₀) ∧
    cut .i32 (.i .add) (.int64 3) (.int64 4) = none ∧
    cut .i32 (.i .add) (.int64 3) (.int32 4) = none ∧
    cut .i32 (.i .add) (.int32 3) (.int64 4) = none ∧
    cut .f32 (.i .add) (.float32 ⟨0⟩) (.float32 ⟨0⟩) = none ∧
    cut .i32 (.i (.div .s)) (.int32 4) (.float32 ⟨0⟩) = none := by
  repeat' apply And.intro
  all_goals decide +kernel

end WasmTest.BinopDomain
