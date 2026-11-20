/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Logrel.IrisFundamentalTrap

/-! Port of `theories/iris/logrel/iris_fundamental_binop.v`. -/

namespace IrisWasm

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm

variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF] [LogrelNaInvs GF]

omit [LogrelNaInvs GF] in
@[rocq_alias iriswasm.binop_type_agree_interp]
theorem binop_type_agree_interp (t : ValueType) (op : Binop) (w1 w2 : Value) :
    BinopTypeAgree t op →
    ⊢ (interpValue t w1 -∗ interpValue t w2 -∗
      ∀ w, ⌜appBinop op w1 w2 = some w⌝ -∗ interpValue t w : IProp GF) := by
  intro h
  cases h <;> simp only [interpValue, interpValueI32, interpValueI64, interpValueF32,
    interpValueF64] <;> iintro %⟨z1, rfl⟩ %⟨z2, rfl⟩ %w %hw <;> ipureintro <;>
    simp [appBinop] at hw <;> obtain ⟨a, -, rfl⟩ := hw <;> exact ⟨a, rfl⟩

@[rocq_alias iriswasm.typing_binop]
theorem typing_binop (C : TContext) (t : ValueType) (op : Binop) :
    BinopTypeAgree t op →
    ⊢ (semanticTyping C (toEList [.binop t op]) (.tf [t, t] [t]) : IProp GF) := by
  intro hop
  apply semantic_typing_immV
  intro i lh hl f ws
  iintro #Hi #Hctx Hf Hfv Hv
  ihave %Hlen := BI.BigSepL2.bigSepL2_length $$ Hv
  rcases ws with _ | ⟨w1, _ | ⟨w2, _ | ⟨_, _⟩⟩⟩ <;> simp at Hlen
  icases Hv with ⟨Hv1, Hv2, -⟩
  simp only [ofVal, vToEList, toEList, List.map_nil, List.map_cons, List.cons_append, List.nil_append]
  cases hs : appBinop op w1 w2 with
  | some w =>
    iapply interp_expression_of_wp $$ [Hf] Hfv
    · iapply wp_binop hs $$ Hf
      inext; ipureintro; rfl
    · unfold interpVal interpValues; iright; iexists [w]
      isplitr
      · ipureintro; rfl
      · isplitl
        · iapply binop_type_agree_interp t op w1 w2 hop $$ Hv1 Hv2 %w %hs
        · iempintro
  | none =>
    iapply interp_expression_of_wp $$ [Hf] Hfv
    · iapply wp_binop_failure hs $$ [] Hf
      inext; ipureintro; rfl
    · unfold interpVal; ileft; ipureintro; rfl

end IrisWasm
