/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Logrel.IrisFundamentalTrap

/-! Port of `theories/iris/logrel/iris_fundamental_relop.v`. -/

namespace IrisWasm

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm

variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF] [LogrelNaInvs GF]

@[rocq_alias iriswasm.typing_relop]
theorem typing_relop (C : TContext) (t : ValueType) (op : Relop) :
    RelopTypeAgree t op →
    ⊢ (semanticTyping C (toEList [.relop t op]) (.tf [t, t] [.i32]) : IProp GF) := by
  intro hop
  apply semantic_typing_immV
  intro i lh hl f ws
  iintro #Hi #Hctx Hf Hfv Hv
  ihave %Hlen := BI.BigSepL2.bigSepL2_length $$ Hv
  rcases ws with _ | ⟨w1, _ | ⟨w2, _ | ⟨_, _⟩⟩⟩ <;> simp at Hlen
  icases Hv with ⟨Hw1, Hw2, -⟩
  ihave %Ht1 := interp_value_types_agree t w1 $$ Hw1
  ihave %Ht2 := interp_value_types_agree t w2 $$ Hw2
  simp only [ofVal, vToEList, toEList, List.map_nil, List.map_cons, List.cons_append, List.nil_append]
  iapply interp_expression_of_wp $$ [Hf] Hfv
  · iapply wp_relop Ht1 Ht2 hop rfl $$ Hf
    inext; ipureintro; rfl
  · unfold interpVal interpValues; iright; iexists [_]
    isplitr
    · ipureintro; rfl
    · isplitl
      · simp only [interpValue, interpValueI32]; ipureintro; exact ⟨_, rfl⟩
      · iempintro

end IrisWasm
