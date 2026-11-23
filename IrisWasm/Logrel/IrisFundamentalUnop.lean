/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Logrel.IrisFundamentalTrap

/-! Port of `theories/iris/logrel/iris_fundamental_unop.v`. -/

namespace IrisWasm

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm

variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF] [LogrelNaInvs GF]

omit [LogrelNaInvs GF] in
@[rocq_alias iriswasm.unop_type_agree_interp]
theorem unop_type_agree_interp (t : ValueType) (op : Unop) (w : Value) :
    UnopTypeAgree t op → ⊢ (interpValue t w -∗ interpValue t (appUnop op w) : IProp GF) := by
  intro h
  cases h <;> cases w <;> simp [interpValue, interpValueI32, interpValueI64, interpValueF32,
    interpValueF64, interpValueV128, appUnop] <;> (iintro H; iexact H)

@[rocq_alias iriswasm.typing_unop]
theorem typing_unop (C : TContext) (t : ValueType) (op : Unop) :
    UnopTypeAgree t op → ⊢ (semanticTyping C (toEList [.unop t op]) (.tf [t] [t]) : IProp GF) := by
  intro hop
  apply semantic_typing_immV
  intro i lh hl f ws
  iintro #Hi #Hctx Hf Hfv Hv
  ihave %Hlen := BI.BigSepL2.bigSepL2_length $$ Hv
  rcases ws with _ | ⟨w, _ | ⟨_, _⟩⟩ <;> simp at Hlen
  icases Hv with ⟨Hw, -⟩
  ihave %Ht := interp_value_types_agree t w $$ Hw
  simp only [ofVal, vToEList, toEList, List.map_nil, List.map_cons, List.cons_append, List.nil_append]
  iapply interp_expression_of_wp $$ [Hf] Hfv
  · iapply wp_unop Ht hop rfl $$ Hf
    inext; ipureintro; rfl
  · unfold interpVal interpValues; iright; iexists [appUnop op w]
    isplitr
    · ipureintro; rfl
    · isplitl
      · iapply unop_type_agree_interp t op w hop $$ Hw
      · iempintro

end IrisWasm
