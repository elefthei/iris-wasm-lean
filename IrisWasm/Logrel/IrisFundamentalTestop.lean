/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Logrel.IrisFundamentalTrap

/-! Port of `theories/iris/logrel/iris_fundamental_testop.v`. -/

namespace IrisWasm

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm

variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF] [LogrelNaInvs GF]

theorem typing_testop (C : TContext) (t : ValueType) (op : Testop) :
    testopTypeOK t op = true →
    ⊢ (semanticTyping C (toEList [.testop t op]) (.tf [t] [.i32]) : IProp GF) := by
  intro ht
  apply semantic_typing_immV
  intro i lh hl f ws
  iintro #Hi #Hctx Hf Hfv Hv
  ihave %Hlen := BI.BigSepL2.bigSepL2_length $$ Hv
  rcases ws with _ | ⟨w1, _ | ⟨_, _⟩⟩ <;> simp at Hlen
  icases Hv with ⟨Hv1, -⟩
  simp only [ofVal, vToEList, toEList, List.map_nil, List.map_cons, List.cons_append, List.nil_append]
  ihave %Hw := interp_value_types_agree t w1 $$ Hv1
  have htw : typeof w1 = t := by simpa [typesAgree] using Hw
  subst t
  cases w1 <;> cases op <;> simp [typeof, testopTypeOK, isIntT] at ht
  all_goals simp only [typeof]
  all_goals
    iapply interp_expression_of_wp $$ [Hf] Hfv
    · rename_i x
      first
      | iapply wp_testop_i32 (v := x) $$ Hf
      | iapply wp_testop_i64 (v := x) $$ Hf
      | iapply wp_testop_v128 (v := x) $$ Hf
      inext; ipureintro; rfl
    · unfold interpVal interpValues; iright; iexists [_]
      isplitr
      · ipureintro; rfl
      · isplitl
        · simp only [interpValue, interpValueI32]; ipureintro; exact ⟨_, rfl⟩
        · iempintro

end IrisWasm
