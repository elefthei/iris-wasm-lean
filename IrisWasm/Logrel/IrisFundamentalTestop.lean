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

@[rocq_alias iriswasm.typing_testop]
theorem typing_testop (C : TContext) (t : ValueType) (op : Testop) :
    isIntT t = true →
    ⊢ (semanticTyping C (toEList [.testop t op]) (.tf [t] [.i32]) : IProp GF) := by
  intro ht
  apply semantic_typing_immV
  intro i lh hl f ws
  iintro #Hi #Hctx Hf Hfv Hv
  ihave %Hlen := BI.BigSepL2.bigSepL2_length $$ Hv
  rcases ws with _ | ⟨w1, _ | ⟨_, _⟩⟩ <;> simp at Hlen
  icases Hv with ⟨Hv1, -⟩
  simp only [ofVal, vToEList, toEList, List.map_nil, List.map_cons, List.cons_append, List.nil_append]
  cases t <;> simp [isIntT] at ht
  · ihave %Hz : ⌜∃ z, w1 = Value.int32 z⌝ $$ [Hv1]
    · simp only [interpValue, interpValueI32]; iexact Hv1
    obtain ⟨z, rfl⟩ := Hz
    iapply interp_expression_of_wp $$ [Hf] Hfv
    · iapply wp_testop_i32 rfl $$ Hf
      inext; ipureintro; rfl
    · unfold interpVal interpValues; iright; iexists [_]
      isplitr
      · ipureintro; rfl
      · isplitl
        · simp only [interpValue, interpValueI32]; ipureintro; exact ⟨_, rfl⟩
        · iempintro
  · ihave %Hz : ⌜∃ z, w1 = Value.int64 z⌝ $$ [Hv1]
    · simp only [interpValue, interpValueI64]; iexact Hv1
    obtain ⟨z, rfl⟩ := Hz
    iapply interp_expression_of_wp $$ [Hf] Hfv
    · iapply wp_testop_i64 rfl $$ Hf
      inext; ipureintro; rfl
    · unfold interpVal interpValues; iright; iexists [_]
      isplitr
      · ipureintro; rfl
      · isplitl
        · simp only [interpValue, interpValueI32]; ipureintro; exact ⟨_, rfl⟩
        · iempintro

end IrisWasm
