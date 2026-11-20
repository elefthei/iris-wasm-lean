/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Logrel.IrisFundamentalTrap

/-! Port of `theories/iris/logrel/iris_fundamental_cvtop.v`. -/

namespace IrisWasm

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm

variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF] [LogrelNaInvs GF]

omit [LogrelNaInvs GF] in
@[rocq_alias iriswasm.interp_value_cvt]
theorem interp_value_cvt (t1 : ValueType) (sx : Option Sx) (w1 v : Value) :
    cvt t1 sx w1 = some v → ⊢ (interpValue t1 v : IProp GF) := by
  intro h
  cases t1 <;> simp [cvt] at h <;> obtain ⟨a, -, rfl⟩ := h <;>
    simp only [interpValue, interpValueI32, interpValueI64, interpValueF32, interpValueF64] <;>
    ipureintro <;> exact ⟨a, rfl⟩

omit [LogrelNaInvs GF] in
@[rocq_alias iriswasm.interp_value_reinterpret]
theorem interp_value_reinterpret (t1 : ValueType) (w1 : Value) :
    ⊢ (interpValue t1 (wasmDeserialise (bits w1) t1) : IProp GF) := by
  cases t1 <;> simp only [interpValue, interpValueI32, interpValueI64, interpValueF32,
    interpValueF64, wasmDeserialise] <;> ipureintro <;> exact ⟨_, rfl⟩

@[rocq_alias iriswasm.typing_cvtop_convert]
theorem typing_cvtop_convert (C : TContext) (t1 t2 : ValueType) (sx : Option Sx) :
    ⊢ (semanticTyping C (toEList [.cvtop t1 .convert t2 sx]) (.tf [t2] [t1]) : IProp GF) := by
  apply semantic_typing_immV
  intro i lh hl f ws
  iintro #Hi #Hctx Hf Hfv Hv
  ihave %Hlen := BI.BigSepL2.bigSepL2_length $$ Hv
  rcases ws with _ | ⟨w1, _ | ⟨_, _⟩⟩ <;> simp at Hlen
  icases Hv with ⟨Hv1, -⟩
  ihave %Ht := interp_value_types_agree t2 w1 $$ Hv1
  simp only [ofVal, vToEList, toEList, List.map_nil, List.map_cons, List.cons_append, List.nil_append]
  cases hs : cvt t1 sx w1 with
  | some w =>
    iapply interp_expression_of_wp $$ [Hf] Hfv
    · iapply wp_cvtop_convert hs Ht $$ Hf
      inext; ipureintro; rfl
    · unfold interpVal interpValues; iright; iexists [w]
      isplitr
      · ipureintro; rfl
      · isplitl
        · iapply interp_value_cvt t1 sx w1 w hs
        · iempintro
  | none =>
    iapply interp_expression_of_wp $$ [Hf] Hfv
    · iapply wp_cvtop_convert_failure hs Ht $$ Hf
      inext; ipureintro; rfl
    · unfold interpVal; ileft; ipureintro; rfl

@[rocq_alias iriswasm.typing_cvtop_reinterpret]
theorem typing_cvtop_reinterpret (C : TContext) (t1 t2 : ValueType) :
    ⊢ (semanticTyping C (toEList [.cvtop t1 .reinterpret t2 none]) (.tf [t2] [t1]) : IProp GF) := by
  apply semantic_typing_immV
  intro i lh hl f ws
  iintro #Hi #Hctx Hf Hfv Hv
  ihave %Hlen := BI.BigSepL2.bigSepL2_length $$ Hv
  rcases ws with _ | ⟨w1, _ | ⟨_, _⟩⟩ <;> simp at Hlen
  icases Hv with ⟨Hv1, -⟩
  ihave %Ht := interp_value_types_agree t2 w1 $$ Hv1
  simp only [ofVal, vToEList, toEList, List.map_nil, List.map_cons, List.cons_append, List.nil_append]
  iapply interp_expression_of_wp $$ [Hf] Hfv
  · iapply wp_cvtop_reinterpret rfl Ht $$ Hf
    inext; ipureintro; rfl
  · unfold interpVal interpValues; iright; iexists [_]
    isplitr
    · ipureintro; rfl
    · isplitl
      · iapply interp_value_reinterpret
      · iempintro

end IrisWasm
