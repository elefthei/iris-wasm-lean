/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Logrel.IrisFundamentalHelpers

/-! Port of `theories/iris/logrel/iris_fundamental_trap.v`.

Also hosts two Lean-only helpers shared by the simple fundamental cases (`IrisFundamental<Case>`):
every Coq case proof starts with the same trap-input case and ends with the same `wp_wand` into
`interp_expression`; they are factored out here. -/

namespace IrisWasm

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm

variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF] [LogrelNaInvs GF]

/-! Lean-only: the Wasm points-to connectives are timeless (their `genHeapGS` is a field of
`WasmG`, not an instance, so iris-lean's generic instance is not found automatically). -/

omit [LogrelNaInvs GF] in
instance wgPointsTo_timeless (n : Nat) (q : DFrac) (g : Global) :
    Timeless (iprop(n ↦[wg]{ q } g) : IProp GF) :=
  @instTimelessPointsTo _ _ _ _ _ WasmG.globHs _ _ _

omit [LogrelNaInvs GF] in
instance wmPointsTo_timeless (n i : Nat) (q : DFrac) (b : Byte) :
    Timeless (iprop(n ↦[wm]{ q }[ i ] b) : IProp GF) :=
  @instTimelessPointsTo _ _ _ _ _ WasmG.memHs _ _ _

omit [LogrelNaInvs GF] in
instance wmlengthPointsTo_timeless (n k : Nat) :
    Timeless (iprop(n ↦[wmlength] k) : IProp GF) :=
  @instTimelessPointsTo _ _ _ _ _ WasmG.memsizeHs _ _ _

/-- Lean-only: reduces `semantic_typing` to the case of an immediate-value input (the trap input
is discharged by `wp_trap`, as every Coq case proof does first). -/
theorem semantic_typing_immV (C : TContext) (es : Expr) (τ1 τ2 : List ValueType)
    (h : ∀ i lh hl f ws, ⊢ (interpInstance C hl i -∗ interpCtx C.label C.return_ hl C.local_ i lh -∗
      ↪[frame] f -∗ interpFrame C.local_ i f -∗ ([∗list] w;τ ∈ ws;τ1, interpValue τ w) -∗
      interpExpression C.label C.return_ hl τ2 lh C.local_ i (ofVal (.immV ws) ++ es) : IProp GF)) :
    ⊢ (semanticTyping C es (.tf τ1 τ2) : IProp GF) := by
  unfold semanticTyping
  iintro %i %lh %hl #Hi #Hctx %f %vs ⟨Hf, Hfv⟩ #Hv
  unfold interpVal interpValues
  icases Hv with (%Heq | ⟨%ws, %Heq, Hv⟩)
  · subst Heq
    have ht := wp_trap (GF := GF) .NotStuck ⊤ (fun v => iprop(⌜v = Val.trapV⌝)) [] es f rfl
    rw [List.nil_append] at ht
    unfold interpExpression
    simp only [ofVal]
    iapply IrisWp.wp_wand (ι := wasmIrisGS) (fun f => iprop(↪[frame] f))
      (Φ := fun v => iprop(⌜v = Val.trapV⌝ ∗ ↪[frame] f)) $$ [Hf]
    · iapply ht $$ [] Hf
      ipureintro; rfl
    · iintro %v ⟨%rfl, Hf⟩
      isplitr
      · ileft; unfold interpVal; ileft; ipureintro; rfl
      · iexists f; iframe
  · subst Heq
    iapply h $$ Hi Hctx Hf Hfv Hv

/-- Lean-only: a WP whose result is `v` with the frame `f` unchanged gives `interp_expression`
when `v` is in the value relation. -/
theorem interp_expression_of_wp (τc : List (List ValueType)) (τto : Option (List ValueType))
    (hl : List (Hostfuncidx × FunctionType)) (τ2 : List ValueType) (lh : Lholed)
    (τl : List ValueType) (i : Instance) (es : Expr) (f : Frame) (v : Val) :
    ⊢ (WP es {{ w, ⌜w = v⌝ ∗ ↪[frame] f }} -∗ interpFrame τl i f -∗ interpVal τ2 v -∗
      interpExpression τc τto hl τ2 lh τl i es : IProp GF) := by
  iintro Hwp Hfv Hv
  unfold interpExpression
  iapply IrisWp.wp_wand (ι := wasmIrisGS) (fun f => iprop(↪[frame] f)) $$ Hwp
  iintro %w ⟨%rfl, Hf⟩
  isplitl [Hv]
  · ileft; iexact Hv
  · iexists f; iframe

omit [LogrelNaInvs GF] in
/-- Lean-only: a value expression reduces to itself, keeping the frame. -/
theorem wp_ofVal_frame (v : Val) (f : Frame) :
    ⊢ (↪[frame] f -∗ WP (ofVal v) {{ w, ⌜w = v⌝ ∗ ↪[frame] f }} : IProp GF) := by
  iintro Hf
  iapply IrisWp.wp_value' (ι := wasmIrisGS) (fun f => iprop(↪[frame] f)) (v := v)
  iframe; ipureintro; rfl

omit [LogrelNaInvs GF] in
/-- Lean-only: a value in the relation of `t` has type `t`. -/
theorem interp_value_types_agree (t : ValueType) (w : Value) :
    ⊢ (interpValue t w -∗ ⌜typesAgree t w = true⌝ : IProp GF) := by
  cases t <;> simp only [interpValue, interpValueI32, interpValueI64, interpValueF32,
    interpValueF64] <;> iintro %⟨z, rfl⟩ <;> ipureintro <;> rfl

@[rocq_alias iriswasm.typing_trap]
theorem typing_trap (C : TContext) (tf : FunctionType) :
    ⊢ (semanticTyping C [.trap] tf : IProp GF) := by
  obtain ⟨τ1, τ2⟩ := tf
  apply semantic_typing_immV
  intro i lh hl f ws
  iintro #Hi #Hctx Hf Hfv Hv
  have ht := wp_trap (GF := GF) .NotStuck ⊤ (fun v => iprop(⌜v = Val.trapV⌝))
    (ofVal (.immV ws)) [] f (const_list_of_val ws)
  rw [List.append_nil] at ht
  iapply interp_expression_of_wp $$ [Hf] Hfv
  · iapply ht $$ [] Hf
    ipureintro; rfl
  · unfold interpVal; ileft; ipureintro; rfl

end IrisWasm
