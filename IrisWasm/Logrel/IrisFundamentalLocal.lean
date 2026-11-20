/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Logrel.IrisFundamentalStuckHost

/-! Port of `theories/iris/logrel/iris_fundamental_local.v`. -/

namespace IrisWasm

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm

variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF] [LogrelNaInvs GF]

attribute [local instance] WasmG.invGS

#rocq_ignore iriswasm.iris_fundamental_local.to_val_call_host_label_inv
  "verbatim duplicate of `to_val_call_host_label_inv` in iris_fundamental_helpers.v; reused"
#rocq_ignore iriswasm.iris_fundamental_local.to_es_list_llfill_contr
  "verbatim duplicate of `to_es_list_llfill_contr` in iris_fundamental_helpers.v; reused"

@[rocq_alias iriswasm.typing_local_no_host]
theorem typing_local_no_host (C : TContext) (es : List BasicInstruction) (τ1 τ2 τs : List ValueType)
    (be_fundamental : ∀ C es τ, BeTyping C es τ → ⊢ semanticTyping (GF := GF) C (toEList es) τ)
    (hnil : C.label = [] ∧ C.return_ = none)
    (htyping : BeTyping (updLocal (updLabel (updReturn C (some τ2)) [τ2]) (τ1 ++ τs)) es
      (.tf [] τ2)) :
    ⊢ semanticTypingLocalNoHost (GF := GF) C es τs (.tf τ1 τ2) := by
  -- the stuck-host result with an empty host list: its call-host outcome is then impossible
  have H := typing_local_stuck_host C es τ1 τ2 τs [] be_fundamental hnil htyping
  unfold semanticTypingLocalStuckHost at H
  unfold semanticTypingLocalNoHost
  isplit
  · ipureintro; exact hnil
  iintro %i #Hi %f %vs Hf Hown #Hv
  ihave H := H
  icases H with ⟨-, H⟩
  ihave H := H $$ %i Hi %f %vs Hf Hown Hv
  unfold interpExpressionClosureStuckHost interpExpressionClosureNoHost
  iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ H
  iintro %w ⟨⟨(Hw | Hch), Hown⟩, Hf⟩
  · iframe
  · rw [fixpoint_interp_call_host_cls_eq]; dsimp only [interpCallHostClsDef]
    icases Hch with ⟨%vh, %ws, %tf, %h, %τs1, %τs2, %Heq, %Htf, %Hin, -⟩
    exact absurd Hin (List.not_mem_nil)

end IrisWasm
