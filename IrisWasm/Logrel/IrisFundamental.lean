/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Logrel.IrisFundamentalConst
import IrisWasm.Logrel.IrisFundamentalCvtop
import IrisWasm.Logrel.IrisFundamentalDrop
import IrisWasm.Logrel.IrisFundamentalNop
import IrisWasm.Logrel.IrisFundamentalRelop
import IrisWasm.Logrel.IrisFundamentalTestop
import IrisWasm.Logrel.IrisFundamentalSelect
import IrisWasm.Logrel.IrisFundamentalUnreachable
import IrisWasm.Logrel.IrisFundamentalUnop
import IrisWasm.Logrel.IrisFundamentalBinop
import IrisWasm.Logrel.IrisFundamentalBr
import IrisWasm.Logrel.IrisFundamentalBlock
import IrisWasm.Logrel.IrisFundamentalLoop
import IrisWasm.Logrel.IrisFundamentalBrIf
import IrisWasm.Logrel.IrisFundamentalCall
import IrisWasm.Logrel.IrisFundamentalComposition
import IrisWasm.Logrel.IrisFundamentalCallIndirect
import IrisWasm.Logrel.IrisFundamentalGetLocal
import IrisWasm.Logrel.IrisFundamentalSetLocal
import IrisWasm.Logrel.IrisFundamentalTeeLocal
import IrisWasm.Logrel.IrisFundamentalGetGlobal
import IrisWasm.Logrel.IrisFundamentalSetGlobal
import IrisWasm.Logrel.IrisFundamentalLoad
import IrisWasm.Logrel.IrisFundamentalStore
import IrisWasm.Logrel.IrisFundamentalCurrentMemory
import IrisWasm.Logrel.IrisFundamentalGrowMemory
import IrisWasm.Logrel.IrisFundamentalNil
import IrisWasm.Logrel.IrisFundamentalWeakening
import IrisWasm.Logrel.IrisFundamentalBrTable
import IrisWasm.Logrel.IrisFundamentalIf
import IrisWasm.Logrel.IrisFundamentalReturn
import IrisWasm.Logrel.IrisFundamentalTrap
import IrisWasm.Logrel.IrisFundamentalLocal
import IrisWasm.Logrel.IrisFundamentalStuckHost
import IrisWasm.Logrel.IrisFundamentalHost

/-! Port of `theories/iris/logrel/iris_fundamental.v`: the fundamental theorem of the logical
relation for basic-instruction typing, and its corollaries for closed function bodies. -/

namespace IrisWasm

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm

variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF] [LogrelNaInvs GF]

attribute [local instance] WasmG.invGS

@[rocq_alias iriswasm.be_fundamental]
theorem be_fundamental (C : TContext) (es : List BasicInstruction) (τ : FunctionType)
    (h : BeTyping C es τ) : ⊢ semanticTyping (GF := GF) C (toEList es) τ := by
  induction h with
  | const => exact typing_const _ _
  | unop h => exact typing_unop _ _ _ h
  | binop h => exact typing_binop _ _ _ h
  | testop h => exact typing_testop _ _ _ h
  | relop h => exact typing_relop _ _ _ h
  | convert => exact typing_cvtop_convert _ _ _ _
  | reinterpret => exact typing_cvtop_reinterpret _ _ _
  | unreachable => exact typing_unreachable _ _ _
  | nop => exact typing_nop _
  | drop => exact typing_drop _ _
  | select => exact typing_select _ _
  | block _ ih => exact typing_block _ _ _ _ ih
  | loop _ ih => exact typing_loop _ _ _ _ ih
  | ifWasm _ _ ih1 ih2 => exact typing_if _ _ _ _ _ ih1 ih2
  | br h1 h2 => exact typing_br _ _ _ _ _ h1 h2
  | brIf h1 h2 => exact typing_br_if _ _ _ h1 h2
  | brTable h => rw [← List.append_assoc]; exact typing_br_table _ _ _ _ _ _ h
  | return_ h => exact typing_return _ _ _ _ h
  | call h1 h2 => exact typing_call _ _ _ h1 h2
  | callIndirect h1 h2 h3 => exact typing_call_indirect _ _ _ _ h1 h2 h3
  | getLocal _ h => exact typing_get_local _ _ _ h
  | setLocal _ h => exact typing_set_local _ _ _ h
  | teeLocal _ h => exact typing_tee_local _ _ _ h
  | getGlobal _ h => exact typing_get_global _ _ _ h
  | setGlobal _ h1 h2 h3 => exact typing_set_global _ _ _ _ h1 h2 h3
  | load h1 h2 => exact typing_load _ _ _ _ _ h1 h2
  | store h1 h2 => exact typing_store _ _ _ _ _ h1 h2
  | currentMemory h => exact typing_current_memory _ h
  | growMemory h => exact typing_grow_memory _ h
  | empty => exact typing_nil _
  | composition _ _ ih1 ih2 =>
    rw [toEList, List.map_append]
    exact typing_composition _ _ _ _ _ _ trivial ih1 ih2
  | weakening _ ih => exact typing_weakening _ _ _ _ _ ih

@[rocq_alias iriswasm.be_fundamental_local]
theorem be_fundamental_local (C : TContext) (es : List BasicInstruction) (τ1 τ2 τs : List ValueType)
    (hnil : C.label = [] ∧ C.return_ = none)
    (htyping : BeTyping (updLocalLabelReturn C (τ1 ++ τs) [τ2] (some τ2)) es (.tf [] τ2)) :
    ⊢ semanticTypingLocalNoHost (GF := GF) C es τs (.tf τ1 τ2) :=
  typing_local_no_host C es τ1 τ2 τs (be_fundamental (GF := GF)) hnil htyping

@[rocq_alias iriswasm.be_fundamental_local_stuck_host]
theorem be_fundamental_local_stuck_host (C : TContext) (es : List BasicInstruction)
    (τ1 τ2 τs : List ValueType) (hl : List (Hostfuncidx × FunctionType))
    (hnil : C.label = [] ∧ C.return_ = none)
    (htyping : BeTyping (updLocalLabelReturn C (τ1 ++ τs) [τ2] (some τ2)) es (.tf [] τ2)) :
    ⊢ semanticTypingLocalStuckHost (GF := GF) hl C es τs (.tf τ1 τ2) :=
  typing_local_stuck_host C es τ1 τ2 τs hl (be_fundamental (GF := GF)) hnil htyping

@[rocq_alias iriswasm.be_fundamental_local_host]
theorem be_fundamental_local_host [HostProgramLogic (hlc := hlc) GF] (C : TContext)
    (es : List BasicInstruction) (τ1 τ2 τs : List ValueType)
    (hl : List (Hostfuncidx × FunctionType)) (hctx : HostProgramLogic.hostCtx hlc GF)
    (hnil : C.label = [] ∧ C.return_ = none)
    (htyping : BeTyping (updLocalLabelReturn C (τ1 ++ τs) [τ2] (some τ2)) es (.tf [] τ2)) :
    ⊢ semanticTypingLocal (GF := GF) C hl es τs (.tf τ1 τ2) hctx :=
  typing_local_host C es τ1 τ2 τs hctx hl (be_fundamental (GF := GF)) hnil htyping

end IrisWasm
