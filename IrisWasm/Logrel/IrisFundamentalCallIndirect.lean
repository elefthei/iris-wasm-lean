/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Logrel.IrisFundamentalHelpers
import IrisWasm.Logrel.IrisFundamentalCall

/-! Port of `theories/iris/logrel/iris_fundamental_call_indirect.v`. -/

namespace IrisWasm

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm OFE

variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF] [LogrelNaInvs GF]

attribute [local instance] WasmG.invGS

open FundAux

namespace FundAux

theorem wfN_sub_wtN (a b c : Nat) : (↑(wfN a) : CoPset) ⊆ ⊤ \ ↑(wtN b c) := by
  have h : (↑(wfN a) : CoPset) ## ↑(wtN b c) :=
    ndot_preserve_disjoint_r c <| ndot_preserve_disjoint_r b <| ndot_preserve_disjoint_l a <|
      ndot_ne_disjoint nroot (by decide : wf ≠ wt)
  intro p hp
  exact CoPset.in_diff.2 ⟨CoPset.subseteq_top p hp, fun hq => h p ⟨hp, hq⟩⟩

/-- A computation that can only trap, run after some constants. -/
theorem wp_vals_trap (C : TContext) (j : Instance) (hl : List (Hostfuncidx × FunctionType))
    (lh : Lholed) (t2 : List ValueType) (vs : List Value) (es : Expr) (f : Frame) :
    ⊢ (↪[frame] f -∗ WP es {{ v, ⌜v = .trapV⌝ ∗ ∃ f, ↪[frame] f ∗ interpFrame (GF := GF) C.local_ j f }}) -∗
      ↪[frame] f -∗
      WP (vToEList vs ++ es)
        {{ v, (interpVal t2 v ∨ interpBr C.local_ j C.return_ hl v lh C.label ∨
            interpReturnOption C.return_ C.local_ j v ∨
            interpCallHost C.local_ j C.return_ hl v lh C.label t2) ∗
          ∃ f, ↪[frame] f ∗ interpFrame C.local_ j f }} := by
  iintro H Hf
  ihave H2 := wp_val_can_trap_app' .NotStuck ⊤ (fun _ => iprop(False)) vs es f
    (interpFrame C.local_ j) $$ [Hf H]
  · isplitr
    · imodintro; iintro H; iexfalso; iexact H
    isplitl [Hf]
    · iexact Hf
    iintro Hf
    ihave H := H $$ Hf
    iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ H
    iintro %v ⟨%Hv, Hfr⟩
    iframe Hfr
    ileft; ipureintro; exact Hv
  iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ H2
  iintro %v ⟨H, Hfr⟩
  iframe Hfr
  icases H with (H | H)
  · ileft; iunfold interpVal; ileft; iexact H
  · iexfalso; iexact H

theorem interp_closure_type (hl : List (Hostfuncidx × FunctionType)) (τf : FunctionType)
    (cl : FunctionClosure) : interpClosure (GF := GF) hl τf cl ⊢ ⌜τf = clType cl⌝ := by
  rcases cl with ⟨_, ⟨_, _⟩, _, _⟩ | ⟨⟨_, _⟩, _⟩ <;> simp only [interpClosure] <;>
    iintro ⟨%H, -⟩ <;> ipureintro <;> exact H

end FundAux

@[rocq_alias iriswasm.interp_instance_get_table]
theorem interp_instance_get_table (C : TContext) (hl : List (Hostfuncidx × FunctionType))
    (j : Instance) (hnil : C.table ≠ []) :
    ⊢ interpInstance (GF := GF) C hl j -∗
      ∃ (τt : TableType) (a : Nat), ⌜C.table[0]? = some τt⌝ ∗ ⌜j.tab[0]? = some a⌝ ∗
        ∃ (tableSize : Nat), a ↪[wtsize] tableSize ∗
          interpTable tableSize (fun _ => interpClosure hl) a := by
  iintro #Hi
  iunfold interpInstance, interpInstance' at Hi
  icases Hi with ⟨-, -, Ht, -⟩
  rcases h0 : C.table[0]? with _ | τt
  · exact absurd (List.eq_nil_of_length_eq_zero
      (by simpa using (List.getElem?_eq_none_iff.1 h0))) hnil
  rcases h1 : j.tab[0]? with _ | a
  · iexfalso; iexact Ht
  icases Ht with ⟨%ts, %tl, -, -, #Hsize, #Ht⟩
  iexists τt, a
  isplitr; · ipureintro; rfl
  isplitr; · ipureintro; rfl
  iexists ts
  isplitr; · iexact Hsize
  iexact Ht

@[rocq_alias iriswasm.interp_instance_type_lookup]
theorem interp_instance_type_lookup (C : TContext) (hl : List (Hostfuncidx × FunctionType))
    (i : Nat) (tf : FunctionType) (j : Instance) (hnth : C.typesT[i]? = some tf) :
    ⊢ interpInstance (GF := GF) C hl j -∗ ⌜j.types[i]? = some tf⌝ := by
  iintro #Hi
  iunfold interpInstance, interpInstance' at Hi
  icases Hi with ⟨%Heq, -⟩
  ipureintro
  rw [Heq]; exact hnth

@[rocq_alias iriswasm.typing_call_indirect]
theorem typing_call_indirect (C : TContext) (i : Nat) (t1s t2s : List ValueType)
    (_hleq : i + 1 ≤ C.typesT.length) (hnth : C.typesT[i]? = some (.tf t1s t2s))
    (htable : C.table ≠ []) :
    ⊢ semanticTyping (GF := GF) C (toEList [.callIndirect i]) (.tf (t1s ++ [.i32]) t2s) := by
  apply semantic_typing_immV
  intro j lh hl f ws
  iintro #Hi #Hctx Hf Hfv #Hv
  ihave ⟨%ws', %wl, %Heq, #Hv', #Hw⟩ := BigSepL2.bigSepL2_app_inv_right $$ Hv
  subst Heq
  ihave %Hlenw := BigSepL2.bigSepL2_length $$ Hw
  obtain ⟨w⟩ : ∃ w, wl = [w] := by
    rcases wl with _ | ⟨w, _ | _⟩ <;> simp at Hlenw; exact ⟨w, rfl⟩
  subst ‹wl = [w]›
  ihave %Hz : iprop(⌜∃ z, w = .int32 z⌝) $$ [Hw]
  · ihave Hw2 := BigSepL2.bigSepL2_cons.1 $$ Hw
    icases Hw2 with ⟨Hw2, -⟩
    isimp only [interpValue, interpValueI32] at Hw2
    iexact Hw2
  obtain ⟨z, rfl⟩ := Hz
  icases interp_instance_get_table C hl j htable $$ Hi with
    ⟨%τt, %ta, %Hlook1, %Hlook2, %tsize, #Htsize, #Ht⟩
  ihave %Htlook := interp_instance_type_lookup C hl i _ j hnth $$ Hi
  unfold interpFrame
  icases Hfv with ⟨%locs, %Heq, #Hlocs, Hown⟩
  subst Heq
  unfold interpExpression
  rw [show ofVal (.immV (ws' ++ [.int32 z])) ++ toEList [.callIndirect i] =
    vToEList ws' ++ [.basic (.const (.int32 z)), .basic (.callIndirect i)] by
    simp [ofVal, vToEList, toEList]]
  by_cases hz : tsize ≤ Wasm.Int.natOfUint z
  · -- the index is out of bounds
    iapply wp_vals_trap $$ [Hown] Hf
    iintro Hf
    ihave H := wp_call_indirect_failure_outofbounds .NotStuck ⊤ (fun v => iprop(⌜v = .trapV⌝))
      ⟨locs, j⟩ i ta z tsize Hlook2 hz $$ Htsize Hf []
    · inext; ipureintro; rfl
    iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ H
    iintro %v ⟨%Hv, Hf⟩
    isplitr; · ipureintro; exact Hv
    iexists ⟨locs, j⟩; iframe Hf; iunfold interpFrame; iexists locs; iframe
    isplitr; · ipureintro; rfl
    iexact Hlocs
  -- the entry is in the table interpretation
  have hlt : (List.replicate tsize 0)[Wasm.Int.natOfUint z]? = some 0 := by
    rw [List.getElem?_replicate]; simp; omega
  iunfold interpTable at Ht
  ihave ⟨%τf, Hent⟩ := BigSepL.bigSepL_lookup hlt $$ Ht
  iunfold interpTableEntry at Hent
  icases Hent with ⟨%fe, #Hzinv, #Hfe⟩
  iapply IrisWp.fupd_wp (ι := wasmIrisGS) (fun f => iprop(↪[frame] f))
  imod NonAtomicInvariant.inv_acc CoPset.subseteq_top CoPset.subseteq_top $$ Hzinv Hown with
    ⟨>Hent, Hown, Hcls⟩
  imodintro
  rcases fe with _ | a
  · -- empty table entry: trap
    iapply wp_vals_trap $$ [Hown Hent Hcls] Hf
    iintro Hf
    iapply IrisWp.wp_fupd (ι := wasmIrisGS) (fun f => iprop(↪[frame] f))
    ihave H := wp_call_indirect_failure_noindex .NotStuck ⊤ (fun v => iprop(⌜v = .trapV⌝))
      ⟨locs, j⟩ i ta z Hlook2 $$ Hent Hf []
    · inext; ipureintro; rfl
    iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ H
    iintro %v ⟨⟨%Hv, Hent⟩, Hf⟩
    imod Hcls $$ [Hent Hown] with Hown
    · iframe
    imodintro
    isplitr; · ipureintro; exact Hv
    iexists ⟨locs, j⟩; iframe Hf; iunfold interpFrame; iexists locs; iframe
    isplitr; · ipureintro; rfl
    iexact Hlocs
  isimp only at Hfe
  iunfold interpFunction at Hfe
  icases Hfe with ⟨%cl, #Hainv, #Hcl⟩
  ihave %Hτf := interp_closure_type hl τf cl $$ Hcl
  iapply IrisWp.fupd_wp (ι := wasmIrisGS) (fun f => iprop(↪[frame] f))
  imod NonAtomicInvariant.inv_acc CoPset.subseteq_top
      (wfN_sub_wtN a ta (Wasm.Int.natOfUint z)) $$ Hainv Hown with ⟨>Hcla, Hown, Hcls'⟩
  imodintro
  by_cases ht : clType cl = .tf t1s t2s
  rotate_left
  · -- the types do not match: trap
    iapply wp_vals_trap $$ [Hown Hent Hcls Hcla Hcls'] Hf
    iintro Hf
    iapply IrisWp.wp_fupd (ι := wasmIrisGS) (fun f => iprop(↪[frame] f))
    ihave H := wp_call_indirect_failure_types .NotStuck ⊤ (fun v => iprop(⌜v = .trapV⌝))
      ⟨locs, j⟩ i ta a z cl (by rw [Htlook]; intro h; exact ht (Option.some.inj h).symm) Hlook2
      $$ Hent Hcla Hf []
    · inext; ipureintro; rfl
    iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ H
    iintro %v ⟨⟨%Hv, Hent, Hcla⟩, Hf⟩
    imod Hcls' $$ [Hcla Hown] with Hown
    · iframe
    imod Hcls $$ [Hent Hown] with Hown
    · iframe
    imodintro
    isplitr; · ipureintro; exact Hv
    iexists ⟨locs, j⟩; iframe Hf; iunfold interpFrame; iexists locs; iframe
    isplitr; · ipureintro; rfl
    iexact Hlocs
  -- success: reduce to the invocation of `a`
  subst Hτf
  rw [ht]
  iapply ctx_empty_elim
  rw [show vToEList ws' ++ [.basic (.const (.int32 z)), .basic (.callIndirect i)] =
    vToEList ws' ++ [.basic (.const (.int32 z)), .basic (.callIndirect i)] ++ [] by simp]
  iapply wp_base_push (v_to_e_is_const_list ws')
  iapply wp_call_indirect_success_ctx .NotStuck ⊤ _ ⟨locs, j⟩ i ta a z cl 0 _
    (by rw [Htlook, ht]) Hlook2 $$ Hent Hcla Hf
  inext
  iintro ⟨Hent, Hcla, Hf⟩
  unfold wpWasmCtx
  iintro %LI %HLI
  have HLI' : LI = vToEList ws' ++ [.invoke a] := by
    simpa [frameBase, lfilled, lfill, v_to_e_is_const_list] using HLI.symm
  subst HLI'
  iapply IrisWp.fupd_wp (ι := wasmIrisGS) (fun f => iprop(↪[frame] f))
  imod Hcls' $$ [Hcla Hown] with Hown
  · iframe
  imod Hcls $$ [Hent Hown] with Hown
  · iframe
  imodintro
  rw [show vToEList ws' = ofVal (.immV ws') from rfl]
  iapply invoke_closure C j hl lh locs ws' a cl t1s t2s $$ Hainv Hcl Hv' Hlocs Hown Hf

end IrisWasm
