/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Logrel.IrisFundamentalTrap

/-! Port of `theories/iris/logrel/iris_fundamental_grow_memory.v`. -/

namespace IrisWasm

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm

variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF] [LogrelNaInvs GF]

theorem typing_grow_memory (C : TContext) (x : Nat) {mt : MemoryType} :
    C.memory[x]? = some mt →
    ⊢ (semanticTyping C (toEList [.growMemory x])
      (.tf [mt.address.valueType] [mt.address.valueType]) : IProp GF) := by
  intro hmem
  let := @WasmG.invGS hlc GF _
  apply semantic_typing_immV
  intro j lh hl f ws
  iintro #Hi #Hctx Hf Hfv Hv
  ihave %Hlen := BI.BigSepL2.bigSepL2_length $$ Hv
  rcases ws with _ | ⟨w, _ | ⟨_, _⟩⟩ <;> simp at Hlen
  icases Hv with ⟨Hw, -⟩
  ihave %hw := interp_address_operand mt.address w $$ Hw
  obtain ⟨c, rfl, hc⟩ := hw
  icases interp_instance_get_mem C hl j x hmem $$ Hi with ⟨%mem, %hlk, -, #Hm⟩
  unfold interpFrame
  icases Hfv with ⟨%locs, %Heq, #Hlocs, Hown⟩
  subst Heq
  simp only [ofVal, vToEList, toEList, List.map_nil, List.map_cons, List.cons_append,
    List.nil_append]
  unfold interpExpression interpMem
  iapply IrisWp.fupd_wp (ι := wasmIrisGS) (fun f => iprop(↪[frame] f))
  imod NonAtomicInvariant.inv_acc CoPset.subseteq_top CoPset.subseteq_top $$ Hm Hown with
    ⟨Hms, Hown, Hcls⟩
  icases Hms with ⟨%ms, >%hwell, >Hmem, >Hsize⟩
  imodintro
  iapply IrisWp.wp_fupd (ι := wasmIrisGS) (fun f => iprop(↪[frame] f))
  iapply IrisWp.wp_wand (ι := wasmIrisGS) (fun f => iprop(↪[frame] f)) $$
    [Hf Hsize] [Hcls Hown Hmem]
  · iapply wp_grow_memory (x := x) (aw := mt.address) _ _ mem ⟨locs, j⟩ (lengthMem ms)
      (fun v => iprop(⌜v = .immV [c.result (lengthMem ms / pageSize)]⌝))
      (fun v => iprop(⌜v = .immV [c.failure]⌝)) c hlk
    iframe; isplitr
    · inext; ipureintro; rfl
    · inext; ipureintro; rfl
  · iintro %v ⟨Hdisj, Hf⟩
    icases Hdisj with (⟨⟨%rfl, Hb, Hsize⟩, %hbound⟩ | ⟨%rfl, Hsize⟩)
    · imod Hcls $$ [Hsize Hmem Hb Hown] with Hown
      · isplitr [Hown]
        · inext
          iexists {ms with data := ms.data.memGrow (c.unsigned * pageSize)}
          simp only [lengthMem, MemoryList.length_grow, MemoryList.data_grow]
          isplitr
          · ipureintro; exact hwell.grow hbound
          iframe
          simp only [memBlockAtPos, MemoryList.length_data, lengthMem, Nat.add_comm]
          iexact Hb
        · iexact Hown
      imodintro
      isplitr
      · ileft; unfold interpVal interpValues; iright; iexists [_]; isplitr
        · ipureintro; rfl
        · isplitl
          · rw [← hc, ← c.address.typeof_natValue (lengthMem ms / pageSize)]
            iapply interp_value_type_of (c.result (lengthMem ms / pageSize))
          · iempintro
      · iexists ⟨locs, j⟩; iframe; unfold interpFrame; iexists locs; iframe
        isplitr
        · ipureintro; rfl
        · iexact Hlocs
    · imod Hcls $$ [Hsize Hmem Hown] with Hown
      · isplitr [Hown]
        · inext; iexists ms; iframe; ipureintro; exact hwell
        · iexact Hown
      imodintro
      isplitr
      · ileft; unfold interpVal interpValues; iright; iexists [_]; isplitr
        · ipureintro; rfl
        · isplitl
          · have ht : typeof c.failure = mt.address.valueType := by rw [← hc]; cases c <;> rfl
            rw [← ht]
            iapply interp_value_type_of c.failure
          · iempintro
      · iexists ⟨locs, j⟩; iframe; unfold interpFrame; iexists locs; iframe
        isplitr
        · ipureintro; rfl
        · iexact Hlocs

end IrisWasm
