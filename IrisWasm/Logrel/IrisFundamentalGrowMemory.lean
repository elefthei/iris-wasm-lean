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

@[rocq_alias iriswasm.typing_grow_memory]
theorem typing_grow_memory (C : TContext) :
    C.memory ≠ [] →
    ⊢ (semanticTyping C (toEList [.growMemory]) (.tf [.i32] [.i32]) : IProp GF) := by
  intro hmem
  let := @WasmG.invGS hlc GF _
  apply semantic_typing_immV
  intro j lh hl f ws
  iintro #Hi #Hctx Hf Hfv Hv
  ihave %Hlen := BI.BigSepL2.bigSepL2_length $$ Hv
  rcases ws with _ | ⟨w, _ | ⟨_, _⟩⟩ <;> simp at Hlen
  icases Hv with ⟨Hw, -⟩
  ihave %Hz : ⌜∃ z, w = Value.int32 z⌝ $$ [Hw]
  · simp only [interpValue, interpValueI32]; iexact Hw
  obtain ⟨z, rfl⟩ := Hz
  icases interp_instance_get_mem C hl j hmem $$ Hi with ⟨%τm, %mem, %Hl1, %Hl2, -, #Hm⟩
  unfold interpFrame
  icases Hfv with ⟨%locs, %Heq, #Hlocs, Hown⟩
  subst Heq
  simp only [ofVal, vToEList, toEList, List.map_nil, List.map_cons, List.cons_append,
    List.nil_append]
  unfold interpExpression interpMem
  iapply IrisWp.fupd_wp (ι := wasmIrisGS) (fun f => iprop(↪[frame] f))
  imod NonAtomicInvariant.inv_acc CoPset.subseteq_top CoPset.subseteq_top $$ Hm Hown with
    ⟨Hms, Hown, Hcls⟩
  icases Hms with ⟨%ms, >Hmem, >Hsize⟩
  imodintro
  iapply IrisWp.wp_fupd (ι := wasmIrisGS) (fun f => iprop(↪[frame] f))
  iapply IrisWp.wp_wand (ι := wasmIrisGS) (fun f => iprop(↪[frame] f)) $$
    [Hf Hsize] [Hcls Hown Hmem]
  · iapply wp_grow_memory _ _ mem ⟨locs, j⟩ (lengthMem ms)
      (fun v => iprop(⌜v = .immV [.int32 (Wasm.Int.intOfZ ((lengthMem ms / pageSize : Nat) :
        _root_.Int))]⌝)) (fun v => iprop(⌜v = .immV [.int32 int32MinusOne]⌝)) z Hl2
    iframe; isplitr
    · inext; ipureintro; rfl
    · inext; ipureintro; rfl
  · iintro %v ⟨Hdisj, Hf⟩
    icases Hdisj with (⟨⟨%rfl, Hb, Hsize⟩, -⟩ | ⟨%rfl, Hsize⟩)
    · imod Hcls $$ [Hsize Hmem Hb Hown] with Hown
      · isplitr [Hown]
        · inext
          iexists (⟨⟨ms.data.data ++ List.replicate (Wasm.Int.nOfUint z * pageSize) (0 : Byte)⟩,
            ms.maxOpt⟩ : Memory)
          simp only [lengthMem, MemoryList.lengthMem, List.length_append, List.length_replicate]
          iframe
          simp only [memBlockAtPos, Nat.add_comm]
          iexact Hb
        · iexact Hown
      imodintro
      isplitr
      · ileft; unfold interpVal interpValues; iright; iexists [_]; isplitr
        · ipureintro; rfl
        · isplitl
          · simp only [interpValue, interpValueI32]; ipureintro; exact ⟨_, rfl⟩
          · iempintro
      · iexists ⟨locs, j⟩; iframe; unfold interpFrame; iexists locs; iframe
        isplitr
        · ipureintro; rfl
        · iexact Hlocs
    · imod Hcls $$ [Hsize Hmem Hown] with Hown
      · iframe
      imodintro
      isplitr
      · ileft; unfold interpVal interpValues; iright; iexists [_]; isplitr
        · ipureintro; rfl
        · isplitl
          · simp only [interpValue, interpValueI32]; ipureintro; exact ⟨_, rfl⟩
          · iempintro
      · iexists ⟨locs, j⟩; iframe; unfold interpFrame; iexists locs; iframe
        isplitr
        · ipureintro; rfl
        · iexact Hlocs

end IrisWasm
