/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Logrel.IrisFundamentalTrap

/-! Port of `theories/iris/logrel/iris_fundamental_load.v`. -/

namespace IrisWasm

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm

variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF] [LogrelNaInvs GF]

omit [LogrelNaInvs GF] in
@[rocq_alias iriswasm.mem_extract_mid]
theorem mem_extract_mid (len : Nat) (mlData : List Byte) (start m : Nat) (cond : Nat → Prop) :
    (∀ a, start ≤ a ∧ a < start + len → cond a) →
    len > 0 →
    mlData.length ≥ start + len →
    ⊢ (([∗list] i ↦ b ∈ mlData, ⌜cond i⌝ → m ↦[wm][ i ] b) -∗
      ∃ bv : Bytes, m ↦[wms][ start ] bv ∗
        (m ↦[wms][ start ] bv -∗ [∗list] i ↦ b ∈ mlData, ⌜cond i⌝ → m ↦[wm][ i ] b) ∗
        ⌜bv.length = len⌝ : IProp GF) := by
  intro hcond _ hb
  have hA : (mlData.take start).length = start := by simp; omega
  have hbv : ((mlData.drop start).take len).length = len := by simp; omega
  have hsplit : mlData = mlData.take start ++
      ((mlData.drop start).take len ++ mlData.drop (start + len)) := by
    rw [← List.drop_drop, List.take_append_drop, List.take_append_drop]
  iintro Hm
  rw [hsplit]
  icases BI.BigSepL.bigSepL_append.1 $$ Hm with ⟨HA, HR⟩
  icases BI.BigSepL.bigSepL_append.1 $$ HR with ⟨Hbv, HC⟩
  iexists (mlData.drop start).take len
  isplitl [Hbv]
  · unfold memBlockAtPos
    iapply BI.BigSepL.bigSepL_mono ?_ $$ Hbv
    intro k x hk
    have hk' := (List.getElem?_eq_some_iff.mp hk).1
    rw [hA, Nat.add_comm k start]
    iintro H
    iapply H
    ipureintro
    exact hcond _ ⟨by omega, by omega⟩
  isplitl [HA HC]
  · iintro Hbv
    iapply BI.BigSepL.bigSepL_append.2
    isplitl [HA]
    · iexact HA
    iapply BI.BigSepL.bigSepL_append.2
    isplitr [HC]
    · unfold memBlockAtPos
      iapply BI.BigSepL.bigSepL_mono ?_ $$ Hbv
      intro k x _
      rw [hA, Nat.add_comm k start]
      iintro H _
      iexact H
    · iexact HC
  · ipureintro; exact hbv

omit [LogrelNaInvs GF] in
@[rocq_alias iriswasm.mem_extract]
theorem mem_extract (ms : Memory) (start len m : Nat) :
    len > 0 →
    lengthMem ms ≥ start + len →
    ⊢ (([∗list] i ↦ b ∈ ms.data.data, m ↦[wm][ i ] b) -∗
      ∃ bv, m ↦[wms][ start ] bv ∗
        (m ↦[wms][ start ] bv -∗ [∗list] i ↦ b ∈ ms.data.data, m ↦[wm][ i ] b) ∗
        ⌜bv.length = len⌝ : IProp GF) := by
  intro hlen hb
  iintro Hm
  ihave Hm := BI.BigSepL.bigSepL_mono
    (Ψ := fun i b => iprop(⌜True⌝ → m ↦[wm][ i ] b)) (fun _ => by iintro H _; iexact H) $$ Hm
  icases mem_extract_mid len ms.data.data start m (fun _ => True) (fun _ _ => trivial) hlen hb
    $$ Hm with ⟨%bv, Hbv, Hcl, %Hl⟩
  iexists bv
  iframe
  isplitl
  · iintro H
    ihave H := Hcl $$ H
    iapply BI.BigSepL.bigSepL_mono ?_ $$ H
    intro _ _ _
    iintro H; iapply H; ipureintro; trivial
  · ipureintro; exact Hl

@[rocq_alias iriswasm.typing_load]
theorem typing_load (C : TContext) (a : AlignmentExponent) (tp_sx : Option (PackedType × Sx))
    (t : ValueType) (off : StaticOffset) :
    C.memory ≠ [] →
    loadStoreTBounds a (optionProjl tp_sx) t = true →
    ⊢ (semanticTyping C (toEList [.load t tp_sx a off]) (.tf [.i32] [t]) : IProp GF) := by
  intro hmem _
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
  -- the number of bytes read
  let nb := match tp_sx with | some (tp, _) => lengthTp tp | none => lengthT t
  by_cases hfail : lengthMem ms < Wasm.Int.nOfUint z + off + nb
  · iapply IrisWp.wp_wand (ι := wasmIrisGS) (fun f => iprop(↪[frame] f)) $$
      [Hf Hsize] [Hcls Hown Hmem]
    · rcases tp_sx with _ | ⟨tp, sx⟩
      · iapply wp_load_failure (fun v => iprop(⌜v = .trapV⌝)) _ _ off a z mem ⟨locs, j⟩ t
          (lengthMem ms) Hl2 hfail
        iframe; inext; ipureintro; rfl
      · iapply wp_load_packed_failure (fun v => iprop(⌜v = .trapV⌝)) _ _ off a z mem ⟨locs, j⟩ t
          (lengthMem ms) tp sx Hl2 hfail
        iframe; inext; ipureintro; rfl
    · iintro %v ⟨⟨%rfl, Hsize⟩, Hf⟩
      imod Hcls $$ [Hsize Hmem Hown] with Hown
      · iframe
      imodintro
      isplitr
      · ileft; unfold interpVal; ileft; ipureintro; rfl
      · iexists ⟨locs, j⟩; iframe; unfold interpFrame; iexists locs; iframe
        isplitr
        · ipureintro; rfl
        · iexact Hlocs
  · have hnb : nb > 0 := by
      rcases tp_sx with _ | ⟨tp, _⟩
      · cases t <;> simp [nb, lengthT]
      · cases tp <;> simp [nb, lengthTp]
    icases mem_extract ms (Wasm.Int.nOfUint z + off) nb mem hnb (by omega) $$ Hmem with
      ⟨%bv, Ha, Hmem, %Hlenbv⟩
    iapply IrisWp.wp_wand (ι := wasmIrisGS) (fun f => iprop(↪[frame] f)) $$
      [Hf Ha] [Hcls Hown Hmem Hsize]
    · rcases tp_sx with _ | ⟨tp, sx⟩
      · iapply wp_load_deserialize (fun v => iprop(⌜v = .immV [wasmDeserialise bv t]⌝)) _ _ t bv
          off a z mem ⟨locs, j⟩ Hlenbv Hl2
        iframe; inext; ipureintro; rfl
      · iapply wp_load_packed_deserialize (fun v => iprop(⌜v = .immV [wasmDeserialise bv t]⌝))
          _ _ t bv off a z mem ⟨locs, j⟩ tp sx Hlenbv Hl2
        iframe; inext; ipureintro; rfl
    · iintro %v ⟨⟨%rfl, Ha⟩, Hf⟩
      ihave Hmem := Hmem $$ Ha
      imod Hcls $$ [Hsize Hmem Hown] with Hown
      · iframe
      imodintro
      isplitr
      · ileft; unfold interpVal interpValues; iright; iexists [_]; isplitr
        · ipureintro; rfl
        · isplitl
          · cases t <;> simp only [interpValue, interpValueI32, interpValueI64, interpValueF32,
              interpValueF64, wasmDeserialise] <;> ipureintro <;> exact ⟨_, rfl⟩
          · iempintro
      · iexists ⟨locs, j⟩; iframe; unfold interpFrame; iexists locs; iframe
        isplitr
        · ipureintro; rfl
        · iexact Hlocs

end IrisWasm
