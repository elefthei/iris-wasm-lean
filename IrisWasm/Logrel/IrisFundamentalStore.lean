/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Logrel.IrisFundamentalTrap

/-! Port of `theories/iris/logrel/iris_fundamental_store.v`. -/

namespace IrisWasm

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm

variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF] [LogrelNaInvs GF]

@[rocq_alias iriswasm.update_list_range]
def updateListRange {A : Type} (l l' : List A) (i : Nat) : List A :=
  l.take i ++ l' ++ l.drop (i + l'.length)

omit [WasmG hlc GF] [LogrelNaInvs GF] in
@[rocq_alias iriswasm.update_list_range_length]
theorem update_list_range_length {A : Type} (l l' : List A) (i : Nat) :
    i + l'.length ≤ l.length → l.length = (updateListRange l l' i).length := by
  intro h
  simp [updateListRange]; omega

omit [WasmG hlc GF] [LogrelNaInvs GF] in
@[rocq_alias iriswasm.update_list_range_lookup]
theorem update_list_range_lookup {A : Type} (l l' : List A) (i : Nat) (a : A) :
    i + l'.length ≤ l.length → l'[0]? = some a → (updateListRange l l' i)[i]? = some a := by
  intro h ha
  have : (l.take i).length = i := by simp; omega
  simp only [updateListRange, List.append_assoc]
  rw [List.getElem?_append_right (by omega), this, Nat.sub_self, List.getElem?_append_left]
  · exact ha
  · cases l' <;> simp_all

omit [LogrelNaInvs GF] in
@[rocq_alias iriswasm.mem_extract_insert_mid]
theorem mem_extract_insert_mid (len : Nat) (mlData : List Byte) (start m : Nat) (cond : Nat → Prop) :
    (∀ a, start ≤ a ∧ a < start + len → cond a) →
    len > 0 →
    mlData.length ≥ start + len →
    ⊢ (([∗list] i ↦ b ∈ mlData, ⌜cond i⌝ → m ↦[wm][ i ] b) -∗
      ∃ bv : Bytes, m ↦[wms][ start ] bv ∗
        (∀ bv', ⌜bv.length = bv'.length⌝ -∗ m ↦[wms][ start ] bv' -∗
          [∗list] i ↦ b ∈ updateListRange mlData bv' start, ⌜cond i⌝ → m ↦[wm][ i ] b) ∗
        ⌜bv.length = len⌝ : IProp GF) := by
  intro hcond _ hb
  have hA : (mlData.take start).length = start := by simp; omega
  have hbv : ((mlData.drop start).take len).length = len := by simp; omega
  have hsplit : mlData = mlData.take start ++
      ((mlData.drop start).take len ++ mlData.drop (start + len)) := by
    rw [← List.drop_drop, List.take_append_drop, List.take_append_drop]
  iintro Hm
  rw (occs := .pos [1]) [hsplit]
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
  · iintro %bv' %Hl Hbv
    rw [hbv] at Hl
    simp only [updateListRange, List.append_assoc, ← Hl]
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
    · rw [hbv, ← Hl]
      iexact HC
  · ipureintro; exact hbv

omit [LogrelNaInvs GF] in
@[rocq_alias iriswasm.mem_extract_insert]
theorem mem_extract_insert (ms : Memory) (start len m : Nat) :
    len > 0 →
    lengthMem ms ≥ start + len →
    ⊢ (([∗list] i ↦ b ∈ ms.data.data, m ↦[wm][ i ] b) -∗
      ∃ bv, m ↦[wms][ start ] bv ∗
        (∀ bv', ⌜bv.length = bv'.length⌝ -∗ m ↦[wms][ start ] bv' -∗
          [∗list] i ↦ b ∈ updateListRange ms.data.data bv' start, m ↦[wm][ i ] b) ∗
        ⌜bv.length = len⌝ : IProp GF) := by
  intro hlen hb
  iintro Hm
  ihave Hm := BI.BigSepL.bigSepL_mono
    (Ψ := fun i b => iprop(⌜True⌝ → m ↦[wm][ i ] b)) (fun _ => by iintro H _; iexact H) $$ Hm
  icases mem_extract_insert_mid len ms.data.data start m (fun _ => True) (fun _ _ => trivial)
    hlen hb $$ Hm with ⟨%bv, Hbv, Hcl, %Hl⟩
  iexists bv
  iframe
  isplitl
  · iintro %bv' %Hl' H
    ihave H := Hcl $$ %bv' %Hl' H
    iapply BI.BigSepL.bigSepL_mono ?_ $$ H
    intro _ _ _
    iintro H; iapply H; ipureintro; trivial
  · ipureintro; exact Hl

@[rocq_alias iriswasm.typing_store]
theorem typing_store (C : TContext) (a : AlignmentExponent) (tp : Option PackedType) (t : ValueType)
    (off : StaticOffset) :
    C.memory ≠ [] →
    loadStoreTBounds a tp t = true →
    ⊢ (semanticTyping C (toEList [.store t tp a off]) (.tf [.i32, t] []) : IProp GF) := by
  intro hmem hbounds
  let := @WasmG.invGS hlc GF _
  apply semantic_typing_immV
  intro j lh hl f ws
  iintro #Hi #Hctx Hf Hfv Hv
  ihave %Hlen := BI.BigSepL2.bigSepL2_length $$ Hv
  rcases ws with _ | ⟨w, _ | ⟨v, _ | ⟨_, _⟩⟩⟩ <;> simp at Hlen
  icases Hv with ⟨Hw, Hv, -⟩
  ihave %Hz : ⌜∃ z, w = Value.int32 z⌝ $$ [Hw]
  · simp only [interpValue, interpValueI32]; iexact Hw
  obtain ⟨z, rfl⟩ := Hz
  ihave %Ht := interp_value_types_agree t v $$ Hv
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
  -- the number of bytes written
  let nb := match tp with | some tp => lengthTp tp | none => lengthT t
  by_cases hfail : lengthMem ms < Wasm.Int.nOfUint z + off + nb
  · iapply IrisWp.wp_wand (ι := wasmIrisGS) (fun f => iprop(↪[frame] f)) $$
      [Hf Hsize] [Hcls Hown Hmem]
    · rcases tp with _ | tp
      · iapply wp_store_failure (fun v => iprop(⌜v = .trapV⌝)) _ _ t v off a z mem ⟨locs, j⟩
          (lengthMem ms) Ht Hl2 hfail
        iframe; inext; ipureintro; rfl
      · iapply wp_store_packed_failure (fun v => iprop(⌜v = .trapV⌝)) _ _ t v off a z mem
          ⟨locs, j⟩ (lengthMem ms) tp Ht Hl2 hfail
        iframe; inext; ipureintro; rfl
    · iintro %v' ⟨⟨%rfl, Hsize⟩, Hf⟩
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
      rcases tp with _ | tp
      · cases t <;> simp [nb, lengthT]
      · cases tp <;> simp [nb, lengthTp]
    icases mem_extract_insert ms (Wasm.Int.nOfUint z + off) nb mem hnb (by omega) $$ Hmem with
      ⟨%bv, Ha, Hmem, %Hlenbv⟩
    -- the bytes written
    let bs := match tp with | some tp => bytesTakefill 0 (lengthTp tp) (bits v) | none => bits v
    have hbs : bv.length = bs.length := by
      rcases tp with _ | tp
      · simp [bs, nb] at Hlenbv ⊢; rw [length_bits v t Ht, Hlenbv]
      · simp [bs, nb] at Hlenbv ⊢; rw [length_bytes_takefill, Hlenbv]
    iapply IrisWp.wp_wand (ι := wasmIrisGS) (fun f => iprop(↪[frame] f))
      (Φ := fun w => iprop((⌜w = .immV []⌝ ∗ mem ↦[wms][ Wasm.Int.nOfUint z + off ] bs) ∗
        ↪[frame] ⟨locs, j⟩)) $$ [Hf Ha] [Hcls Hown Hmem Hsize]
    · rcases tp with _ | tp
      · iapply wp_store (fun v => iprop(⌜v = .immV []⌝)) _ _ t v bv off a z mem ⟨locs, j⟩ Ht
          Hlenbv Hl2
        iframe; inext; ipureintro; rfl
      · have htp : lengthTp tp < lengthT t := by
          simp [loadStoreTBounds] at hbounds; exact hbounds.1.2
        iapply wp_store_packed (fun v => iprop(⌜v = .immV []⌝)) _ _ t v bv off a z mem ⟨locs, j⟩
          tp Ht Hlenbv htp Hl2
        iframe; inext; ipureintro; rfl
    · iintro %v' ⟨⟨%rfl, Ha⟩, Hf⟩
      ihave Hmem := Hmem $$ %bs %hbs Ha
      imod Hcls $$ [Hsize Hmem Hown] with Hown
      · isplitr [Hown]
        · inext
          iexists (⟨⟨updateListRange ms.data.data bs (Wasm.Int.nOfUint z + off)⟩, ms.maxOpt⟩ :
            Memory)
          have : lengthMem ms =
              (updateListRange ms.data.data bs (Wasm.Int.nOfUint z + off)).length :=
            update_list_range_length _ _ _ (by
              simp [lengthMem, MemoryList.lengthMem] at hfail ⊢; omega)
          simp only [lengthMem, MemoryList.lengthMem] at this ⊢
          rw [← this]
          iframe
        · iexact Hown
      imodintro
      isplitr
      · ileft; unfold interpVal interpValues; iright; iexists []; isplitr
        · ipureintro; rfl
        · iempintro
      · iexists ⟨locs, j⟩; iframe; unfold interpFrame; iexists locs; iframe
        isplitr
        · ipureintro; rfl
        · iexact Hlocs

end IrisWasm
