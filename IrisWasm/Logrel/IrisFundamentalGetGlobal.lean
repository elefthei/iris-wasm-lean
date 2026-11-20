/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Logrel.IrisFundamentalTrap

/-! Port of `theories/iris/logrel/iris_fundamental_get_global.v`. -/

namespace IrisWasm

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm

variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF] [LogrelNaInvs GF]

@[rocq_alias iriswasm.typing_get_global]
theorem typing_get_global (C : TContext) (i : Nat) (t : ValueType) :
    (C.global[i]?).map (·.t) = some t →
    ⊢ (semanticTyping C (toEList [.getGlobal i]) (.tf [] [t]) : IProp GF) := by
  intro hnth
  let := @WasmG.invGS hlc GF _
  apply semantic_typing_immV
  intro j lh hl f ws
  iintro #Hi #Hctx Hf Hfv Hv
  ihave %Hlen := BI.BigSepL2.bigSepL2_length $$ Hv
  rcases ws with _ | ⟨_, _⟩ <;> simp at Hlen
  icases interp_instance_lookup_global C hl j i t hnth $$ Hi with ⟨%gt, %mt, %n, %Hgt, %Hn, %rfl, #Hg⟩
  ihave #HP : iprop(∃ (P : ValueType → Value → IProp GF), (□ ∀ w, P t w -∗ interpValue t w) ∗
      NonAtomicInvariant.inv (LogrelNaInvs.logrelNais GF) (wgN n)
        iprop(∃ w, n ↦[wg] (⟨mt, w⟩ : Global) ∗ P t w)) $$ [Hg]
  · cases mt
    · unfold interpGlobal; iexact Hg
    · unfold interpGlobal; iexists fun t => interpValue t; isplitr
      · imodintro; iintro %w H; iexact H
      · iexact Hg
  icases HP with ⟨%P, #Hcond, #Hinv⟩
  unfold interpFrame
  icases Hfv with ⟨%locs, %Heq, #Hlocs, Hown⟩
  subst Heq
  simp only [ofVal, vToEList, toEList, List.map_nil, List.map_cons, List.nil_append]
  unfold interpExpression
  iapply IrisWp.fupd_wp (ι := wasmIrisGS) (fun f => iprop(↪[frame] f))
  imod NonAtomicInvariant.inv_acc CoPset.subseteq_top CoPset.subseteq_top $$ Hinv Hown with ⟨Hn, Hown, Hcls⟩
  icases Hn with ⟨%w, >Hn, HP⟩
  imodintro
  iapply IrisWp.wp_fupd (ι := wasmIrisGS) (fun f => iprop(↪[frame] f))
  iapply IrisWp.wp_wand (ι := wasmIrisGS) (fun f => iprop(↪[frame] f)) $$
    [Hf Hn HP] [Hcls Hown]
  · iapply wp_get_global _ _ w _ i (fun v => iprop(⌜v = .immV [w]⌝ ∗ P t w)) ⟨mt, w⟩ n Hn rfl
      $$ [HP] Hf Hn
    inext; isplitr
    · ipureintro; rfl
    · iexact HP
  · iintro %v ⟨⟨%rfl, HP⟩, Hn, Hf⟩
    ihave #Hw := Hcond $$ %w HP
    imod Hcls $$ [Hn HP Hown] with Hown
    · iframe
    imodintro
    isplitr
    · ileft; unfold interpVal interpValues; iright; iexists [w]; isplitr
      · ipureintro; rfl
      · isplitl
        · iexact Hw
        · iempintro
    · iexists ⟨locs, j⟩; iframe; unfold interpFrame; iexists locs; iframe
      isplitr
      · ipureintro; rfl
      · iexact Hlocs

end IrisWasm
