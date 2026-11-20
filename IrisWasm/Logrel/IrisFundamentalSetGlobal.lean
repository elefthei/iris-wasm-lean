/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Logrel.IrisFundamentalTrap

/-! Port of `theories/iris/logrel/iris_fundamental_set_global.v`. -/

namespace IrisWasm

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm

variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF] [LogrelNaInvs GF]

@[rocq_alias iriswasm.typing_set_global]
theorem typing_set_global (C : TContext) (i : Nat) (g : GlobalType) (t : ValueType) :
    C.global[i]? = some g →
    g.t = t →
    isMut g = true →
    ⊢ (semanticTyping C (toEList [.setGlobal i]) (.tf [t] []) : IProp GF) := by
  intro hnth hgt hmut
  let := @WasmG.invGS hlc GF _
  apply semantic_typing_immV
  intro j lh hl f ws
  iintro #Hi #Hctx Hf Hfv Hv
  ihave %Hlen := BI.BigSepL2.bigSepL2_length $$ Hv
  rcases ws with _ | ⟨v, _ | ⟨_, _⟩⟩ <;> simp at Hlen
  icases Hv with ⟨#Hv, -⟩
  have hnth' : (C.global[i]?).map (·.t) = some t := by simp [hnth, hgt]
  icases interp_instance_lookup_global C hl j i t hnth' $$ Hi with
    ⟨%gt, %mt, %n, %Hgt, %Hn, %rfl, #Hg⟩
  rw [hnth] at Hgt; cases Hgt
  cases mt with
  | immut => simp [isMut] at hmut
  | «mut» =>
  unfold interpGlobal
  unfold interpFrame
  icases Hfv with ⟨%locs, %Heq, #Hlocs, Hown⟩
  subst Heq
  simp only [ofVal, vToEList, toEList, List.map_nil, List.map_cons, List.cons_append,
    List.nil_append]
  unfold interpExpression
  iapply IrisWp.fupd_wp (ι := wasmIrisGS) (fun f => iprop(↪[frame] f))
  imod NonAtomicInvariant.inv_acc CoPset.subseteq_top CoPset.subseteq_top $$ Hg Hown with
    ⟨Hn, Hown, Hcls⟩
  icases Hn with ⟨%w, >Hn, -⟩
  imodintro
  iapply IrisWp.wp_fupd (ι := wasmIrisGS) (fun f => iprop(↪[frame] f))
  iapply IrisWp.wp_wand (ι := wasmIrisGS) (fun f => iprop(↪[frame] f)) $$
    [Hf Hn] [Hcls Hown]
  · iapply wp_set_global _ _ v _ i (fun v => iprop(⌜v = .immV []⌝)) ⟨.mut, w⟩ n Hn $$ [] Hf Hn
    inext; ipureintro; rfl
  · iintro %v' ⟨%rfl, Hn, Hf⟩
    imod Hcls $$ [Hn Hown] with Hown
    · iframe; inext; iexact Hv
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
