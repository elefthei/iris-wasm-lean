/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Examples.Stack.StackInstantiationInterp
import IrisWasm.Logrel.IrisInterpInstanceAlloc
import IrisWasm.Rules.Proofmode

/-! Port of `theories/iris/examples/stack/stack_module_robust.v`.

The file-local Coq notation `{{{{ P }}}} es {{{{ v, Q }}}}` (over host expressions, mask `⊤`) is
written out as `□ ∀ Φ, P -∗ (∀ v, Q -∗ Φ v) -∗ WP es @ NotStuck ; ⊤ {{ v, Φ v }}`. -/

namespace IrisWasm.Examples.Stack

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm
open scoped Iris.Std.PartialMap

@[rocq_alias iriswasm.stack_adv_instantiate]
def stackAdvInstantiate (exp_addrs : List Nat) (stack_mod_addr adv_mod_addr : Nat) : List HostE :=
  [.instantiate exp_addrs stack_mod_addr [],
   .instantiate [] adv_mod_addr (exp_addrs.take 5)]

@[rocq_alias iriswasm.stack_module_imports]
def stackModuleImports : List ExternT :=
  [.func (.tf [] [.i32]),
   .func (.tf [.i32] [.i32]),
   .func (.tf [.i32] [.i32]),
   .func (.tf [.i32] [.i32]),
   .func (.tf [.i32, .i32] [])]

@[rocq_alias iriswasm.module_typing_exports_length]
theorem module_typing_exports_length (m : Module) (impts expts : List ExternT) :
    ModuleTyping m impts expts → m.exports.length = expts.length := by
  rintro ⟨fts, gts, h⟩
  obtain ⟨tfs, fs, ts, ms, gs, els, ds, iOpt, imps, exps⟩ := m
  exact h.2.2.2.2.2.2.2.2.length_eq

private theorem forall₂_lookup_r {A B : Type} {R : A → B → Prop} {l₁ : List A} {l₂ : List B}
    (h : Wasm.List.Forall₂ R l₁ l₂) {k : Nat} {b : B} (hb : l₂[k]? = some b) :
    ∃ a, l₁[k]? = some a ∧ R a b := by
  induction h generalizing k with
  | nil => simp at hb
  | cons hr _ ih =>
    cases k with
    | zero => simp at hb; subst hb; exact ⟨_, rfl, hr⟩
    | succ k => simpa using ih (by simpa using hb)

section RobustStack
variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF] [LogrelNaInvs GF]

attribute [local instance] WasmG.invGS

@[rocq_alias iriswasm.interp_instance_func_lookup]
theorem interp_instance_func_lookup (n f : Nat) (t : TContext)
    (l : List (Hostfuncidx × FunctionType)) (inst : Instance) :
    inst.funcs[n]? = some f →
    ⊢ (interpInstance t l inst -∗
      ∃ τf, ⌜t.funcT[n]? = some τf⌝ ∗ interpFunction τf (fun _ => interpClosure l) f :
        IProp GF) := by
  intro hf
  iintro Hi
  simp only [interpInstance, interpInstance']
  icases Hi with ⟨_, Hf, _⟩
  ihave %Hlen := BI.BigSepL2.bigSepL2_length $$ Hf
  obtain ⟨x, hx⟩ : ∃ x, t.funcT[n]? = some x := by
    have : n < inst.funcs.length := (List.getElem?_eq_some_iff.1 hf).1
    exact ⟨_, List.getElem?_eq_getElem (Hlen ▸ this)⟩
  iexists x
  isplitr
  · ipureintro; exact hx
  · iapply BI.BigSepL2.bigSepL2_lookup hf hx $$ Hf

@[rocq_alias iriswasm.module_typing_start_type]
theorem module_typing_start_type (m : Module) (impts expts : List ExternT)
    (fts : List FunctionType) (gts : List GlobalType) (t : TContext) (start : ModuleStart)
    (idnstart : Nat) (inst : Instance) (n : Nat) (tf : FunctionType)
    (l : List (Hostfuncidx × FunctionType)) :
    ModuleTypingBody m impts expts fts gts →
    t.funcT = extTFuncs impts ++ fts →
    m.start = some start →
    start.func = .funcidx n →
    inst.funcs[n]? = some idnstart →
    t.funcT[n]? = some tf →
    ⊢ (interpInstance t l inst -∗ ⌜tf = .tf [] []⌝ : IProp GF) := by
  intro hm ht hs hn _ htn
  iintro _
  ipureintro
  obtain ⟨tfs, fs, ts, ms, gs, els, ds, iOpt, imps, exps⟩ := m
  simp only at hs; subst hs
  have h := hm.2.2.2.2.2.2.1
  simp [predOption, moduleStartTyping, hn, ← ht, htn] at h
  exact h.2

@[rocq_alias iriswasm.module_typing_func_not_import]
theorem module_typing_func_not_import (m : Module) (impts expts : List ExternT)
    (fts : List FunctionType) (gts : List GlobalType) (t : TContext) (inst : Instance) (n : Nat)
    (r1 r2 : List ValueType) (f : Nat) :
    t = { typesT := m.types, funcT := extTFuncs impts ++ fts, global := extTGlobs impts ++ gts
          table := extTTabs impts ++ m.tables.map (·.type), memory := extTMems impts ++ m.mems
          local_ := [], label := [], return_ := none } →
    getImportFuncCount m = (extTFuncs impts).length →
    ModuleTypingBody m impts expts fts gts →
    inst.funcs[n]? = some f →
    t.funcT[n]? = some (.tf r1 r2) →
    FunctionType.tf r1 r2 ∉ extTFuncs impts →
    ∃ (n' fidx : Nat) (locs : List ValueType) (es : List BasicInstruction),
      (inst.funcs.drop (getImportFuncCount m))[n']? = some f ∧
      m.funcs[n']? = some ({ type := .typeidx fidx, locals := locs, body := es } : ModuleFunc) ∧
      m.types.getD fidx (.tf [] []) = .tf r1 r2 ∧
      BeTyping (updLocalLabelReturn t (r1 ++ locs) [r2] (some r2)) es (.tf [] r2) := by
  intro ht hlen hm hn htn hnin
  subst ht
  rw [hlen]
  simp only at htn
  have hge : (extTFuncs impts).length ≤ n := by
    apply Nat.le_of_not_lt; intro hlt
    rw [List.getElem?_append_left hlt] at htn
    exact hnin (List.mem_of_getElem? htn)
  rw [List.getElem?_append_right hge] at htn
  obtain ⟨tfs, fs, ts, ms, gs, els, ds, iOpt, imps, exps⟩ := m
  obtain ⟨mf, hmf, htyp⟩ := forall₂_lookup_r hm.1 htn
  obtain ⟨⟨fidx⟩, locs, es⟩ := mf
  obtain ⟨_, hnth, hbe⟩ := htyp
  refine ⟨n - (extTFuncs impts).length, fidx, locs, es, ?_, hmf, ?_, ?_⟩
  · rw [List.getElem?_drop, Nat.add_sub_cancel' hge]; exact hn
  · simpa using hnth
  · simpa [updLocalLabelReturn] using hbe

local notation "logrelNais" => LogrelNaInvs.logrelNais (GF := GF)

omit [LogrelNaInvs GF] in
private theorem wp_wand_s {s : Stuckness} {E : CoPset} {e : Expr} {Φ Ψ : Val → IProp GF} :
    iprop(WP e @ s ; E {{ Φ }}) ⊢ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s ; E {{ Ψ }} :=
  IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)

omit [LogrelNaInvs GF] in
private theorem fupd_wp_s {s : Stuckness} {E : CoPset} {e : Expr} {Φ : Val → IProp GF} :
    iprop(|={E}=> WP e @ s ; E {{ Φ }}) ⊢ WP e @ s ; E {{ Φ }} :=
  IrisWp.fupd_wp (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)

/-- Running a well-typed start function of type `[] → []` from the empty frame (Lean helper
factored out of the Coq proof of `instantiate_stack_adv_spec`). -/
private theorem start_spec (C : TContext) (inst : Instance) (idnstart : Nat)
    (locs : List ValueType) (es : List BasicInstruction) (hC : C.label = [] ∧ C.return_ = none)
    (hes : BeTyping (updLocalLabelReturn C ([] ++ locs) [[]] (some [])) es (.tf [] [])) :
    ⊢ iprop((↪[frame] emptyFrame : IProp GF) -∗
      NonAtomicInvariant.own logrelNais ⊤ -∗
      NonAtomicInvariant.inv logrelNais (wfN idnstart)
        iprop(idnstart ↦[wf] (.funcNative inst (.tf [] []) locs es)) -∗
      interpInstance C [] inst -∗
      WP ([.invoke idnstart] : Expr) @ Stuckness.NotStuck ; ⊤
        {{ w, (⌜w = Val.trapV ∨ w = Val.immV []⌝ ∗ NonAtomicInvariant.own logrelNais ⊤) ∗
          ↪[frame] emptyFrame }}) := by
  iintro Hf Hown #Ha #Hi
  iapply fupd_wp_s
  imod NonAtomicInvariant.inv_acc CoPset.subseteq_top CoPset.subseteq_top $$ Ha Hown with
    ⟨>Haf, Hown, Hcls⟩
  imodintro
  rw [show ([.invoke idnstart] : Expr) = [] ++ [.invoke idnstart] from rfl]
  iapply wp_invoke_native .NotStuck ⊤ _ [] [] [] [] locs idnstart es inst 0 emptyFrame
    rfl rfl rfl $$ Hf Haf
  inext
  iintro ⟨Hf, Haf⟩
  iapply fupd_wp_s
  imod Hcls $$ [Haf Hown] with Hown
  · iframe
  imodintro
  ihave H : wpWasmCtxFrame .NotStuck ⊤ [.basic (.block (.tf [] []) es)]
      (fun v => iprop((interpVal [] v ∗ NonAtomicInvariant.own logrelNais ⊤) ∗
        ↪[frame] emptyFrame))
      0 ⟨[] ++ nZeros locs, inst⟩ 0 (.base [] []) $$ [Hf Hown]
  · rw [← List.nil_append [AdministrativeInstruction.basic (.block (.tf [] []) es)]]
    iapply wp_block_local_ctx (vs := []) (t1s := []) rfl rfl rfl rfl $$ Hf
    inext
    iintro Hf
    iapply (wandIff_equiv (wp_wasm_empty_ctx_frame _ _ _ _ _ _)).1
    unfold wpWasmFrame
    simp only [List.nil_append]
    ihave Hl := be_fundamental_local (GF := GF) C es [] [] locs hC hes
    iunfold semanticTypingLocalNoHost at Hl
    icases Hl with ⟨-, Hl⟩
    iunfold interpExpressionClosureNoHost at Hl
    iapply Hl $$ %inst Hi %emptyFrame %(nZeros locs) Hf Hown
    simp only [List.nil_append]
    iunfold interpVal
    iright
    iunfold interpValues
    iexists nZeros locs
    isplitr; · ipureintro; rfl
    iapply n_zeros_interp_values
  unfold wpWasmCtxFrame
  ispecialize H $$ %_ %(FundAux.lfilled_empty'.2 rfl)
  iapply wp_wand_s $$ H
  iintro %v ⟨⟨Hv, Hown⟩, Hf⟩
  iframe Hf Hown
  iunfold interpVal at Hv
  icases Hv with (%Hv | Hv)
  · ipureintro; exact .inl Hv
  · iunfold interpValues at Hv
    icases Hv with ⟨%ws, %Hws, Hws⟩
    subst Hws
    ihave %Hlen := BI.BigSepL2.bigSepL2_length $$ Hws
    cases ws with
    | cons _ _ => simp at Hlen
    | nil => ipureintro; exact .inr rfl

variable [HvisG GF] [HmsG GF] [HasG GF]

omit [WasmG hlc GF] [LogrelNaInvs GF] [HvisG GF] [HmsG GF] [HasG GF] in
private theorem nodupKeys_zip (ks : List Nat) (l : List FunctionClosure) (h : ks.Nodup) :
    NoDupKeys (ks.zip l) := by
  induction ks generalizing l with
  | nil => exact .nil
  | cons k ks ih =>
    cases l with
    | nil => exact .nil
    | cons v l =>
      obtain ⟨hk, hks⟩ := List.nodup_cons.1 h
      refine List.nodup_cons.2 ⟨fun hm => hk ?_, ih l hks⟩
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.1 hm
      exact (List.of_mem_zip hab).1

omit [LogrelNaInvs GF] in
/-- `wp_seq_host_nostart` for a first instantiation that returns `immHV []` together with a
resource `R` (Lean helper: lets `R` be inferred from the first instantiation's spec). -/
private theorem wp_seq_host_nostart_imm (E : CoPset) (Φ : HostVal → IProp GF) (R : IProp GF)
    (v_exps : List Vi) (modi : Nat) (v_imps : List Vimp) (m : Module) (es : List HostE)
    (hstart : m.start = none) :
    ⊢ modi ↪[mods] m -∗
      (modi ↪[mods] m -∗ WP (([.instantiate v_exps modi v_imps], []) : HostExpr)
        @ Stuckness.NotStuck ; E {{ w, ⌜w = .immHV []⌝ ∗ modi ↪[mods] m ∗ R }}) -∗
      (R -∗ modi ↪[mods] m -∗ WP ((es, []) : HostExpr) @ E {{ v, Φ v }}) -∗
      WP ((.instantiate v_exps modi v_imps :: es, []) : HostExpr) @ E {{ v, Φ v }} := by
  iintro Hmod Hes1 Hes2
  iapply wp_seq_host_nostart .NotStuck E Φ (fun w => iprop(⌜w = .immHV []⌝ ∗ R)) v_exps modi
    v_imps m es [] hstart rfl $$ [] Hmod [Hes1] [Hes2]
  · iintro ⟨%H, -⟩; cases H
  · iintro Hmod
    iapply Iris.wp_wand $$ [Hes1 Hmod]
    · iapply Hes1 $$ Hmod
    iintro %w ⟨%Hw, Hmod, HR⟩
    iframe
    ipureintro; exact Hw
  · iintro %w ⟨%Hw, HR⟩ Hmod
    iapply Hes2 $$ HR Hmod

@[rocq_alias iriswasm.instantiate_stack_adv_spec]
theorem instantiate_stack_adv_spec (adv_module : Module) (start : Nat) (exp_addrs : List Nat)
    (stack_mod_addr adv_mod_addr : Nat) :
    exp_addrs.length = 8 →
    -- we assume the adversary module imports the stack module
    ModuleTyping adv_module stackModuleImports [] →
    -- that it does have a start function
    adv_module.start = some { func := .funcidx start } →
    -- that it adheres to the module restrictions (i.e. only constant initializers for globals)
    ModuleRestrictions adv_module →
    -- if the adversary module declares a table, there cannot be more initializers than its size
    ModuleElemBoundCheckGmap ∅ [] adv_module →
    -- if the adversary module declares a memory, there cannot be more initializers than its size
    ModuleDataBoundCheckGmap ∅ [] adv_module →
    ⊢ iprop(□ ∀ Φ : HostVal → IProp GF,
        (stack_mod_addr ↪[mods] stackModule ∗
          adv_mod_addr ↪[mods] adv_module ∗
          NonAtomicInvariant.own (LogrelNaInvs.logrelNais (GF := GF)) ⊤ ∗
          ownVisPointers exp_addrs ∗
          ↪[frame] emptyFrame) -∗
        (∀ v, (((⌜v = .trapHV ∨ v = .immHV []⌝) ∗
            NonAtomicInvariant.own (LogrelNaInvs.logrelNais (GF := GF)) ⊤ ∗
            ∃ (newStackAddrIs : Nat → IProp GF) (isStack : Nat → List I32 → IProp GF),
              NonAtomicInvariant.inv (LogrelNaInvs.logrelNais (GF := GF)) stkN
                (stackModuleInv (fun n0 => isStack n0) newStackAddrIs)) ∗
            ↪[frame] emptyFrame) -∗ Φ v) -∗
        WP ((stackAdvInstantiate exp_addrs stack_mod_addr adv_mod_addr, []) : HostExpr)
          @ Stuckness.NotStuck ; ⊤ {{ v, Φ v }}) := by
  intro hlen htyp hstart hrestr hbst hbsm
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, rfl⟩ :
      ∃ e0 e1 e2 e3 e4 e5 e6 e7, exp_addrs = [e0, e1, e2, e3, e4, e5, e6, e7] := by
    match exp_addrs, hlen with
    | [e0, e1, e2, e3, e4, e5, e6, e7], _ => exact ⟨e0, e1, e2, e3, e4, e5, e6, e7, rfl⟩
  imodintro
  iintro %Φ ⟨Hmod_stack, Hmod_adv, Hown, Hvis, Hemptyframe⟩ HΦ
  unfold stackAdvInstantiate
  have Hvalid := instantiate_stack_valid (GF := GF) .NotStuck ⊤ [e0, e1, e2, e3, e4, e5, e6, e7] stack_mod_addr rfl
  simp only [stackInstantiatePara] at Hvalid
  iapply wp_seq_host_nostart_imm ⊤ Φ _ _ stack_mod_addr [] stackModule _ rfl $$ Hmod_stack [Hvis]
  · iintro Hmod_stack
    iapply Hvalid $$ Hmod_stack Hvis
  iintro ⟨%idf0, %idf1, %idf2, %idf3, %idf4, %idf5, %idf6, %idt, %nm0, %nm1, %nm2, %nm3, %nm4, %nm5,
    %nm6, %nm7, %f0, %f1, %f2, %f3, %f4, %f5, %f6, %istack, %l0, %l1, %l2, %l3, %l4, %l5, %l6,
    %stacktab, %isStack, %newStackAddrIs, HimpsH, HimpsW, %Hnodup, %Hfnodup, %Htablen, #Hinv,
    -, #Hinterp⟩ Hmod_stack
  simp only [importResourcesWasmTypecheckSepL2, importResourcesHost, stackInstVis, expts, funcTypes,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  icases HimpsW with ⟨-, ⟨%cl0, Hcl0, %Hcl0⟩, ⟨%cl1, Hcl1, %Hcl1⟩, ⟨%cl2, Hcl2, %Hcl2⟩,
    ⟨%cl3, Hcl3, %Hcl3⟩, ⟨%cl4, Hcl4, %Hcl4⟩, -⟩
  icases HimpsH with ⟨Hvis0, Hvis1, Hvis2, Hvis3, Hvis4, -⟩
  have hk := nodupKeys_zip _ [FunctionClosure.funcNative istack (.tf [] [.i32]) l0 f0,
     .funcNative istack (.tf [.i32] [.i32]) l1 f1,
     .funcNative istack (.tf [.i32] [.i32]) l2 f2,
     .funcNative istack (.tf [.i32] [.i32]) l3 f3,
     .funcNative istack (.tf [.i32, .i32] []) l4 f4,
     .funcNative istack (.tf [.i32, .i32] []) l5 f5,
     .funcNative istack (.tf [.i32] [.i32]) l6 f6] Hfnodup
  obtain rfl := Option.some.inj ((LawfulPartialMap.get?_ofList_some (k := idf0) (v := (.funcNative istack (.tf [] [.i32]) l0 f0))
    (by simp) hk).symm.trans Hcl0.1)
  obtain rfl := Option.some.inj ((LawfulPartialMap.get?_ofList_some (k := idf1) (v := (.funcNative istack (.tf [.i32] [.i32]) l1 f1))
    (by simp) hk).symm.trans Hcl1.1)
  obtain rfl := Option.some.inj ((LawfulPartialMap.get?_ofList_some (k := idf2) (v := (.funcNative istack (.tf [.i32] [.i32]) l2 f2))
    (by simp) hk).symm.trans Hcl2.1)
  obtain rfl := Option.some.inj ((LawfulPartialMap.get?_ofList_some (k := idf3) (v := (.funcNative istack (.tf [.i32] [.i32]) l3 f3))
    (by simp) hk).symm.trans Hcl3.1)
  obtain rfl := Option.some.inj ((LawfulPartialMap.get?_ofList_some (k := idf4) (v := (.funcNative istack (.tf [.i32, .i32] []) l4 f4))
    (by simp) hk).symm.trans Hcl4.1)
  have hnd5 : [idf0, idf1, idf2, idf3, idf4].Nodup := by
    simp at Hfnodup ⊢; grind
  have hk5 := nodupKeys_zip _ [FunctionClosure.funcNative istack (.tf [] [.i32]) l0 f0,
     .funcNative istack (.tf [.i32] [.i32]) l1 f1,
     .funcNative istack (.tf [.i32] [.i32]) l2 f2,
     .funcNative istack (.tf [.i32] [.i32]) l3 f3,
     .funcNative istack (.tf [.i32, .i32] []) l4 f4] hnd5
  rw [show List.take 5 [e0, e1, e2, e3, e4, e5, e6, e7] = [e0, e1, e2, e3, e4] from rfl]
  have hext : extTabs (List.map (·.desc) ([⟨nm0, .func ⟨idf0⟩⟩, ⟨nm1, .func ⟨idf1⟩⟩,
      ⟨nm2, .func ⟨idf2⟩⟩, ⟨nm3, .func ⟨idf3⟩⟩, ⟨nm4, .func ⟨idf4⟩⟩] : List ModuleExport)) = [] ∧
      extMems (List.map (·.desc) ([⟨nm0, .func ⟨idf0⟩⟩, ⟨nm1, .func ⟨idf1⟩⟩,
      ⟨nm2, .func ⟨idf2⟩⟩, ⟨nm3, .func ⟨idf3⟩⟩, ⟨nm4, .func ⟨idf4⟩⟩] : List ModuleExport)) = [] := by
    simp [extTabs, extMems]
  iapply instantiation_spec_operational_start_seq .NotStuck ⊤ adv_mod_addr [e0, e1, e2, e3, e4]
    [⟨nm0, .func ⟨idf0⟩⟩, ⟨nm1, .func ⟨idf1⟩⟩, ⟨nm2, .func ⟨idf2⟩⟩, ⟨nm3, .func ⟨idf3⟩⟩,
      ⟨nm4, .func ⟨idf4⟩⟩] [] adv_module stackModuleImports []
    (PartialMap.ofList ([idf0, idf1, idf2, idf3, idf4].zip
      [.funcNative istack (.tf [] [.i32]) l0 f0,
       .funcNative istack (.tf [.i32] [.i32]) l1 f1,
       .funcNative istack (.tf [.i32] [.i32]) l2 f2,
       .funcNative istack (.tf [.i32] [.i32]) l3 f3,
       .funcNative istack (.tf [.i32, .i32] []) l4 f4]))
    ∅ ∅ ∅ start Φ [] hstart htyp hrestr $$ Hemptyframe
    [Hmod_adv Hvis0 Hvis1 Hvis2 Hvis3 Hvis4 Hcl0 Hcl1 Hcl2 Hcl3 Hcl4] [Hown HΦ]
  · simp only [instantiationResourcesPre, instantiationResourcesPreWasm, importResourcesHost,
      exportOwnershipHost]
    iframe Hmod_adv
    isplitl [Hvis0 Hvis1 Hvis2 Hvis3 Hvis4]
    · iapply BI.BigSepL2.bigSepL2_cons.2
      iframe
      iapply BI.BigSepL2.bigSepL2_nil.2
      iempintro
    isplitl
    · isplitl
      · iapply (irwt_nodup_equiv _ _ _ _ _ _ (by simp; grind)).2
        simp only [importResourcesWasmTypecheckSepL2, importResourcesWasmDomcheck, stackModuleImports]
        isplitr
        · ipureintro
          simp only [List.zip_cons_cons, List.zip_nil_left, LawfulPartialMap.ofList_cons,
            LawfulPartialMap.dom_insert_iff]
          simp [PartialMap.ofList, PartialMap.dom, get?_empty, extFuncAddrs,
            extTabAddrs, extMemAddrs, extGlobAddrs, extFuncs, extTabs, extMems, extGlobs]
          grind
        iapply BI.BigSepL2.bigSepL2_cons.2
        isplitl [Hcl0]
        · iexists _; iframe Hcl0
          ipureintro; exact ⟨LawfulPartialMap.get?_ofList_some (by simp) hk5, rfl⟩
        iapply BI.BigSepL2.bigSepL2_cons.2
        isplitl [Hcl1]
        · iexists _; iframe Hcl1
          ipureintro; exact ⟨LawfulPartialMap.get?_ofList_some (by simp) hk5, rfl⟩
        iapply BI.BigSepL2.bigSepL2_cons.2
        isplitl [Hcl2]
        · iexists _; iframe Hcl2
          ipureintro; exact ⟨LawfulPartialMap.get?_ofList_some (by simp) hk5, rfl⟩
        iapply BI.BigSepL2.bigSepL2_cons.2
        isplitl [Hcl3]
        · iexists _; iframe Hcl3
          ipureintro; exact ⟨LawfulPartialMap.get?_ofList_some (by simp) hk5, rfl⟩
        iapply BI.BigSepL2.bigSepL2_cons.2
        isplitl [Hcl4]
        · iexists _; iframe Hcl4
          ipureintro; exact ⟨LawfulPartialMap.get?_ofList_some (by simp) hk5, rfl⟩
        iapply BI.BigSepL2.bigSepL2_nil.2
        iempintro
      isplit
      · ipureintro; unfold ModuleElemBoundCheckGmap; rw [hext.1]; exact hbst
      · ipureintro; unfold ModuleDataBoundCheckGmap; rw [hext.2]; exact hbsm
    isplit
    · iapply BI.BigSepL.bigSepL_nil.2; iempintro
    · ipureintro; exact (module_typing_exports_length _ _ _ htyp).symm
  iintro %idnstart Hf Hpost
  simp only [instantiationResourcesPost, instantiationResourcesPostWasm]
  icases Hpost with ⟨-, -, %inst, ⟨%g_inits, %tabA, %memA, %globA, %wts', %wms', Himpres, %Hinst,
    %Htab, %Hwts', %-, %Hmem, %Hwms', %-, %Hgv, %Hglob, Hres⟩, -⟩
  obtain ⟨fts, gts, hbody⟩ := (module_typing_body_eq _ _ _).1 htyp
  subst Htab Hwts' Hmem Hwms' Hglob
  have hcs : inst.funcs[start]? = some idnstart := by
    have h := Hinst.2.2.2.2.2
    simpa [checkStart, hstart, optionBind] using h
  iapply Iris.fupd_wp
  imod interp_instance_alloc [] ⊤ adv_module stackModuleImports [] _ _ ∅ ∅ ∅ inst fts gts g_inits
    hbody ⟨Hinst.1, Hinst.2.1, Hinst.2.2.1, Hinst.2.2.2.1, Hinst.2.2.2.2.1⟩ Hgv.1
    $$ Hinterp [] [] Himpres Hres with ⟨#Hi, Hres, -⟩
  · iapply BI.BigSepM.bigSepM_empty.2; iempintro
  · iapply BI.BigSepM.bigSepM_empty.2; iempintro
  imodintro
  ihave ⟨%τf, %Hτf, -⟩ := interp_instance_func_lookup start idnstart _ [] inst hcs $$ Hi
  ihave %Heq := module_typing_start_type adv_module stackModuleImports [] fts gts _
    ⟨.funcidx start⟩ idnstart inst start τf [] hbody rfl hstart rfl hcs Hτf $$ Hi
  subst Heq
  obtain ⟨n', fidx, locs, es, hl1, hl2, hnth, hes⟩ := module_typing_func_not_import adv_module
    stackModuleImports [] fts gts _ inst start [] [] idnstart rfl (mod_imps_len_t htyp).1 hbody hcs
    Hτf (by simp [stackModuleImports, extTFuncs])
  simp only [moduleInstResourcesWasmInvs, moduleInstResourcesFuncInvs]
  icases Hres with ⟨Hresf, -⟩
  ihave #Hstart := BI.BigSepL2.bigSepL2_lookup hl2 hl1 $$ Hresf
  simp only [Hinst.1, hnth]
  iapply wp_lift_wasm .NotStuck ⊤ [] [.invoke idnstart] Φ
  iapply wp_wand_s $$ [Hf Hown]
  · iapply start_spec _ inst idnstart locs es ⟨rfl, rfl⟩ hes $$ Hf Hown Hstart Hi
  iintro %v ⟨⟨%Hv, Hown⟩, Hf⟩
  rcases Hv with rfl | rfl
  · iapply IrisHost.wp_value .NotStuck ⊤ _ .trapHV Φ
      (show hostToVal (([], ofVal Val.trapV) : HostExpr) = some .trapHV from IrisHost.to_of_val .trapHV)
    iapply HΦ
    iframe
    isplitr
    · ipureintro; exact .inl rfl
    · iexists newStackAddrIs, isStack; iexact Hinv
  · iapply IrisHost.wp_value .NotStuck ⊤ _ (.immHV []) Φ
      (show hostToVal (([], ofVal (Val.immV [])) : HostExpr) = some (.immHV []) from
        IrisHost.to_of_val (.immHV []))
    iapply HΦ
    iframe
    isplitr
    · ipureintro; exact .inr rfl
    · iexists newStackAddrIs, isStack; iexact Hinv

end RobustStack

end IrisWasm.Examples.Stack
