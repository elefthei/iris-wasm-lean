/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Examples.IrisRobustExample
import IrisWasm.Logrel.IrisInterpInstanceAlloc
import Wasm.ModuleValidation

/-! Port of `theories/iris/examples/iris_robust_example_host.v`.

`lse_func_impts`, `lse_module_typing`, `module_restrictions_lse`, `adv_lse_instantiate` and
`instantiate_lse` are also declared in `iris_robust_example.v`; this file's versions live in
`namespace IrisWasm.Examples.IrisRobustExampleHost`. The Coq section notation
`{{{{ P }}}} es {{{{ v, Q }}}}` is written out in the statements. -/

namespace IrisWasm.Examples.IrisRobustExampleHost

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm IrisWasm IrisWasm.Examples
open scoped Iris.Std.PartialMap

variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF] [LogrelNaInvs GF] [HvisG GF]
  [HmsG GF] [HasG GF]

attribute [local instance] WasmG.invGS

local notation "logrelNais" => LogrelNaInvs.logrelNais (GF := GF)

section Host_instance

@[rocq_alias iriswasm.host_wp]
instance hostWp : HostProgramLogic (hlc := hlc) GF where
  hostFunction := HostExpr
  result := HostVal
  hostCtx := List HostE
  fillHost decls es := (decls, es)
  valOfHostVal := IrisWasm.valOfHostVal
  wpHost s E he Φ := iprop(WP he @ s ; E {{ Φ }})
  wpHostBind decls es Φ := by
    iintro Hwp
    iapply wp_lift_wasm
    iexact Hwp
  wpHostWand es Φ Ψ := by
    iintro Hwp Hwand
    iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ Hwp Hwand
  fupdWpHost e Φ := by
    iintro Hwp
    iapply Iris.fupd_wp
    iexact Hwp
  wpFupdHost e Φ := by
    iintro Hwp
    iapply Iris.wp_fupd
    iexact Hwp

end Host_instance

section Host_robust_example

@[rocq_alias iriswasm.lse_log_expr]
def lseLogExpr (f log : Nat) : List BasicInstruction :=
  [.const (xx 42), .setLocal 0, .call f, .getLocal 0, .call log]

@[rocq_alias iriswasm.lse_log]
def lseLog (f log : Nat) : Expr := toEList (lseLogExpr f log)

@[rocq_alias iriswasm.log]
def log : String := "logN"

@[rocq_alias iriswasm.logN]
def logN : Namespace := ndot nroot log

private instance haOwn_timeless (q : DFrac) (n : Nat) (a : HostAction) :
    Timeless (haOwn (GF := GF) q n a) := by
  unfold haOwn; infer_instance

@[rocq_alias iriswasm.lse_log_return_value]
theorem lse_log_return_value (f : Frame) (log logFunc h : Nat) (w : Val) (inst : Instance)
    (hlog : inst.funcs[log]? = some logFunc) :
    ⊢ NonAtomicInvariant.inv logrelNais logN iprop(h ↦[ha] HostAction.print) -∗
      interpValues [] w -∗
      NonAtomicInvariant.inv logrelNais (wfN logFunc)
        iprop(logFunc ↦[wf] (.funcHost (.tf [.i32] []) (.hostfuncidx h))) -∗
      NonAtomicInvariant.own logrelNais ⊤ -∗
      ↪[frame] (⟨[xx 42], inst⟩ : Frame) -∗
      WP (ofVal w) CTX 0 ; (.base [] [.basic (.getLocal 0), .basic (.call log)])
        {{ v, WP (ofVal v) CTX 1 ; (.rec_ [] 0 [] (.base [] []) [])
          {{ w0, ∃ f0,
            ((↪[frame] f : IProp GF) -∗
              WP (ofVal w0) @ Stuckness.NotStuck ; ⊤ FRAME 0 ; f0
                {{ w1, WP (([], ofVal w1) : HostExpr)
                  {{ w2, (⌜w2 = HostVal.trapHV⌝ ∨
                    (⌜w2 = HostVal.immHV []⌝ ∗ NonAtomicInvariant.own logrelNais ⊤)) ∗
                    ↪[frame] f }} }}) ∗ ↪[frame] f0 }} }} := by
  iintro #Hh Hv #Hl Hown Hf
  iunfold interpValues at Hv
  icases Hv with ⟨%ws, %Hw, #Hws⟩
  ihave %Hlen := BI.BigSepL2.bigSepL2_length $$ Hws
  subst Hw
  obtain rfl : ws = [] := List.eq_nil_of_length_eq_zero (by simpa using Hlen)
  iapply wp_base_pull
  dsimp only [pullBase]
  iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).1
  simp only [show ofVal (Val.immV []) = [] from rfl, List.nil_append]
  rw [show ([.basic (.getLocal 0), .basic (.call log)] : Expr) =
    [.basic (.getLocal 0)] ++ [.basic (.call log)] from rfl]
  iapply wp_seq _ _ _ (fun vs => iprop(⌜vs = .immV [xx 42]⌝ ∗ ↪[frame] (⟨[xx 42], inst⟩ : Frame)))
  isplitl []
  · iintro ⟨%H, -⟩; cases H
  isplitl [Hf]
  · iapply wp_get_local _ _ _ _ _ _ rfl $$ [] Hf
    inext; ipureintro; rfl
  iintro %w ⟨%hw, Hf⟩
  subst hw
  simp only [show ofVal (Val.immV [xx 42]) = [.basic (.const (xx 42))] from rfl, List.cons_append,
    List.nil_append]
  iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).2
  rw [show ([.basic (.const (xx 42)), .basic (.call log)] : Expr) =
    [.basic (.const (xx 42))] ++ [.basic (.call log)] ++ [] from rfl]
  iapply wp_base_push rfl
  iapply wp_call_ctx _ _ _ ⟨[xx 42], inst⟩ log logFunc 0 _ hlog $$ Hf
  inext
  iintro Hf
  iapply wp_base_pull
  dsimp only [frameBase, pullBase]
  iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).1
  simp only [List.nil_append, List.append_nil]
  iapply IrisWp.fupd_wp (ι := wasmIrisGS) (fun f => iprop(↪[frame] f))
  imod NonAtomicInvariant.inv_acc CoPset.subseteq_top CoPset.subseteq_top $$ Hl Hown with
    ⟨>Hlog, Hown, Hcls⟩
  imodintro
  iapply wp_invoke_host .NotStuck ⊤ [.basic (.const (xx 42))] [xx 42] 1 [.i32] [] logFunc
    (.hostfuncidx h) ⟨[xx 42], inst⟩ _ rfl rfl rfl $$ Hlog Hf
  inext
  iintro Hlog Hf
  iapply IrisWp.fupd_wp (ι := wasmIrisGS) (fun f => iprop(↪[frame] f))
  imod Hcls $$ [Hlog Hown] with Hown
  · iframe
  imodintro
  rw [show ([.callHost (.tf [.i32] []) (.hostfuncidx h) [xx 42]] : Expr) =
    ofVal (.callHostV (.tf [.i32] []) (.hostfuncidx h) [xx 42] (.base [] [])) by
      simp [ofVal, llfill, vToEList]]
  iapply IrisWp.wp_value (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) ⟨rfl⟩
  rw [show Lholed.rec_ [] 0 [] (.base [] []) [] = pushBase (.base [] []) 0 [] [] [] from rfl]
  iapply wp_label_push_nil_inv
  iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).1
  rw [show ([.label 0 [] (ofVal (.callHostV (.tf [.i32] []) (.hostfuncidx h) [xx 42]
      (.base [] [])))]
      : Expr) = ofVal (.callHostV (.tf [.i32] []) (.hostfuncidx h) [xx 42]
        (.label [] 0 [] (.base [] []) [])) by simp [ofVal, llfill, vToEList]]
  iapply IrisWp.wp_value (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) ⟨rfl⟩
  iexists ⟨[xx 42], inst⟩
  iframe Hf
  iintro Hf
  unfold wpWasmFrame
  rw [show ([.local 0 ⟨[xx 42], inst⟩ (ofVal (.callHostV (.tf [.i32] []) (.hostfuncidx h) [xx 42]
        (.label [] 0 [] (.base [] []) [])))] : Expr) =
      ofVal (.callHostV (.tf [.i32] []) (.hostfuncidx h) [xx 42]
        (.local [] 0 ⟨[xx 42], inst⟩ (.label [] 0 [] (.base [] []) []) [])) by
      simp [ofVal, llfill, vToEList]]
  iapply IrisWp.wp_value (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) ⟨rfl⟩
  iapply Iris.fupd_wp
  imod NonAtomicInvariant.inv_acc CoPset.subseteq_top CoPset.subseteq_top $$ Hh Hown with
    ⟨>HL, Hown, Hcls⟩
  imodintro
  iapply wp_call_host_action_no_state_change .NotStuck ⊤ [] (.tf [.i32] []) (.hostfuncidx h) h
    .print [xx 42] _ [] (.local [] 0 ⟨[xx 42], inst⟩ (.label [] 0 [] (.base [] []) []) [])
    (ofVal (.callHostV (.tf [.i32] []) (.hostfuncidx h) [xx 42]
      (.local [] 0 ⟨[xx 42], inst⟩ (.label [] 0 [] (.base [] []) []) []))) _ rfl rfl rfl
    (fun s0 f0 => .print s0 f0 _)
  isplitl [HL]
  · iexact HL
  inext
  iintro HL
  iapply Iris.fupd_wp
  imod Hcls $$ [HL Hown] with Hown
  · iframe
  imodintro
  iapply wp_lift_wasm
  simp only [llfill, vToEList, List.map_nil, List.nil_append, List.append_nil]
  iapply (wp_frame_rewrite _ _ _ _ _ _).1
  have hnv : toVal [.local 0 ⟨[xx 42], inst⟩ [.label 0 [] []]] = none :=
    to_val_immV_AI_local_is_basic_None 0 _ 0 [] (.base [] []) [] trivial
  iapply wp_frame_bind _ _ _ 0 ⟨[xx 42], inst⟩ f _ hnv $$ Hf
  iintro Hf
  iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ [Hf]
  · iapply wp_label_value (Φ := fun v => iprop(⌜v = Val.immV []⌝))
      (show toVal ([] : Expr) = some (.immV []) from rfl) $$ Hf
    inext; ipureintro; rfl
  iintro %v ⟨%hv, Hf⟩
  subst hv
  iexists ⟨[xx 42], inst⟩
  iframe Hf
  iintro Hf
  unfold wpWasmFrame
  rw [show ofVal (Val.immV []) = [] from rfl]
  iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ [Hf]
  · iapply (wp_frame_rewrite _ _ _ _ _ _).1
    iapply wp_frame_value _ _ (fun v => iprop(⌜v = Val.immV []⌝)) [] 0 ⟨[xx 42], inst⟩ f []
      rfl rfl $$ Hf
    inext; ipureintro; rfl
  iintro %v ⟨%hv, Hf⟩
  subst hv
  iapply IrisHost.wp_value _ _ _ (.immHV []) _ rfl
  iframe Hf
  iright
  iframe
  ipureintro; rfl

@[rocq_alias iriswasm.iris_robust_example_host.llholed_basic_sh_append]
theorem llholed_basic_sh_append (vh : Llholed) (e : List AdministrativeInstruction)
    (he : isBasicExpr e) (hvh : llholedBasic vh) : llholedBasic (llhAppend vh e) := by
  cases vh with
  | base => exact is_basic_app _ _ hvh he
  | label => exact ⟨is_basic_app _ _ hvh.1 he, hvh.2⟩
  | «local» => exact ⟨is_basic_app _ _ hvh.1 he, hvh.2⟩

/-- The Löb induction of `lse_log_return_call_host`, generalised over the returned value. -/
private theorem lse_log_return_call_host_aux (f : Frame) (log logFunc h : Nat) (inst : Instance)
    (hlog : inst.funcs[log]? = some logFunc) :
    ⊢ NonAtomicInvariant.inv logrelNais logN iprop(h ↦[ha] HostAction.print) -∗
      NonAtomicInvariant.inv logrelNais (wfN logFunc)
        iprop(logFunc ↦[wf] (.funcHost (.tf [.i32] []) (.hostfuncidx h))) -∗
      ∀ w, ▷ interpCallHostCls [(.hostfuncidx h, .tf [.i32] [])] [] w -∗
      NonAtomicInvariant.own logrelNais ⊤ -∗
      ↪[frame] (⟨[xx 42], inst⟩ : Frame) -∗
      WP (ofVal w) CTX 0 ; (.base [] [.basic (.getLocal 0), .basic (.call log)])
        {{ v, WP (ofVal v) CTX 1 ; (.rec_ [] 0 [] (.base [] []) [])
          {{ w0, ∃ f0,
            ((↪[frame] f : IProp GF) -∗
              WP (ofVal w0) @ Stuckness.NotStuck ; ⊤ FRAME 0 ; f0
                {{ w1, WP (([], ofVal w1) : HostExpr)
                  {{ w2, (⌜w2 = HostVal.trapHV⌝ ∨
                    (⌜w2 = HostVal.immHV []⌝ ∗ NonAtomicInvariant.own logrelNais ⊤)) ∗
                    ↪[frame] f }} }}) ∗ ↪[frame] f0 }} }} := by
  iintro #Hh #Hl
  iloeb as IH
  iintro %w Hv Hown Hf
  rw [fixpoint_interp_call_host_cls_eq]
  iunfold interpCallHostClsDef at Hv
  iapply wp_base_pull
  dsimp only [pullBase]
  iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).1
  icases Hv with ⟨%vh, %v, %tf, %h', %τs1, %τs2, >%Heq, >%Htf, >%Hin, >%Hb, >Hw, Hcont⟩
  simp only [List.mem_singleton, Prod.mk.injEq] at Hin
  obtain ⟨rfl, rfl⟩ := Hin
  cases Htf
  subst Heq
  iunfold interpVal at Hw
  iunfold interpValues at Hw
  icases Hw with (%Hc | ⟨%ws, %Hws, Hws⟩)
  · cases Hc
  cases Hws
  ihave %Hlen := BI.BigSepL2.bigSepL2_length $$ Hws
  obtain ⟨x, rfl⟩ : ∃ x, v = [x] := by
    match v, Hlen with
    | [x], _ => exact ⟨x, rfl⟩
  have hb' : llholedBasic (llhAppend vh [.basic (.getLocal 0), .basic (.call log)]) :=
    llholed_basic_sh_append _ _ ⟨trivial, trivial, trivial⟩ Hb
  generalize hvh' : llhAppend vh [.basic (.getLocal 0), .basic (.call log)] = vh' at hb'
  rw [show [] ++ ofVal (.callHostV (.tf [.i32] []) (.hostfuncidx h) [x] vh) ++
      [.basic (.getLocal 0), .basic (.call log)] =
      ofVal (.callHostV (.tf [.i32] []) (.hostfuncidx h) [x] vh') by
    subst hvh'; simp [ofVal, llfill_sh_append, llfill, vToEList]]
  iapply IrisWp.wp_value (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) ⟨rfl⟩
  rw [show Lholed.rec_ [] 0 [] (.base [] []) [] = pushBase (.base [] []) 0 [] [] [] from rfl]
  iapply wp_label_push_nil_inv
  iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).1
  rw [show ([.label 0 [] (ofVal (.callHostV (.tf [.i32] []) (.hostfuncidx h) [x] vh'))]
      : Expr) = ofVal (.callHostV (.tf [.i32] []) (.hostfuncidx h) [x]
        (.label [] 0 [] vh' [])) by simp [ofVal, llfill, vToEList]]
  iapply IrisWp.wp_value (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) ⟨rfl⟩
  iexists ⟨[xx 42], inst⟩
  iframe Hf
  iintro Hf
  iapply (wp_frame_rewrite _ _ _ _ _ _).2
  rw [show ([.local 0 ⟨[xx 42], inst⟩ (ofVal (.callHostV (.tf [.i32] []) (.hostfuncidx h) [x]
        (.label [] 0 [] vh' [])))] : Expr) =
      ofVal (.callHostV (.tf [.i32] []) (.hostfuncidx h) [x]
        (.local [] 0 ⟨[xx 42], inst⟩ (.label [] 0 [] vh' []) [])) by
      simp [ofVal, llfill, vToEList]]
  iapply IrisWp.wp_value (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) ⟨rfl⟩
  iapply Iris.fupd_wp
  imod NonAtomicInvariant.inv_acc CoPset.subseteq_top CoPset.subseteq_top $$ Hh Hown with
    ⟨>HL, Hown, Hcls⟩
  imodintro
  iapply wp_call_host_action_no_state_change .NotStuck ⊤ [] (.tf [.i32] []) (.hostfuncidx h) h
    .print [x] _ [] (.local [] 0 ⟨[xx 42], inst⟩ (.label [] 0 [] vh' []) [])
    (ofVal (.callHostV (.tf [.i32] []) (.hostfuncidx h) [x]
      (.local [] 0 ⟨[xx 42], inst⟩ (.label [] 0 [] vh' []) []))) _ rfl rfl rfl
    (fun s0 f0 => .print s0 f0 _)
  isplitl [HL]
  · iexact HL
  inext
  iintro HL
  iapply Iris.fupd_wp
  imod Hcls $$ [HL Hown] with Hown
  · iframe
  imodintro
  iapply wp_lift_wasm
  simp only [llfill, vToEList, List.map_nil, List.nil_append]
  iapply (wp_frame_rewrite _ _ _ _ _ _).1
  have hnv : toVal [.local 0 ⟨[xx 42], inst⟩ [.label 0 [] (llfill vh' [])]] = none :=
    to_val_immV_AI_local_is_basic_None 0 _ 0 [] vh' [] hb'
  iapply wp_frame_bind _ _ _ 0 ⟨[xx 42], inst⟩ f _ hnv $$ Hf
  iintro Hf
  iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).2
  iapply wp_label_push_nil
  iapply wp_ctx_bind _ _ _ _ _ _ (show BaseIsEmpty (pushBase (.base [] []) 0 [] [] []) from
    ⟨rfl, rfl⟩)
  subst hvh'
  rw [llfill_sh_append]
  simp only [llfill, vToEList, List.map_nil, List.nil_append]
  rw [show llfill vh [] ++ [.basic (.getLocal 0), .basic (.call log)] =
    [] ++ llfill vh [] ++ [.basic (.getLocal 0), .basic (.call log)] from rfl]
  iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).2
  iapply wp_base_push rfl
  simp only [frameBase, List.append_nil]
  rw [← List.append_nil (llfill vh [])]
  iapply wp_seq_can_trap_ctx _ _ _
    (fun vs => iprop((interpValues [] vs ∨
      ▷ interpCallHostCls [(.hostfuncidx h, .tf [.i32] [])] [] vs) ∗
      NonAtomicInvariant.own logrelNais ⊤))
    (llfill vh []) [] 0 _ (fun f' => iprop(⌜f' = ⟨[xx 42], inst⟩⌝)) ⟨[xx 42], inst⟩
  isplitr
  · iintro ⟨H, -⟩
    icases H with (H | H)
    · iunfold interpValues at H
      icases H with ⟨%ws, %Hc, -⟩
      cases Hc
    · rw [fixpoint_interp_call_host_cls_eq]
      iunfold interpCallHostClsDef at H
      icases H with ⟨%_, %_, %_, %_, %_, %_, >%Hc, -⟩
      cases Hc
  isplitr
  · iintro %f1 ⟨Hf1, %hf1⟩
    subst hf1
    iapply wp_label_push_nil_inv
    iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).1
    iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ [Hf1]
    · iapply wp_label_trap (Φ := fun v => iprop(⌜v = Val.trapV⌝))
        (to_of_val .trapV) $$ Hf1
      inext; ipureintro; rfl
    iintro %v ⟨%hv, Hf1⟩
    subst hv
    iexists ⟨[xx 42], inst⟩
    iframe Hf1
    iintro Hf
    iapply (wp_frame_rewrite _ _ _ _ _ _).2
    rw [show ofVal Val.trapV = [.trap] from rfl]
    iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ [Hf]
    · iapply (wp_frame_rewrite _ _ _ _ _ _).1
      iapply wp_frame_trap _ _ (fun v => iprop(⌜v = Val.trapV⌝)) 0 ⟨[xx 42], inst⟩ f $$ Hf
      inext; ipureintro; rfl
    iintro %v ⟨%hv, Hf⟩
    subst hv
    iapply IrisHost.wp_value _ _ _ .trapHV _
      (show hostToVal (([], ofVal Val.trapV) : HostExpr) = some .trapHV from
        IrisHost.to_of_val .trapHV)
    iframe Hf
    ileft; ipureintro; rfl
  isplitl [Hf]
  · iexact Hf
  isplitl [Hown Hcont]
  · iintro Hf
    ihave Hc := Hcont $$ %(Val.immV []) %(⟨[xx 42], inst⟩ : Frame) [] Hf Hown
    · iunfold interpVal; iright; iunfold interpValues
      iexists []
      isplitr
      · ipureintro; rfl
      iapply BigSepL2.bigSepL2_nil.2; iempintro
    rw [show llfill vh [] = llfill vh (ofVal (.immV [])) from rfl]
    iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ Hc
    iintro %v ⟨Hv, Hf, Hown⟩
    isplitl [Hv Hown]
    · iunfold interpVal at Hv
      icases Hv with ((%Hv | Hv) | Hv)
      · ileft; ipureintro; exact Hv
      · iright; isplitl [Hv]
        · ileft; iexact Hv
        · iexact Hown
      · iright; isplitl [Hv]
        · iright; iexact Hv
        · iexact Hown
    · iexists ⟨[xx 42], inst⟩
      iframe Hf
      ipureintro; rfl
  iintro %w' %f1 ⟨⟨Hv, Hown⟩, Hf, %hf1⟩
  subst hf1
  simp only [List.append_nil, Nat.zero_add, pushBase]
  icases Hv with (Hv | Hv)
  · iapply lse_log_return_value f log logFunc h w' inst hlog $$ Hh Hv Hl Hown Hf
  · iapply IH $$ %w' Hv Hown Hf

@[rocq_alias iriswasm.lse_log_return_call_host]
theorem lse_log_return_call_host (f : Frame) (log logFunc h : Nat) (w : Val) (inst : Instance)
    (hlog : inst.funcs[log]? = some logFunc) :
    ⊢ NonAtomicInvariant.inv logrelNais logN iprop(h ↦[ha] HostAction.print) -∗
      ▷ interpCallHostCls [(.hostfuncidx h, .tf [.i32] [])] [] w -∗
      NonAtomicInvariant.inv logrelNais (wfN logFunc)
        iprop(logFunc ↦[wf] (.funcHost (.tf [.i32] []) (.hostfuncidx h))) -∗
      NonAtomicInvariant.own logrelNais ⊤ -∗
      ↪[frame] (⟨[xx 42], inst⟩ : Frame) -∗
      WP (ofVal w) CTX 0 ; (.base [] [.basic (.getLocal 0), .basic (.call log)])
        {{ v, WP (ofVal v) CTX 1 ; (.rec_ [] 0 [] (.base [] []) [])
          {{ w0, ∃ f0,
            ((↪[frame] f : IProp GF) -∗
              WP (ofVal w0) @ Stuckness.NotStuck ; ⊤ FRAME 0 ; f0
                {{ w1, WP (([], ofVal w1) : HostExpr)
                  {{ w2, (⌜w2 = HostVal.trapHV⌝ ∨
                    (⌜w2 = HostVal.immHV []⌝ ∗ NonAtomicInvariant.own logrelNais ⊤)) ∗
                    ↪[frame] f }} }}) ∗ ↪[frame] f0 }} }} := by
  iintro #Hh Hv #Hl Hown Hf
  iapply lse_log_return_call_host_aux f log logFunc h inst hlog $$ Hh Hl %w Hv Hown Hf

@[rocq_alias iriswasm.lse_log_spec]
theorem lse_log_spec (C : TContext) (i : Instance) (f : Frame) (g gFunc : Nat)
    (es : List BasicInstruction) (locs : List ValueType) (log logFunc h idnstart : Nat)
    (inst : Instance)
    (hC : C.label = [] ∧ C.return_ = none)
    (htyp : BeTyping (updLocalLabelReturn C locs [[]] (some [])) es (.tf [] []))
    (hg : inst.funcs[g]? = some gFunc)
    (hlog : inst.funcs[log]? = some logFunc) :
    ⊢ iprop(□ ∀ Φ : HostVal → IProp GF,
        (↪[frame] f ∗
          NonAtomicInvariant.own logrelNais ⊤ ∗
          idnstart ↦[wf] (.funcNative inst (.tf [] []) [.i32] (lseLogExpr g log)) ∗
          NonAtomicInvariant.inv logrelNais (wfN gFunc)
            iprop(gFunc ↦[wf] (.funcNative i (.tf [] []) locs es)) ∗
          interpInstance C [(.hostfuncidx h, .tf [.i32] [])] i ∗
          NonAtomicInvariant.inv logrelNais logN iprop(h ↦[ha] HostAction.print) ∗
          NonAtomicInvariant.inv logrelNais (wfN logFunc)
            iprop(logFunc ↦[wf] (.funcHost (.tf [.i32] []) (.hostfuncidx h)))) -∗
        (∀ w, ((⌜w = HostVal.trapHV⌝ ∨
            (⌜w = HostVal.immHV []⌝ ∗ NonAtomicInvariant.own logrelNais ⊤)) ∗
            ↪[frame] f) -∗ Φ w) -∗
        WP (([], [.invoke idnstart]) : HostExpr) @ Stuckness.NotStuck ; ⊤ {{ v, Φ v }}) := by
  imodintro
  iintro %Φ ⟨Hf, Hown, Hidnstart, #Hadv, #Hi, #Hh, #Hlog⟩ HΦ
  iapply Iris.wp_wand (Φ := fun w => iprop((⌜w = HostVal.trapHV⌝ ∨
      (⌜w = HostVal.immHV []⌝ ∗ NonAtomicInvariant.own logrelNais ⊤)) ∗ ↪[frame] f))
    $$ [Hf Hown Hidnstart] HΦ
  iapply wp_lift_wasm
  rw [show ([.invoke idnstart] : Expr) = [] ++ [.invoke idnstart] from rfl]
  iapply wp_invoke_native _ _ _ [] [] [] [] [.i32] idnstart (lseLogExpr g log) inst 0 f rfl rfl rfl
    $$ Hf Hidnstart
  inext
  iintro ⟨Hf, Hidnstart⟩
  iapply (wp_frame_rewrite _ _ _ _ _ _).1
  iapply wp_frame_bind _ _ _ 0 _ f _ (toVal_native_frame_none _ _ _) $$ Hf
  iintro Hf
  iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).2
  iapply wp_label_push_nil
  iapply wp_ctx_bind _ _ _ _ _ _ (show BaseIsEmpty (pushBase (.base [] []) 0 [] [] []) from
    ⟨rfl, rfl⟩)
  simp only [lseLogExpr, toEList, List.map_cons, List.map_nil, List.nil_append]
  rw [show [AdministrativeInstruction.basic (.const (xx 42)), .basic (.setLocal 0),
      .basic (.call g), .basic (.getLocal 0), .basic (.call log)] = [.basic (.const (xx 42)), .basic (.setLocal 0)] ++
      [.basic (.call g), .basic (.getLocal 0), .basic (.call log)] from rfl]
  iapply wp_seq _ _ _ (fun vs => iprop(⌜vs = .immV []⌝ ∗
    ↪[frame] (⟨(nZeros [.i32]).set 0 (xx 42), inst⟩ : Frame)))
  isplitl []
  · iintro ⟨%H, -⟩; cases H
  isplitl [Hf]
  · iapply wp_set_local _ _ _ _ _ _ (by simp [nZeros]) $$ [] Hf
    inext; ipureintro; rfl
  iintro %w ⟨%hw, Hf⟩
  subst hw
  rw [show (nZeros [.i32]).set 0 (xx 42) = [xx 42] from rfl]
  iapply IrisWp.fupd_wp (ι := wasmIrisGS) (fun f => iprop(↪[frame] f))
  imod NonAtomicInvariant.inv_acc CoPset.subseteq_top CoPset.subseteq_top $$ Hadv Hown with
    ⟨>Hg, Hown, Hcls⟩
  imodintro
  rw [show ofVal (.immV []) ++ [AdministrativeInstruction.basic (.call g), .basic (.getLocal 0),
      .basic (.call log)] = [] ++ [.basic (.call g)] ++ [.basic (.getLocal 0), .basic (.call log)]
      from rfl]
  iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).2
  iapply wp_base_push rfl
  iapply wp_call_ctx _ _ _ ⟨[xx 42], inst⟩ g gFunc 0 _ hg $$ Hf
  inext
  iintro Hf
  simp only [frameBase, List.append_nil]
  rw [← List.append_nil [AdministrativeInstruction.invoke gFunc]]
  iapply wp_seq_can_trap_ctx _ _ _
    (fun vs => iprop((interpValues [] vs ∨
      interpCallHostCls [(.hostfuncidx h, .tf [.i32] [])] [] vs) ∗
      NonAtomicInvariant.own logrelNais ⊤))
    [.invoke gFunc] [] 0 _ (fun f' => iprop(⌜f' = ⟨[xx 42], inst⟩⌝)) ⟨[xx 42], inst⟩
  isplitr
  · iintro ⟨H, -⟩
    icases H with (H | H)
    · iunfold interpValues at H
      icases H with ⟨%ws, %Hc, -⟩
      cases Hc
    · rw [fixpoint_interp_call_host_cls_eq]
      iunfold interpCallHostClsDef at H
      icases H with ⟨%_, %_, %_, %_, %_, %_, %Hc, -⟩
      cases Hc
  isplitr
  · iintro %f1 ⟨Hf1, %hf1⟩
    subst hf1
    iapply wp_label_push_nil_inv
    iapply (wandIff_equiv (wp_wasm_empty_ctx _ _ _ _)).1
    iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ [Hf1]
    · iapply wp_label_trap (Φ := fun v => iprop(⌜v = Val.trapV⌝))
        (to_of_val .trapV) $$ Hf1
      inext; ipureintro; rfl
    iintro %v ⟨%hv, Hf1⟩
    subst hv
    iexists ⟨[xx 42], inst⟩
    iframe Hf1
    iintro Hf
    iapply (wp_frame_rewrite _ _ _ _ _ _).2
    rw [show ofVal Val.trapV = [.trap] from rfl]
    iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ [Hf]
    · iapply (wp_frame_rewrite _ _ _ _ _ _).1
      iapply wp_frame_trap _ _ (fun v => iprop(⌜v = Val.trapV⌝)) 0 ⟨[xx 42], inst⟩ f $$ Hf
      inext; ipureintro; rfl
    iintro %v ⟨%hv, Hf⟩
    subst hv
    iapply IrisHost.wp_value _ _ _ .trapHV _
      (show hostToVal (([], ofVal Val.trapV) : HostExpr) = some .trapHV from
        IrisHost.to_of_val .trapHV)
    iframe Hf
    ileft; ipureintro; rfl
  isplitl [Hf]
  · iexact Hf
  isplitl [Hg Hown Hcls]
  · iintro Hf
    rw [← List.nil_append [AdministrativeInstruction.invoke gFunc]]
    iapply wp_invoke_native _ _ _ [] [] [] [] locs gFunc es i 0 ⟨[xx 42], inst⟩ rfl rfl rfl
      $$ Hf Hg
    inext
    iintro ⟨Hf, Hg⟩
    iapply IrisWp.fupd_wp (ι := wasmIrisGS) (fun f => iprop(↪[frame] f))
    imod Hcls $$ [Hg Hown] with Hown
    · iframe
    imodintro
    ihave HH := be_fundamental_local_stuck_host (GF := GF) C es [] [] locs
      [(.hostfuncidx h, .tf [.i32] [])] hC htyp
    iunfold semanticTypingLocalStuckHost at HH
    icases HH with ⟨-, HH⟩
    ihave Hc := HH $$ %i Hi %⟨[xx 42], inst⟩ %(nZeros locs) Hf Hown []
    · iunfold interpVal; iright; iunfold interpValues
      iexists nZeros locs
      isplitr
      · ipureintro; rfl
      simp only [List.nil_append]
      iapply n_zeros_interp_values
    iunfold interpExpressionClosureStuckHost at Hc
    simp only [List.nil_append]
    iapply IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) $$ Hc
    iintro %v ⟨⟨Hv, Hown⟩, Hf⟩
    isplitl [Hv Hown]
    · icases Hv with (Hv | Hv)
      · iunfold interpVal at Hv
        icases Hv with (%Hv | Hv)
        · ileft; ipureintro; exact Hv
        · iright; isplitl [Hv]
          · ileft; iexact Hv
          · iexact Hown
      · iright; isplitl [Hv]
        · iright; iexact Hv
        · iexact Hown
    · iexists ⟨[xx 42], inst⟩
      iframe Hf
      ipureintro; rfl
  iintro %w' %f1 ⟨⟨Hv, Hown⟩, Hf, %hf1⟩
  subst hf1
  simp only [List.append_nil, Nat.zero_add, pushBase]
  icases Hv with (Hv | Hv)
  · iapply lse_log_return_value f log logFunc h w' inst hlog $$ Hh Hv Hlog Hown Hf
  · iapply lse_log_return_call_host f log logFunc h w' inst hlog $$ Hh [Hv] Hlog Hown Hf
    inext; iexact Hv

@[rocq_alias iriswasm.lse_log_module]
def lseLogModule : Module where
  types := [.tf [] [], .tf [.i32] [], .tf [] []]
  funcs := [{ type := .typeidx 0, locals := [.i32], body := lseLogExpr 0 1 }]
  tables := []
  mems := []
  globals := []
  elem := []
  data := []
  start := some { func := .funcidx 2 }
  imports := [
    { module := nameOfString "Adv", name := nameOfString "adv_call", desc := .func 0 },
    { module := nameOfString "Host", name := nameOfString "log_call", desc := .func 1 }]
  exports := []

@[rocq_alias iriswasm.iris_robust_example_host.lse_func_impts]
def lseFuncImpts : List ExternT := [.func (.tf [] []), .func (.tf [.i32] [])]

@[rocq_alias iriswasm.iris_robust_example_host.lse_module_typing]
theorem lse_module_typing : ModuleTyping lseLogModule lseFuncImpts [] := by
  apply (validateModule_iff _ ⟨_, _⟩).mp
  rfl

@[rocq_alias iriswasm.iris_robust_example_host.module_restrictions_lse]
theorem module_restrictions_lse : ModuleRestrictions lseLogModule :=
  ⟨⟨[], rfl⟩, ⟨[], rfl⟩, ⟨[], rfl⟩⟩

@[rocq_alias iriswasm.iris_robust_example_host.adv_lse_instantiate]
def advLseInstantiate : List HostE :=
  [.instantiate [1] 0 [0], .instantiate [] 1 [1, 0]]

omit [WasmG hlc GF] [LogrelNaInvs GF] [HvisG GF] [HmsG GF] [HasG GF] in
private theorem forall2_lookup_r {A B : Type} {R : A → B → Prop} {l1 : List A} {l2 : List B}
    (h : Wasm.List.Forall₂ R l1 l2) {i : Nat} {b : B} (hb : l2[i]? = some b) :
    ∃ a, l1[i]? = some a ∧ R a b := by
  induction h generalizing i with
  | nil => simp at hb
  | cons hab _ ih =>
    cases i with
    | zero => simp at hb; subst hb; exact ⟨_, rfl, hab⟩
    | succ i => simpa using ih (by simpa using hb)

omit [WasmG hlc GF] [LogrelNaInvs GF] [HvisG GF] [HmsG GF] [HasG GF] in
/-- What the adversary's module typing says about it (Lean helper: the Coq proof of
`instantiate_lse` derives these facts inline). -/
private theorem adv_typing_facts (adv : Module)
    (htyp : ModuleTyping adv [.func (.tf [.i32] [])] [.func (.tf [] [])]) :
    ∃ fts gts, ModuleTypingBody adv [.func (.tf [.i32] [])] [.func (.tf [] [])] fts gts ∧
      getImportFuncCount adv = 1 ∧
      ∃ nm n mf k, adv.exports = [⟨nm, .func (.funcidx (n + 1))⟩] ∧ adv.funcs[n]? = some mf ∧
        mf.type = .typeidx k ∧ adv.types.getD k (.tf [] []) = .tf [] [] ∧
        BeTyping (updLocalLabelReturn
          { typesT := adv.types, funcT := extTFuncs [.func (.tf [.i32] [])] ++ fts
            global := extTGlobs [.func (.tf [.i32] [])] ++ gts
            table := extTTabs [.func (.tf [.i32] [])] ++ adv.tables.map (·.type)
            memory := extTMems [.func (.tf [.i32] [])] ++ adv.mems
            local_ := [], label := [], return_ := none } mf.locals [[]] (some []))
          mf.body (.tf [] []) := by
  obtain ⟨fts, gts, h⟩ := htyp
  refine ⟨fts, gts, h, ?_⟩
  obtain ⟨tfs, fs, ts, ms, gs, els, ds, iOpt, imps, exps⟩ := adv
  obtain ⟨hfs, -, -, -, -, -, -, himps, -, hexps⟩ := h
  cases himps with
  | cons hi hnil =>
  cases hnil
  rename_i imp
  refine ⟨?_, ?_⟩
  · obtain ⟨imod, iname, desc⟩ := imp
    cases desc <;> simp_all [moduleImportTyping, moduleContext, getImportFuncCount]
  cases hexps with
  | cons he hnil =>
  cases hnil
  rename_i e
  obtain ⟨nm, desc⟩ := e
  cases desc with
  | func fi =>
    obtain ⟨nidx⟩ := fi
    cases nidx with
    | zero => simp [moduleExportTyping, moduleContext, extTFuncs] at he
    | succ n =>
    have hft : fts[n]? = some (.tf [] []) := by
      simp [moduleExportTyping, moduleContext, extTFuncs] at he
      split at he <;> simp_all
    obtain ⟨⟨⟨k⟩, locs, body⟩, hmf, hty⟩ := forall2_lookup_r hfs hft
    obtain ⟨hk, hbe⟩ := hty
    change tfs[k]? = _ at hk
    refine ⟨nm, n, _, k, rfl, hmf, rfl, by simp [List.getD_eq_getElem?_getD, hk], ?_⟩
    simpa [moduleContext, updLocalLabelReturn] using hbe
  | table t => obtain ⟨_⟩ := t; simp [moduleExportTyping] at he
  | mem m => obtain ⟨_⟩ := m; simp [moduleExportTyping] at he
  | global g => obtain ⟨_⟩ := g; simp [moduleExportTyping] at he

@[rocq_alias iriswasm.iris_robust_example_host.instantiate_lse]
theorem instantiate_lse (advModule : Module) (logFunc h : Nat)
    -- we assume the adversary module has an export of the () → ()
    (htyp : ModuleTyping advModule [.func (.tf [.i32] [])] [.func (.tf [] [])])
    -- that it does not have a start function
    (hnostart : advModule.start = none)
    -- that it adheres to the module restrictions (i.e. only constant initializers for globals)
    (hrestrict : ModuleRestrictions advModule)
    -- if the adversary module declares a table, there cannot be more initializers than its size
    (hboundst : ModuleElemBoundCheckGmap ∅ [] advModule)
    -- if the adversary module declares a memory, there cannot be more initializers than its size
    (hboundsm : ModuleDataBoundCheckGmap ∅ [] advModule) :
    ⊢ iprop(□ ∀ Φ : HostVal → IProp GF,
        (↪[frame] emptyFrame ∗
          logFunc ↦[wf] (.funcHost (.tf [.i32] []) (.hostfuncidx h)) ∗
          h ↦[ha] HostAction.print ∗
          0 ↪[mods] advModule ∗
          1 ↪[mods] lseLogModule ∗
          NonAtomicInvariant.own logrelNais ⊤ ∗
          (∃ name, 0 ↪[vis] (⟨name, .func (.funcidx logFunc)⟩ : ModuleExport)) ∗
          (∃ vs, 1 ↪[vis] vs)) -∗
        (∀ v, (⌜v = HostVal.trapHV⌝ ∨
            (⌜v = HostVal.immHV []⌝ ∗ NonAtomicInvariant.own logrelNais ⊤)) -∗ Φ v) -∗
        WP ((advLseInstantiate, []) : HostExpr) @ Stuckness.NotStuck ; ⊤ {{ v, Φ v }}) := by
  obtain ⟨fts, gts, Hbody, Hfc, nm, n, mf, k, Hexps, Hmf, Hmft, Hk, Hbe⟩ :=
    adv_typing_facts advModule htyp
  imodintro
  iintro %Φ ⟨Hemptyframe, Hlogfunc, Hh, Hmod_adv, Hmod_lse, Hown, ⟨%log, Hvis1⟩, ⟨%vs, Hvis⟩⟩ HΦ
  unfold advLseInstantiate
  iapply wp_seq_host_nostart .NotStuck ⊤ Φ
    (fun w => iprop(⌜w = HostVal.immHV []⌝ ∗
      importResourcesHost [0] [⟨log, .func (.funcidx logFunc)⟩] ∗
      ∃ inst, instantiationResourcesPostWasm advModule [⟨log, .func (.funcidx logFunc)⟩]
          [.func (.tf [.i32] [])]
          (PartialMap.singleton logFunc (.funcHost (.tf [.i32] []) (.hostfuncidx h))) ∅ ∅ ∅ none
          inst ∗
        moduleExportResourcesHost [1] advModule.exports inst))
    [1] 0 [0] advModule _ [] hnostart rfl $$ [] Hmod_adv [Hvis Hvis1 Hlogfunc]
  · iintro ⟨%H, -⟩; cases H
  · iintro Hmod_adv
    iapply Iris.wp_wand $$ [Hmod_adv Hvis Hvis1 Hlogfunc]
    · iapply instantiation_spec_operational_no_start .NotStuck ⊤ 0 [0]
        [⟨log, .func (.funcidx logFunc)⟩] [1] advModule [.func (.tf [.i32] [])]
        [.func (.tf [] [])] (PartialMap.singleton logFunc (.funcHost (.tf [.i32] []) (.hostfuncidx h)))
        ∅ ∅ ∅ hnostart htyp hrestrict
      unfold instantiationResourcesPre importResourcesHost exportOwnershipHost
        instantiationResourcesPreWasm importResourcesWasmTypecheck
      unfold_irwt_all
      iframe Hmod_adv
      isplitl [Hvis1]
      · iapply BI.BigSepL2.bigSepL2_singleton.2
        iexact Hvis1
      isplitl [Hlogfunc]
      · isplitl [Hlogfunc]
        · isplitl [Hlogfunc]
          · isplitl [Hlogfunc]
            · iapply BI.BigSepM.bigSepM_singleton.2; iexact Hlogfunc
            ipureintro
            refine ⟨.cons ⟨_, RobustAux.singleton_get _ _, rfl⟩ .nil, fun k => ?_⟩
            rw [RobustAux.singleton_dom]; simp [extFuncAddrs, extFuncs, eq_comm]
          isplitr
          · iapply RobustAux.empty_map_check _ ⟨.cons trivial .nil,
              fun k => by simp [PartialMap.dom, get?_empty, extTabAddrs, extTabs]⟩
          isplitr
          · iapply RobustAux.empty_map_check _ ⟨.cons trivial .nil,
              fun k => by simp [PartialMap.dom, get?_empty, extMemAddrs, extMems]⟩
          iapply RobustAux.empty_map_check _ ⟨.cons trivial .nil,
            fun k => by simp [PartialMap.dom, get?_empty, extGlobAddrs, extGlobs]⟩
        isplitr
        · ipureintro; exact hboundst
        ipureintro; exact hboundsm
      isplitl [Hvis]
      · iapply BI.BigSepL.bigSepL_singleton.2
        iexists vs; iexact Hvis
      ipureintro; simp [Hexps]
    · iintro %v ⟨%Hv, Hpost⟩
      iunfold instantiationResourcesPost at Hpost
      icases Hpost with ⟨Hmod, Himps, Hpost⟩
      iframe Hmod Himps Hpost
      ipureintro; exact Hv
  iintro %w ⟨%Hw, Himps, ⟨%inst_adv, Hpost, Hexp⟩⟩ Hmod_adv
  unfold instantiationResourcesPostWasm moduleInstResourcesWasm moduleExportResourcesHost
    importResourcesHost importResourcesWasmTypecheck importFuncWasmCheck importFuncResources
  rw [Hexps, Hfc]
  icases Hexp with ⟨⟨%nm', Hn⟩, -⟩
  ihave Hvis1 := BI.BigSepL2.bigSepL2_singleton.1 $$ Himps
  icases Hpost with ⟨%g_inits, %tabA, %memA, %globA, %wts', %wms', ⟨⟨Hlogf, %Hlogfc⟩, Himpsrest⟩,
    %HH, %Htabeq, %Hwts', %-, %Hmemeq, %Hwms', %-, %Hgv, %Hgleq, Hresf, Hrest, Hresm, Hresg⟩
  ihave Hlogfunc := BI.BigSepM.bigSepM_singleton.1 $$ Hlogf
  unfold moduleInstResourcesFunc
  ihave ⟨%Hflen, Hresf⟩ := BI.persistent_entails_right BI.BigSepL2.bigSepL2_length $$ Hresf
  obtain ⟨advf, Hadv⟩ : ∃ advf, (inst_adv.funcs.drop 1)[n]? = some advf := by
    have := (List.getElem?_eq_some_iff.1 Hmf).1
    exact ⟨_, List.getElem?_eq_getElem (Hflen ▸ this)⟩
  ihave ⟨Hadvf, Hcls⟩ := BI.BigSepL2.bigSepL2_lookup_acc Hmf Hadv $$ Hresf
  have hgd : inst_adv.funcs.getD (n + 1) 0 = advf := by
    rw [List.getElem?_drop, Nat.add_comm] at Hadv
    simp [List.getD_eq_getElem?_getD, Hadv]
  dsimp only
  rw [hgd]
  have htyk : inst_adv.types.getD (match mf.type with | .typeidx k => k) (.tf [] []) = .tf [] [] := by
    rw [HH.1, Hmft]; exact Hk
  rw [htyk]
  ihave %Hne := @pointsTo_ne GF Nat FunctionClosure NatMap _ WasmG.funcHs _ _ _ _ _ $$ Hadvf Hlogfunc
  have hadvlog : get? (PartialMap.singleton logFunc (.funcHost (.tf [.i32] []) (.hostfuncidx h)) :
      NatMap FunctionClosure) advf = none := LawfulPartialMap.get?_singleton_ne (Ne.symm Hne)
  iapply instantiation_spec_operational_start .NotStuck ⊤ 1 [1, 0]
    [⟨nm', .func ⟨advf⟩⟩, ⟨log, .func ⟨logFunc⟩⟩] [] lseLogModule lseFuncImpts []
    (PartialMap.insert (PartialMap.singleton logFunc (.funcHost (.tf [.i32] []) (.hostfuncidx h)))
      advf (.funcNative inst_adv (.tf [] []) mf.locals mf.body))
    ∅ ∅ ∅ 2 Φ rfl lse_module_typing module_restrictions_lse $$ Hemptyframe
    [Hmod_lse Hn Hvis1 Hadvf Hlogfunc]
  · unfold instantiationResourcesPre importResourcesHost exportOwnershipHost
      instantiationResourcesPreWasm importResourcesWasmTypecheck
    unfold_irwt_all
    iframe Hmod_lse
    isplitl [Hn Hvis1]
    · iapply BI.BigSepL2.bigSepL2_cons.2
      isplitl [Hn]
      · iexact Hn
      iapply BI.BigSepL2.bigSepL2_singleton.2
      iexact Hvis1
    isplitl [Hadvf Hlogfunc]
    · isplitl [Hadvf Hlogfunc]
      · isplitl [Hadvf Hlogfunc]
        · isplitl [Hadvf Hlogfunc]
          · iapply (BI.BigSepM.bigSepM_insert hadvlog).2
            isplitl [Hadvf]
            · iexact Hadvf
            iapply BI.BigSepM.bigSepM_singleton.2; iexact Hlogfunc
          ipureintro
          refine ⟨.cons ⟨_, get?_insert_eq rfl, rfl⟩
            (.cons ⟨_, by rw [get?_insert_ne Hne]; exact RobustAux.singleton_get _ _, rfl⟩ .nil),
            fun k => ?_⟩
          by_cases hk : advf = k
          · subst hk; simp [PartialMap.dom, get?_insert_eq, extFuncAddrs, extFuncs]
          · rw [PartialMap.dom, get?_insert_ne hk, ← PartialMap.dom, RobustAux.singleton_dom]
            simp [extFuncAddrs, extFuncs, eq_comm]
            exact fun h' => absurd h' hk
        isplitr
        · iapply RobustAux.empty_map_check _ ⟨.cons trivial (.cons trivial .nil),
            fun k => by simp [PartialMap.dom, get?_empty, extTabAddrs, extTabs]⟩
        isplitr
        · iapply RobustAux.empty_map_check _ ⟨.cons trivial (.cons trivial .nil),
            fun k => by simp [PartialMap.dom, get?_empty, extMemAddrs, extMems]⟩
        iapply RobustAux.empty_map_check _ ⟨.cons trivial (.cons trivial .nil),
          fun k => by simp [PartialMap.dom, get?_empty, extGlobAddrs, extGlobs]⟩
      isplitr
      · ipureintro; intro e he; simp [lseLogModule] at he
      ipureintro; intro e he; simp [lseLogModule] at he
    isplitr
    · iapply BI.BigSepL.bigSepL_nil.2; iempintro
    ipureintro; rfl
  iintro %idnstart Hf Hpost
  unfold instantiationResourcesPost instantiationResourcesPostWasm moduleInstResourcesWasm
    importResourcesWasmTypecheck
  unfold_irwt_all
  icases Hpost with ⟨-, -, %inst, ⟨%g_inits', %tabA', %memA', %globA', %wts'', %wms'',
    ⟨⟨Hwf, -⟩, -⟩, %HH', %-, %-, %-, %-, %-, %-, %-, %-, Hrf, -⟩, -⟩
  ihave ⟨Hwfadv, Hwlog⟩ := (BI.BigSepM.bigSepM_insert hadvlog).1 $$ Hwf
  ihave Hwlog := BI.BigSepM.bigSepM_singleton.1 $$ Hwlog
  ihave Hresf := Hcls $$ Hwfadv
  obtain ⟨Hity, ⟨tf, Htf⟩, -, -, -, Hcs⟩ := HH'
  have hg : inst.funcs[0]? = some advf := by rw [← Htf]; rfl
  have hlog : inst.funcs[1]? = some logFunc := by rw [← Htf]; rfl
  have hs : inst.funcs[2]? = some idnstart := of_decide_eq_true Hcs
  rw [show lseLogModule.funcs = [⟨.typeidx 0, [.i32], lseLogExpr 0 1⟩] from rfl]
  unfold moduleInstResourcesFunc
  ihave ⟨%a', %xs', %hfd, Hidn, -⟩ := BI.BigSepL2.bigSepL2_cons_inv_left.1 $$ Hrf
  have ha' : a' = idnstart := by
    rw [show getImportFuncCount lseLogModule = 2 from rfl] at hfd
    have := congrArg (·[0]?) hfd; simp at this; rw [hs] at this; exact (Option.some.inj this).symm
  subst ha' Hwts' Hwms' Htabeq Hmemeq Hgleq
  rw [Hity]
  ihave HR : moduleInstResourcesWasm advModule inst_adv (moduleInstBuildTables advModule inst_adv)
      (moduleInstBuildMems advModule inst_adv)
      (moduleInstGlobalInit (moduleInstBuildGlobals advModule.globals) g_inits)
      $$ [Hresf Hrest Hresm Hresg]
  · unfold moduleInstResourcesWasm moduleInstResourcesFunc
    rw [Hfc]; iframe
  iapply Iris.fupd_wp
  imod interp_instance_alloc [(.hostfuncidx h, .tf [.i32] [])] ⊤ advModule [.func (.tf [.i32] [])]
    [.func (.tf [] [])] [⟨log, .func ⟨logFunc⟩⟩]
    (PartialMap.singleton logFunc (.funcHost (.tf [.i32] []) (.hostfuncidx h))) ∅ ∅ ∅ inst_adv
    fts gts g_inits Hbody ⟨HH.1, HH.2.1, HH.2.2.1, HH.2.2.2.1, HH.2.2.2.2.1⟩ Hgv.1
    $$ [] [] [] [Hwlog Himpsrest] HR with ⟨Hi, Hinvs, Himpinvs⟩
  · iapply BI.BigSepM.bigSepM_singleton.2
    simp only [interpClosure, clType]
    isplit <;> ipureintro <;> simp
  · iapply BI.BigSepM.bigSepM_empty.2; iempintro
  · iapply BI.BigSepM.bigSepM_empty.2; iempintro
  · unfold importResourcesWasmTypecheck importFuncWasmCheck importFuncResources
    isplitl [Hwlog]
    · isplitl
      · iapply BI.BigSepM.bigSepM_singleton.2; iexact Hwlog
      ipureintro; exact Hlogfc
    unfold importTabWasmCheck importMemWasmCheck importGlobWasmCheck importTabResources
      importMemResources importGlobResources tabTypecheck memTypecheck globTypecheck tabDomcheck
      memDomcheck globDomcheck
    iexact Himpsrest
  unfold moduleInstResourcesWasmInvs moduleInstResourcesFuncInvs
  icases Hinvs with ⟨Hires, -⟩
  rw [Hfc]
  ihave Ha := BI.BigSepL2.bigSepL2_lookup Hmf Hadv $$ Hires
  rw [htyk]
  unfold importResourcesWasmTypecheckInvs importFuncWasmCheckInvs importFuncNainv
  icases Himpinvs with ⟨⟨Hlinv, -⟩, -⟩
  ihave Hlinv := BI.BigSepM.bigSepM_singleton.1 $$ Hlinv
  rw [show lseLogModule.types = [.tf [] [], .tf [.i32] [], .tf [] []] from rfl]
  dsimp only
  simp only [List.getD_cons_zero]
  ihave Hhinv := NonAtomicInvariant.inv_alloc (p := logrelNais) (E := ⊤) (N := logN)
    (P := iprop(h ↦[ha] HostAction.print)) $$ [Hh]
  · inext; iexact Hh
  imod Hhinv with #Hhinv
  imodintro
  iapply lse_log_spec _ inst_adv emptyFrame 0 advf mf.body mf.locals 1 logFunc h a' inst ⟨rfl, rfl⟩
    Hbe hg hlog $$ [Hf Hown Hidn Ha Hi Hhinv Hlinv] [HΦ]
  · iframe; iexact Hhinv
  iintro %v ⟨Hv, -⟩
  iapply HΦ; iexact Hv

end Host_robust_example

end IrisWasm.Examples.IrisRobustExampleHost
