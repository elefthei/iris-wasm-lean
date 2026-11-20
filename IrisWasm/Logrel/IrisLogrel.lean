/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import Iris.Instances.Lib.NaInvariants
import IrisWasm.Language.IrisAtomicity
import IrisWasm.Language.IrisWpDef
import IrisWasm.Helpers.Prelude.IrisLfilledProperties
import IrisWasm.Rules.IrisRulesPure
import IrisWasm.Rules.IrisRulesStructural
import IrisWasm.Rules.IrisRulesControl
import IrisWasm.Rules.IrisRulesResources
import IrisWasm.Rules.IrisRulesCalls
import IrisWasm.Rules.IrisRulesTrap
import IrisWasm.Rules.IrisRulesBind

/-! Port of `theories/iris/logrel/iris_logrel.v`.

Coq's non-expansive maps `leibnizO A -n> iPropO Σ` are plain functions `A → IProp GF` (every domain is
discrete); the two fixpoints are taken in the function-space COFE. Coq's `≡` on `iProp` is `=` in Lean. -/

namespace IrisWasm

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm OFE

@[rocq_alias iriswasm.wf] def wf : String := "wfN"
@[rocq_alias iriswasm.wt] def wt : String := "wtN"
@[rocq_alias iriswasm.wm] def wm : String := "wmN"
@[rocq_alias iriswasm.wg] def wg : String := "wgN"
@[rocq_alias iriswasm.wfN] def wfN (a : Nat) : Namespace := ndot (ndot nroot wf) a
@[rocq_alias iriswasm.wtN] def wtN (a b : Nat) : Namespace := ndot (ndot (ndot nroot wt) a) b
@[rocq_alias iriswasm.wmN] def wmN (a : Nat) : Namespace := ndot (ndot nroot wm) a
@[rocq_alias iriswasm.wgN] def wgN (a : Nat) : Namespace := ndot (ndot nroot wg) a

/-! ### Pure auxiliary definitions -/

@[rocq_alias iriswasm.get_base_l]
def getBaseL : {i : Nat} → ValidHoled i → List Value
  | _, .base vs _ => vs
  | _, .rec_ _ _ _ lh' _ => getBaseL lh'

@[rocq_alias iriswasm.simple_get_base_l]
def simpleGetBaseL : SimpleValidHoled → List Value
  | .base vs _ => vs
  | .rec_ _ _ _ lh' _ => simpleGetBaseL lh'

@[rocq_alias iriswasm.is_basic]
def isBasic : AdministrativeInstruction → Prop
  | .basic _ => True
  | _ => False

@[rocq_alias iriswasm.is_basic_expr]
def isBasicExpr : List AdministrativeInstruction → Prop
  | [] => True
  | a :: ai => isBasic a ∧ isBasicExpr ai

@[rocq_alias iriswasm.llholed_basic]
def llholedBasic : Llholed → Prop
  | .base _ ai => isBasicExpr ai
  | .label _ _ _ vh ai => isBasicExpr ai ∧ llholedBasic vh
  | .local _ _ _ vh ai => isBasicExpr ai ∧ llholedBasic vh

@[rocq_alias iriswasm.lholed_valid]
def LholedValid : Lholed → Prop
  | .base vs _ => constList vs = true
  | .rec_ vs _ _ lh' _ => constList vs = true ∧ LholedValid lh'

@[rocq_alias iriswasm.lholed_valid_fill]
theorem lholed_valid_fill (lh : Lholed) :
    ∀ es, LholedValid lh → ∃ LI, lfilled (lhDepth lh) lh es LI = true := by
  intro es hv
  induction lh with
  | base vs es' => exact ⟨_, (lfilled_Ind_Equivalent ..).2 (.lfilledBase vs es es' hv)⟩
  | rec_ vs n es1 lh' es2 ih =>
    obtain ⟨LI, h⟩ := ih hv.2
    exact ⟨_, (lfilled_Ind_Equivalent ..).2
      (.lfilledRec _ vs n es1 lh' es2 es LI hv.1 ((lfilled_Ind_Equivalent ..).1 h))⟩

@[rocq_alias iriswasm.length_lholeds]
def lengthLholeds : List (List ValueType) → Lholed → Prop
  | [], .base _ _ => True
  | τs :: τc, .rec_ _ n _ lh' _ => τs.length = n ∧ lengthLholeds τc lh'
  | _, _ => False

variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF] [LogrelNaInvs GF]

attribute [local instance] WasmG.invGS

/-- `na_own logrel_nais E`. -/
local notation "logrelNais" => LogrelNaInvs.logrelNais (GF := GF)

/-! ### Value relation -/

@[rocq_alias iriswasm.interp_value_i32]
def interpValueI32 (w : Value) : IProp GF := iprop(⌜∃ z, w = .int32 z⌝)
@[rocq_alias iriswasm.interp_value_i64]
def interpValueI64 (w : Value) : IProp GF := iprop(⌜∃ z, w = .int64 z⌝)
@[rocq_alias iriswasm.interp_value_f32]
def interpValueF32 (w : Value) : IProp GF := iprop(⌜∃ z, w = .float32 z⌝)
@[rocq_alias iriswasm.interp_value_f64]
def interpValueF64 (w : Value) : IProp GF := iprop(⌜∃ z, w = .float64 z⌝)

@[rocq_alias iriswasm.interp_value]
def interpValue : ValueType → Value → IProp GF
  | .i32 => interpValueI32
  | .i64 => interpValueI64
  | .f32 => interpValueF32
  | .f64 => interpValueF64

@[rocq_alias iriswasm.interp_values]
def interpValues (τs : List ValueType) (v : Val) : IProp GF :=
  iprop(∃ ws, ⌜v = .immV ws⌝ ∗ [∗list] w;τ ∈ ws;τs, interpValue τ w)

@[rocq_alias iriswasm.interp_val]
def interpVal (τs : List ValueType) (v : Val) : IProp GF :=
  iprop(⌜v = .trapV⌝ ∨ interpValues τs v)

/-! ### Frame relation -/

@[rocq_alias iriswasm.interp_frame]
def interpFrame (τs : List ValueType) (i : Instance) (f : Frame) : IProp GF :=
  iprop(∃ vs, ⌜f = ⟨vs, i⟩⌝ ∗ interpVal τs (.immV vs) ∗ NonAtomicInvariant.own logrelNais ⊤)

/-! ### Return relation -/

@[rocq_alias iriswasm.interp_return_option]
def interpReturnOption (τr : Option (List ValueType)) (_τl : List ValueType) (_i : Instance)
    (w : Val) : IProp GF :=
  iprop(∃ (vh : SimpleValidHoled) (v : List Value), ⌜w = .retV vh⌝ ∗ ⌜simpleGetBaseL vh = v⌝ ∗
    match τr with
    | some τr => ∃ τs'', interpVal (τs'' ++ τr) (.immV v) ∗
        ∀ f f', ↪[frame] f' -∗
          WP ([.local τr.length f (ofVal w)] : Expr) {{ vs, interpVal τr vs ∗ ↪[frame] f' }}
    | none => False)

/-! ### Closure relation -/

omit [LogrelNaInvs GF] in
/-- Non-expansiveness of the Wasm WP in its postcondition. -/
private theorem wp_wasm_ne {n : Nat} {s : Stuckness} {E : CoPset} {e : Expr}
    {Φ Ψ : Val → IProp GF} (h : ∀ v, Φ v ≡{n}≡ Ψ v) :
    (Wp.wp s E e Φ : IProp GF) ≡{n}≡ Wp.wp s E e Ψ :=
  (IrisWp.wp_ne (P := fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)).ne h

/-- Congruence steps for the contractiveness proofs below (Coq's `repeat (apply …_ne)`). -/
local macro "logrel_ne" : tactic => `(tactic| repeat' (first
  | refine wp_wasm_ne fun _ => ?_
  | refine BI.exists_ne fun _ => ?_
  | refine BI.forall_ne fun _ => ?_
  | refine BI.sep_ne.ne ?_ ?_
  | refine BI.wand_ne.ne ?_ ?_
  | refine BI.or_ne.ne ?_ ?_
  | refine BI.intuitionistically_ne.ne ?_
  | refine BI.persistently_ne.ne ?_
  | refine BI.and_ne.ne ?_ ?_
  | exact .rfl))

@[rocq_alias iriswasm.interp_call_host_cls_def]
def interpCallHostClsDef (hostList : List (Hostfuncidx × FunctionType)) (τ2 : List ValueType)
    (interpCallHost' : Val → IProp GF) (w : Val) : IProp GF :=
  iprop(∃ (vh : Llholed) (v : List Value) (tf : FunctionType) (h : Hostfuncidx)
      (τs1 τs2 : List ValueType),
    ⌜w = .callHostV tf h v vh⌝ ∗
    ⌜tf = .tf τs1 τs2⌝ ∗
    ⌜(h, tf) ∈ hostList⌝ ∗
    ⌜llholedBasic vh⌝ ∗
    interpVal τs1 (.immV v) ∗
    □ (∀ v2 f, interpVal τs2 v2 -∗
        ↪[frame] f -∗ NonAtomicInvariant.own logrelNais ⊤ -∗
        WP (llfill vh (ofVal v2))
          {{ vs, (interpVal τ2 vs ∨ ▷ interpCallHost' vs) ∗ ↪[frame] f ∗
            NonAtomicInvariant.own logrelNais ⊤ }}))

@[rocq_alias iriswasm.interp_call_host_cls_def_contractive]
instance interpCallHostClsDef_contractive (hl : List (Hostfuncidx × FunctionType))
    (t2 : List ValueType) : OFE.Contractive (interpCallHostClsDef (GF := GF) hl t2) where
  distLater_dist {n x y} H w := by
    unfold interpCallHostClsDef
    logrel_ne
    exact OFE.Contractive.distLater_dist (f := BI.later) fun m hm => H m hm _

@[rocq_alias iriswasm.interp_call_host_cls]
def interpCallHostCls (hostList : List (Hostfuncidx × FunctionType)) (t2 : List ValueType) :
    Val → IProp GF :=
  fixpoint (interpCallHostClsDef hostList t2)

@[rocq_alias iriswasm.fixpoint_interp_call_host_cls_eq]
theorem fixpoint_interp_call_host_cls_eq (hostList : List (Hostfuncidx × FunctionType))
    (t2 : List ValueType) (v : Val) :
    (interpCallHostCls hostList t2 v : IProp GF) =
      interpCallHostClsDef hostList t2 (interpCallHostCls hostList t2) v :=
  congrFun (fixpoint_unfold (interpCallHostClsDef hostList t2).toContractiveHom) v

@[rocq_alias iriswasm.interp_closure_native]
def interpClosureNative (i : Instance) (tf1s tf2s tlocs : List ValueType) (e : Expr)
    (hl : List (Hostfuncidx × FunctionType)) : IProp GF :=
  iprop(∀ vcs f, interpVal tf1s (.immV vcs) -∗
    NonAtomicInvariant.own logrelNais ⊤ -∗
    ↪[frame] f -∗
    WP e FRAME (tf2s.length) ; (⟨vcs ++ nZeros tlocs, i⟩ : Frame)
      CTX 1 ; (Lholed.rec_ [] tf2s.length [] (.base [] []) [])
      {{ v, (interpVal tf2s v ∨ interpCallHostCls hl tf2s v) ∗
        NonAtomicInvariant.own logrelNais ⊤ ∗ ↪[frame] f }})

@[rocq_alias iriswasm.interp_closure]
def interpClosure (hostList : List (Hostfuncidx × FunctionType)) (τf : FunctionType) :
    FunctionClosure → IProp GF
  | .funcNative i (.tf tf1s tf2s) tlocs e =>
    iprop(⌜τf = .tf tf1s tf2s⌝ ∗ □ ▷ interpClosureNative i tf1s tf2s tlocs (toEList e) hostList)
  | .funcHost (.tf tf1s tf2s) h => iprop(⌜τf = .tf tf1s tf2s⌝ ∗ ⌜(h, τf) ∈ hostList⌝)

@[rocq_alias iriswasm.interp_function]
def interpFunction (τf : FunctionType)
    (interpClosure' : Nat → FunctionType → FunctionClosure → IProp GF) (n : Nat) : IProp GF :=
  iprop(∃ (cl : FunctionClosure), NonAtomicInvariant.inv logrelNais (wfN n) iprop(n ↦[wf] cl) ∗
    interpClosure' n τf cl)

/-! ### Table relation -/

@[rocq_alias iriswasm.interp_table_entry]
def interpTableEntry (τf : FunctionType)
    (interpClosure' : Nat → FunctionType → FunctionClosure → IProp GF) (n m : Nat) : IProp GF :=
  iprop(∃ (fe : Funcelem), NonAtomicInvariant.inv logrelNais (wtN n m) iprop(n ↦[wt][ m ] fe) ∗
    match fe with
    | some a => interpFunction τf interpClosure' a
    | none => True)

@[rocq_alias iriswasm.interp_table]
def interpTable (tableSize : Nat)
    (interpClosure' : Nat → FunctionType → FunctionClosure → IProp GF) (n : Nat) : IProp GF :=
  iprop([∗list] k ↦ _x ∈ List.replicate tableSize 0,
    ∃ (τf : FunctionType), interpTableEntry τf interpClosure' n k)

/-! ### Memory relation -/

@[rocq_alias iriswasm.interp_mem]
def interpMem (n : Nat) : IProp GF :=
  NonAtomicInvariant.inv logrelNais (wmN n) iprop(∃ (mem : Memory),
    ([∗list] k ↦ b ∈ mem.data.data, n ↦[wm][ k ] b) ∗ n ↦[wmlength] lengthMem mem)

/-! ### Globals relation -/

@[rocq_alias iriswasm.interp_global]
def interpGlobal (τg : GlobalType) (n : Nat) : IProp GF :=
  match τg.mut_ with
  | .immut => iprop(∃ (P : ValueType → Value → IProp GF),
      (□ ∀ w, P τg.t w -∗ interpValue τg.t w) ∗
      NonAtomicInvariant.inv logrelNais (wgN n)
        iprop(∃ w, n ↦[wg] (⟨.immut, w⟩ : Global) ∗ P τg.t w))
  | .mut => NonAtomicInvariant.inv logrelNais (wgN n)
      iprop(∃ w, n ↦[wg] (⟨.mut, w⟩ : Global) ∗ interpValue τg.t w)

/-! ### Instance relation -/

@[rocq_alias iriswasm.interp_instance']
def interpInstance' (τctx : TContext)
    (interpClosure' interpClosure'' : Nat → FunctionType → FunctionClosure → IProp GF)
    (i : Instance) : IProp GF :=
  iprop(
    -- Type declarations
    ⌜i.types = τctx.typesT⌝ ∗
    -- Function declarations
    ([∗list] kf;tf ∈ i.funcs;τctx.funcT, interpFunction tf interpClosure' kf) ∗
    -- Function tables
    (match τctx.table[0]? with
     | some τt => match i.tab[0]? with
       | some a => ∃ (tableSize : Nat) (tableLim : Option Nat),
           ⌜tableLim.isSome.toNat ≤ τt.limits.max.isSome.toNat⌝ ∗
           a ↪[wtlimit] tableLim ∗
           a ↪[wtsize] tableSize ∗
           interpTable tableSize interpClosure'' a
       | none => False
     | none => True) ∗
    -- Linear memory
    (match τctx.memory[0]? with
     | some τm => match i.memory[0]? with
       | some a => a ↪[wmlimit] τm.max ∗ interpMem a
       | none => False
     | none => True) ∗
    -- Global declarations
    ([∗list] kg;gt ∈ i.globs;τctx.global, interpGlobal gt kg))

@[rocq_alias iriswasm.interp_instance]
def interpInstance (τctx : TContext) (hostList : List (Hostfuncidx × FunctionType))
    (i : Instance) : IProp GF :=
  interpInstance' τctx (fun _ => interpClosure hostList) (fun _ => interpClosure hostList) i

@[rocq_alias iriswasm.interp_function_persistent]
instance interpFunction_persistent (τf : FunctionType) (n : Nat)
    (icl : Nat → FunctionType → FunctionClosure → IProp GF)
    [∀ n τf cl, Persistent (icl n τf cl)] : Persistent (interpFunction τf icl n) := by
  unfold interpFunction; infer_instance

@[rocq_alias iriswasm.interp_global_persistent]
instance interpGlobal_persistent (τg : GlobalType) (n : Nat) :
    Persistent (interpGlobal (GF := GF) τg n) := by
  unfold interpGlobal
  cases τg.mut_ <;> dsimp only <;> infer_instance

private instance interpTableEntry_persistent (τf : FunctionType) (n m : Nat)
    (icl : Nat → FunctionType → FunctionClosure → IProp GF)
    [∀ n τf cl, Persistent (icl n τf cl)] : Persistent (interpTableEntry τf icl n m) := by
  unfold interpTableEntry
  have (fe : Funcelem) : Persistent (match fe with
      | some a => interpFunction τf icl a
      | none => iprop(True) : IProp GF) := by
    cases fe <;> dsimp only <;> infer_instance
  infer_instance

@[rocq_alias iriswasm.interp_instance_persistent']
instance interpInstance_persistent' (τctx : TContext) (i : Instance)
    (icl icl' : Nat → FunctionType → FunctionClosure → IProp GF)
    [∀ n τf cl, Persistent (icl n τf cl)] [∀ n τf cl, Persistent (icl' n τf cl)] :
    Persistent (interpInstance' τctx icl icl' i) := by
  unfold interpInstance' interpTable interpMem
  cases τctx.table[0]? <;> cases i.tab[0]? <;> cases τctx.memory[0]? <;> cases i.memory[0]? <;>
    dsimp only <;> infer_instance

@[rocq_alias iriswasm.interp_value_persistent]
instance interpValue_persistent (τ : ValueType) (vs : Value) :
    Persistent (interpValue (GF := GF) τ vs) := by
  cases τ <;> unfold interpValue interpValueI32 interpValueI64 interpValueF32 interpValueF64 <;>
    infer_instance

@[rocq_alias iriswasm.interp_val_persistent]
instance interpVal_persistent (τr : List ValueType) (vs : Val) :
    Persistent (interpVal (GF := GF) τr vs) := by
  unfold interpVal interpValues; infer_instance

@[rocq_alias iriswasm.interp_call_host_cls_persistent]
instance interpCallHostCls_persistent (hl : List (Hostfuncidx × FunctionType))
    (t : List ValueType) (v : Val) : Persistent (interpCallHostCls (GF := GF) hl t v) := by
  rw [fixpoint_interp_call_host_cls_eq]; unfold interpCallHostClsDef; infer_instance

@[rocq_alias iriswasm.interp_instance_persistent]
instance interpInstance_persistent (τctx : TContext) (hl : List (Hostfuncidx × FunctionType))
    (i : Instance) : Persistent (interpInstance (GF := GF) τctx hl i) := by
  have (n : Nat) (τf : FunctionType) (cl : FunctionClosure) :
      Persistent ((fun _ => interpClosure (GF := GF) hl) n τf cl) := by
    rcases cl with ⟨_, ⟨_, _⟩, _, _⟩ | ⟨⟨_, _⟩, _⟩ <;> dsimp only [interpClosure] <;> infer_instance
  exact @interpInstance_persistent' hlc GF _ _ τctx i _ _ this this

/-! ### Expression relation -/

/-- Coq `HR`: the call-host relation. -/
local notation "HR" => Val → Lholed → List (List ValueType) → List ValueType → IProp GF
/-- Coq `BR`: the break relation. -/
local notation "BR" => Val → Lholed → List (List ValueType) → IProp GF

@[rocq_alias iriswasm.interp_call_host_br_def]
def interpCallHostBrDef (τl : List ValueType) (i : Instance) (τro : Option (List ValueType))
    (hostList : List (Hostfuncidx × FunctionType)) (interpCallHostBr' : HR × BR) : HR × BR :=
  (fun w lh τc τ2 => iprop(
    ∃ (vh : Llholed) (v : List Value) (tf : FunctionType) (h : Hostfuncidx)
      (τs1 τs2 : List ValueType),
    ⌜w = .callHostV tf h v vh⌝ ∗
    ⌜tf = .tf τs1 τs2⌝ ∗
    ⌜(h, tf) ∈ hostList⌝ ∗
    ⌜llholedBasic vh⌝ ∗
    interpVal τs1 (.immV v) ∗
    □ (∀ v2 f, interpVal τs2 v2 -∗
        ↪[frame] f ∗ interpFrame τl i f -∗
        WP (llfill vh (ofVal v2))
          {{ vs, (interpVal τ2 vs ∨
                  ▷ interpCallHostBr'.2 vs lh τc ∨
                  interpReturnOption τro τl i vs ∨
                  ▷ interpCallHostBr'.1 vs lh τc τ2) ∗
                 ∃ f, ↪[frame] f ∗ interpFrame τl i f }})),
   fun w lh τc => iprop(
    ∃ j, ∃ (vh : ValidHoled j) (v : List Value) (p : Nat), ⌜w = .brV vh⌝ ∗ ⌜getBaseL vh = v⌝ ∗
      ⌜lhDepth (lhOfVh vh) = p⌝ ∗
      ∃ τs' vs k es lh' es' lh'' τs'',
        ⌜τc[j - p]? = some τs'⌝ ∗
        ⌜getLayer lh (lhDepth lh - (j - p + 1)) = some (vs, k, es, lh', es')⌝ ∗
        ⌜lhDepth lh'' = lhDepth lh - (j - p + 1)⌝ ∧ ⌜(lhMinus lh lh'').isSome = true⌝ ∗
        interpVal (τs'' ++ τs') (.immV v) ∗
        ∀ f, ↪[frame] f ∗ interpFrame τl i f -∗
          WP (ofVal (.immV (v.drop τs''.length)) ++ [.basic (.br (j - p))])
            CTX (lhDepth lh' + 1) ; (Lholed.rec_ vs k es lh' es')
            {{ vs, ((∃ τs, interpVal τs vs) ∨
                    ▷ interpCallHostBr'.2 vs lh'' (τc.drop (j - p + 1)) ∨
                    interpReturnOption τro τl i vs ∨
                    ▷ (∃ τs, interpCallHostBr'.1 vs lh'' (τc.drop (j - p + 1)) τs)) ∗
                   ∃ f, ↪[frame] f ∗ interpFrame τl i f }}))

omit [LogrelNaInvs GF] in
@[rocq_alias iriswasm.dist_later_prod]
theorem dist_later_prod (o o1 : HR) (o0 o2 : BR) (n : Nat) :
    DistLater n (o, o0) (o1, o2) → DistLater n o o1 ∧ DistLater n o0 o2 :=
  fun h => ⟨fun m hm => (h m hm).1, fun m hm => (h m hm).2⟩

@[rocq_alias iriswasm.interp_call_host_br_def_contractive]
instance interpCallHostBrDef_contractive (τl : List ValueType) (i : Instance)
    (τto : Option (List ValueType)) (hl : List (Hostfuncidx × FunctionType)) :
    OFE.Contractive (interpCallHostBrDef (GF := GF) τl i τto hl) where
  distLater_dist {n x y} H := by
    obtain ⟨H1, H2⟩ := dist_later_prod x.1 y.1 x.2 y.2 n H
    refine ⟨fun w lh τc τ2 => ?_, fun w lh τc => ?_⟩
    all_goals
      dsimp only [interpCallHostBrDef]
      logrel_ne
    all_goals
      first
      | exact OFE.Contractive.distLater_dist (f := BI.later) fun m hm => H1 m hm _ _ _ _
      | exact OFE.Contractive.distLater_dist (f := BI.later) fun m hm => H2 m hm _ _ _
      | exact OFE.Contractive.distLater_dist (f := BI.later) fun m hm =>
          BI.exists_ne fun _ => H1 m hm _ _ _ _

@[rocq_alias iriswasm.interp_call_host_br]
def interpCallHostBr (τl : List ValueType) (i : Instance) (τto : Option (List ValueType))
    (hostList : List (Hostfuncidx × FunctionType)) : HR × BR :=
  fixpoint (interpCallHostBrDef τl i τto hostList)

@[rocq_alias iriswasm.interp_call_host]
def interpCallHost (τl : List ValueType) (i : Instance) (τto : Option (List ValueType))
    (hostList : List (Hostfuncidx × FunctionType)) : HR :=
  (interpCallHostBr τl i τto hostList).1

@[rocq_alias iriswasm.interp_br]
def interpBr (τl : List ValueType) (i : Instance) (τto : Option (List ValueType))
    (hostList : List (Hostfuncidx × FunctionType)) : BR :=
  (interpCallHostBr τl i τto hostList).2

@[rocq_alias iriswasm.fixpoint_interp_br_eq]
theorem fixpoint_interp_br_eq (τc : List (List ValueType)) (τl : List ValueType) (i : Instance)
    (τto : Option (List ValueType)) (hostList : List (Hostfuncidx × FunctionType)) (v : Val)
    (lh : Lholed) :
    (interpBr τl i τto hostList v lh τc : IProp GF) =
      (interpCallHostBrDef τl i τto hostList (interpCallHostBr τl i τto hostList)).2 v lh τc :=
  congrArg (fun p : HR × BR => p.2 v lh τc)
    (fixpoint_unfold (interpCallHostBrDef τl i τto hostList).toContractiveHom)

@[rocq_alias iriswasm.fixpoint_interp_call_host_eq]
theorem fixpoint_interp_call_host_eq (lh : Lholed) (τc : List (List ValueType))
    (τl : List ValueType) (i : Instance) (τto : Option (List ValueType))
    (hostList : List (Hostfuncidx × FunctionType)) (v : Val) (t2 : List ValueType) :
    (interpCallHost τl i τto hostList v lh τc t2 : IProp GF) =
      (interpCallHostBrDef τl i τto hostList (interpCallHostBr τl i τto hostList)).1 v lh τc t2 :=
  congrArg (fun p : HR × BR => p.1 v lh τc t2)
    (fixpoint_unfold (interpCallHostBrDef τl i τto hostList).toContractiveHom)

@[rocq_alias iriswasm.interp_br_body]
def interpBrBody (τc : List (List ValueType)) (lh : Lholed) (j p : Nat) (w : List Value)
    (τl : List ValueType) (i : Instance) (τto : Option (List ValueType))
    (hl : List (Hostfuncidx × FunctionType)) : IProp GF :=
  iprop(∃ τs' vs k es lh' es' lh'' τs'',
    ⌜τc[j - p]? = some τs'⌝ ∗
    ⌜getLayer lh (lhDepth lh - (j - p + 1)) = some (vs, k, es, lh', es')⌝ ∗
    ⌜lhDepth lh'' = lhDepth lh - (j - p + 1)⌝ ∧ ⌜(lhMinus lh lh'').isSome = true⌝ ∗
    interpVal (τs'' ++ τs') (.immV w) ∗
    ∀ f, ↪[frame] f ∗ interpFrame τl i f -∗
      WP (ofVal (.immV (w.drop τs''.length)) ++ [.basic (.br (j - p))])
        CTX (lhDepth lh' + 1) ; (Lholed.rec_ vs k es lh' es')
        {{ vs, ((∃ τs, interpVal τs vs) ∨
                ▷ interpBr τl i τto hl vs lh'' (τc.drop (j - p + 1)) ∨
                interpReturnOption τto τl i vs ∨
                ▷ (∃ τs, interpCallHost τl i τto hl vs lh'' (τc.drop (j - p + 1)) τs)) ∗
               ∃ f, ↪[frame] f ∗ interpFrame τl i f }})

@[rocq_alias iriswasm.interp_expression]
def interpExpression (τc : List (List ValueType)) (τto : Option (List ValueType))
    (hostList : List (Hostfuncidx × FunctionType)) (τs : List ValueType) (lh : Lholed)
    (τl : List ValueType) (i : Instance) (es : Expr) : IProp GF :=
  iprop(WP es {{ vs, (interpVal τs vs ∨
                      interpBr τl i τto hostList vs lh τc ∨
                      interpReturnOption τto τl i vs ∨
                      interpCallHost τl i τto hostList vs lh τc τs) ∗
                     ∃ f, ↪[frame] f ∗ interpFrame τl i f }})

/-! ### Context relation -/

@[rocq_alias iriswasm.interp_ctx_continuation]
def interpCtxContinuation (τc : List (List ValueType)) (τto : Option (List ValueType))
    (hl : List (Hostfuncidx × FunctionType)) (lh : Lholed) (k : Nat) (τs τl : List ValueType)
    (i : Instance) : IProp GF :=
  iprop(∃ vs j es lh' es' lh'',
    ⌜getLayer lh (lhDepth lh - (k + 1)) = some (vs, j, es, lh', es')⌝ ∧
    ⌜lhDepth lh'' = lhDepth lh - (k + 1)⌝ ∧ ⌜(lhMinus lh lh'').isSome = true⌝ ∧
    (□ ∀ v f, interpVal τs v -∗ ↪[frame] f ∗ interpFrame τl i f -∗
      ∃ τs2, interpExpression (τc.drop (k + 1)) τto hl τs2 lh'' τl i
        (vs ++ (ofVal v ++ es) ++ es')))

@[rocq_alias iriswasm.interp_ctx_continuations]
def interpCtxContinuations (τc : List (List ValueType)) (τto : Option (List ValueType))
    (hl : List (Hostfuncidx × FunctionType)) (τl : List ValueType) (i : Instance) (lh : Lholed) :
    IProp GF :=
  iprop([∗list] k ↦ τs ∈ τc, interpCtxContinuation τc τto hl lh k τs τl i)

@[rocq_alias iriswasm.interp_ctx]
def interpCtx (τc : List (List ValueType)) (τto : Option (List ValueType))
    (hl : List (Hostfuncidx × FunctionType)) (τl : List ValueType) (i : Instance) (lh : Lholed) :
    IProp GF :=
  iprop(⌜BaseIsEmpty lh⌝ ∗
    ⌜lengthLholeds τc.reverse lh⌝ ∗
    ⌜LholedValid lh⌝ ∗
    interpCtxContinuations τc τto hl τl i lh)

@[rocq_alias iriswasm.interp_ctx_continuations_persistent]
instance interpCtxContinuations_persistent (τc : List (List ValueType))
    (τto : Option (List ValueType)) (hl : List (Hostfuncidx × FunctionType))
    (τl : List ValueType) (i : Instance) (lh : Lholed) :
    Persistent (interpCtxContinuations (GF := GF) τc τto hl τl i lh) := by
  unfold interpCtxContinuations interpCtxContinuation; infer_instance

@[rocq_alias iriswasm.interp_ctx_persistent]
instance interpCtx_persistent (τc : List (List ValueType)) (τto : Option (List ValueType))
    (hl : List (Hostfuncidx × FunctionType)) (τl : List ValueType) (i : Instance) (lh : Lholed) :
    Persistent (interpCtx (GF := GF) τc τto hl τl i lh) := by
  unfold interpCtx; infer_instance

@[rocq_alias iriswasm.semantic_typing]
def semanticTyping (τctx : TContext) (es : Expr) : FunctionType → IProp GF
  | .tf τ1 τ2 => iprop(∀ i lh hl, interpInstance τctx hl i -∗
      interpCtx τctx.label τctx.return_ hl τctx.local_ i lh -∗
      ∀ f vs, ↪[frame] f ∗ interpFrame τctx.local_ i f -∗
        interpVal τ1 vs -∗
        interpExpression τctx.label τctx.return_ hl τ2 lh τctx.local_ i (ofVal vs ++ es))

/-! ### Relations for closed contexts -/

@[rocq_alias iriswasm.interp_expression_closure_stuck_host]
def interpExpressionClosureStuckHost (hl : List (Hostfuncidx × FunctionType))
    (τs : List ValueType) (f : Frame) (es : Expr) : IProp GF :=
  iprop(WP es {{ vs, ((interpVal τs vs ∨ interpCallHostCls hl τs vs) ∗
    NonAtomicInvariant.own logrelNais ⊤) ∗ ↪[frame] f }})

@[rocq_alias iriswasm.semantic_typing_local_stuck_host]
def semanticTypingLocalStuckHost (hl : List (Hostfuncidx × FunctionType)) (τctx : TContext)
    (es : List BasicInstruction) (ts : List ValueType) (tf : FunctionType) : IProp GF :=
  iprop(⌜τctx.label = [] ∧ τctx.return_ = none⌝ ∧
    match tf with
    | .tf τ1 τ2 => ∀ i, interpInstance τctx hl i -∗
        ∀ f vs, ↪[frame] f -∗ NonAtomicInvariant.own logrelNais ⊤ -∗
          interpVal (τ1 ++ ts) (.immV vs) -∗
          interpExpressionClosureStuckHost hl τ2 f
            [.local τ2.length ⟨vs, i⟩ [.label τ2.length [] (toEList es)]])

@[rocq_alias iriswasm.interp_expression_closure_no_host]
def interpExpressionClosureNoHost (τs : List ValueType) (f : Frame) (es : Expr) : IProp GF :=
  iprop(WP es {{ vs, (interpVal τs vs ∗ NonAtomicInvariant.own logrelNais ⊤) ∗ ↪[frame] f }})

@[rocq_alias iriswasm.semantic_typing_local_no_host]
def semanticTypingLocalNoHost (τctx : TContext) (es : List BasicInstruction)
    (ts : List ValueType) (tf : FunctionType) : IProp GF :=
  iprop(⌜τctx.label = [] ∧ τctx.return_ = none⌝ ∧
    match tf with
    | .tf τ1 τ2 => ∀ i, interpInstance τctx [] i -∗
        ∀ f vs, ↪[frame] f -∗ NonAtomicInvariant.own logrelNais ⊤ -∗
          interpVal (τ1 ++ ts) (.immV vs) -∗
          interpExpressionClosureNoHost τ2 f
            [.local τ2.length ⟨vs, i⟩ [.label τ2.length [] (toEList es)]])

/-! ### Host integration -/

/-- Coq `host_program_logic`: an abstract host language whose WP can bind Wasm expressions. -/
@[rocq_alias iriswasm.host_program_logic]
class HostProgramLogic (GF : BundledGFunctors) [WasmG hlc GF] where
  hostFunction : Type
  result : Type
  /-- host context -/
  hostCtx : Type
  fillHost : hostCtx → Expr → hostFunction
  /-- translation of host results to Wasm values -/
  valOfHostVal : result → Val
  /-- the host WP -/
  wpHost (s : Stuckness) : CoPset → hostFunction → (result → IProp GF) → IProp GF
  /-- host bind lemma -/
  wpHostBind : ∀ hctx es (Φ : result → IProp GF),
    ⊢ WP es {{ v, wpHost .NotStuck ⊤ (fillHost hctx (ofVal v)) Φ }} -∗
      wpHost .NotStuck ⊤ (fillHost hctx es) Φ
  /-- host wand (stated, as upstream, for the Wasm WP) -/
  wpHostWand : ∀ (es : Expr) (Φ Ψ : Val → IProp GF),
    ⊢ WP es {{ Φ }} -∗ (∀ r, Φ r -∗ Ψ r) -∗ WP es {{ Ψ }}
  /-- host fupd intro -/
  fupdWpHost : ∀ e (Φ : result → IProp GF),
    ⊢ (|={⊤}=> wpHost .NotStuck ⊤ e Φ) -∗ wpHost .NotStuck ⊤ e Φ
  wpFupdHost : ∀ e (Φ : result → IProp GF),
    ⊢ wpHost .NotStuck ⊤ e (fun v => iprop(|={⊤}=> Φ v)) -∗ wpHost .NotStuck ⊤ e Φ

/-- `WPh h {{ Φ }}` / `WPh h {{ r, Q }}`: the host WP at `NotStuck` and mask `⊤`. -/
syntax "WPh " term:max ppSpace wpPostcond : term
macro_rules
  | `(WPh $h $post:wpPostcond) => do
    let (Φ, _) ← Iris.parseWpPostcond post
    `(HostProgramLogic.wpHost Stuckness.NotStuck ⊤ $h $Φ)

section logrelHost
variable [HostProgramLogic (hlc := hlc) GF]
open HostProgramLogic

@[rocq_alias iriswasm.interp_expression_closure]
def interpExpressionClosure (hctx : hostCtx hlc GF) (τs : List ValueType) (f : Frame) (es : Expr) :
    IProp GF :=
  iprop(WPh (fillHost hctx es) {{ vs, (interpVal τs (valOfHostVal vs) ∗
    NonAtomicInvariant.own logrelNais ⊤) ∗ ↪[frame] f }})

@[rocq_alias iriswasm.interp_closure_host]
def interpClosureHost (t2 : List ValueType) (hctx : hostCtx hlc GF) (tf1s tf2s : List ValueType)
    (h : Hostfuncidx) : IProp GF :=
  iprop(□ ∀ vcs f llh, interpVal tf1s (.immV vcs) -∗
    NonAtomicInvariant.own logrelNais ⊤ -∗
    ↪[frame] f -∗
    ▷ (∀ v2, interpVal tf2s v2 -∗ NonAtomicInvariant.own logrelNais ⊤ -∗ ↪[frame] f -∗
        WPh (fillHost hctx (llfill llh (ofVal v2))) {{ r, (interpVal t2 (valOfHostVal r) ∗
          NonAtomicInvariant.own logrelNais ⊤) ∗ ↪[frame] f }}) -∗
    WPh (fillHost hctx (llfill llh [.callHost (.tf tf1s tf2s) h vcs]))
      {{ r, (interpVal t2 (valOfHostVal r) ∗ NonAtomicInvariant.own logrelNais ⊤) ∗
        ↪[frame] f }})

@[rocq_alias iriswasm.interp_host_calls]
def interpHostCalls (t2 : List ValueType) (hctx : hostCtx hlc GF)
    (hl : List (Hostfuncidx × FunctionType)) : IProp GF :=
  iprop([∗list] ht ∈ hl, match ht with
    | (h, .tf tf1s tf2s) => interpClosureHost t2 hctx tf1s tf2s h)

@[rocq_alias iriswasm.interp_host_calls_persistent]
instance interpHostCalls_persistent (t2 : List ValueType) (hctx : hostCtx hlc GF)
    (hl : List (Hostfuncidx × FunctionType)) : Persistent (interpHostCalls t2 hctx hl) := by
  have (ht : Hostfuncidx × FunctionType) : Persistent (match ht with
      | (h, .tf tf1s tf2s) => interpClosureHost (GF := GF) t2 hctx tf1s tf2s h) := by
    rcases ht with ⟨_, ⟨_, _⟩⟩; dsimp only [interpClosureHost]; infer_instance
  unfold interpHostCalls; infer_instance

@[rocq_alias iriswasm.interp_host_return]
def interpHostReturn (hctx : hostCtx hlc GF) (τ2 : List ValueType) : IProp GF :=
  iprop(□ ∀ v f, interpVal τ2 v -∗
    NonAtomicInvariant.own logrelNais ⊤ -∗
    ↪[frame] f -∗
    WPh (fillHost hctx (ofVal v)) {{ r, (interpVal τ2 (valOfHostVal r) ∗
      NonAtomicInvariant.own logrelNais ⊤) ∗ ↪[frame] f }})

@[rocq_alias iriswasm.semantic_typing_local]
def semanticTypingLocal (τctx : TContext) (hl : List (Hostfuncidx × FunctionType))
    (es : List BasicInstruction) (ts : List ValueType) (tf : FunctionType) (hctx : hostCtx hlc GF) :
    IProp GF :=
  iprop(⌜τctx.label = [] ∧ τctx.return_ = none⌝ ∧
    match tf with
    | .tf τ1 τ2 => ∀ i, interpInstance τctx hl i -∗
        interpHostCalls τ2 hctx hl -∗
        interpHostReturn hctx τ2 -∗
        ∀ f vs, ↪[frame] f -∗ NonAtomicInvariant.own logrelNais ⊤ -∗
          interpVal (τ1 ++ ts) (.immV vs) -∗
          interpExpressionClosure hctx τ2 f
            [.local τ2.length ⟨vs, i⟩ [.label τ2.length [] (toEList es)]])

end logrelHost

end IrisWasm
