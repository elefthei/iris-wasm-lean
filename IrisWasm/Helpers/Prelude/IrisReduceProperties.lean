/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Helpers.Prelude.IrisWasmLangProperties
import IrisWasm.Helpers.Prelude.IrisLfilledProperties

/-! Port of `theories/iris/helpers/prelude/iris_reduce_properties.v`. -/

namespace IrisWasm

open Wasm Iris Iris.ProgramLogic

/-! ## Infrastructure for the `no_reduce` tactic (not in Coq) -/

/-- `ForallPrefixesNE P l`: `P` holds for every nonempty prefix of `l`. -/
def ForallPrefixesNE {α : Type} (P : List α → Prop) : List α → Prop
  | [] => True
  | a :: l => P [a] ∧ ForallPrefixesNE (fun x => P (a :: x)) l

/-- `ForallInfixesNE P l`: `P` holds for every nonempty contiguous sublist of `l`. -/
def ForallInfixesNE {α : Type} (P : List α → Prop) : List α → Prop
  | [] => True
  | a :: l => ForallPrefixesNE P (a :: l) ∧ ForallInfixesNE P l

theorem ForallPrefixesNE.app {α : Type} {P : List α → Prop} :
    ∀ {l : List α}, ForallPrefixesNE P l → ∀ {es aft : List α}, l = es ++ aft → es ≠ [] → P es
  | [], _, es, aft, h, hne => by
    cases es with
    | nil => exact absurd rfl hne
    | cons => simp at h
  | a :: l, ⟨h1, h2⟩, es, aft, h, hne => by
    cases es with
    | nil => exact absurd rfl hne
    | cons b es =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      cases es with
      | nil => exact h1
      | cons c es =>
        exact ForallPrefixesNE.app (P := fun x => P (a :: x)) h2 rfl (List.cons_ne_nil _ _)

theorem ForallInfixesNE.app {α : Type} {P : List α → Prop} :
    ∀ {l : List α}, ForallInfixesNE P l → ∀ {bef es aft : List α}, l = bef ++ (es ++ aft) →
      es ≠ [] → P es
  | [], _, bef, es, aft, h, hne => by
    cases es with
    | nil => exact absurd rfl hne
    | cons => cases bef <;> simp at h
  | a :: l, ⟨h1, h2⟩, bef, es, aft, h, hne => by
    cases bef with
    | nil => exact h1.app h hne
    | cons b bef =>
      simp only [List.cons_append, List.cons.injEq] at h
      exact h2.app h.2 hne

theorem no_reduce_gen {s : StoreRecord} {f : Frame} {L : List AdministrativeInstruction}
    {s' : StoreRecord} {f' : Frame} {es' : List AdministrativeInstruction}
    (h : Reduce s f L s' f' es')
    (k : ∀ s f es s' f' es', Reduce s f es s' f' es' → es = L → False) : False :=
  k _ _ _ _ _ _ h rfl

theorem no_reduce_snoc {vs L : List AdministrativeInstruction} {x : AdministrativeInstruction}
    (h : vs ++ [x] = L) (hx : x ∉ L) : False := by
  subst h; simp at hx

theorem lfilled_zero_singleton_mem {lh : Lholed} {x : AdministrativeInstruction}
    {L : List AdministrativeInstruction} (h : lfilled 0 lh [x] L = true) : x ∈ L := by
  obtain ⟨_, _, _, _, rfl⟩ := lfilled_zero_inv h
  simp

theorem lfilled_succ_label_mem {k : Nat} {lh : Lholed} {es L : List AdministrativeInstruction}
    (h : lfilled (k + 1) lh es L = true) :
    ∃ n es' l, AdministrativeInstruction.label n es' l ∈ L := by
  cases lh with
  | base => simp [lfilled, lfill] at h
  | rec_ vs n es' lh' es'' =>
    obtain ⟨_, l3, _, rfl⟩ := lfilled_succ_rec_inv h
    exact ⟨n, es', l3, by simp⟩

theorem no_reduce_label {s : StoreRecord} {f : Frame} {es0 : List AdministrativeInstruction}
    {s' : StoreRecord} {f' : Frame} {es0' : List AdministrativeInstruction} {k : Nat} {lh : Lholed}
    {L : List AdministrativeInstruction}
    (hred : Reduce s f es0 s' f' es0') (hfill : lfilled k lh es0 L = true)
    (ih : es0 = L → False) (hlab : ∀ n es LI, AdministrativeInstruction.label n es LI ∉ L)
    (hk : ForallInfixesNE (fun x => Reduce s f x s' f' es0' → x ≠ L → False) L) : False := by
  cases k with
  | zero =>
    obtain ⟨vs, es', rfl, _, hL⟩ := lfilled_zero_inv hfill
    by_cases he : es0 = L
    · exact ih he
    · exact hk.app (P := fun x => Reduce s f x s' f' es0' → x ≠ L → False) hL
        (reduce_not_nil hred) hred he
  | succ k =>
    cases lh with
    | base => simp [lfilled, lfill] at hfill
    | rec_ vs n es' lh' es'' =>
      obtain ⟨_, l3, _, hL⟩ := lfilled_succ_rec_inv hfill
      exact hlab n es' l3 (by rw [hL]; simp)

/-- Proves `False` from `H : Reduce s f L s' f' es'` where `L` is an explicit list of
instructions none of whose nonempty contiguous sublists is a redex (internal; see `no_reduce`). -/
syntax "no_reduce_core " ident : tactic

macro_rules
  | `(tactic| no_reduce_core $H) => `(tactic|
      (refine IrisWasm.no_reduce_gen $H ?_
       intro _ _ _ _ _ _ H' hL
       revert hL
       induction H' with
       | simple hs =>
         intro hL
         cases hs with
         | trap lh hne hfill =>
           subst hL
           first
             | exact hne rfl
             | exact absurd (IrisWasm.lfilled_zero_singleton_mem hfill) (by simp)
         | block => exact IrisWasm.no_reduce_snoc hL (by simp)
         | loop => exact IrisWasm.no_reduce_snoc hL (by simp)
         | _ => first | (cases hL; done) | (simp at hL; done)
       | invokeNative => intro hL; exact IrisWasm.no_reduce_snoc hL (by simp)
       | invokeHost => intro hL; exact IrisWasm.no_reduce_snoc hL (by simp)
       | label _ _ _ _ hsub hfill _ ih =>
         intro hL
         subst hL
         refine IrisWasm.no_reduce_label hsub hfill ih (by simp) ?_
         simp only [IrisWasm.ForallInfixesNE, IrisWasm.ForallPrefixesNE]
         repeat' constructor
         all_goals
           intro H'' hne
           first
             | exact absurd rfl hne
             | no_reduce_core H''
       | _ => intro hL; first | (cases hL; done) | (simp at hL; done)))

/-- Port of Ltac `no_reduce Heqes Hred`: from `Heqes : [explicit list] = es` and
`Hred : Reduce s f es s' f' es'`, proves the goal by deriving `False`, provided no nonempty
contiguous sublist of the explicit list reduces (and the list contains no `label`). -/
syntax "no_reduce " ident ppSpace ident : tactic

macro_rules
  | `(tactic| no_reduce $Heqes $Hred) => `(tactic|
      (exfalso
       first | subst $Heqes:ident | rw [← $Heqes:ident] at $Hred:ident
       no_reduce_core $Hred))

/-! ## Lemmas -/

@[rocq_alias iriswasm.values_no_reduce]
theorem values_no_reduce {s : StoreRecord} {f : Frame} {vs : List AdministrativeInstruction}
    {s' : StoreRecord} {f' : Frame} {es' : List AdministrativeInstruction} :
    Reduce s f vs s' f' es' → constList vs = true → False := by
  intro H
  induction H with
  | simple hs =>
    intro hc
    cases hs with
    | trap lh _ hfill =>
      have := List.all_eq_true.mp hc _ (lfilled_zero_singleton_mem hfill)
      simp [isConst] at this
    | _ => simp_all [constList, isConst]
  | label _ _ _ _ _ hf _ ih => intro hc; exact ih (lfilled_const _ _ _ _ hf hc).2
  | _ => intro hc; simp_all [constList, isConst]

/-- Port of Ltac `values_no_reduce` (`eapply values_no_reduce => //=`): applies `values_no_reduce`,
closing the reduction premise by assumption and trying to compute the `constList` premise. -/
macro "values_no_reduce" : tactic => `(tactic|
  focus
    refine IrisWasm.values_no_reduce ?_ ?_
    all_goals try assumption
    all_goals try (simp [Wasm.constList, Wasm.isConst]; done))

@[rocq_alias iriswasm.empty_no_reduce]
theorem empty_no_reduce {s : StoreRecord} {f : Frame} {s' : StoreRecord} {f' : Frame}
    {es' : List AdministrativeInstruction} : Reduce s f [] s' f' es' → False := by
  intro Hred
  no_reduce_core Hred

/-- Port of Ltac `empty_list_no_reduce` (`exfalso; eapply empty_no_reduce => //=`). -/
macro "empty_list_no_reduce" : tactic => `(tactic|
  (exfalso; exact IrisWasm.empty_no_reduce (by assumption)))

@[rocq_alias iriswasm.test_no_reduce1]
theorem test_no_reduce1 {s : StoreRecord} {f : Frame} {v : Value} {s' : StoreRecord} {f' : Frame}
    {es' : List AdministrativeInstruction} :
    Reduce s f [.basic (.const v)] s' f' es' → False := by
  intro Hred
  no_reduce_core Hred

@[rocq_alias iriswasm.test_no_reduce_trap]
theorem test_no_reduce_trap {s : StoreRecord} {f : Frame} {s' : StoreRecord} {f' : Frame}
    {es' : List AdministrativeInstruction} : Reduce s f [.trap] s' f' es' → False := by
  intro Hred
  no_reduce_core Hred

@[rocq_alias iriswasm.test_no_reduce2]
theorem test_no_reduce2 {s : StoreRecord} {f : Frame} {v1 v2 : Value} {s' : StoreRecord}
    {f' : Frame} {es' : List AdministrativeInstruction} :
    Reduce s f [.basic (.const v1), .basic (.const v2)] s' f' es' → False := by
  intro Hred
  no_reduce_core Hred

@[rocq_alias iriswasm.test_no_reduce3]
theorem test_no_reduce3 {s : StoreRecord} {f : Frame} {v1 v2 v3 : Value} {s' : StoreRecord}
    {f' : Frame} {es' : List AdministrativeInstruction} :
    Reduce s f [.basic (.const v1), .basic (.const v2), .basic (.const v3)] s' f' es' → False := by
  intro Hred
  no_reduce_core Hred

@[rocq_alias iriswasm.reduce_load_false]
theorem reduce_load_false {s0 : StoreRecord} {f : Frame} {s' : StoreRecord} {f' : Frame}
    {es es' : List AdministrativeInstruction} {x0 : ValueType} {x1 : Option (PackedType × Sx)}
    {x2 : AlignmentExponent} {x3 : StaticOffset} :
    es = [.basic (.load x0 x1 x2 x3)] → Reduce s0 f es s' f' es' → False := by
  intro Heq Hred
  no_reduce Heq Hred

@[rocq_alias iriswasm.reduce_store_false]
theorem reduce_store_false {s0 : StoreRecord} {f : Frame} {s' : StoreRecord} {f' : Frame}
    {es es' : List AdministrativeInstruction} {x0 : ValueType} {x1 : Option PackedType}
    {x2 : AlignmentExponent} {x3 : StaticOffset} :
    es = [.basic (.store x0 x1 x2 x3)] → Reduce s0 f es s' f' es' → False := by
  intro Heq Hred
  no_reduce Heq Hred

@[rocq_alias iriswasm.reduce_store_false_2]
theorem reduce_store_false_2 {s0 : StoreRecord} {f : Frame} {s' : StoreRecord} {f' : Frame}
    {es es' : List AdministrativeInstruction} {x0 : ValueType} {x1 : Option PackedType}
    {x2 : AlignmentExponent} {x3 : StaticOffset} {v : Value} :
    es = [.basic (.const v), .basic (.store x0 x1 x2 x3)] → Reduce s0 f es s' f' es' → False := by
  intro Heq Hred
  no_reduce Heq Hred

@[rocq_alias iriswasm.reduce_val_false]
theorem reduce_val_false {s0 : StoreRecord} {f : Frame} {s' : StoreRecord} {f' : Frame}
    {es es' : List AdministrativeInstruction} :
    (∃ v, toVal es = some v) → Reduce s0 f es s' f' es' → False := by
  rintro ⟨v, hv⟩ H
  rw [val_head_stuck_reduce H] at hv
  cases hv

@[rocq_alias iriswasm.reduce_br_false]
theorem reduce_br_false {s : StoreRecord} {f : Frame} {vs0 : List AdministrativeInstruction}
    {j : Nat} {es es0 : List AdministrativeInstruction} {s' : StoreRecord} {f' : Frame}
    {es' : List AdministrativeInstruction} :
    constList vs0 = true → es = vs0 ++ [.basic (.br j)] ++ es0 → Reduce s f es s' f' es' →
      False := by
  intro hc heq H
  obtain ⟨vs, rfl⟩ := const_es_exists hc
  subst heq
  exact reduce_val_false ⟨_, to_val_br_eq vs j es0⟩ H

@[rocq_alias iriswasm.reduce_ret_false]
theorem reduce_ret_false {s : StoreRecord} {f : Frame} {vs0 : List AdministrativeInstruction}
    {es es0 : List AdministrativeInstruction} {s' : StoreRecord} {f' : Frame}
    {es' : List AdministrativeInstruction} :
    constList vs0 = true → es = vs0 ++ [.basic .return_] ++ es0 → Reduce s f es s' f' es' →
      False := by
  intro hc heq H
  obtain ⟨vs, rfl⟩ := const_es_exists hc
  subst heq
  exact reduce_val_false ⟨_, to_val_ret_eq vs es0⟩ H

/-- Port of Ltac `intruse_among_values vs Hin Hvs`: from `Hin : x ∈ vs` (with `x` not a constant)
and `Hvs : constList vs = true`, proves the goal. -/
syntax "intruse_among_values " term:max ppSpace ident ppSpace ident : tactic

macro_rules
  | `(tactic| intruse_among_values $_vs $Hin $Hvs) => `(tactic|
      (exfalso
       have Hf := List.all_eq_true.mp $Hvs _ $Hin
       simp [Wasm.isConst] at Hf))

#rocq_ignore iriswasm.not_enough_arguments
  "Ltac used only in this file; the four lemmas using it are proved directly"

theorem not_mem_const {vs : List AdministrativeInstruction} {x : AdministrativeInstruction}
    (hc : constList vs = true) (hm : x ∈ vs) (hx : isConst x = false) : False := by
  have := List.all_eq_true.mp hc _ hm
  simp_all

/-- A frame decomposition of `vs ++ [X]` (with `vs` constant) around a reducing `es0` must put the
last instruction `X` inside `es0`. -/
theorem snoc_frame {s : StoreRecord} {f : Frame} {s' : StoreRecord} {f' : Frame}
    {bef es0 aft vs es0' : List AdministrativeInstruction} {X : AdministrativeInstruction}
    (hc : constList vs = true) (h : bef ++ (es0 ++ aft) = vs ++ [X])
    (hred : Reduce s f es0 s' f' es0') :
    ∃ es1, es0 = es1 ++ [X] ∧ constList es1 = true ∧ es1.length ≤ vs.length := by
  rcases List.eq_nil_or_concat aft with rfl | ⟨L, b, rfl⟩
  · rcases List.eq_nil_or_concat es0 with rfl | ⟨L, b, rfl⟩
    · exact absurd rfl (reduce_not_nil hred)
    · simp only [List.concat_eq_append, List.append_nil, ← List.append_assoc] at h
      obtain ⟨rfl, h2⟩ := List.append_inj' h rfl
      simp only [List.cons.injEq, and_true] at h2
      subst h2
      simp only [constList, List.all_append, Bool.and_eq_true] at hc
      exact ⟨L, by simp, hc.2, by simp⟩
  · simp only [List.concat_eq_append, ← List.append_assoc] at h
    obtain ⟨rfl, -⟩ := List.append_inj' h rfl
    simp only [constList, List.all_append, Bool.and_eq_true] at hc
    exact (values_no_reduce hred hc.1.2).elim

@[rocq_alias iriswasm.block_not_enough_arguments_no_reduce]
theorem block_not_enough_arguments_no_reduce {s : StoreRecord} {f : Frame}
    {vs : List AdministrativeInstruction} {t1s t2s : List ValueType} {esb : List BasicInstruction}
    {s' : StoreRecord} {f' : Frame} {es' : List AdministrativeInstruction} :
    Reduce s f (vs ++ [.basic (.block (.tf t1s t2s) esb)]) s' f' es' → constList vs = true →
      vs.length < t1s.length → False := by
  intro H hc hlen
  generalize hL : vs ++ [AdministrativeInstruction.basic (.block (.tf t1s t2s) esb)] = es at H
  induction H generalizing vs with
  | simple hs =>
    cases hs with
    | block n hc' hn ht1 _ =>
      obtain ⟨rfl, h2⟩ := List.append_inj' hL rfl
      simp only [List.cons.injEq, AdministrativeInstruction.basic.injEq,
        BasicInstruction.block.injEq, FunctionType.tf.injEq, and_true] at h2
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
      omega
    | trap lh hne hfill =>
      subst hL
      have hm := lfilled_zero_singleton_mem hfill
      simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hm
      exact not_mem_const hc hm rfl
    | _ => have h := congrArg List.getLast? hL; simp at h
  | label es0 es0' k lh hsub hf hf' ih =>
    subst hL
    cases k with
    | succ k =>
      obtain ⟨_, _, _, hm⟩ := lfilled_succ_label_mem hf
      simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hm
      exact not_mem_const hc hm rfl
    | zero =>
      obtain ⟨bef, aft, rfl, _, h⟩ := lfilled_zero_inv hf
      obtain ⟨es1, rfl, hc1, hl1⟩ := snoc_frame hc h.symm hsub
      exact ih hc1 (by omega) rfl
  | _ => have h := congrArg List.getLast? hL; simp at h

@[rocq_alias iriswasm.loop_not_enough_arguments_no_reduce]
theorem loop_not_enough_arguments_no_reduce {s : StoreRecord} {f : Frame}
    {vs : List AdministrativeInstruction} {t1s t2s : List ValueType} {esb : List BasicInstruction}
    {s' : StoreRecord} {f' : Frame} {es' : List AdministrativeInstruction} :
    Reduce s f (vs ++ [.basic (.loop (.tf t1s t2s) esb)]) s' f' es' → constList vs = true →
      vs.length < t1s.length → False := by
  intro H hc hlen
  generalize hL : vs ++ [AdministrativeInstruction.basic (.loop (.tf t1s t2s) esb)] = es at H
  induction H generalizing vs with
  | simple hs =>
    cases hs with
    | loop m hc' hn ht1 _ =>
      obtain ⟨rfl, h2⟩ := List.append_inj' hL rfl
      simp only [List.cons.injEq, AdministrativeInstruction.basic.injEq,
        BasicInstruction.loop.injEq, FunctionType.tf.injEq, and_true] at h2
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
      omega
    | trap lh hne hfill =>
      subst hL
      have hm := lfilled_zero_singleton_mem hfill
      simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hm
      exact not_mem_const hc hm rfl
    | _ => have h := congrArg List.getLast? hL; simp at h
  | label es0 es0' k lh hsub hf hf' ih =>
    subst hL
    cases k with
    | succ k =>
      obtain ⟨_, _, _, hm⟩ := lfilled_succ_label_mem hf
      simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hm
      exact not_mem_const hc hm rfl
    | zero =>
      obtain ⟨bef, aft, rfl, _, h⟩ := lfilled_zero_inv hf
      obtain ⟨es1, rfl, hc1, hl1⟩ := snoc_frame hc h.symm hsub
      exact ih hc1 (by omega) rfl
  | _ => have h := congrArg List.getLast? hL; simp at h

@[rocq_alias iriswasm.v_to_e_length]
theorem v_to_e_length (vs : List Value) : (vToEList vs).length = vs.length := by
  simp [vToEList]

@[rocq_alias iriswasm.invoke_not_enough_arguments_no_reduce_native]
theorem invoke_not_enough_arguments_no_reduce_native {s : StoreRecord} {f : Frame}
    {vs : List AdministrativeInstruction} {a0 : Nat} {s' : StoreRecord} {f' : Frame}
    {es' : List AdministrativeInstruction} {i' : Instance} {t1s t2s ts : List ValueType}
    {es'' : List BasicInstruction} :
    s.funcs[a0]? = some (.funcNative i' (.tf t1s t2s) ts es'') →
    Reduce s f (vs ++ [.invoke a0]) s' f' es' → constList vs = true →
      vs.length < t1s.length → False := by
  intro Hs H hc hlen
  generalize hL : vs ++ [AdministrativeInstruction.invoke a0] = es at H
  induction H generalizing vs with
  | simple hs =>
    cases hs with
    | trap lh hne hfill =>
      subst hL
      have hm := lfilled_zero_singleton_mem hfill
      simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hm
      exact not_mem_const hc hm rfl
    | _ => have h := congrArg List.getLast? hL; simp at h
  | invokeNative cl t1s' ts' vcs n k zs i hcl hcleq hves hvcs hts ht1 =>
    obtain ⟨rfl, h2⟩ := List.append_inj' hL rfl
    simp only [List.cons.injEq, AdministrativeInstruction.invoke.injEq, and_true] at h2
    subst h2 hcleq hves
    rw [Hs] at hcl
    simp only [Option.some.injEq, FunctionClosure.funcNative.injEq, FunctionType.tf.injEq] at hcl
    obtain ⟨rfl, ⟨rfl, rfl⟩, rfl, rfl⟩ := hcl
    simp [v_to_e_length] at hlen
    omega
  | invokeHost cl m n hcl hcleq =>
    obtain ⟨rfl, h2⟩ := List.append_inj' hL rfl
    simp only [List.cons.injEq, AdministrativeInstruction.invoke.injEq, and_true] at h2
    subst h2 hcleq
    rw [Hs] at hcl
    simp at hcl
  | label es0 es0' k lh hsub hf hf' ih =>
    subst hL
    cases k with
    | succ k =>
      obtain ⟨_, _, _, hm⟩ := lfilled_succ_label_mem hf
      simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hm
      exact not_mem_const hc hm rfl
    | zero =>
      obtain ⟨bef, aft, rfl, _, h⟩ := lfilled_zero_inv hf
      obtain ⟨es1, rfl, hc1, hl1⟩ := snoc_frame hc h.symm hsub
      exact ih Hs hc1 (by omega) rfl
  | _ => have h := congrArg List.getLast? hL; simp at h

@[rocq_alias iriswasm.invoke_not_enough_arguments_no_reduce_host]
theorem invoke_not_enough_arguments_no_reduce_host {s : StoreRecord} {f : Frame}
    {vs : List AdministrativeInstruction} {a0 : Nat} {s' : StoreRecord} {f' : Frame}
    {es' : List AdministrativeInstruction} {t1s t2s : List ValueType} {h : Hostfuncidx} :
    s.funcs[a0]? = some (.funcHost (.tf t1s t2s) h) →
    Reduce s f (vs ++ [.invoke a0]) s' f' es' → constList vs = true →
      vs.length < t1s.length → False := by
  intro Hs H hc hlen
  generalize hL : vs ++ [AdministrativeInstruction.invoke a0] = es at H
  induction H generalizing vs with
  | simple hs =>
    cases hs with
    | trap lh hne hfill =>
      subst hL
      have hm := lfilled_zero_singleton_mem hfill
      simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hm
      exact not_mem_const hc hm rfl
    | _ => have h := congrArg List.getLast? hL; simp at h
  | invokeNative cl t1s' ts' vcs n k zs i hcl hcleq =>
    obtain ⟨rfl, h2⟩ := List.append_inj' hL rfl
    simp only [List.cons.injEq, AdministrativeInstruction.invoke.injEq, and_true] at h2
    subst h2 hcleq
    rw [Hs] at hcl
    simp at hcl
  | invokeHost cl m n hcl hcleq hves hvcs ht1 =>
    obtain ⟨rfl, h2⟩ := List.append_inj' hL rfl
    simp only [List.cons.injEq, AdministrativeInstruction.invoke.injEq, and_true] at h2
    subst h2 hcleq hves
    rw [Hs] at hcl
    simp only [Option.some.injEq, FunctionClosure.funcHost.injEq, FunctionType.tf.injEq] at hcl
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hcl
    simp [v_to_e_length] at hlen
    omega
  | label es0 es0' k lh hsub hf hf' ih =>
    subst hL
    cases k with
    | succ k =>
      obtain ⟨_, _, _, hm⟩ := lfilled_succ_label_mem hf
      simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hm
      exact not_mem_const hc hm rfl
    | zero =>
      obtain ⟨bef, aft, rfl, _, h⟩ := lfilled_zero_inv hf
      obtain ⟨es1, rfl, hc1, hl1⟩ := snoc_frame hc h.symm hsub
      exact ih Hs hc1 (by omega) rfl
  | _ => have h := congrArg List.getLast? hL; simp at h

@[rocq_alias iriswasm.prim_step_obs_efs_empty]
theorem prim_step_obs_efs_empty {es es' : Expr} {σ σ' : State} {obs : List Observation}
    {efs : List Expr} :
    primStep (es, σ) obs (es', σ', efs) → (obs, efs) = ([], []) := by
  obtain ⟨_, _, _⟩ := σ; obtain ⟨_, _, _⟩ := σ'
  rintro ⟨_, rfl, rfl⟩; rfl

@[rocq_alias iriswasm.append_reducible]
theorem append_reducible (es1 es2 : List AdministrativeInstruction) (σ : State) :
    toVal es1 = none → PrimStep.Reducible ((es1 : Expr), σ) →
      PrimStep.Reducible ((es1 ++ es2 : Expr), σ) := by
  intro _ ⟨obs, e', σ', efs, h⟩
  obtain ⟨s, v, i⟩ := σ; obtain ⟨s', v', i'⟩ := σ'
  obtain ⟨h, rfl, rfl⟩ := h
  exact ⟨[], e' ++ es2, (s', v', i'), [], r_elimr es2 h, rfl, rfl⟩

@[rocq_alias iriswasm.AI_trap_reducible]
theorem AI_trap_reducible (es2 : List AdministrativeInstruction) (σ : State) :
    es2 ≠ [] → PrimStep.Reducible (([.trap] ++ es2 : Expr), σ) := by
  intro hne
  obtain ⟨s, v, i⟩ := σ
  refine ⟨[], [.trap], (s, v, i), [], .simple (.trap (.base [] es2) ?_ ?_), rfl, rfl⟩
  · cases es2 with
    | nil => exact absurd rfl hne
    | cons => simp
  · simp [lfilled, lfill, constList]

@[rocq_alias iriswasm.AI_trap_reducible_2]
theorem AI_trap_reducible_2 (es1 : List AdministrativeInstruction) (σ : State) :
    es1 ≠ [] → constList es1 = true → PrimStep.Reducible ((es1 ++ [.trap] : Expr), σ) := by
  intro hne hc
  obtain ⟨s, v, i⟩ := σ
  refine ⟨[], [.trap], (s, v, i), [], .simple (.trap (.base es1 []) ?_ ?_), rfl, rfl⟩
  · cases es1 with
    | nil => exact absurd rfl hne
    | cons => simp
  · simp [lfilled, lfill, hc]

@[rocq_alias iriswasm.AI_trap_irreducible]
theorem AI_trap_irreducible {ws : StoreRecord} {f : Frame} {ws' : StoreRecord} {f' : Frame}
    {es' : List AdministrativeInstruction} : Reduce ws f [.trap] ws' f' es' → False := by
  exact test_no_reduce_trap

@[rocq_alias iriswasm.AI_trap_reduce_det]
theorem AI_trap_reduce_det {v : Value} {ws : StoreRecord} {f : Frame} {ws' : StoreRecord}
    {f' : Frame} {es' : List AdministrativeInstruction} :
    Reduce ws f [.basic (.const v), .trap] ws' f' es' → (ws', f', es') = (ws, f, [.trap]) := by
  intro H
  generalize hL : [AdministrativeInstruction.basic (.const v), .trap] = es at H
  induction H with
  | simple hs =>
    cases hs with
    | trap => rfl
    | block => exact (no_reduce_snoc hL.symm (by simp)).elim
    | loop => exact (no_reduce_snoc hL.symm (by simp)).elim
    | _ => first | (cases hL; done) | (simp at hL; done)
  | invokeNative => exact (no_reduce_snoc hL.symm (by simp)).elim
  | invokeHost => exact (no_reduce_snoc hL.symm (by simp)).elim
  | label es0 es0' k lh hsub hf hf' ih =>
    subst hL
    cases k with
    | succ k =>
      obtain ⟨_, _, _, hm⟩ := lfilled_succ_label_mem hf
      simp at hm
    | zero =>
      obtain ⟨bef, aft, rfl, hbef, h⟩ := lfilled_zero_inv hf
      have hne := reduce_not_nil hsub
      rcases bef with _ | ⟨x, _ | ⟨y, bef⟩⟩ <;> rcases es0 with _ | ⟨z, _ | ⟨w, es0⟩⟩ <;>
        simp at h hne
      · obtain ⟨rfl, rfl⟩ := h; exact (test_no_reduce1 hsub).elim
      · obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        obtain ⟨rfl, rfl, rfl⟩ : (_, _, _) = _ := ih rfl
        obtain ⟨_, rfl⟩ := lfilled_zero_base_inv hf'
        simp
      · obtain ⟨rfl, rfl, rfl⟩ := h; exact (AI_trap_irreducible hsub).elim
  | _ => first | (cases hL; done) | (simp at hL; done)

@[rocq_alias iriswasm.prepend_reducible]
theorem prepend_reducible (es1 es2 : List AdministrativeInstruction) (σ : State) :
    (constList es1 = true ∨ es1 = [.trap]) → PrimStep.Reducible ((es2 : Expr), σ) →
      PrimStep.Reducible ((es1 ++ es2 : Expr), σ) := by
  rintro (hc | rfl) ⟨obs, e', σ', efs, h⟩
  · obtain ⟨s, v, i⟩ := σ; obtain ⟨s', v', i'⟩ := σ'
    obtain ⟨h, rfl, rfl⟩ := h
    exact ⟨[], es1 ++ e', (s', v', i'), [], r_eliml hc h, rfl, rfl⟩
  · obtain ⟨s, v, i⟩ := σ; obtain ⟨s', v', i'⟩ := σ'
    exact AI_trap_reducible es2 _ (reduce_not_nil h.1)

@[rocq_alias iriswasm.first_non_value_reduce]
theorem first_non_value_reduce {s : StoreRecord} {f : Frame} {es : List AdministrativeInstruction}
    {s' : StoreRecord} {f' : Frame} {es' : List AdministrativeInstruction} :
    Reduce s f es s' f' es' →
      ∃ vs e es'', constList vs = true ∧ (toVal [e] = none ∨ e = .trap) ∧ es = vs ++ e :: es'' := by
  intro H
  exact first_non_value es (val_head_stuck_reduce H)

/-- If a non-constant `X` preceded by constants sits in `bef ++ es0 ++ aft` (with `bef` constant
and `es0` reducing), then `X` lies inside `es0`, preceded there by constants only. -/
private theorem split_const_frame {X : AdministrativeInstruction}
    {vs1 es2 bef es0 aft es0' : List AdministrativeInstruction}
    {s : StoreRecord} {f : Frame} {s' : StoreRecord} {f' : Frame}
    (hX : isConst X = false) (hc : constList vs1 = true) (hb : constList bef = true)
    (hL : vs1 ++ X :: es2 = bef ++ (es0 ++ aft)) (hsub : Reduce s f es0 s' f' es0') :
    ∃ x y, constList x = true ∧ vs1 = bef ++ x ∧ es0 = x ++ X :: y ∧ es2 = y ++ aft := by
  rcases List.append_eq_append_iff.mp hL with ⟨xs, hbef, h2⟩ | ⟨bs, hvs, h2⟩
  · cases xs with
    | cons a xs =>
      simp only [List.cons_append, List.cons.injEq] at h2
      obtain ⟨rfl, -⟩ := h2
      exact (not_mem_const (x := X) hb (by simp [hbef]) hX).elim
    | nil =>
      simp only [List.nil_append] at h2
      rcases List.cons_eq_append_iff.mp h2 with ⟨rfl, -⟩ | ⟨ds, rfl, rfl⟩
      · exact (reduce_not_nil hsub rfl).elim
      · exact ⟨[], ds, rfl, by simp [hbef], rfl, rfl⟩
  · subst hvs
    simp only [constList, List.all_append, Bool.and_eq_true] at hc
    rcases List.append_eq_append_iff.mp h2 with ⟨cs, rfl, -⟩ | ⟨ds, rfl, h3⟩
    · simp only [List.all_append, Bool.and_eq_true] at hc
      exact (values_no_reduce hsub hc.2.1).elim
    · rcases List.cons_eq_append_iff.mp h3 with ⟨rfl, -⟩ | ⟨ds', rfl, rfl⟩
      · exact (values_no_reduce hsub (by simpa [constList] using hc.2)).elim
      · exact ⟨bs, ds', hc.2, rfl, rfl, rfl⟩

/-- Core of `trap_reduce_length`, with the `lfilled` premise and conclusion unfolded. -/
private theorem trap_reduce_aux {s : StoreRecord} {f : Frame} {es : List AdministrativeInstruction}
    {s' : StoreRecord} {f' : Frame} {es' : List AdministrativeInstruction}
    (H : Reduce s f es s' f' es') :
    ∀ {vs1 es2 : List AdministrativeInstruction}, constList vs1 = true →
      vs1 ++ .trap :: es2 = es →
      ∃ n1 n2, (n1 + (es2.length - n2) < vs1.length + es2.length ∧ n1 ≤ vs1.length ∧
          n2 ≤ es2.length) ∧
        es' = vs1.take n1 ++ .trap :: es2.drop n2 ∧ (s, f) = (s', f') := by
  induction H with
  | simple hs =>
    intro vs1 es2 hc hL
    have hm : AdministrativeInstruction.trap ∈ _ :=
      hL ▸ List.mem_append_right vs1 List.mem_cons_self
    cases hs with
    | trap lh hne hfill =>
      obtain ⟨bef, aft, rfl, hb, rfl⟩ := lfilled_zero_inv hfill
      obtain ⟨rfl, -, rfl⟩ := first_values _ _ _ _ _ _ rfl rfl hc hb hL
      refine ⟨0, es2.length, ⟨?_, by omega, by omega⟩, by simp, rfl⟩
      cases vs1 <;> cases es2 <;> simp_all <;> omega
    | block _ hcv | loop _ hcv => simp at hm; exact (not_mem_const hcv hm rfl).elim
    | teeLocal hv => simp at hm; subst hm; simp [isConst] at hv
    | _ => simp at hm
  | label es0 es0' k lh hsub hf hf' ih =>
    intro vs1 es2 hc hL
    cases k with
    | succ k =>
      cases lh with
      | base => simp [lfilled, lfill] at hf
      | rec_ vs n es' lh' es'' =>
        obtain ⟨hcv, l3, _, rfl⟩ := lfilled_succ_rec_inv hf
        cases (first_values _ _ _ _ _ _ rfl rfl hc hcv hL).2.1
    | zero =>
      obtain ⟨bef, aft, rfl, hb, rfl⟩ := lfilled_zero_inv hf
      obtain ⟨_, rfl⟩ := lfilled_zero_base_inv hf'
      obtain ⟨x, y, hx, rfl, rfl, rfl⟩ := split_const_frame rfl hc hb hL hsub
      obtain ⟨n1, n2, ⟨h1, h2, h3⟩, rfl, hsf⟩ := ih hx rfl
      refine ⟨bef.length + n1, n2, ⟨by simp; omega, by simp; omega, by simp; omega⟩, ?_, hsf⟩
      rw [List.take_length_add_append, List.drop_append_of_le_length h3]
      simp
  | _ =>
    intro vs1 es2 hc hL
    have hm : AdministrativeInstruction.trap ∈ _ :=
      hL ▸ List.mem_append_right vs1 List.mem_cons_self
    first
      | (simp at hm; done)
      | (subst_vars; simp [vToEList] at hm)

@[rocq_alias iriswasm.trap_reduce_length]
theorem trap_reduce_length {s : StoreRecord} {f : Frame} {es : List AdministrativeInstruction}
    {s' : StoreRecord} {f' : Frame} {es' vs1 es2 : List AdministrativeInstruction} :
    lfilled 0 (.base vs1 es2) [.trap] es = true → Reduce s f es s' f' es' →
      ∃ n1 n2, (n1 + (es2.length - n2) < vs1.length + es2.length ∧ n1 ≤ vs1.length ∧
          n2 ≤ es2.length) ∧
        lfilled 0 (.base (vs1.take n1) (es2.drop n2)) [.trap] es' = true ∧ (s, f) = (s', f') := by
  intro hfill H
  obtain ⟨hc, rfl⟩ := lfilled_zero_base_inv hfill
  obtain ⟨n1, n2, hn, rfl, hsf⟩ := trap_reduce_aux H hc rfl
  exact ⟨n1, n2, hn, by simp [lfilled, lfill, const_list_take _ hc], hsf⟩

@[rocq_alias iriswasm.trap_reduce]
theorem trap_reduce {s : StoreRecord} {f : Frame} {es : List AdministrativeInstruction}
    {s' : StoreRecord} {f' : Frame} {es' : List AdministrativeInstruction} {lh : Lholed} :
    lfilled 0 lh [.trap] es = true → Reduce s f es s' f' es' →
      ∃ lh', lfilled 0 lh' [.trap] es' = true ∧ (s, f) = (s', f') := by
  intro hfill H
  obtain ⟨vs1, es2, rfl, -, -⟩ := lfilled_zero_inv hfill
  obtain ⟨_, _, _, h, h'⟩ := trap_reduce_length hfill H
  exact ⟨_, h, h'⟩

@[rocq_alias iriswasm.lfilled_reducible]
theorem lfilled_reducible {i : Nat} {lh : Lholed} {e LI : List AdministrativeInstruction}
    {σ : State} :
    lfilled i lh e LI = true → PrimStep.Reducible ((e : Expr), σ) →
      PrimStep.Reducible ((LI : Expr), σ) := by
  intro hfill ⟨obs, e', σ', efs, h⟩
  obtain ⟨LI', hLI'⟩ := lfilled_swap e' hfill
  obtain ⟨s, v, i⟩ := σ; obtain ⟨s', v', i'⟩ := σ'
  obtain ⟨h, rfl, rfl⟩ := h
  exact ⟨[], LI', (s', v', i'), [], .label _ _ _ _ h hfill hLI', rfl, rfl⟩

@[rocq_alias iriswasm.local_frame_reducible]
theorem local_frame_reducible (n : Nat) {e : List AdministrativeInstruction} {s : StoreRecord}
    {v : List Value} {i : Instance} (v' : List Value) (i' : Instance) :
    PrimStep.Reducible ((e : Expr), ((s, v, i) : State)) →
      PrimStep.Reducible (([.local n ⟨v, i⟩ e] : Expr), ((s, v', i') : State)) := by
  intro ⟨obs, e', σ', efs, h⟩
  obtain ⟨s'', v'', i''⟩ := σ'
  obtain ⟨h, rfl, rfl⟩ := h
  exact ⟨[], [.local n ⟨v'', i''⟩ e'], (s'', v', i'), [], .local h, rfl, rfl⟩

@[rocq_alias iriswasm.local_frame_lfilled_reducible]
theorem local_frame_lfilled_reducible {j : Nat} {lh : Lholed} {LI : List AdministrativeInstruction}
    (n : Nat) {e : List AdministrativeInstruction} {s : StoreRecord} {v : List Value}
    {i : Instance} (v' : List Value) (i' : Instance) :
    lfilled j lh e LI = true → PrimStep.Reducible ((e : Expr), ((s, v, i) : State)) →
      PrimStep.Reducible (([.local n ⟨v, i⟩ LI] : Expr), ((s, v', i') : State)) := by
  intro hfill hred
  exact local_frame_reducible n v' i' (lfilled_reducible hfill hred)

/-- Atomic case of `reduce_focus`: the redex is the whole list, split at its last instruction. -/
private theorem focus_of_last {s : StoreRecord} {f : Frame} {es : List AdministrativeInstruction}
    {s' : StoreRecord} {f' : Frame} {es' : List AdministrativeInstruction}
    (H : Reduce s f es s' f' es') (hne : es ≠ []) (hc : constList es.dropLast = true)
    (he : isConst (es.getLast hne) = false) :
    ∃ k lh vs e es'', constList vs = true ∧ isConst e = false ∧
      Reduce s f (vs ++ [e]) s' f' es'' ∧ lfilled k lh (vs ++ [e]) es = true ∧
      lfilled k lh es'' es' = true := by
  refine ⟨0, .base [] [], es.dropLast, es.getLast hne, es', hc, he, ?_, ?_, ?_⟩
  · rwa [List.dropLast_concat_getLast]
  · simp [lfilled, lfill, constList, List.dropLast_concat_getLast]
  · simp [lfilled, lfill, constList]

@[rocq_alias iriswasm.reduce_focus]
theorem reduce_focus {s : StoreRecord} {f : Frame} {es : List AdministrativeInstruction}
    {s' : StoreRecord} {f' : Frame} {es' : List AdministrativeInstruction} :
    Reduce s f es s' f' es' →
      (∃ k lh vs e es'', constList vs = true ∧ isConst e = false ∧
          Reduce s f (vs ++ [e]) s' f' es'' ∧ lfilled k lh (vs ++ [e]) es = true ∧
          lfilled k lh es'' es' = true) ∨
      (∃ k lh bef aft, constList bef = true ∧ bef ++ aft ≠ [] ∧
          lfilled k lh (bef ++ [.trap] ++ aft) es = true ∧ lfilled k lh [.trap] es' = true ∧
          (s, f) = (s', f')) := by
  intro H
  have H' := H
  revert H'
  induction H with
  | simple hs =>
    intro hred
    cases hs with
    | trap lh hne hfill =>
      obtain ⟨bef, aft, rfl, hb, rfl⟩ := lfilled_zero_inv hfill
      refine Or.inr ⟨0, .base [] [], bef, aft, hb, ?_, by simp [lfilled, lfill, constList],
        by simp [lfilled, lfill, constList], rfl⟩
      rintro h
      simp only [List.append_eq_nil_iff] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hne rfl
    | _ => exact Or.inl (focus_of_last hred (by simp) (by simp_all [constList, isConst])
        (by simp_all [isConst]))
  | label es0 es0' k lh hsub hf hf' ih =>
    intro _
    rcases ih hsub with ⟨k0, lh0, vs, e, es'', hc, he, hr, h1, h2⟩ |
        ⟨k0, lh0, bef, aft, hb, hne, h1, h2, hsf⟩
    · obtain ⟨lh', h3, h4⟩ := lfilled_trans2 _ _ _ _ _ _ _ _ _ _ h1 h2 hf hf'
      exact Or.inl ⟨_, _, vs, e, es'', hc, he, hr, h3, h4⟩
    · obtain ⟨lh', h3, h4⟩ := lfilled_trans2 _ _ _ _ _ _ _ _ _ _ h1 h2 hf hf'
      exact Or.inr ⟨_, _, bef, aft, hb, hne, h3, h4, hsf⟩
  | _ =>
    intro hred
    exact Or.inl (focus_of_last hred (by simp)
      (by simp_all [constList, isConst, vToEList]) (by simp_all [isConst]))

private theorem lfilled_zero_base_of {vs es es' LI : List AdministrativeInstruction}
    (hc : constList vs = true) (h : LI = vs ++ (es ++ es')) : lfilled 0 (.base vs es') es LI = true := by
  subst h; simp [lfilled, lfill, hc]

private theorem snoc_inj {a b : List AdministrativeInstruction} {x y : AdministrativeInstruction}
    (h : a ++ [x] = b ++ [y]) : a = b ∧ x = y := by
  simpa using List.append_inj' h rfl

/-- Core of `reduce_append`: a reduction of `es ++ [e]` with `es` not constant either leaves `e`
untouched or is a trap reduction. -/
private theorem reduce_snoc_aux {s : StoreRecord} {f : Frame} {L : List AdministrativeInstruction}
    {s' : StoreRecord} {f' : Frame} {es' : List AdministrativeInstruction}
    (H : Reduce s f L s' f' es') :
    ∀ {es : List AdministrativeInstruction} {e : AdministrativeInstruction}, es ++ [e] = L →
      constList es = false →
      (∃ T, es' = T ++ [e] ∧ Reduce s f es s' f' T) ∨
        (∃ lh lh', lfilled 0 lh [.trap] es' = true ∧ lfilled 0 lh' [.trap] es = true ∧
          (s, f) = (s', f')) := by
  induction H with
  | simple hs =>
    intro es e hL hnc
    cases hs with
    | trap lh hne hfill =>
      obtain ⟨bef, aft, rfl, hb, rfl⟩ := lfilled_zero_inv hfill
      rcases List.eq_nil_or_concat aft with rfl | ⟨A, x, rfl⟩
      · obtain ⟨rfl, -⟩ := snoc_inj (b := bef) (by simpa using hL)
        simp [hb] at hnc
      · obtain ⟨rfl, rfl⟩ := snoc_inj (b := bef ++ .trap :: A) (by simpa using hL)
        exact Or.inr ⟨.base [] [], .base bef A, by simp [lfilled, lfill, constList],
          lfilled_zero_base_of hb (by simp), rfl⟩
    | _ =>
      have h := congrArg List.dropLast hL
      simp at h
      subst h
      first | (simp_all; done) | simp_all [constList, isConst]
  | label es0 es0' k lh hsub hf hf' ih =>
    intro es e hL hnc
    cases k with
    | zero =>
      obtain ⟨bef, aft, rfl, hb, rfl⟩ := lfilled_zero_inv hf
      obtain ⟨_, rfl⟩ := lfilled_zero_base_inv hf'
      rcases List.eq_nil_or_concat aft with rfl | ⟨A, x, rfl⟩
      · rcases List.eq_nil_or_concat es0 with rfl | ⟨E, x, rfl⟩
        · exact (reduce_not_nil hsub rfl).elim
        obtain ⟨rfl, rfl⟩ := snoc_inj (b := bef ++ E) (by simpa using hL)
        have hE : constList E = false := by
          rw [show constList (bef ++ E) = (constList bef && constList E) by
            simp [constList]] at hnc
          simpa [hb] using hnc
        rcases ih (es := E) (e := e) (by simp) hE with ⟨T, rfl, hr⟩ | ⟨lh1, lh2, h1, h2, hsf⟩
        · exact Or.inl ⟨bef ++ T, by simp,
            .label _ _ 0 (.base bef []) hr (lfilled_zero_base_of hb (by simp))
              (lfilled_zero_base_of hb (by simp))⟩
        · obtain ⟨b1, a1, rfl, hb1, rfl⟩ := lfilled_zero_inv h1
          obtain ⟨b2, a2, rfl, hb2, rfl⟩ := lfilled_zero_inv h2
          refine Or.inr ⟨.base (bef ++ b1) a1, .base (bef ++ b2) a2, ?_, ?_, hsf⟩
          · exact lfilled_zero_base_of (by simp [constList, List.all_append] at *; simp_all)
              (by simp)
          · exact lfilled_zero_base_of (by simp [constList, List.all_append] at *; simp_all)
              (by simp)
      · obtain ⟨rfl, rfl⟩ := snoc_inj (b := bef ++ (es0 ++ A)) (by simpa using hL)
        exact Or.inl ⟨bef ++ (es0' ++ A), by simp,
          .label _ _ 0 (.base bef A) hsub (lfilled_zero_base_of hb rfl)
            (lfilled_zero_base_of hb rfl)⟩
    | succ k =>
      cases lh with
      | base => simp [lfilled, lfill] at hf
      | rec_ bef n es1 lh' aft =>
        obtain ⟨hcv, l, hl, hL'⟩ := lfilled_succ_rec_inv hf
        obtain ⟨-, l', hl', rfl⟩ := lfilled_succ_rec_inv hf'
        subst hL'
        rcases List.eq_nil_or_concat aft with rfl | ⟨A, x, rfl⟩
        · obtain ⟨rfl, -⟩ := snoc_inj (b := bef) (by simpa using hL)
          simp [hcv] at hnc
        · obtain ⟨rfl, rfl⟩ := snoc_inj (b := bef ++ .label n es1 l :: A) (by simpa using hL)
          exact Or.inl ⟨bef ++ .label n es1 l' :: A, by simp,
            .label _ _ (k + 1) (.rec_ bef n es1 lh' A) hsub (by simp [lfilled, lfill, hcv, hl])
              (by simp [lfilled, lfill, hcv, hl'])⟩
  | _ =>
    intro es e hL hnc
    have h := congrArg List.dropLast hL
    simp at h
    subst h
    first | (simp_all; done) | simp_all [constList, isConst, vToEList]

@[rocq_alias iriswasm.reduce_append]
theorem reduce_append :
    ∀ (e : AdministrativeInstruction) (es es' : Expr) (σ σ' : State) (efs : List Expr)
      (obs : List Observation),
      PrimStep.Reducible (es, σ) → primStep (es ++ [e], σ) obs (es', σ', efs) →
      (es' = es'.take (es'.length - 1) ++ [e] ∧
          primStep (es, σ) obs (es'.take (es'.length - 1), σ', efs)) ∨
        (∃ lh lh', lfilled 0 lh [.trap] es' = true ∧ lfilled 0 lh' [.trap] es = true ∧
          σ = σ') := by
  intro e es es' σ σ' efs obs ⟨_, _, ⟨s1, v1, i1⟩, _, hes⟩ hstep
  obtain ⟨s, v, i⟩ := σ; obtain ⟨s', v', i'⟩ := σ'
  obtain ⟨hstep, rfl, rfl⟩ := hstep
  have hnc : constList es = false := by
    cases h : constList es
    · rfl
    · exact (values_no_reduce hes.1 h).elim
  rcases reduce_snoc_aux hstep rfl hnc with ⟨T, rfl, hr⟩ | ⟨lh, lh', h1, h2, hsf⟩
  · left
    simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel, List.take_left']
    exact ⟨by simp, hr, rfl, rfl⟩
  · simp only [Prod.mk.injEq, Frame.mk.injEq] at hsf
    obtain ⟨rfl, rfl, rfl⟩ := hsf
    exact Or.inr ⟨lh, lh', h1, h2, rfl⟩

private theorem br_no_reduce_aux {s : StoreRecord} {f : Frame} {es : List AdministrativeInstruction}
    {s' : StoreRecord} {f' : Frame} {es' : List AdministrativeInstruction} {i : Nat}
    (H : Reduce s f es s' f' es') :
    ∀ {vs1 es2 : List AdministrativeInstruction}, constList vs1 = true →
      vs1 ++ .basic (.br i) :: es2 = es → False := by
  induction H with
  | simple hs =>
    intro vs1 es2 hc hL
    have hm : AdministrativeInstruction.basic (.br i) ∈ _ :=
      hL ▸ List.mem_append_right vs1 List.mem_cons_self
    cases hs with
    | trap lh hne hfill =>
      obtain ⟨bef, aft, rfl, hb, rfl⟩ := lfilled_zero_inv hfill
      cases (first_values _ _ _ _ _ _ rfl rfl hc hb hL).2.1
    | block _ hcv | loop _ hcv => simp at hm; exact not_mem_const hcv hm rfl
    | teeLocal hv => simp at hm; subst hm; simp [isConst] at hv
    | _ => simp at hm
  | label es0 es0' k lh hsub hf hf' ih =>
    intro vs1 es2 hc hL
    cases k with
    | succ k =>
      cases lh with
      | base => simp [lfilled, lfill] at hf
      | rec_ vs n es' lh' es'' =>
        obtain ⟨hcv, l3, _, rfl⟩ := lfilled_succ_rec_inv hf
        cases (first_values _ _ _ _ _ _ rfl rfl hc hcv hL).2.1
    | zero =>
      obtain ⟨bef, aft, rfl, hb, rfl⟩ := lfilled_zero_inv hf
      obtain ⟨x, y, hx, rfl, rfl, rfl⟩ := split_const_frame rfl hc hb hL hsub
      exact ih hx rfl
  | _ =>
    intro vs1 es2 hc hL
    have hm : AdministrativeInstruction.basic (.br i) ∈ _ :=
      hL ▸ List.mem_append_right vs1 List.mem_cons_self
    first
      | (simp at hm; done)
      | (subst_vars; simp [vToEList] at hm)

@[rocq_alias iriswasm.br_no_reduce]
theorem br_no_reduce {s : StoreRecord} {f : Frame} {lh : Lholed} {i : Nat}
    {es : List AdministrativeInstruction} {s' : StoreRecord} {f' : Frame}
    {es' : List AdministrativeInstruction} :
    lfilled 0 lh [.basic (.br i)] es = true → Reduce s f es s' f' es' → False := by
  intro hfill H
  obtain ⟨vs1, es2, rfl, hc, rfl⟩ := lfilled_zero_inv hfill
  exact br_no_reduce_aux H hc rfl

/-- Atomic case of `lfilled_first_non_value`: split the redex at its last instruction. -/
private theorem fnv_last {s : StoreRecord} {f : Frame} {es : List AdministrativeInstruction}
    {s' : StoreRecord} {f' : Frame} {es' : List AdministrativeInstruction} {k : Nat} {lh : Lholed}
    {les les' : List AdministrativeInstruction}
    (H : Reduce s f es s' f' es') (hne : es ≠ []) (hc : constList es.dropLast = true)
    (he : isConst (es.getLast hne) = false)
    (hlab : ∀ n es0 LI, es.getLast hne = .label n es0 LI → False)
    (h1 : lfilled k lh es les = true) (h2 : lfilled k lh es' les' = true) :
    ∃ vs e esf es'' k0 lh0,
      constList vs = true ∧
      (∀ n es LI, e = .label n es LI →
        (s, f) = (s', f') ∧
          (constList LI = true ∨ LI = [.trap] ∨
            ∃ k lh vs i, lfilled k lh (vs ++ [.basic (.br i)]) LI = true)) ∧
      isConst e = false ∧
      Reduce s f (vs ++ e :: esf) s' f' es'' ∧
      lfilled k0 lh0 (vs ++ e :: esf) les = true ∧
      lfilled k0 lh0 es'' les' = true := by
  have heq := List.dropLast_concat_getLast hne
  refine ⟨es.dropLast, es.getLast hne, [], es', k, lh, hc,
    fun n es0 LI h => (hlab n es0 LI h).elim, he, ?_, ?_, h2⟩
  · rwa [heq]
  · rwa [heq]

@[rocq_alias iriswasm.lfilled_first_non_value]
theorem lfilled_first_non_value {s : StoreRecord} {f : Frame} {es : List AdministrativeInstruction}
    {s' : StoreRecord} {f' : Frame} {es' : List AdministrativeInstruction} {k : Nat} {lh : Lholed}
    {les les' : List AdministrativeInstruction} :
    Reduce s f es s' f' es' → lfilled k lh es les = true → lfilled k lh es' les' = true →
      ∃ vs e esf es'' k0 lh0,
        constList vs = true ∧
        (∀ n es LI, e = .label n es LI →
          (s, f) = (s', f') ∧
            (constList LI = true ∨ LI = [.trap] ∨
              ∃ k lh vs i, lfilled k lh (vs ++ [.basic (.br i)]) LI = true)) ∧
        isConst e = false ∧
        Reduce s f (vs ++ e :: esf) s' f' es'' ∧
        lfilled k0 lh0 (vs ++ e :: esf) les = true ∧
        lfilled k0 lh0 es'' les' = true := by
  intro H
  have H' := H
  revert H'
  induction H generalizing k lh les les' with
  | simple hs =>
    intro hred h1 h2
    cases hs with
    | trap lh0 hne hfill =>
      obtain ⟨bef, aft, rfl, hb, rfl⟩ := lfilled_zero_inv hfill
      refine ⟨bef, .trap, aft, [.trap], k, lh, hb, ?_, rfl, hred, h1, h2⟩
      intro n es LI h; cases h
    | labelConst hcv =>
      refine ⟨[], _, [], _, k, lh, rfl, ?_, rfl, hred, h1, h2⟩
      intro n es LI h
      simp only [AdministrativeInstruction.label.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨rfl, .inl hcv⟩
    | labelTrap =>
      refine ⟨[], _, [], _, k, lh, rfl, ?_, rfl, hred, h1, h2⟩
      intro n es LI h
      simp only [AdministrativeInstruction.label.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨rfl, .inr (.inl rfl)⟩
    | br i lh0 hcv hlen hfill =>
      refine ⟨[], _, [], _, k, lh, rfl, ?_, rfl, hred, h1, h2⟩
      intro n es LI h
      simp only [AdministrativeInstruction.label.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨rfl, .inr (.inr ⟨i, lh0, _, i, hfill⟩)⟩
    | _ =>
      exact fnv_last hred (by simp) (by simp_all [constList, isConst]) (by simp_all [isConst])
        (by intro n es LI h; simp at h) h1 h2
  | label es0 es0' k1 lh1 hsub hf hf' ih =>
    intro _ h1 h2
    obtain ⟨lh'', h3, h4⟩ := lfilled_trans2 _ _ _ _ _ _ _ _ _ _ hf hf' h1 h2
    exact ih hsub h3 h4
  | _ =>
    intro hred h1 h2
    exact fnv_last hred (by simp) (by simp_all [constList, isConst, vToEList])
      (by simp_all [isConst]) (by intro n es LI h; simp at h) h1 h2

theorem br_lfilled_to_val {i : Nat} {lh : Lholed} {vs LI : List AdministrativeInstruction}
    (hc : constList vs = true) (h : lfilled i lh (vs ++ [.basic (.br i)]) LI = true) :
    toVal LI ≠ none := by
  obtain ⟨x, rfl⟩ := const_es_exists hc
  obtain ⟨lh', h'⟩ := lh_pull_const_r_app i lh x _ _ h
  obtain ⟨vh, -, rfl⟩ := lfilled_to_vfill (i := i) h' (Nat.le_refl _)
  rw [show vfill vh [.basic (.br i)] = ofVal (.brV vh) from rfl, to_of_val]
  simp

theorem ret_lfilled_to_val {i : Nat} {lh : Lholed} {vs LI : List AdministrativeInstruction}
    (hc : constList vs = true) (h : lfilled i lh (vs ++ [.basic .return_]) LI = true) :
    toVal LI ≠ none := by
  obtain ⟨x, rfl⟩ := const_es_exists hc
  obtain ⟨sh, rfl⟩ := lfilled_to_sfill _ _ _ _ h
  rw [← sfill_sh_pull_const_r,
    show sfill (shPullConstR sh x) [.basic .return_] = ofVal (.retV (shPullConstR sh x)) from rfl,
    to_of_val]
  simp

/-- Core of `reduce_det_label`/`reduce_focus_one`: a reduction of `l1 ++ label n es es1 :: l2`
(with `l1` constant and `es1` not a value) happens inside `es1`. -/
private theorem det_label_aux {ws : StoreRecord} {f : Frame} {L : List AdministrativeInstruction}
    {ws' : StoreRecord} {f' : Frame} {es2 : List AdministrativeInstruction} {n : Nat}
    {es es1 : List AdministrativeInstruction}
    (H : Reduce ws f L ws' f' es2) :
    ∀ {l1 l2 : List AdministrativeInstruction}, constList l1 = true →
      l1 ++ .label n es es1 :: l2 = L → toVal es1 = none →
      ∃ es2', es2 = l1 ++ .label n es es2' :: l2 ∧ Reduce ws f es1 ws' f' es2' := by
  induction H with
  | simple hs =>
    intro l1 l2 hc hL hv
    exfalso
    have hm : AdministrativeInstruction.label n es es1 ∈ _ :=
      hL ▸ List.mem_append_right l1 List.mem_cons_self
    cases hs with
    | labelConst hcv =>
      obtain ⟨rfl, he, rfl⟩ := first_values l1 _ l2 [] _ [] rfl rfl hc rfl hL
      simp only [AdministrativeInstruction.label.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      obtain ⟨_, hv'⟩ := const_list_to_val _ hcv
      simp_all
    | labelTrap =>
      obtain ⟨rfl, he, rfl⟩ := first_values l1 _ l2 [] _ [] rfl rfl hc rfl hL
      simp only [AdministrativeInstruction.label.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      have := to_of_val .trapV
      simp_all [ofVal]
    | br j lh0 hcv hlen hfill =>
      obtain ⟨rfl, he, rfl⟩ := first_values l1 _ l2 [] _ [] rfl rfl hc rfl hL
      simp only [AdministrativeInstruction.label.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      exact br_lfilled_to_val hcv hfill hv
    | trap lh0 hne hfill =>
      obtain ⟨bef, aft, rfl, hb, rfl⟩ := lfilled_zero_inv hfill
      cases (first_values _ _ _ _ _ _ rfl rfl hc hb hL).2.1
    | block _ hcv | loop _ hcv => simp at hm; exact not_mem_const hcv hm rfl
    | teeLocal hv' => simp at hm; subst hm; simp [isConst] at hv'
    | _ => simp at hm
  | label es0 es0' k lh hsub hf hf' ih =>
    intro l1 l2 hc hL hv
    cases k with
    | zero =>
      obtain ⟨bef, aft, rfl, hb, rfl⟩ := lfilled_zero_inv hf
      obtain ⟨_, rfl⟩ := lfilled_zero_base_inv hf'
      obtain ⟨x, y, hx, rfl, rfl, rfl⟩ := split_const_frame rfl hc hb hL hsub
      obtain ⟨es2', rfl, hr⟩ := ih hx rfl hv
      exact ⟨es2', by simp, hr⟩
    | succ k =>
      cases lh with
      | base => simp [lfilled, lfill] at hf
      | rec_ bef n1 es3 lh' aft =>
        obtain ⟨hcv, l, hl, rfl⟩ := lfilled_succ_rec_inv hf
        obtain ⟨-, l', hl', rfl⟩ := lfilled_succ_rec_inv hf'
        obtain ⟨rfl, he, rfl⟩ := first_values _ _ _ _ _ _ rfl rfl hc hcv hL
        simp only [AdministrativeInstruction.label.injEq] at he
        obtain ⟨rfl, rfl, rfl⟩ := he
        exact ⟨l', rfl, .label es0 es0' k lh' hsub (by simp [lfilled, hl])
          (by simp [lfilled, hl'])⟩
  | _ =>
    intro l1 l2 hc hL hv
    exfalso
    have hm : AdministrativeInstruction.label n es es1 ∈ _ :=
      hL ▸ List.mem_append_right l1 List.mem_cons_self
    first
      | (simp at hm; done)
      | (subst_vars; simp [vToEList] at hm)

/-- Core of `reduce_return_trap_label`. -/
private theorem return_trap_label_aux {s : StoreRecord} {f : Frame}
    {L : List AdministrativeInstruction} {s' : StoreRecord} {f' : Frame}
    {es' : List AdministrativeInstruction} {n : Nat} {es0 : List AdministrativeInstruction}
    (H : Reduce s f L s' f' es') :
    ∀ {vs es'' : List AdministrativeInstruction}, constList vs = true →
      vs ++ .label n es0 [.trap] :: es'' = L → ∃ lh', lfilled 0 lh' [.trap] es' = true := by
  have hz : lfilled 0 (.base [] []) [.trap] [.trap] = true := by
    simp [lfilled, lfill, constList]
  induction H with
  | simple hs =>
    intro vs es'' hc hL
    have hm : AdministrativeInstruction.label n es0 [.trap] ∈ _ :=
      hL ▸ List.mem_append_right vs List.mem_cons_self
    cases hs with
    | labelTrap => exact ⟨_, hz⟩
    | labelConst hcv =>
      obtain ⟨rfl, he, rfl⟩ := first_values vs _ es'' [] _ [] rfl rfl hc rfl hL
      simp only [AdministrativeInstruction.label.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      simp [constList, isConst] at hcv
    | br j lh0 hcv hlen hfill =>
      obtain ⟨rfl, he, rfl⟩ := first_values vs _ es'' [] _ [] rfl rfl hc rfl hL
      simp only [AdministrativeInstruction.label.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      exact (lfilled_trap_not_br _ _ _ hz _ _ _ _ hcv hfill).elim
    | trap lh0 hne hfill =>
      obtain ⟨bef, aft, rfl, hb, rfl⟩ := lfilled_zero_inv hfill
      cases (first_values _ _ _ _ _ _ rfl rfl hc hb hL).2.1
    | block _ hcv | loop _ hcv => simp at hm; exact (not_mem_const hcv hm rfl).elim
    | teeLocal hv' => simp at hm; subst hm; simp [isConst] at hv'
    | _ => simp at hm
  | label es1 es1' k lh hsub hf hf' ih =>
    intro vs es'' hc hL
    cases k with
    | zero =>
      obtain ⟨bef, aft, rfl, hb, rfl⟩ := lfilled_zero_inv hf
      obtain ⟨x, y, hx, rfl, rfl, rfl⟩ := split_const_frame rfl hc hb hL hsub
      obtain ⟨lh1, h1⟩ := ih hx rfl
      obtain ⟨lh2, h2⟩ := lfilled_trans h1 hf'
      exact ⟨lh2, h2⟩
    | succ k =>
      cases lh with
      | base => simp [lfilled, lfill] at hf
      | rec_ bef n1 es3 lh' aft =>
        obtain ⟨hcv, l, hl, rfl⟩ := lfilled_succ_rec_inv hf
        obtain ⟨-, he, -⟩ := first_values _ _ _ _ _ _ rfl rfl hc hcv hL
        simp only [AdministrativeInstruction.label.injEq] at he
        obtain ⟨-, -, rfl⟩ := he
        have hl' : lfilled k lh' es1 [.trap] = true := by simp [lfilled, hl]
        exfalso
        cases k with
        | succ k =>
          obtain ⟨_, _, _, hm⟩ := lfilled_succ_label_mem hl'
          simp at hm
        | zero =>
          obtain ⟨b, a, rfl, -, he⟩ := lfilled_zero_inv hl'
          have hne := reduce_not_nil hsub
          rcases b with _ | ⟨_, _⟩ <;> rcases es1 with _ | ⟨_, _⟩ <;> simp at he hne
          obtain ⟨rfl, rfl, rfl⟩ := he
          exact AI_trap_irreducible hsub
  | _ =>
    intro vs es'' hc hL
    exfalso
    have hm : AdministrativeInstruction.label n es0 [.trap] ∈ _ :=
      hL ▸ List.mem_append_right vs List.mem_cons_self
    first
      | (simp at hm; done)
      | (subst_vars; simp [vToEList] at hm)

@[rocq_alias iriswasm.reduce_return_trap_label]
theorem reduce_return_trap_label {es : List AdministrativeInstruction} {s' : StoreRecord}
    {f' : Frame} {vs : List AdministrativeInstruction} {n : Nat}
    {es'0 es'' es' : List AdministrativeInstruction} :
    Reduce s' f' es s' f' es' → constList vs = true →
      es = vs ++ [.label n es'0 [.trap]] ++ es'' → ∃ lh', lfilled 0 lh' [.trap] es' = true := by
  intro H hc heq
  exact return_trap_label_aux (n := n) (es0 := es'0) (es'' := es'') H hc (by simp [heq])

@[rocq_alias iriswasm.reduce_focus_one]
theorem reduce_focus_one {es1 : List AdministrativeInstruction} {s : StoreRecord} {f : Frame}
    {s' : StoreRecord} {f' : Frame} {vs : List AdministrativeInstruction} {n : Nat}
    {es'0 LI es'' es' : List AdministrativeInstruction} :
    Reduce s f es1 s' f' es' → es1 = vs ++ [.label n es'0 LI] ++ es'' → constList vs = true →
      toVal LI = none →
      (∀ i j lh vs0, constList vs0 = true → lfilled i lh (vs0 ++ [.basic (.br j)]) LI = true →
        False) →
      ∃ LI', Reduce s f LI s' f' LI' := by
  intro H heq hc hv _
  obtain ⟨es2', -, hr⟩ :=
    det_label_aux (n := n) (es := es'0) (l2 := es'') H hc (by simp [heq]) hv
  exact ⟨es2', hr⟩

/-- A list with a trap in an evaluation context is not constant. -/
private theorem lfilled_trap_not_const {i : Nat} {lh : Lholed} {L : List AdministrativeInstruction}
    (h : lfilled i lh [.trap] L = true) : constList L = false := by
  cases hc : constList L
  · rfl
  · cases i with
    | zero => exact (not_mem_const hc (lfilled_zero_singleton_mem h) rfl).elim
    | succ i =>
      obtain ⟨_, _, _, hm⟩ := lfilled_succ_label_mem h
      exact (not_mem_const hc hm rfl).elim

private theorem lfilled_succ_singleton {k : Nat} {lh : Lholed} {es : List AdministrativeInstruction}
    {n : Nat} {es0 L : List AdministrativeInstruction}
    (h : lfilled (k + 1) lh es [.label n es0 L] = true) : ∃ lh', lfilled k lh' es L = true := by
  cases lh with
  | base => simp [lfilled, lfill] at h
  | rec_ bef n' es' lh' aft =>
    obtain ⟨_, l, hl, he⟩ := lfilled_succ_rec_inv h
    rcases bef with _ | ⟨_, _⟩ <;> simp at he
    exact ⟨lh', by simp_all [lfilled]⟩

/-- Lift a reduction of a label body to a constant-prefixed list containing that label. -/
private theorem label_lift {s : StoreRecord} {f : Frame} {s' : StoreRecord} {f' : Frame}
    {bef aft es L L' : List AdministrativeInstruction} {n : Nat}
    (hb : constList bef = true) (H : Reduce s f L s' f' L') :
    Reduce s f (bef ++ .label n es L :: aft) s' f' (bef ++ .label n es L' :: aft) :=
  .label _ _ 1 (.rec_ bef n es (.base [] []) aft) H
    (by simp [lfilled, lfill, hb, show constList [] = true from rfl])
    (by simp [lfilled, lfill, hb, show constList [] = true from rfl])

/-- Core of `trap_reduce_nested`. -/
private theorem trap_nested_aux {s : StoreRecord} {f : Frame} {es : List AdministrativeInstruction}
    {s' : StoreRecord} {f' : Frame} {es' : List AdministrativeInstruction}
    (H : Reduce s f es s' f' es') :
    ∀ {i lh}, lfilled i lh [.trap] es = true →
      (∃ lh' j, lfilled j lh' [.trap] es' = true ∧ j ≤ i) ∧ (s, f) = (s', f') := by
  have hz : lfilled 0 (.base [] []) [.trap] [.trap] = true := by
    simp [lfilled, lfill, constList]
  induction H with
  | simple hs =>
    intro i lh h
    refine ⟨?_, rfl⟩
    cases hs with
    | trap | labelTrap | localTrap => exact ⟨_, 0, hz, Nat.zero_le _⟩
    | labelConst hcv =>
      cases i with
      | zero => have hm := lfilled_zero_singleton_mem h; simp at hm
      | succ k =>
        obtain ⟨_, h'⟩ := lfilled_succ_singleton h
        simp [lfilled_trap_not_const h'] at hcv
    | br j lh0 hcv hlen hfill =>
      cases i with
      | zero => have hm := lfilled_zero_singleton_mem h; simp at hm
      | succ k =>
        obtain ⟨_, h'⟩ := lfilled_succ_singleton h
        exact (lfilled_trap_not_br _ _ _ h' _ _ _ _ hcv hfill).elim
    | block _ hcv | loop _ hcv =>
      cases i with
      | zero =>
        have hm := lfilled_zero_singleton_mem h; simp at hm
        exact (not_mem_const hcv hm rfl).elim
      | succ k =>
        obtain ⟨_, _, _, hm⟩ := lfilled_succ_label_mem h; simp at hm
        exact (not_mem_const hcv hm rfl).elim
    | teeLocal hv =>
      cases i with
      | zero => have hm := lfilled_zero_singleton_mem h; simp at hm; subst hm; simp [isConst] at hv
      | succ k =>
        obtain ⟨_, _, _, hm⟩ := lfilled_succ_label_mem h; simp at hm; subst hm; simp [isConst] at hv
    | _ =>
      cases i with
      | zero => have hm := lfilled_zero_singleton_mem h; simp at hm
      | succ k => obtain ⟨_, _, _, hm⟩ := lfilled_succ_label_mem h; simp at hm
  | label es0 es0' k1 lh1 hsub hf hf' ih =>
    intro i lh h
    have hnc : constList es0 = false := by
      cases hc : constList es0
      · rfl
      · exact (values_no_reduce hsub hc).elim
    have hnt : es0 ≠ [.trap] := by rintro rfl; exact AI_trap_irreducible hsub
    obtain ⟨j, lh2, h2, hj⟩ := lfilled_singleton .trap k1 lh1 es0 _ i lh (reduce_not_nil hsub) hnc
      hnt rfl (by intro _ _ _ h; cases h) hf h
    obtain ⟨⟨lh3, j', h3, hj'⟩, hsf⟩ := ih h2
    obtain ⟨lh4, h4⟩ := lfilled_trans h3 hf'
    exact ⟨⟨lh4, j' + k1, h4, by omega⟩, hsf⟩
  | _ =>
    intro i lh h
    exfalso
    cases i with
    | zero =>
      have hm := lfilled_zero_singleton_mem h
      first | (simp at hm; done) | (subst_vars; simp [vToEList] at hm)
    | succ k =>
      obtain ⟨_, _, _, hm⟩ := lfilled_succ_label_mem h
      first | (simp at hm; done) | (subst_vars; simp [vToEList] at hm)

@[rocq_alias iriswasm.trap_reduce_state_eq]
theorem trap_reduce_state_eq {i : Nat} {lh : Lholed} {es : List AdministrativeInstruction}
    {s : StoreRecord} {f : Frame} {s' : StoreRecord} {f' : Frame}
    {es' : List AdministrativeInstruction} :
    Reduce s f es s' f' es' → lfilled i lh [.trap] es = true → (s, f) = (s', f') := by
  intro H h
  exact (trap_nested_aux H h).2

@[rocq_alias iriswasm.trap_reduce_lfilled]
theorem trap_reduce_lfilled {i : Nat} {lh : Lholed} {es : List AdministrativeInstruction}
    {s : StoreRecord} {f : Frame} {s' : StoreRecord} {f' : Frame}
    {es' : List AdministrativeInstruction} :
    Reduce s f es s' f' es' → lfilled i lh [.trap] es = true →
      ∃ lh' j, lfilled j lh' [.trap] es' = true ∧ j ≤ i := by
  intro H h
  exact (trap_nested_aux H h).1

@[rocq_alias iriswasm.trap_reduce_nested]
theorem trap_reduce_nested {s : StoreRecord} {f : Frame} {es : List AdministrativeInstruction}
    {s' : StoreRecord} {f' : Frame} {es' : List AdministrativeInstruction} {lh : Lholed} {i : Nat} :
    lfilled i lh [.trap] es = true → Reduce s f es s' f' es' →
      (∃ lh' j, lfilled j lh' [.trap] es' = true ∧ j ≤ i) ∧ (s, f) = (s', f') := by
  intro h H
  exact trap_nested_aux H h

@[rocq_alias iriswasm.trap_context_reduce]
theorem trap_context_reduce {locs : StoreRecord} {s : Frame} {LI : List AdministrativeInstruction}
    {lh : Lholed} {k : Nat} :
    lfilled (k + 1) lh [.trap] LI = true → ∃ e', Reduce locs s LI locs s e' := by
  intro hfill
  induction k generalizing LI lh with
  | zero =>
    cases lh with
    | base => simp [lfilled, lfill] at hfill
    | rec_ bef n es lh' aft =>
      obtain ⟨hb, l, hl, rfl⟩ := lfilled_succ_rec_inv hfill
      have hl' : lfilled 0 lh' [.trap] l = true := by simp [lfilled, hl]
      by_cases ht : l = [.trap]
      · subst ht
        exact ⟨bef ++ .trap :: aft, .label _ _ 0 (.base bef aft)
          (.simple (.labelTrap (n := n) (es := es)))
          (lfilled_zero_base_of hb (by simp)) (lfilled_zero_base_of hb (by simp))⟩
      · exact ⟨_, label_lift hb (.simple (.trap lh' ht hl'))⟩
  | succ k ih =>
    cases lh with
    | base => simp [lfilled, lfill] at hfill
    | rec_ bef n es lh' aft =>
      obtain ⟨hb, l, hl, rfl⟩ := lfilled_succ_rec_inv hfill
      obtain ⟨e', he'⟩ := ih (LI := l) (lh := lh') (by simp [lfilled, hl])
      exact ⟨_, label_lift hb he'⟩

@[rocq_alias iriswasm.to_val_trapV_lfilled_None]
theorem to_val_trapV_lfilled_None {es : List AdministrativeInstruction} {k : Nat} {lh : Lholed}
    {LI : List AdministrativeInstruction} :
    toVal es = some .trapV → lfilled (k + 1) lh es LI = true → toVal LI = none := by
  intro hv hfill
  obtain rfl := to_val_trap_is_singleton es hv
  obtain ⟨_, H⟩ := trap_context_reduce (locs := default) (s := default) hfill
  exact val_head_stuck_reduce H

@[rocq_alias iriswasm.lfilled_to_val_0]
theorem lfilled_to_val_0 {i : Nat} {lh : Lholed} {e es : List AdministrativeInstruction}
    {v : Val} :
    toVal e = some .trapV → lfilled i lh e es = true → toVal es = some v → i = 0 := by
  intro he hfill hes
  cases i with
  | zero => rfl
  | succ i => rw [to_val_trapV_lfilled_None he hfill] at hes; cases hes

@[rocq_alias iriswasm.reduce_det_local]
theorem reduce_det_local {ws : StoreRecord} {f : Frame} {ws' : StoreRecord} {f' : Frame}
    {es1 es2 : List AdministrativeInstruction} {n : Nat} {f0 : Frame} :
    toVal es1 = none → Reduce ws f [.local n f0 es1] ws' f' es2 →
      ∃ es2' f1, es2 = [.local n f1 es2'] ∧ f = f' ∧ Reduce ws f0 es1 ws' f1 es2' := by
  intro hv H
  generalize hL : [AdministrativeInstruction.local n f0 es1] = L at H
  induction H with
  | simple hs =>
    exfalso
    cases hs with
    | localConst hcv =>
      simp only [List.cons.injEq, AdministrativeInstruction.local.injEq, and_true] at hL
      obtain ⟨-, -, rfl⟩ := hL
      obtain ⟨_, hv'⟩ := const_list_to_val _ hcv
      simp_all
    | localTrap =>
      simp only [List.cons.injEq, AdministrativeInstruction.local.injEq, and_true] at hL
      obtain ⟨-, -, rfl⟩ := hL
      have := to_of_val .trapV
      simp_all [ofVal]
    | return_ i lh hcv hlen hfill =>
      simp only [List.cons.injEq, AdministrativeInstruction.local.injEq, and_true] at hL
      obtain ⟨-, -, rfl⟩ := hL
      exact ret_lfilled_to_val hcv hfill hv
    | trap lh hne hfill =>
      subst hL
      have hm := lfilled_zero_singleton_mem hfill
      simp at hm
    | _ => first | (cases hL; done) | (simp at hL; done) |
        (have h := congrArg List.getLast? hL; simp at h)
  | «local» hr =>
    simp only [List.cons.injEq, AdministrativeInstruction.local.injEq, and_true] at hL
    obtain ⟨rfl, rfl, rfl⟩ := hL
    exact ⟨_, _, rfl, rfl, hr⟩
  | label es0 es0' k lh hsub hf hf' ih =>
    subst hL
    cases k with
    | succ k =>
      obtain ⟨_, _, _, hm⟩ := lfilled_succ_label_mem hf
      simp at hm
    | zero =>
      obtain ⟨bef, aft, rfl, -, he⟩ := lfilled_zero_inv hf
      obtain ⟨-, rfl⟩ := lfilled_zero_base_inv hf'
      have hne := reduce_not_nil hsub
      rcases bef with _ | ⟨_, _⟩ <;> rcases es0 with _ | ⟨_, _⟩ <;> simp at he hne
      obtain ⟨rfl, rfl, rfl⟩ := he
      obtain ⟨es2', f1, rfl, rfl, hr⟩ := ih rfl
      exact ⟨es2', f1, rfl, rfl, hr⟩
  | _ => first | (cases hL; done) | (simp at hL; done) |
      (have h := congrArg List.getLast? hL; simp at h)

@[rocq_alias iriswasm.reduce_det_label]
theorem reduce_det_label {ws : StoreRecord} {f : Frame} {ws' : StoreRecord} {f' : Frame}
    {es1 : List AdministrativeInstruction} {n : Nat} {es es'' es2 : List AdministrativeInstruction} :
    Reduce ws f es'' ws' f' es2 →
      ∀ l1 l2, es'' = l1 ++ [.label n es es1] ++ l2 → constList l1 = true → toVal es1 = none →
        ∃ es2', es2 = l1 ++ [.label n es es2'] ++ l2 ∧ Reduce ws f es1 ws' f' es2' := by
  intro H l1 l2 heq hc hv
  obtain ⟨es2', rfl, hr⟩ := det_label_aux (n := n) (es := es) (l2 := l2) H hc (by simp [heq]) hv
  exact ⟨es2', by simp, hr⟩

@[rocq_alias iriswasm.reduce_det_label_nil]
theorem reduce_det_label_nil {ws : StoreRecord} {f : Frame} {ws' : StoreRecord} {f' : Frame}
    {es1 es2 : List AdministrativeInstruction} {n : Nat} {es : List AdministrativeInstruction} :
    toVal es1 = none → Reduce ws f [.label n es es1] ws' f' es2 →
      ∃ es2', es2 = [.label n es es2'] ∧ Reduce ws f es1 ws' f' es2' := by
  intro hv H
  obtain ⟨es2', h, hr⟩ := reduce_det_label H [] [] rfl rfl hv
  exact ⟨es2', by simpa using h, hr⟩

end IrisWasm
