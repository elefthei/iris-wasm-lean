/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import Wasm.Properties

/-! Port of `theories/type_preservation.v`: type preservation for Wasm reduction.
Arguments determined by a hypothesis are implicit (as Coq's `Set Implicit Arguments`).
Coq names also declared in another iris-wasm file (`b_e_elim`, `upd_label_overwrite`,
`nth_error_map`) live in `namespace Wasm.TypePreservation`. -/

namespace Wasm

open AdministrativeInstruction (basic)

@[rocq_alias iriswasm.t_be_value]
def TBeValue (bes : List BasicInstruction) : Prop := constList (toEList bes) = true

#rocq_ignore iriswasm.b_to_a_revert "Ltac used only in type_preservation.v"
#rocq_ignore iriswasm.invert_be_typing "Ltac used only in type_preservation.v"
#rocq_ignore iriswasm.type_preservation.auto_basic "Ltac used only in type_preservation.v"
#rocq_ignore iriswasm.basic_inversion' "Ltac used only in type_preservation.v"
#rocq_ignore iriswasm.et_dependent_ind "Ltac used only in type_preservation.v"
#rocq_ignore iriswasm.convert_et_to_bet "Ltac used only in type_preservation.v"
#rocq_ignore iriswasm.type_preservation.split_et_composition "Ltac used only in type_preservation.v"
#rocq_ignore iriswasm.type_preservation.invert_e_typing "Ltac used only in type_preservation.v"

namespace TypePreservation

@[rocq_alias iriswasm.type_preservation.b_e_elim]
theorem b_e_elim {bes : List BasicInstruction} {es : List AdministrativeInstruction}
    (h : toEList bes = es) : bes = toBList es ∧ EsIsBasic es :=
  Wasm.b_e_elim h

@[rocq_alias iriswasm.type_preservation.upd_label_overwrite]
theorem upd_label_overwrite (C : TContext) (l1 l2 : List (List ValueType)) :
    updLabel (updLabel C l1) l2 = updLabel C l2 := rfl

end TypePreservation

open TypePreservation (upd_label_overwrite)

/-! ### Inversion lemmas for basic instructions -/

@[rocq_alias iriswasm.BI_const_typing]
theorem BI_const_typing {C : TContext} {econst : Value} {t1s t2s : List ValueType}
    (h : BeTyping C [.const econst] (.tf t1s t2s)) : t2s = t1s ++ [typeof econst] := by
  generalize hes : [BasicInstruction.const econst] = es at h
  generalize htf : FunctionType.tf t1s t2s = tf at h
  induction h generalizing t1s t2s
  case const => cases hes; cases htf; rfl
  case composition h1 _ _ ih =>
    obtain ⟨rfl, rfl⟩ := extract_list1 hes.symm
    obtain rfl := empty_typing h1
    exact ih rfl htf
  case weakening ts _ _ _ ih =>
    cases htf; rw [ih hes rfl]; simp
  all_goals cases hes

@[rocq_alias iriswasm.BI_const2_typing]
theorem BI_const2_typing {C : TContext} {econst1 econst2 : Value} {t1s t2s : List ValueType}
    (h : BeTyping C [.const econst1, .const econst2] (.tf t1s t2s)) :
    t2s = t1s ++ [typeof econst1, typeof econst2] := by
  obtain ⟨ts, t1s', t2s', t3s, rfl, rfl, H3, H4⟩ := composition_typing_single (es1 := [_]) h
  rw [BI_const_typing H4, BI_const_typing H3]; simp

@[rocq_alias iriswasm.BI_const3_typing]
theorem BI_const3_typing {C : TContext} {econst1 econst2 econst3 : Value}
    {t1s t2s : List ValueType}
    (h : BeTyping C [.const econst1, .const econst2, .const econst3] (.tf t1s t2s)) :
    t2s = t1s ++ [typeof econst1, typeof econst2, typeof econst3] := by
  obtain ⟨ts, t1s', t2s', t3s, rfl, rfl, H3, H4⟩ := composition_typing_single (es1 := [_, _]) h
  rw [BI_const_typing H4, BI_const2_typing H3]; simp

@[rocq_alias iriswasm.Const_list_typing_empty]
theorem Const_list_typing_empty (C : TContext) (vs : List Value) :
    BeTyping C (toBList (vToEList vs)) (.tf [] (vsToVts vs)) := by
  induction vs with
  | nil => exact .empty
  | cons a vs ih =>
    exact bet_composition_front (t2s := [typeof a]) .const (bet_weakening_empty_1 [typeof a] ih)

@[rocq_alias iriswasm.Unop_typing]
theorem Unop_typing {C : TContext} {t : ValueType} {op : Unop} {t1s t2s : List ValueType}
    (h : BeTyping C [.unop t op] (.tf t1s t2s)) : t1s = t2s ∧ ∃ ts, t1s = ts ++ [t] := by
  generalize hes : [BasicInstruction.unop t op] = es at h
  generalize htf : FunctionType.tf t1s t2s = tf at h
  induction h generalizing t1s t2s
  case unop => cases hes; cases htf; exact ⟨rfl, [], rfl⟩
  case composition h1 _ _ ih =>
    obtain ⟨rfl, rfl⟩ := extract_list1 hes.symm
    obtain rfl := empty_typing h1
    exact ih rfl htf
  case weakening ts _ _ _ ih =>
    cases htf; obtain ⟨rfl, ts', rfl⟩ := ih hes rfl; exact ⟨rfl, ts ++ ts', by simp⟩
  all_goals cases hes

@[rocq_alias iriswasm.Binop_typing]
theorem Binop_typing {C : TContext} {t : ValueType} {op : Binop} {t1s t2s : List ValueType}
    (h : BeTyping C [.binop t op] (.tf t1s t2s)) :
    t1s = t2s ++ [t] ∧ ∃ ts, t2s = ts ++ [t] := by
  generalize hes : [BasicInstruction.binop t op] = es at h
  generalize htf : FunctionType.tf t1s t2s = tf at h
  induction h generalizing t1s t2s
  case binop => cases hes; cases htf; exact ⟨rfl, [], rfl⟩
  case composition h1 _ _ ih =>
    obtain ⟨rfl, rfl⟩ := extract_list1 hes.symm
    obtain rfl := empty_typing h1
    exact ih rfl htf
  case weakening ts _ _ _ ih =>
    cases htf; obtain ⟨rfl, ts', rfl⟩ := ih hes rfl; exact ⟨by simp, ts ++ ts', by simp⟩
  all_goals cases hes

@[rocq_alias iriswasm.Testop_typing]
theorem Testop_typing {C : TContext} {t : ValueType} {op : Testop} {t1s t2s : List ValueType}
    (h : BeTyping C [.testop t op] (.tf t1s t2s)) :
    ∃ ts, t1s = ts ++ [t] ∧ t2s = ts ++ [.i32] := by
  generalize hes : [BasicInstruction.testop t op] = es at h
  generalize htf : FunctionType.tf t1s t2s = tf at h
  induction h generalizing t1s t2s
  case testop => cases hes; cases htf; exact ⟨[], rfl, rfl⟩
  case composition h1 _ _ ih =>
    obtain ⟨rfl, rfl⟩ := extract_list1 hes.symm
    obtain rfl := empty_typing h1
    exact ih rfl htf
  case weakening ts _ _ _ ih =>
    cases htf; obtain ⟨ts', rfl, rfl⟩ := ih hes rfl; exact ⟨ts ++ ts', by simp, by simp⟩
  all_goals cases hes

@[rocq_alias iriswasm.Relop_typing]
theorem Relop_typing {C : TContext} {t : ValueType} {op : Relop} {t1s t2s : List ValueType}
    (h : BeTyping C [.relop t op] (.tf t1s t2s)) :
    ∃ ts, t1s = ts ++ [t, t] ∧ t2s = ts ++ [.i32] := by
  generalize hes : [BasicInstruction.relop t op] = es at h
  generalize htf : FunctionType.tf t1s t2s = tf at h
  induction h generalizing t1s t2s
  case relop => cases hes; cases htf; exact ⟨[], rfl, rfl⟩
  case composition h1 _ _ ih =>
    obtain ⟨rfl, rfl⟩ := extract_list1 hes.symm
    obtain rfl := empty_typing h1
    exact ih rfl htf
  case weakening ts _ _ _ ih =>
    cases htf; obtain ⟨ts', rfl, rfl⟩ := ih hes rfl; exact ⟨ts ++ ts', by simp, by simp⟩
  all_goals cases hes

@[rocq_alias iriswasm.Cvtop_typing]
theorem Cvtop_typing {C : TContext} {t1 t2 : ValueType} {op : Cvtop} {sx : Option Sx}
    {t1s t2s : List ValueType} (h : BeTyping C [.cvtop t2 op t1 sx] (.tf t1s t2s)) :
    ∃ ts, t1s = ts ++ [t1] ∧ t2s = ts ++ [t2] := by
  generalize hes : [BasicInstruction.cvtop t2 op t1 sx] = es at h
  generalize htf : FunctionType.tf t1s t2s = tf at h
  induction h generalizing t1s t2s
  case convert => cases hes; cases htf; exact ⟨[], rfl, rfl⟩
  case reinterpret => cases hes; cases htf; exact ⟨[], rfl, rfl⟩
  case truncSat => cases hes; cases htf; exact ⟨[], rfl, rfl⟩
  case composition h1 _ _ ih =>
    obtain ⟨rfl, rfl⟩ := extract_list1 hes.symm
    obtain rfl := empty_typing h1
    exact ih rfl htf
  case weakening ts _ _ _ ih =>
    cases htf; obtain ⟨ts', rfl, rfl⟩ := ih hes rfl; exact ⟨ts ++ ts', by simp, by simp⟩
  all_goals cases hes

@[rocq_alias iriswasm.Nop_typing]
theorem Nop_typing {C : TContext} {t1s t2s : List ValueType}
    (h : BeTyping C [.nop] (.tf t1s t2s)) : t1s = t2s := by
  generalize hes : [BasicInstruction.nop] = es at h
  generalize htf : FunctionType.tf t1s t2s = tf at h
  induction h generalizing t1s t2s
  case nop => cases htf; rfl
  case composition h1 _ _ ih =>
    obtain ⟨rfl, rfl⟩ := extract_list1 hes.symm
    obtain rfl := empty_typing h1
    exact ih rfl htf
  case weakening ts _ _ _ ih =>
    cases htf; rw [ih hes rfl]
  all_goals cases hes

@[rocq_alias iriswasm.Drop_typing]
theorem Drop_typing {C : TContext} {t1s t2s : List ValueType}
    (h : BeTyping C [.drop] (.tf t1s t2s)) : ∃ t, t1s = t2s ++ [t] := by
  generalize hes : [BasicInstruction.drop] = es at h
  generalize htf : FunctionType.tf t1s t2s = tf at h
  induction h generalizing t1s t2s
  case drop t => cases htf; exact ⟨t, rfl⟩
  case composition h1 _ _ ih =>
    obtain ⟨rfl, rfl⟩ := extract_list1 hes.symm
    obtain rfl := empty_typing h1
    exact ih rfl htf
  case weakening ts _ _ _ ih =>
    cases htf; obtain ⟨t, rfl⟩ := ih hes rfl; exact ⟨t, by simp⟩
  all_goals cases hes

@[rocq_alias iriswasm.Select_typing]
theorem Select_typing {C : TContext} {t1s t2s : List ValueType}
    (h : BeTyping C [.select] (.tf t1s t2s)) :
    ∃ ts t, t1s = ts ++ [t, t, .i32] ∧ t2s = ts ++ [t] := by
  generalize hes : [BasicInstruction.select] = es at h
  generalize htf : FunctionType.tf t1s t2s = tf at h
  induction h generalizing t1s t2s
  case select t => cases htf; exact ⟨[], t, rfl, rfl⟩
  case composition h1 _ _ ih =>
    obtain ⟨rfl, rfl⟩ := extract_list1 hes.symm
    obtain rfl := empty_typing h1
    exact ih rfl htf
  case weakening ts _ _ _ ih =>
    cases htf; obtain ⟨ts', t, rfl, rfl⟩ := ih hes rfl; exact ⟨ts ++ ts', t, by simp, by simp⟩
  all_goals cases hes

theorem Vbitselect_typing {C : TContext} {t1s t2s : List ValueType}
    (h : BeTyping C [.vbitselect] (.tf t1s t2s)) :
    ∃ ts, t1s = ts ++ [.v128, .v128, .v128] ∧ t2s = ts ++ [.v128] := by
  generalize hes : [BasicInstruction.vbitselect] = es at h
  generalize htf : FunctionType.tf t1s t2s = tf at h
  induction h generalizing t1s t2s
  case vbitselect => cases htf; exact ⟨[], rfl, rfl⟩
  case composition h1 _ _ ih =>
    obtain ⟨rfl, rfl⟩ := extract_list1 hes.symm
    obtain rfl := empty_typing h1
    exact ih rfl htf
  case weakening ts _ _ _ ih =>
    cases htf; obtain ⟨ts', rfl, rfl⟩ := ih hes rfl; exact ⟨ts ++ ts', by simp, by simp⟩
  all_goals cases hes

#rocq_ignore iriswasm.If_typing "Core block type inversion recovers a resolved signature"
theorem If_typing {C : TContext} {bt : BlockType} {e1s e2s : List BasicInstruction}
    {ts ts' : List ValueType} (h : BeTyping C [.if_ bt e1s e2s] (.tf ts ts')) :
    ∃ ts0 t1s t2s, expandBlockType C.typesT bt = some (.tf t1s t2s) ∧
      ts = ts0 ++ t1s ++ [.i32] ∧ ts' = ts0 ++ t2s ∧
      BeTyping (updLabel C ([t2s] ++ C.label)) e1s (.tf t1s t2s) ∧
      BeTyping (updLabel C ([t2s] ++ C.label)) e2s (.tf t1s t2s) := by
  generalize hes : [BasicInstruction.if_ bt e1s e2s] = es at h
  generalize htf : FunctionType.tf ts ts' = tf at h
  induction h generalizing ts ts'
  case ifWasm hs h1 h2 _ _ => cases hes; cases htf; exact ⟨[], _, _, hs, rfl, rfl, h1, h2⟩
  case composition h1 _ _ ih =>
    obtain ⟨rfl, rfl⟩ := extract_list1 hes.symm
    obtain rfl := empty_typing h1
    exact ih rfl htf
  case weakening ts _ _ _ ih =>
    cases htf; obtain ⟨ts0, _, _, hs, rfl, rfl, H3, H4⟩ := ih hes rfl
    exact ⟨ts ++ ts0, _, _, hs, by simp, by simp, H3, H4⟩
  all_goals cases hes

@[rocq_alias iriswasm.Br_if_typing]
theorem Br_if_typing {C : TContext} {ts1 ts2 : List ValueType} {i : Nat}
    (h : BeTyping C [.brIf i] (.tf ts1 ts2)) :
    ∃ ts ts', ts2 = ts ++ ts' ∧ ts1 = ts2 ++ [.i32] ∧ i < C.label.length ∧
      plop2 C i ts' = true := by
  generalize hes : [BasicInstruction.brIf i] = es at h
  generalize htf : FunctionType.tf ts1 ts2 = tf at h
  induction h generalizing ts1 ts2
  case brIf h1 h2 => cases hes; cases htf; exact ⟨[], _, rfl, rfl, h1, h2⟩
  case composition h1 _ _ ih =>
    obtain ⟨rfl, rfl⟩ := extract_list1 hes.symm
    obtain rfl := empty_typing h1
    exact ih rfl htf
  case weakening ts _ _ _ ih =>
    cases htf; obtain ⟨ts0, ts', rfl, H2, H3, H4⟩ := ih hes rfl
    exact ⟨ts ++ ts0, ts', by simp, by simp [H2], H3, H4⟩
  all_goals cases hes

@[rocq_alias iriswasm.Br_table_typing]
theorem Br_table_typing {C : TContext} {ts1 ts2 : List ValueType} {ids : List Nat} {i0 : Nat}
    (h : BeTyping C [.brTable ids i0] (.tf ts1 ts2)) :
    ∃ ts1' ts, ts1 = ts1' ++ ts ++ [.i32] ∧
      (ids ++ [i0]).all (fun i => decide (i < C.label.length) && plop2 C i ts) = true := by
  generalize hes : [BasicInstruction.brTable ids i0] = es at h
  generalize htf : FunctionType.tf ts1 ts2 = tf at h
  induction h generalizing ts1 ts2
  case brTable h1 => cases hes; cases htf; exact ⟨_, _, (List.append_assoc _ _ _).symm, h1⟩
  case composition h1 _ _ ih =>
    obtain ⟨rfl, rfl⟩ := extract_list1 hes.symm
    obtain rfl := empty_typing h1
    exact ih rfl htf
  case weakening ts _ _ _ ih =>
    cases htf; obtain ⟨ts1', ts', rfl, H2⟩ := ih hes rfl
    exact ⟨ts ++ ts1', ts', by simp, H2⟩
  all_goals cases hes

@[rocq_alias iriswasm.Tee_local_typing]
theorem Tee_local_typing {C : TContext} {i : Nat} {ts1 ts2 : List ValueType}
    (h : BeTyping C [.teeLocal i] (.tf ts1 ts2)) :
    ∃ ts t, ts1 = ts2 ∧ ts1 = ts ++ [t] ∧ i < C.local_.length ∧ C.local_[i]? = some t := by
  generalize hes : [BasicInstruction.teeLocal i] = es at h
  generalize htf : FunctionType.tf ts1 ts2 = tf at h
  induction h generalizing ts1 ts2
  case teeLocal h1 h2 => cases hes; cases htf; exact ⟨[], _, rfl, rfl, h1, h2⟩
  case composition h1 _ _ ih =>
    obtain ⟨rfl, rfl⟩ := extract_list1 hes.symm
    obtain rfl := empty_typing h1
    exact ih rfl htf
  case weakening ts _ _ _ ih =>
    cases htf; obtain ⟨ts', t, rfl, H2, H3, H4⟩ := ih hes rfl
    exact ⟨ts ++ ts', t, rfl, by simp [H2], H3, H4⟩
  all_goals cases hes

@[rocq_alias iriswasm.Const_list_typing]
theorem Const_list_typing {C : TContext} {vs : List Value} {t1s t2s : List ValueType}
    (h : BeTyping C (toBList (vToEList vs)) (.tf t1s t2s)) : t2s = t1s ++ vs.map typeof := by
  induction vs generalizing t1s t2s with
  | nil => simpa using (empty_typing h).symm
  | cons a vs ih =>
    obtain ⟨ts, t1s', t2s', t3s, rfl, rfl, H3, H4⟩ := composition_typing (es1 := [_]) h
    rw [ih H4, BI_const_typing H3]; simp

/-! ### Preservation for simple basic reductions -/

/-- Inverts a `ReduceSimple` hypothesis whose indices are not in constructor form. -/
local macro "rs_invert " h:ident " with " hA:ident hB:ident : tactic => `(tactic| (
  have ⟨A, B, h', $hA, $hB⟩ : ∃ A B, ReduceSimple A B ∧ _ = A ∧ _ = B := ⟨_, _, $h, rfl, rfl⟩
  cases h' <;> simp [toEList] at $hA:ident $hB:ident))

private theorem bet_const_of {C : TContext} {v : Value} {t1s t2s : List ValueType}
    (h : t2s = t1s ++ [typeof v]) : BeTyping C [.const v] (.tf t1s t2s) :=
  h ▸ bet_weakening_empty_1 t1s .const

private theorem bet_empty_of {C : TContext} {t1s t2s : List ValueType} (h : t1s = t2s) :
    BeTyping C [] (.tf t1s t2s) :=
  h ▸ bet_weakening_empty_both t1s .empty

private theorem cvt_typeof {t : ValueType} {sx : Option Sx} {v v' : Value}
    (h : cvt t sx v = some v') : typeof v' = t := by
  cases t <;> simp [cvt] at h <;> obtain ⟨_, _, rfl⟩ := h <;> rfl

@[rocq_alias iriswasm.app_binop_type_preserve]
theorem app_binop_type_preserve {op : Binop} {v1 v2 v : Value} (h : appBinop op v1 v2 = some v) :
    typeof v = typeof v1 := by
  unfold appBinop at h
  split at h <;> simp at h <;> (first | subst v | obtain ⟨_, _, rfl⟩ := h) <;> rfl

@[rocq_alias iriswasm.t_Unop_preserve]
theorem t_Unop_preserve {C : TContext} {v : Value} {t : ValueType} {op : Unop}
    {be : BasicInstruction} {tf : FunctionType} (h : BeTyping C [.const v, .unop t op] tf)
    (hr : ReduceSimple (toEList [.const v, .unop t op]) (toEList [be])) : BeTyping C [be] tf := by
  rs_invert hr with hA hB
  obtain ⟨rfl, rfl, rfl⟩ := hA; subst hB
  obtain ⟨t1s, t2s⟩ := tf
  obtain ⟨ts, t1s', t2s', t3s, rfl, rfl, H3, H4⟩ := composition_typing_single (es1 := [_]) h
  obtain ⟨rfl, -⟩ := Unop_typing H4
  refine .weakening (bet_const_of ?_)
  rw [BI_const_typing H3]; cases op <;> cases v <;> rfl

@[rocq_alias iriswasm.t_Binop_preserve_success]
theorem t_Binop_preserve_success {C : TContext} {v1 v2 : Value} {t : ValueType} {op : Binop}
    {be : BasicInstruction} {tf : FunctionType}
    (h : BeTyping C [.const v1, .const v2, .binop t op] tf)
    (hr : ReduceSimple (toEList [.const v1, .const v2, .binop t op]) (toEList [be])) :
    BeTyping C [be] tf := by
  rs_invert hr with hA hB
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hA; subst hB
  obtain ⟨t1s, t2s⟩ := tf
  obtain ⟨ts, t1s', t2s', t3s, rfl, rfl, H3, H4⟩ := composition_typing_single (es1 := [_, _]) h
  obtain ⟨h1, -⟩ := Binop_typing H4
  have h2 := BI_const2_typing H3
  rw [h1] at h2
  obtain ⟨h5, -⟩ := concat_cancel_last (l2 := t1s' ++ [typeof v1]) (by simpa using h2)
  have hv := app_binop_type_preserve ‹appBinop op v1 v2 = some _›
  exact .weakening (bet_const_of (by rw [h5, hv]))

private theorem testop_const_preserve {C : TContext} {v : Value} {t : ValueType} {op : Testop}
    {r : I32} {tf : FunctionType} (h : BeTyping C [.const v, .testop t op] tf) :
    BeTyping C [.const (.int32 r)] tf := by
  obtain ⟨t1s, t2s⟩ := tf
  obtain ⟨ts, t1s', t2s', t3s, rfl, rfl, H3, H4⟩ := composition_typing_single (es1 := [_]) h
  obtain ⟨ts', h1, rfl⟩ := Testop_typing H4
  rw [BI_const_typing H3] at h1
  obtain ⟨rfl, -⟩ := concat_cancel_last h1
  exact .weakening (bet_const_of rfl)

@[rocq_alias iriswasm.t_Relop_preserve]
theorem t_Relop_preserve {C : TContext} {v1 v2 : Value} {t : ValueType} {be : BasicInstruction}
    {op : Relop} {tf : FunctionType} (h : BeTyping C [.const v1, .const v2, .relop t op] tf)
    (hr : ReduceSimple [basic (.const v1), basic (.const v2), basic (.relop t op)] [basic be]) :
    BeTyping C [be] tf := by
  rs_invert hr with hA hB
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hA; subst hB
  obtain ⟨t1s, t2s⟩ := tf
  obtain ⟨ts, t1s', t2s', t3s, rfl, rfl, H3, H4⟩ := composition_typing_single (es1 := [_, _]) h
  obtain ⟨ts', h1, rfl⟩ := Relop_typing H4
  rw [BI_const2_typing H3] at h1
  obtain ⟨rfl, -⟩ := concat_cancel_last_n h1 rfl
  exact .weakening (bet_const_of rfl)

@[rocq_alias iriswasm.typeof_deserialise]
theorem typeof_deserialise (v : Bytes) (t : ValueType) : typeof (wasmDeserialise v t) = t := by
  cases t <;> rfl

@[rocq_alias iriswasm.be_typing_const_deserialise]
theorem be_typing_const_deserialise (C : TContext) (v : Value) (t : ValueType) :
    BeTyping C [.const (wasmDeserialise (bits v) t)] (.tf [] [t]) := by
  exact bet_const_of (by rw [typeof_deserialise]; rfl)

private theorem cvtop_const_preserve {C : TContext} {v w : Value} {src dst : ValueType}
    {op : Cvtop} {sx : Option Sx} {tf : FunctionType}
    (h : BeTyping C [.const v, .cvtop dst op src sx] tf) (hw : typeof w = dst) :
    BeTyping C [.const w] tf := by
  obtain ⟨t1s, t2s⟩ := tf
  obtain ⟨ts, t1s', t2s', t3s, rfl, rfl, H3, H4⟩ := composition_typing_single (es1 := [_]) h
  obtain ⟨ts', h1, rfl⟩ := Cvtop_typing H4
  rw [BI_const_typing H3] at h1
  obtain ⟨rfl, -⟩ := concat_cancel_last h1
  exact .weakening (bet_const_of (by rw [hw]))

@[rocq_alias iriswasm.t_Convert_preserve]
theorem t_Convert_preserve {C : TContext} {v : Value} {t1 t2 : ValueType} {sx : Option Sx}
    {be : BasicInstruction} {tf : FunctionType}
    (h : BeTyping C [.const v, .cvtop t2 .convert t1 sx] tf)
    (hr : ReduceSimple [basic (.const v), basic (.cvtop t2 .convert t1 sx)] [basic be]) :
    BeTyping C [be] tf := by
  rs_invert hr with hA hB
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hA; subst hB
  exact cvtop_const_preserve h (cvt_typeof (by assumption))

@[rocq_alias iriswasm.t_Reinterpret_preserve]
theorem t_Reinterpret_preserve {C : TContext} {v : Value} {t1 t2 : ValueType}
    {be : BasicInstruction} {tf : FunctionType}
    (h : BeTyping C [.const v, .cvtop t2 .reinterpret t1 none] tf)
    (hr : ReduceSimple [basic (.const v), basic (.cvtop t2 .reinterpret t1 none)] [basic be]) :
    BeTyping C [be] tf := by
  rs_invert hr with hA hB
  obtain ⟨rfl, rfl, rfl⟩ := hA; subst hB
  exact cvtop_const_preserve h (typeof_deserialise ..)

@[rocq_alias iriswasm.t_Drop_preserve]
theorem t_Drop_preserve {C : TContext} {v : Value} {tf : FunctionType}
    (h : BeTyping C [.const v, .drop] tf) : BeTyping C [] tf := by
  obtain ⟨t1s, t2s⟩ := tf
  obtain ⟨ts, t1s', t2s', t3s, rfl, rfl, H3, H4⟩ := composition_typing_single (es1 := [_]) h
  obtain ⟨t, h1⟩ := Drop_typing H4
  rw [BI_const_typing H3] at h1
  obtain ⟨rfl, -⟩ := concat_cancel_last h1
  exact .weakening (bet_empty_of rfl)

@[rocq_alias iriswasm.t_Select_preserve]
theorem t_Select_preserve {C : TContext} {v1 v2 : Value} {n : I32} {tf : FunctionType}
    {be : BasicInstruction}
    (h : BeTyping C [.const v1, .const v2, .const (.int32 n), .select] tf)
    (hr : ReduceSimple [basic (.const v1), basic (.const v2), basic (.const (.int32 n)),
      basic .select] [basic be]) :
    BeTyping C [be] tf := by
  obtain ⟨t1s, t2s⟩ := tf
  obtain ⟨ts, t1s', t2s', t3s, rfl, rfl, H3, H4⟩ := composition_typing_single (es1 := [_, _, _]) h
  obtain ⟨ts', t, h1, rfl⟩ := Select_typing H4
  rw [BI_const3_typing H3] at h1
  obtain ⟨rfl, h2⟩ := concat_cancel_last_n h1 rfl
  simp only [List.cons.injEq] at h2
  obtain ⟨h3, h4, -⟩ := h2
  rs_invert hr with hA hB
  · obtain ⟨rfl, rfl, rfl⟩ := hA; subst hB
    exact .weakening (bet_const_of (by rw [h4]))
  · obtain ⟨rfl, rfl, rfl⟩ := hA; subst hB
    exact .weakening (bet_const_of (by rw [h3]))

private theorem vbitselect_preserve {C : TContext} {x y mask : BitVec 128} {tf : FunctionType}
    (h : BeTyping C [.const (.vec128 x), .const (.vec128 y), .const (.vec128 mask),
      .vbitselect] tf) :
    BeTyping C [.const (.vec128 (Wasm.vbitselect x y mask))] tf := by
  obtain ⟨t1s, t2s⟩ := tf
  obtain ⟨ts, t1s', t2s', t3s, rfl, rfl, H3, H4⟩ := composition_typing_single (es1 := [_, _, _]) h
  obtain ⟨ts', h1, rfl⟩ := Vbitselect_typing H4
  rw [BI_const3_typing H3] at h1
  obtain ⟨rfl, -⟩ := concat_cancel_last_n h1 rfl
  exact .weakening (bet_const_of rfl)

@[rocq_alias iriswasm.t_If_be_preserve]
theorem t_If_be_preserve {C : TContext} {c : I32} {bt : BlockType}
    {es1 es2 : List BasicInstruction} {tf : FunctionType} {be : BasicInstruction}
    (h : BeTyping C [.const (.int32 c), .if_ bt es1 es2] tf)
    (hr : ReduceSimple (toEList [.const (.int32 c), .if_ bt es1 es2]) [basic be]) :
    BeTyping C [be] tf := by
  obtain ⟨t1s, t2s⟩ := tf
  obtain ⟨ts, t1s', t2s', t3s, rfl, rfl, H3, H4⟩ := composition_typing_single (es1 := [_]) h
  obtain ⟨ts0, tn, tm, hs, h1, rfl, B1, B2⟩ := If_typing H4
  rw [BI_const_typing H3] at h1
  obtain ⟨rfl, -⟩ := concat_cancel_last h1
  rs_invert hr with hA hB
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := hA; subst hB
    exact .weakening (.weakening (.block hs B2))
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := hA; subst hB
    exact .weakening (.weakening (.block hs B1))

@[rocq_alias iriswasm.t_Br_if_true_preserve]
theorem t_Br_if_true_preserve {C : TContext} {c : I32} {i : Nat} {tf : FunctionType}
    {be : BasicInstruction} (h : BeTyping C [.const (.int32 c), .brIf i] tf)
    (hr : ReduceSimple (toEList [.const (.int32 c), .brIf i]) [basic be]) :
    BeTyping C [be] tf := by
  rs_invert hr with hA hB
  obtain ⟨rfl, rfl⟩ := hA; subst hB
  obtain ⟨t1s, t2s⟩ := tf
  obtain ⟨ts, t1s', t2s', t3s, rfl, rfl, H3, H4⟩ := composition_typing_single (es1 := [_]) h
  obtain ⟨ts0, ts', rfl, h1, h2, h3⟩ := Br_if_typing H4
  rw [BI_const_typing H3] at h1
  obtain ⟨rfl, -⟩ := concat_cancel_last h1
  exact .weakening (.br h2 h3)

@[rocq_alias iriswasm.t_Br_if_false_preserve]
theorem t_Br_if_false_preserve {C : TContext} {c : I32} {i : Nat} {tf : FunctionType}
    (h : BeTyping C [.const (.int32 c), .brIf i] tf)
    (hr : ReduceSimple (toEList [.const (.int32 c), .brIf i]) []) : BeTyping C [] tf := by
  obtain ⟨t1s, t2s⟩ := tf
  obtain ⟨ts, t1s', t2s', t3s, rfl, rfl, H3, H4⟩ := composition_typing_single (es1 := [_]) h
  obtain ⟨ts0, ts', -, h1, -⟩ := Br_if_typing H4
  rw [BI_const_typing H3] at h1
  obtain ⟨rfl, -⟩ := concat_cancel_last h1
  exact .weakening (bet_empty_of rfl)

@[rocq_alias iriswasm.t_Br_table_preserve]
theorem t_Br_table_preserve {C : TContext} {c : I32} {ids : List Nat} {i0 : Nat}
    {tf : FunctionType} {be : BasicInstruction}
    (h : BeTyping C [.const (.int32 c), .brTable ids i0] tf)
    (hr : ReduceSimple (toEList [.const (.int32 c), .brTable ids i0]) [basic be]) :
    BeTyping C [be] tf := by
  obtain ⟨t1s, t2s⟩ := tf
  obtain ⟨ts, t1s', t2s', t3s, rfl, rfl, H3, H4⟩ := composition_typing_single (es1 := [_]) h
  obtain ⟨ts1', ts', h1, hall⟩ := Br_table_typing H4
  rw [BI_const_typing H3] at h1
  obtain ⟨rfl, -⟩ := concat_cancel_last h1
  have key : ∀ j ∈ ids ++ [i0], BeTyping C [.br j] (.tf (ts1' ++ ts') t2s') := by
    intro j hj
    have := List.all_eq_true.mp hall j hj
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact .br this.1 this.2
  rs_invert hr with hA hB
  · obtain ⟨rfl, rfl, rfl⟩ := hA; subst hB
    exact .weakening (key _ (List.mem_append_left _ (List.mem_of_getElem? ‹_[_]? = _›)))
  · obtain ⟨rfl, rfl, rfl⟩ := hA; subst hB
    exact .weakening (key _ (by simp))

@[rocq_alias iriswasm.t_Tee_local_preserve]
theorem t_Tee_local_preserve {C : TContext} {v : Value} {i : Nat} {tf : FunctionType}
    (h : BeTyping C [.const v, .teeLocal i] tf) :
    BeTyping C [.const v, .const v, .setLocal i] tf := by
  obtain ⟨t1s, t2s⟩ := tf
  obtain ⟨ts, t1s', t2s', t3s, rfl, rfl, H3, H4⟩ := composition_typing_single (es1 := [_]) h
  obtain ⟨ts', t, h0, h1, h2, h3⟩ := Tee_local_typing H4
  rw [BI_const_typing H3] at h0 h1
  obtain ⟨rfl, rfl⟩ := concat_cancel_last h1
  subst h0
  exact .weakening (bet_composition_front (bet_weakening_empty_1 _ .const)
    (bet_composition_front (bet_weakening_empty_1 _ .const)
      (bet_weakening_empty_2 (t1s' ++ [typeof v]) (.setLocal h2 h3))))

/-- Preservation for all `BeTyping`-typeable simple reductions. -/
@[rocq_alias iriswasm.t_be_simple_preservation]
theorem t_be_simple_preservation {bes bes' : List BasicInstruction}
    {es es' : List AdministrativeInstruction} {C : TContext} {tf : FunctionType}
    (hty : BeTyping C bes tf) (hr : ReduceSimple es es') (hb1 : EsIsBasic es)
    (hb2 : EsIsBasic es') (he1 : toEList bes = es) (he2 : toEList bes' = es') :
    BeTyping C bes' tf := by
  subst he1 he2
  rs_invert hr with hA hB
  case nop => subst hA hB; obtain ⟨t1s, t2s⟩ := tf; exact bet_empty_of (Nop_typing hty)
  case teeLocal hc =>
    simp only [List.map_eq_cons_iff, List.map_eq_nil_iff] at hA hB
    obtain ⟨b, _, rfl, rfl, c, _, rfl, hc', rfl⟩ := hA
    obtain ⟨b1, _, rfl, hb1', b2, _, rfl, hb2', b3, _, rfl, hb3', rfl⟩ := hB
    simp only [basic.injEq] at hc' hb1' hb2' hb3'; subst hc' hb1' hb2' hb3'
    cases b2 <;> simp [isConst] at hc
    exact t_Tee_local_preserve hty
  all_goals
    first
      | obtain rfl := to_e_list_injective (bes' := [_, _]) hA
      | obtain rfl := to_e_list_injective (bes' := [_, _, _]) hA
      | obtain rfl := to_e_list_injective (bes' := [_, _, _, _]) hA
    subst hB
    first
      | exact t_Unop_preserve hty hr
      | exact t_Binop_preserve_success hty hr
      | exact testop_const_preserve hty
      | exact t_Relop_preserve hty hr
      | exact t_Convert_preserve hty hr
      | exact t_Reinterpret_preserve hty hr
      | exact cvtop_const_preserve hty (truncSat_typeof (by assumption))
      | exact t_Drop_preserve hty
      | exact t_Select_preserve hty hr
      | exact vbitselect_preserve hty
      | exact t_If_be_preserve hty hr
      | exact t_Br_if_true_preserve hty hr
      | exact t_Br_if_false_preserve hty hr
      | exact t_Br_table_preserve hty hr

/-! ### Administrative instructions -/

private theorem et_empty {s : StoreRecord} {C : TContext} {t1s t2s : List ValueType}
    (h : ETyping s C [] (.tf t1s t2s)) : t1s = t2s :=
  empty_typing (et_to_bet (es := []) trivial h)

/-- `e_composition_typing` with the common prefix folded back into both halves. -/
private theorem e_comp_weak {s : StoreRecord} {C : TContext} {es1 es2 : List AdministrativeInstruction}
    {t1s t2s : List ValueType} (h : ETyping s C (es1 ++ es2) (.tf t1s t2s)) :
    ∃ t3s, ETyping s C es1 (.tf t1s t3s) ∧ ETyping s C es2 (.tf t3s t2s) := by
  obtain ⟨ts, t1s', t2s', t3s, rfl, rfl, H3, H4⟩ := e_composition_typing h
  exact ⟨ts ++ t3s, .weakening H3, .weakening H4⟩

private theorem label_typing_aux {s : StoreRecord} {C : TContext}
    {les : List AdministrativeInstruction} {tf : FunctionType} (h : ETyping s C les tf) :
    ∀ {n : Nat} {es0 es : List AdministrativeInstruction} {ts1 ts2 : List ValueType},
      les = [.label n es0 es] → tf = .tf ts1 ts2 →
      ∃ ts ts2', ts2 = ts1 ++ ts2' ∧ ETyping s C es0 (.tf ts ts2') ∧
        ETyping s (updLabel C ([ts] ++ C.label)) es (.tf [] ts2') ∧ ts.length = n := by
  match h with
  | .a _ => intro _ _ _ _ _ hes; simp [toEList, List.map_eq_cons_iff] at hes
  | .composition h1 h2 =>
    have ih := @label_typing_aux _ _ _ _ h2
    intro _ _ _ _ _ hes htf
    obtain ⟨rfl, rfl⟩ := extract_list1 hes
    cases htf
    obtain rfl := et_empty h1
    exact ih rfl rfl
  | .weakening h1 =>
    have ih := @label_typing_aux _ _ _ _ h1
    intro _ _ _ _ _ hes htf
    cases htf
    obtain ⟨ts', ts2', rfl, H2, H3, H4⟩ := ih hes rfl
    exact ⟨ts', ts2', by simp, H2, H3, H4⟩
  | .label h1 h2 h3 =>
    intro _ _ _ _ _ hes htf
    cases hes; cases htf
    exact ⟨_, _, rfl, h1, h2, h3⟩
  | .trap | .local .. | .invoke .. | .callHost .. => intro _ _ _ _ _ hes; cases hes

private theorem local_typing_aux {s : StoreRecord} {C : TContext}
    {les : List AdministrativeInstruction} {tf : FunctionType} (h : ETyping s C les tf) :
    ∀ {n : Nat} {f : Frame} {es : List AdministrativeInstruction} {t1s t2s : List ValueType},
      les = [.local n f es] → tf = .tf t1s t2s →
      ∃ ts, t2s = t1s ++ ts ∧ STyping s (some ts) f es ts ∧ ts.length = n := by
  match h with
  | .a _ => intro _ _ _ _ _ hes; simp [toEList, List.map_eq_cons_iff] at hes
  | .composition h1 h2 =>
    have ih := @local_typing_aux _ _ _ _ h2
    intro _ _ _ _ _ hes htf
    obtain ⟨rfl, rfl⟩ := extract_list1 hes
    cases htf
    obtain rfl := et_empty h1
    exact ih rfl rfl
  | .weakening h1 =>
    have ih := @local_typing_aux _ _ _ _ h1
    intro _ _ _ _ _ hes htf
    cases htf
    obtain ⟨ts', rfl, H2, H3⟩ := ih hes rfl
    exact ⟨ts', by simp, H2, H3⟩
  | .local h1 h2 =>
    intro _ _ _ _ _ hes htf
    cases hes; cases htf
    exact ⟨_, rfl, h1, h2⟩
  | .trap | .invoke .. | .label .. | .callHost .. => intro _ _ _ _ _ hes; cases hes

private theorem invoke_typing_aux {s : StoreRecord} {C : TContext}
    {les : List AdministrativeInstruction} {tf : FunctionType} (h : ETyping s C les tf) :
    ∀ {a : Nat} {t1s t2s : List ValueType}, les = [.invoke a] → tf = .tf t1s t2s →
      ∃ ts t1s' t2s' cl, t1s = ts ++ t1s' ∧ t2s = ts ++ t2s' ∧ s.funcs[a]? = some cl ∧
        ClTyping s cl (.tf t1s' t2s') := by
  match h with
  | .a _ => intro _ _ _ hes; simp [toEList, List.map_eq_cons_iff] at hes
  | .composition h1 h2 =>
    have ih := @invoke_typing_aux _ _ _ _ h2
    intro _ _ _ hes htf
    obtain ⟨rfl, rfl⟩ := extract_list1 hes
    cases htf
    obtain rfl := et_empty h1
    exact ih rfl rfl
  | .weakening (ts := ts) h1 =>
    have ih := @invoke_typing_aux _ _ _ _ h1
    intro _ _ _ hes htf
    cases htf
    obtain ⟨ts', t1s', t2s', cl, rfl, rfl, H3, H4⟩ := ih hes rfl
    exact ⟨ts ++ ts', t1s', t2s', cl, by simp, by simp, H3, H4⟩
  | .invoke h1 h2 =>
    intro _ _ _ hes htf
    cases hes; subst htf
    exact ⟨[], _, _, _, rfl, rfl, h1, h2⟩
  | .trap | .local .. | .label .. | .callHost .. => intro _ _ _ hes; cases hes

@[rocq_alias iriswasm.t_const_ignores_context]
theorem t_const_ignores_context {s : StoreRecord} (s' : StoreRecord) {C : TContext}
    (C' : TContext) {es : List AdministrativeInstruction} {tf : FunctionType}
    (hc : constList es = true) (h : ETyping s C es tf) : ETyping s' C' es tf := by
  obtain ⟨vs, rfl⟩ := const_es_exists hc
  obtain ⟨t1s, t2s⟩ := tf
  have hb := const_list_is_basic hc
  obtain rfl := Const_list_typing (et_to_bet hb h)
  exact ety_a' s' hb (bet_weakening_empty_1 t1s (Const_list_typing_empty C' vs))

#rocq_ignore iriswasm.Block_typing "Core block type inversion recovers a resolved signature"
theorem Block_typing {C : TContext} {bt : BlockType} {es : List BasicInstruction}
    {tn tm : List ValueType} (h : BeTyping C [.block bt es] (.tf tn tm)) :
    ∃ ts t1s t2s, expandBlockType C.typesT bt = some (.tf t1s t2s) ∧
      tn = ts ++ t1s ∧ tm = ts ++ t2s ∧
      BeTyping (updLabel C ([t2s] ++ C.label)) es (.tf t1s t2s) := by
  generalize hes : [BasicInstruction.block bt es] = es at h
  generalize htf : FunctionType.tf tn tm = tf at h
  induction h generalizing tn tm
  case block hs h1 _ => cases hes; cases htf; exact ⟨[], _, _, hs, rfl, rfl, h1⟩
  case composition h1 _ _ ih =>
    obtain ⟨rfl, rfl⟩ := extract_list1 hes.symm
    obtain rfl := empty_typing h1
    exact ih rfl htf
  case weakening ts _ _ _ ih =>
    cases htf; obtain ⟨ts0, _, _, hs, rfl, rfl, H⟩ := ih hes rfl
    exact ⟨ts ++ ts0, _, _, hs, by simp, by simp, H⟩
  all_goals cases hes

#rocq_ignore iriswasm.Loop_typing "Core block type inversion recovers a resolved signature"
theorem Loop_typing {C : TContext} {bt : BlockType} {es : List BasicInstruction}
    {tn tm : List ValueType} (h : BeTyping C [.loop bt es] (.tf tn tm)) :
    ∃ ts t1s t2s, expandBlockType C.typesT bt = some (.tf t1s t2s) ∧
      tn = ts ++ t1s ∧ tm = ts ++ t2s ∧
      BeTyping (updLabel C ([t1s] ++ C.label)) es (.tf t1s t2s) := by
  generalize hes : [BasicInstruction.loop bt es] = es at h
  generalize htf : FunctionType.tf tn tm = tf at h
  induction h generalizing tn tm
  case loop hs h1 _ => cases hes; cases htf; exact ⟨[], _, _, hs, rfl, rfl, h1⟩
  case composition h1 _ _ ih =>
    obtain ⟨rfl, rfl⟩ := extract_list1 hes.symm
    obtain rfl := empty_typing h1
    exact ih rfl htf
  case weakening ts _ _ _ ih =>
    cases htf; obtain ⟨ts0, _, _, hs, rfl, rfl, H⟩ := ih hes rfl
    exact ⟨ts ++ ts0, _, _, hs, by simp, by simp, H⟩
  all_goals cases hes

@[rocq_alias iriswasm.Break_typing]
theorem Break_typing {n : Nat} {C : TContext} {t1s t2s : List ValueType}
    (h : BeTyping C [.br n] (.tf t1s t2s)) :
    ∃ ts ts0, n < C.label.length ∧ plop2 C n ts = true ∧ t1s = ts0 ++ ts := by
  generalize hes : [BasicInstruction.br n] = es at h
  generalize htf : FunctionType.tf t1s t2s = tf at h
  induction h generalizing t1s t2s
  case br h1 h2 => cases hes; cases htf; exact ⟨_, _, h1, h2, rfl⟩
  case composition h1 _ _ ih =>
    obtain ⟨rfl, rfl⟩ := extract_list1 hes.symm
    obtain rfl := empty_typing h1
    exact ih rfl htf
  case weakening ts _ _ _ ih =>
    cases htf; obtain ⟨ts1, ts0, H1, H2, rfl⟩ := ih hes rfl; exact ⟨ts1, ts ++ ts0, H1, H2, by simp⟩
  all_goals cases hes

@[rocq_alias iriswasm.Label_typing]
theorem Label_typing {s : StoreRecord} {C : TContext} {n : Nat}
    {es0 es : List AdministrativeInstruction} {ts1 ts2 : List ValueType}
    (h : ETyping s C [.label n es0 es] (.tf ts1 ts2)) :
    ∃ ts ts2', ts2 = ts1 ++ ts2' ∧ ETyping s C es0 (.tf ts ts2') ∧
      ETyping s (updLabel C ([ts] ++ C.label)) es (.tf [] ts2') ∧ ts.length = n := by
  exact label_typing_aux h rfl rfl

@[rocq_alias iriswasm.Lfilled_break_typing]
theorem Lfilled_break_typing {n m k : Nat} {lh : Lholed} {vs LI : List AdministrativeInstruction}
    {ts : List ValueType} {s : StoreRecord} {C : TContext} {t2s : List ValueType}
    {tss : List (List ValueType)}
    (h : ETyping s (updLabel C (tss ++ [ts] ++ C.label)) LI (.tf [] t2s))
    (hc : constList vs = true) (hl : ts.length = vs.length)
    (hlf : lfilled n lh (vs ++ [basic (.br m)]) LI = true) (hk : tss.length = k)
    (hs : n + k = m) : ETyping s C vs (.tf [] ts) := by
  obtain ⟨vs', rfl⟩ := const_es_exists hc
  have hb := const_list_is_basic hc
  induction n generalizing lh LI t2s tss k with
  | zero =>
    cases (lfilled_Ind_Equivalent _ _ _ _).1 hlf with
    | lfilledBase vs0 _ es' _ =>
      obtain ⟨a, H1, -⟩ := e_comp_weak h
      obtain ⟨b, -, H3⟩ := e_comp_weak H1
      obtain ⟨c, H5, H6⟩ := e_comp_weak H3
      have hc' := Const_list_typing (et_to_bet hb H5)
      obtain ⟨ts1, ts0, -, hp, rfl⟩ := Break_typing (et_to_bet (by simp [EsIsBasic, EIsBasic]) H6)
      subst hs hk
      have hts : ts = ts1 := by simpa [plop2, updLabel] using hp
      subst hts
      obtain ⟨-, hvs⟩ := concat_cancel_last_n hc' (by simp [hl, v_to_e_size])
      exact ety_a' s hb (by rw [hvs]; exact Const_list_typing_empty C vs')
  | succ n ih =>
    cases (lfilled_Ind_Equivalent _ _ _ _).1 hlf with
    | lfilledRec _ vs0 n0 es0 lh' es'' _ LI' _ hlf' =>
      obtain ⟨a, H1, -⟩ := e_comp_weak h
      obtain ⟨b, -, H3⟩ := e_comp_weak H1
      obtain ⟨ts', ts2', -, -, H4, -⟩ := Label_typing H3
      exact ih (tss := ts' :: tss) (h := H4) (hlf := (lfilled_Ind_Equivalent _ _ _ _).2 hlf')
        (hk := rfl) (hs := by simp at hs hk ⊢; omega)

@[rocq_alias iriswasm.Local_typing]
theorem Local_typing {s : StoreRecord} {C : TContext} {n : Nat} {f : Frame}
    {es : List AdministrativeInstruction} {t1s t2s : List ValueType}
    (h : ETyping s C [.local n f es] (.tf t1s t2s)) :
    ∃ ts, t2s = t1s ++ ts ∧ STyping s (some ts) f es ts ∧ ts.length = n := by
  exact local_typing_aux h rfl rfl

@[rocq_alias iriswasm.Return_typing]
theorem Return_typing {C : TContext} {t1s t2s : List ValueType}
    (h : BeTyping C [.return_] (.tf t1s t2s)) :
    ∃ ts ts', t1s = ts' ++ ts ∧ C.return_ = some ts := by
  generalize hes : [BasicInstruction.return_] = es at h
  generalize htf : FunctionType.tf t1s t2s = tf at h
  induction h generalizing t1s t2s
  case return_ h1 => cases hes; cases htf; exact ⟨_, _, rfl, h1⟩
  case composition h1 _ _ ih =>
    obtain ⟨rfl, rfl⟩ := extract_list1 hes.symm
    obtain rfl := empty_typing h1
    exact ih rfl htf
  case weakening ts _ _ _ ih =>
    cases htf; obtain ⟨ts1, ts0, rfl, H⟩ := ih hes rfl; exact ⟨ts1, ts ++ ts0, by simp, H⟩
  all_goals cases hes

@[rocq_alias iriswasm.Lfilled_return_typing]
theorem Lfilled_return_typing {n : Nat} {lh : Lholed} {vs LI : List AdministrativeInstruction}
    {ts : List ValueType} {s : StoreRecord} {C : TContext} {lab : List (List ValueType)}
    {t2s : List ValueType} (h : ETyping s (updLabel C lab) LI (.tf [] t2s))
    (hc : constList vs = true) (hl : ts.length = vs.length)
    (hlf : lfilled n lh (vs ++ [basic .return_]) LI = true) (hr : some ts = C.return_) :
    ETyping s C vs (.tf [] ts) := by
  obtain ⟨vs', rfl⟩ := const_es_exists hc
  have hb := const_list_is_basic hc
  induction n generalizing lh LI lab t2s with
  | zero =>
    cases (lfilled_Ind_Equivalent _ _ _ _).1 hlf with
    | lfilledBase vs0 _ es' _ =>
      obtain ⟨a, H1, -⟩ := e_comp_weak h
      obtain ⟨b, -, H3⟩ := e_comp_weak H1
      obtain ⟨c, H5, H6⟩ := e_comp_weak H3
      have hc' := Const_list_typing (et_to_bet hb H5)
      obtain ⟨ts1, ts0, rfl, hret⟩ := Return_typing (et_to_bet (by simp [EsIsBasic, EIsBasic]) H6)
      have hts : ts = ts1 := Option.some.inj (hr.trans hret)
      subst hts
      obtain ⟨-, hvs⟩ := concat_cancel_last_n hc' (by simp [hl, v_to_e_size])
      exact ety_a' s hb (by rw [hvs]; exact Const_list_typing_empty C vs')
  | succ n ih =>
    cases (lfilled_Ind_Equivalent _ _ _ _).1 hlf with
    | lfilledRec _ vs0 n0 es0 lh' es'' _ LI' _ hlf' =>
      obtain ⟨a, H1, -⟩ := e_comp_weak h
      obtain ⟨b, -, H3⟩ := e_comp_weak H1
      obtain ⟨ts', ts2', -, -, H4, -⟩ := Label_typing H3
      exact ih H4 ((lfilled_Ind_Equivalent _ _ _ _).2 hlf')

@[rocq_alias iriswasm.Local_return_typing]
theorem Local_return_typing {s : StoreRecord} {C : TContext}
    {vs : List AdministrativeInstruction} {f : Frame} {LI : List AdministrativeInstruction}
    {tf : FunctionType} {n : Nat} {lh : Lholed}
    (h : ETyping s C [.local vs.length f LI] tf) (hc : constList vs = true)
    (hlf : lfilled n lh (vs ++ [basic .return_]) LI = true) : ETyping s C vs tf := by
  obtain ⟨t1s, t2s⟩ := tf
  obtain ⟨ts, rfl, hS, hlen⟩ := Local_typing h
  cases hS with
  | sTyping _ hC hE _ =>
    subst hC
    have hE' : ETyping s (updLabel (updReturn _ (some ts)) _) LI (.tf [] ts) := hE
    have := Lfilled_return_typing hE' hc hlen hlf rfl
    exact et_weakening_empty_1 t1s (t_const_ignores_context s C hc this)

private theorem isConst_iff' {e : AdministrativeInstruction} :
    isConst e = true ↔ ∃ v, e = .basic (.const v) := by
  rcases e with b | _ | _ | _ | _ | _ <;> simp [isConst]
  cases b <;> simp

private theorem simple_basic {s : StoreRecord} {C : TContext}
    {es es' : List AdministrativeInstruction} {tf : FunctionType} (h : ETyping s C es tf)
    (hr : ReduceSimple es es') (hb1 : EsIsBasic es) (hb2 : EsIsBasic es') : ETyping s C es' tf :=
  ety_a' s hb2 (t_be_simple_preservation (et_to_bet hb1 h) hr hb1 hb2
    (e_b_elim rfl hb1).symm (e_b_elim rfl hb2).symm)

@[rocq_alias iriswasm.t_simple_preservation]
theorem t_simple_preservation {s : StoreRecord} {i : Instance}
    {es es' : List AdministrativeInstruction} {C : TContext} {loc : List ValueType}
    {lab : List (List ValueType)} {ret : Option (List ValueType)} {tf : FunctionType}
    (hit : instTyping s i C = true)
    (h : ETyping s (updLabel (updLocalReturn C loc ret) lab) es tf)
    (hr : ReduceSimple es es') :
    ETyping s (updLabel (updLocalReturn C loc ret) lab) es' tf := by
  have hr' := hr
  cases hr
  case teeLocal hv =>
    obtain ⟨c, rfl⟩ := isConst_iff'.1 hv
    exact simple_basic h hr' (by simp [EsIsBasic, EIsBasic]) (by simp [EsIsBasic, EIsBasic])
  case labelConst hc =>
    obtain ⟨a, b⟩ := tf
    obtain ⟨ts, ts2', rfl, -, H, -⟩ := Label_typing h
    exact et_weakening_empty_1 a (t_const_ignores_context s _ hc H)
  case br i lh hc hn hlf =>
    obtain ⟨a, b⟩ := tf
    obtain ⟨ts, ts2', rfl, H1, H2, hl⟩ := Label_typing h
    have := Lfilled_break_typing (tss := []) (k := 0) H2 hc (hl.trans hn.symm) hlf rfl rfl
    exact et_weakening_empty_1 a (et_composition' this H1)
  case localConst hc hn =>
    obtain ⟨a, b⟩ := tf
    obtain ⟨ts, rfl, hS, -⟩ := Local_typing h
    cases hS with
    | sTyping _ _ hE _ => exact et_weakening_empty_1 a (t_const_ignores_context s _ hc hE)
  case return_ i lh hc hn hlf =>
    subst hn; exact Local_return_typing h hc hlf
  all_goals first
    | exact .trap
    | exact simple_basic h hr' (by simp [EsIsBasic, EIsBasic]) (by simp [EsIsBasic, EIsBasic])

/-! ### Calls, locals, globals, memory -/

@[rocq_alias iriswasm.Call_typing]
theorem Call_typing {j : Nat} {C : TContext} {t1s t2s : List ValueType}
    (h : BeTyping C [.call j] (.tf t1s t2s)) :
    ∃ ts t1s' t2s', j < C.funcT.length ∧ C.funcT[j]? = some (.tf t1s' t2s') ∧
      t1s = ts ++ t1s' ∧ t2s = ts ++ t2s' := by
  generalize hes : [BasicInstruction.call j] = es at h
  generalize htf : FunctionType.tf t1s t2s = tf at h
  induction h generalizing t1s t2s
  case call h1 h2 => cases hes; subst htf; exact ⟨[], _, _, h1, h2, rfl, rfl⟩
  case composition h1 _ _ ih =>
    obtain ⟨rfl, rfl⟩ := extract_list1 hes.symm
    obtain rfl := empty_typing h1
    exact ih rfl htf
  case weakening ts _ _ _ ih =>
    cases htf; obtain ⟨ts0, a, b, H1, H2, rfl, rfl⟩ := ih hes rfl; exact ⟨ts ++ ts0, a, b, H1, H2, by simp, by simp⟩
  all_goals cases hes

@[rocq_alias iriswasm.Call_indirect_typing]
theorem Call_indirect_typing {i : Nat} {C : TContext} {t1s t2s : List ValueType}
    (h : BeTyping C [.callIndirect i] (.tf t1s t2s)) :
    ∃ tn tm ts, C.table ≠ [] ∧ i < C.typesT.length ∧ C.typesT[i]? = some (.tf tn tm) ∧
      t1s = ts ++ tn ++ [.i32] ∧ t2s = ts ++ tm := by
  generalize hes : [BasicInstruction.callIndirect i] = es at h
  generalize htf : FunctionType.tf t1s t2s = tf at h
  induction h generalizing t1s t2s
  case callIndirect h1 h2 h3 => cases hes; cases htf; exact ⟨_, _, [], h3, h1, h2, rfl, rfl⟩
  case composition h1 _ _ ih =>
    obtain ⟨rfl, rfl⟩ := extract_list1 hes.symm
    obtain rfl := empty_typing h1
    exact ih rfl htf
  case weakening ts _ _ _ ih =>
    cases htf; obtain ⟨a, b, ts0, H0, H1, H2, rfl, rfl⟩ := ih hes rfl; exact ⟨a, b, ts ++ ts0, H0, H1, H2, by simp, by simp⟩
  all_goals cases hes

@[rocq_alias iriswasm.globs_agree_function]
theorem globs_agree_function (s : StoreRecord) :
    Function (fun x y => globalsAgree s.globals x y = true) := by
  intro x y1 y2 ⟨h1, h2⟩
  simp only [globalsAgree, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h1 h2
  obtain ⟨hl, h1⟩ := h1
  rw [List.getElem?_eq_getElem hl] at h1 h2
  simp only [Option.map_some, Option.some.injEq, globalAgree, Bool.and_eq_true,
    beq_iff_eq] at h1 h2
  cases y1; cases y2; simp_all

@[rocq_alias iriswasm.functions_agree_function]
theorem functions_agree_function (s : StoreRecord) :
    Function (fun x y => functionsAgree s.funcs x y = true) := by
  intro x y1 y2 ⟨h1, h2⟩
  exact functions_agree_injective h1 h2

@[rocq_alias iriswasm.tc_func_reference1]
theorem tc_func_reference1 {j k : Nat} {i : Instance} {s : StoreRecord} {f : FunctionClosure}
    {C : TContext} {tf : FunctionType} (h1 : i.funcs[j]? = some k) (h2 : s.funcs[k]? = some f)
    (hit : instTyping s i C = true) (h3 : C.funcT[j]? = some tf) : tf = clType f := by
  have := all2_projection (instTyping_spec hit).2.1 h1 h3
  simp only [functionsAgree, Bool.and_eq_true, beq_iff_eq, h2, Option.map_some,
    Option.some.injEq] at this
  exact this.2.symm

@[rocq_alias iriswasm.tc_func_reference2]
theorem tc_func_reference2 {s : StoreRecord} {C : TContext} {i : Instance} {j : Nat}
    {cl : FunctionClosure} {tf : FunctionType} (h1 : i.types[j]? = some (clType cl))
    (hit : instTyping s i C = true) (h2 : C.typesT[j]? = some tf) : tf = clType cl := by
  rw [(instTyping_spec hit).1, h2] at h1
  exact Option.some.inj h1

@[rocq_alias iriswasm.Invoke_func_native_typing]
theorem Invoke_func_native_typing {s : StoreRecord} {i : Instance} {C : TContext} {a : Nat}
    {cl : FunctionClosure} {tn tm ts : List ValueType} {es : List BasicInstruction}
    {t1s t2s : List ValueType} (h : ETyping s C [.invoke a] (.tf t1s t2s))
    (hn : s.funcs[a]? = some cl) (hcl : cl = .funcNative i (.tf tn tm) ts es) :
    ∃ ts' C', t1s = ts' ++ tn ∧ t2s = ts' ++ tm ∧ instTyping s i C' = true ∧
      BeTyping (updLocalLabelReturn C' (C'.local_ ++ tn ++ ts) ([tm] ++ C'.label) (some tm)) es
        (.tf [] tm) := by
  subst hcl
  obtain ⟨ts', t1s', t2s', cl', rfl, rfl, hn', hcl⟩ := invoke_typing_aux h rfl rfl
  rw [hn] at hn'; cases hn'
  cases hcl with
  | native hit htf hC hes =>
    cases htf; subst hC
    exact ⟨ts', _, rfl, rfl, hit, hes⟩

@[rocq_alias iriswasm.Invoke_func_host_typing]
theorem Invoke_func_host_typing {s : StoreRecord} {C : TContext} {a : Nat}
    {cl : FunctionClosure} {h : Hostfuncidx} {tn tm t1s t2s : List ValueType}
    (hty : ETyping s C [.invoke a] (.tf t1s t2s)) (hn : s.funcs[a]? = some cl)
    (hcl : cl = .funcHost (.tf tn tm) h) : ∃ ts, t1s = ts ++ tn ∧ t2s = ts ++ tm := by
  subst hcl
  obtain ⟨ts', t1s', t2s', cl', rfl, rfl, hn', hcl⟩ := invoke_typing_aux hty rfl rfl
  rw [hn] at hn'; cases hn'
  cases hcl
  exact ⟨ts', rfl, rfl⟩

@[rocq_alias iriswasm.Get_local_typing]
theorem Get_local_typing {C : TContext} {i : Nat} {t1s t2s : List ValueType}
    (h : BeTyping C [.getLocal i] (.tf t1s t2s)) :
    ∃ t, C.local_[i]? = some t ∧ t2s = t1s ++ [t] ∧ i < C.local_.length := by
  generalize hes : [BasicInstruction.getLocal i] = es at h
  generalize htf : FunctionType.tf t1s t2s = tf at h
  induction h generalizing t1s t2s
  case getLocal h1 h2 => cases hes; cases htf; exact ⟨_, h2, rfl, h1⟩
  case composition h1 _ _ ih =>
    obtain ⟨rfl, rfl⟩ := extract_list1 hes.symm
    obtain rfl := empty_typing h1
    exact ih rfl htf
  case weakening ts _ _ _ ih =>
    cases htf; obtain ⟨t, H1, rfl, H3⟩ := ih hes rfl; exact ⟨t, H1, by simp, H3⟩
  all_goals cases hes

@[rocq_alias iriswasm.Set_local_typing]
theorem Set_local_typing {C : TContext} {i : Nat} {t1s t2s : List ValueType}
    (h : BeTyping C [.setLocal i] (.tf t1s t2s)) :
    ∃ t, C.local_[i]? = some t ∧ t1s = t2s ++ [t] ∧ i < C.local_.length := by
  generalize hes : [BasicInstruction.setLocal i] = es at h
  generalize htf : FunctionType.tf t1s t2s = tf at h
  induction h generalizing t1s t2s
  case setLocal h1 h2 => cases hes; cases htf; exact ⟨_, h2, rfl, h1⟩
  case composition h1 _ _ ih =>
    obtain ⟨rfl, rfl⟩ := extract_list1 hes.symm
    obtain rfl := empty_typing h1
    exact ih rfl htf
  case weakening ts _ _ _ ih =>
    cases htf; obtain ⟨t, H1, rfl, H3⟩ := ih hes rfl; exact ⟨t, H1, by simp, H3⟩
  all_goals cases hes

@[rocq_alias iriswasm.Get_global_typing]
theorem Get_global_typing {C : TContext} {i : Nat} {t1s t2s : List ValueType}
    (h : BeTyping C [.getGlobal i] (.tf t1s t2s)) :
    ∃ t, (C.global[i]?).map GlobalType.t = some t ∧ t2s = t1s ++ [t] ∧
      i < C.global.length := by
  generalize hes : [BasicInstruction.getGlobal i] = es at h
  generalize htf : FunctionType.tf t1s t2s = tf at h
  induction h generalizing t1s t2s
  case getGlobal h1 h2 => cases hes; cases htf; exact ⟨_, h2, rfl, h1⟩
  case composition h1 _ _ ih =>
    obtain ⟨rfl, rfl⟩ := extract_list1 hes.symm
    obtain rfl := empty_typing h1
    exact ih rfl htf
  case weakening ts _ _ _ ih =>
    cases htf; obtain ⟨t, H1, rfl, H3⟩ := ih hes rfl; exact ⟨t, H1, by simp, H3⟩
  all_goals cases hes

@[rocq_alias iriswasm.Set_global_typing]
theorem Set_global_typing {C : TContext} {i : Nat} {t1s t2s : List ValueType}
    (h : BeTyping C [.setGlobal i] (.tf t1s t2s)) :
    ∃ g t, C.global[i]? = some g ∧ g.t = t ∧ isMut g = true ∧ t1s = t2s ++ [t] ∧
      i < C.global.length := by
  generalize hes : [BasicInstruction.setGlobal i] = es at h
  generalize htf : FunctionType.tf t1s t2s = tf at h
  induction h generalizing t1s t2s
  case setGlobal h1 h2 h3 h4 => cases hes; cases htf; exact ⟨_, _, h2, h3, h4, rfl, h1⟩
  case composition h1 _ _ ih =>
    obtain ⟨rfl, rfl⟩ := extract_list1 hes.symm
    obtain rfl := empty_typing h1
    exact ih rfl htf
  case weakening ts _ _ _ ih =>
    cases htf; obtain ⟨g, t, H1, H2, H3, rfl, H5⟩ := ih hes rfl; exact ⟨g, t, H1, H2, H3, by simp, H5⟩
  all_goals cases hes

#rocq_ignore iriswasm.Load_typing "Core load typing inverts the selected memory and offset bounds"
theorem Load_typing {C : TContext} {t : ValueType} {ma : MemArg}
    {tpSx : Option (PackedType × Sx)} {t1s t2s : List ValueType}
    (h : BeTyping C [.load t tpSx ma] (.tf t1s t2s)) :
    ∃ (mt : MemoryType) (ts : List ValueType), t1s = ts ++ [mt.address.valueType] ∧ t2s = ts ++ [t] ∧
      C.memory[ma.memory]? = some mt ∧ loadStoreTBounds ma.align (optionProjl tpSx) t = true ∧
      ma.offset < 2 ^ mt.address.width := by
  generalize hes : [BasicInstruction.load t tpSx ma] = es at h
  generalize htf : FunctionType.tf t1s t2s = tf at h
  induction h generalizing t1s t2s
  case load hm hb ho => cases hes; cases htf; exact ⟨_, [], rfl, rfl, hm, hb, ho⟩
  case composition h1 _ _ ih =>
    obtain ⟨rfl, rfl⟩ := extract_list1 hes.symm
    obtain rfl := empty_typing h1
    exact ih rfl htf
  case weakening ts _ _ _ ih =>
    cases htf
    obtain ⟨mt, ts0, rfl, rfl, H⟩ := ih hes rfl
    exact ⟨mt, ts ++ ts0, by simp, by simp, H⟩
  all_goals cases hes

#rocq_ignore iriswasm.Store_typing "Core store typing inverts the selected memory and offset bounds"
theorem Store_typing {C : TContext} {t : ValueType} {ma : MemArg}
    {tp : Option PackedType} {t1s t2s : List ValueType}
    (h : BeTyping C [.store t tp ma] (.tf t1s t2s)) :
    ∃ mt : MemoryType, t1s = t2s ++ [mt.address.valueType, t] ∧
      C.memory[ma.memory]? = some mt ∧ loadStoreTBounds ma.align tp t = true ∧
      ma.offset < 2 ^ mt.address.width := by
  generalize hes : [BasicInstruction.store t tp ma] = es at h
  generalize htf : FunctionType.tf t1s t2s = tf at h
  induction h generalizing t1s t2s
  case store hm hb ho => cases hes; cases htf; exact ⟨_, rfl, hm, hb, ho⟩
  case composition h1 _ _ ih =>
    obtain ⟨rfl, rfl⟩ := extract_list1 hes.symm
    obtain rfl := empty_typing h1
    exact ih rfl htf
  case weakening ts _ _ _ ih =>
    cases htf; obtain ⟨mt, rfl, H⟩ := ih hes rfl; exact ⟨mt, by simp, H⟩
  all_goals cases hes

#rocq_ignore iriswasm.Current_memory_typing "Core memory.size types an explicit memory index"
theorem Current_memory_typing {C : TContext} {x : Nat} {t1s t2s : List ValueType}
    (h : BeTyping C [.currentMemory x] (.tf t1s t2s)) :
    ∃ mt : MemoryType, C.memory[x]? = some mt ∧ t2s = t1s ++ [mt.address.valueType] := by
  generalize hes : [BasicInstruction.currentMemory x] = es at h
  generalize htf : FunctionType.tf t1s t2s = tf at h
  induction h generalizing t1s t2s
  case currentMemory h1 => cases hes; cases htf; exact ⟨_, h1, rfl⟩
  case composition h1 _ _ ih =>
    obtain ⟨rfl, rfl⟩ := extract_list1 hes.symm
    obtain rfl := empty_typing h1
    exact ih rfl htf
  case weakening ts _ _ _ ih =>
    cases htf; obtain ⟨mt, H1, rfl⟩ := ih hes rfl; exact ⟨mt, H1, by simp⟩
  all_goals cases hes

#rocq_ignore iriswasm.Grow_memory_typing "Core memory.grow types an explicit memory index"
theorem Grow_memory_typing {C : TContext} {x : Nat} {t1s t2s : List ValueType}
    (h : BeTyping C [.growMemory x] (.tf t1s t2s)) :
    ∃ (mt : MemoryType) (ts : List ValueType), C.memory[x]? = some mt ∧ t2s = t1s ∧
      t1s = ts ++ [mt.address.valueType] := by
  generalize hes : [BasicInstruction.growMemory x] = es at h
  generalize htf : FunctionType.tf t1s t2s = tf at h
  induction h generalizing t1s t2s
  case growMemory h1 => cases hes; cases htf; exact ⟨_, [], h1, rfl, rfl⟩
  case composition h1 _ _ ih =>
    obtain ⟨rfl, rfl⟩ := extract_list1 hes.symm
    obtain rfl := empty_typing h1
    exact ih rfl htf
  case weakening ts _ _ _ ih =>
    cases htf; obtain ⟨mt, ts0, H1, rfl, rfl⟩ := ih hes rfl
    exact ⟨mt, ts ++ ts0, H1, rfl, by simp⟩
  all_goals cases hes

@[rocq_alias iriswasm.store_typed_cl_typed]
theorem store_typed_cl_typed {s : StoreRecord} {n : Nat} {f : FunctionClosure}
    (h : s.funcs[n]? = some f) (hst : StoreTyping s) : ClTyping s f (clType f) := by
  obtain ⟨tf, htf⟩ := hst.1 f (List.mem_of_getElem? h)
  exact cl_typing_unique htf ▸ htf

@[rocq_alias iriswasm.inst_t_context_local_empty]
theorem inst_t_context_local_empty {s : StoreRecord} {i : Instance} {C : TContext}
    (h : instTyping s i C = true) : C.local_ = [] := by
  exact (instTyping_spec h).2.2.2.2.2.1

@[rocq_alias iriswasm.inst_t_context_label_empty]
theorem inst_t_context_label_empty {s : StoreRecord} {i : Instance} {C : TContext}
    (h : instTyping s i C = true) : C.label = [] := by
  exact (instTyping_spec h).2.2.2.2.2.2.1

@[rocq_alias iriswasm.global_type_reference]
theorem global_type_reference {s : StoreRecord} {i : Instance} {j : Nat} {C : TContext}
    {v : Value} {t : ValueType} (hit : instTyping s i C = true) (hv : sglobVal s i j = some v)
    (ht : (C.global[j]?).map GlobalType.t = some t) : typeof v = t := by
  simp only [sglobVal, sglob, sglobInd, optionBind] at hv
  cases hk : i.globs[j]? with
  | none => simp [hk] at hv
  | some k =>
    cases hg : s.globals[k]? with
    | none => simp [hk, hg] at hv
    | some g =>
      simp only [hk, hg, Option.map_some, Option.some.injEq] at hv
      subst hv
      obtain ⟨gt, hgt, rfl⟩ := Option.map_eq_some_iff.1 ht
      have := all2_projection (instTyping_spec hit).2.2.1 hk hgt
      simp only [globalsAgree, Bool.and_eq_true, beq_iff_eq, hg, Option.map_some,
        Option.some.injEq, globalAgree] at this
      exact this.2.2.symm

@[rocq_alias iriswasm.upd_label_unchanged]
theorem upd_label_unchanged {C : TContext} {lab : List (List ValueType)} (h : C.label = lab) :
    updLabel C lab = C := by
  subst h; rfl

@[rocq_alias iriswasm.upd_label_unchanged_typing]
theorem upd_label_unchanged_typing {s : StoreRecord} {C : TContext}
    {es : List AdministrativeInstruction} {tf : FunctionType} (h : ETyping s C es tf) :
    ETyping s (updLabel C C.label) es tf := by
  rwa [upd_label_unchanged rfl]

@[rocq_alias iriswasm.upd_label_upd_local_return_combine]
theorem upd_label_upd_local_return_combine (C : TContext) (loc : List ValueType)
    (lab : List (List ValueType)) (ret : Option (List ValueType)) :
    updLabel (updLocalReturn C loc ret) lab = updLocalLabelReturn C loc lab ret := by
  rfl

/-- Coq `set_nth vd l i e`; the default `vd` is irrelevant since `i < length l`. -/
@[rocq_alias iriswasm.set_nth_same_unchanged]
theorem set_nth_same_unchanged {X : Type} {l : List X} {e : X} {i : Nat} (h : l[i]? = some e) :
    l.set i e = l := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 h
  simp

@[rocq_alias iriswasm.set_nth_map]
theorem set_nth_map {X Y : Type} {l : List X} (e : X) {i : Nat} (f : X → Y) (h : i < l.length) :
    (l.set i e).map f = (l.map f).set i (f e) := by
  simp [List.map_set]

@[rocq_alias iriswasm.n_zeros_typing]
theorem n_zeros_typing (ts : List ValueType) : (nZeros ts).map typeof = ts := by
  simp only [nZeros, List.map_map]
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [List.map_cons, ih]; cases t <;> rfl

/-! ### Store extension -/

private theorem all2_mono {X Y : Type} {f g : X → Y → Bool}
    (hfg : ∀ x y, f x y = true → g x y = true) :
    ∀ {l1 : List X} {l2 : List Y}, List.all2 f l1 l2 = true → List.all2 g l1 l2 = true
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | _ :: _, _ :: _, h => by
    simp only [List.all2_cons, Bool.and_eq_true] at h ⊢
    exact ⟨hfg _ _ h.1, all2_mono hfg h.2⟩

private theorem all2_get {X Y : Type} {f : X → Y → Bool} :
    ∀ {l1 : List X} {l2 : List Y}, List.all2 f l1 l2 = true →
      l1.length = l2.length ∧
        ∀ (n : Nat) x, l1[n]? = some x → ∃ y, l2[n]? = some y ∧ f x y = true
  | [], [], _ => ⟨rfl, by simp⟩
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | _ :: _, b :: _, h => by
    simp only [List.all2_cons, Bool.and_eq_true] at h
    obtain ⟨hl, hg⟩ := all2_get h.2
    refine ⟨by simp [hl], fun n x hx => ?_⟩
    cases n with
    | zero => simp at hx; subst hx; exact ⟨b, rfl, h.1⟩
    | succ n => simpa using hg n x (by simpa using hx)

@[rocq_alias iriswasm.global_agree_extension]
theorem global_agree_extension {g0 g1 : Global} {g : GlobalType} (h1 : globalAgree g0 g = true)
    (h2 : globExtension g0 g1 = true) : globalAgree g1 g = true := by
  obtain ⟨m0, v0⟩ := g0; obtain ⟨m1, v1⟩ := g1; obtain ⟨gm, gt⟩ := g
  cases m0 <;> cases m1 <;> simp_all [globalAgree, globExtension]

@[rocq_alias iriswasm.glob_extension_C]
theorem glob_extension_C {sg sg' : List Global} {ig : List Nat} {tcg : List GlobalType}
    (h1 : List.all2 (globalsAgree sg) ig tcg = true) (h2 : List.all2 globExtension sg sg' = true) :
    List.all2 (globalsAgree sg') ig tcg = true := by
  refine all2_mono (fun n gt h => ?_) h1
  obtain ⟨hl, hg⟩ := all2_get h2
  simp only [globalsAgree, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h ⊢
  obtain ⟨hn, h⟩ := h
  obtain ⟨g0, hg0, hag⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨g1, hg1, hext⟩ := hg n g0 hg0
  exact ⟨hl ▸ hn, by rw [hg1]; simp [global_agree_extension hag hext]⟩

@[rocq_alias iriswasm.memi_agree_extension]
theorem memi_agree_extension {m0 m1 : List Memory} {n : Nat} {m : MemoryType}
    (h1 : memiAgree m0 n m = true) (h2 : List.all2 memExtension m0 m1 = true) :
    memiAgree m1 n m = true := by
  obtain ⟨hl, hg⟩ := all2_get h2
  simp only [memiAgree, Bool.and_eq_true, decide_eq_true_eq] at h1 ⊢
  obtain ⟨hn, h1⟩ := h1
  cases hm0 : m0[n]? with
  | none => simp [hm0] at h1
  | some mem0 =>
    obtain ⟨mem1, hm1, hext⟩ := hg n mem0 hm0
    rw [hm0] at h1; rw [hm1]
    simp only [memTyping, Limits.matches, memExtension, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      at h1 hext ⊢
    exact ⟨hl ▸ hn, hext.1.1.1.symm.trans h1.1, Nat.le_trans h1.2.1 hext.1.2,
      by rw [← hext.1.1.2]; exact h1.2.2⟩

@[rocq_alias iriswasm.mem_extension_C]
theorem mem_extension_C {sm sm' : List Memory} {im : List Nat} {tcm : List MemoryType}
    (h1 : List.all2 (memiAgree sm) im tcm = true) (h2 : List.all2 memExtension sm sm' = true) :
    List.all2 (memiAgree sm') im tcm = true := by
  exact all2_mono (fun _ _ h => memi_agree_extension h h2) h1

@[rocq_alias iriswasm.tabi_agree_extension]
theorem tabi_agree_extension {t0 t1 : List Tableinst} {n : Nat} {t : TableType}
    (h1 : tabiAgree t0 n t = true) (h2 : List.all2 tabExtension t0 t1 = true) :
    tabiAgree t1 n t = true := by
  obtain ⟨hl, hg⟩ := all2_get h2
  simp only [tabiAgree, Bool.and_eq_true, decide_eq_true_eq] at h1 ⊢
  obtain ⟨hn, h1⟩ := h1
  cases ht0 : t0[n]? with
  | none => simp [ht0] at h1
  | some tab0 =>
    obtain ⟨tab1, ht1, hext⟩ := hg n tab0 ht0
    rw [ht0] at h1; rw [ht1]
    simp only [tabTyping, Limits.matches, tabExtension, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      at h1 hext ⊢
    exact ⟨hl ▸ hn, Nat.le_trans h1.1 hext.1, by rw [← hext.2]; exact h1.2⟩

@[rocq_alias iriswasm.tab_extension_C]
theorem tab_extension_C {st st' : List Tableinst} {it : List Nat} {tct : List TableType}
    (h1 : List.all2 (tabiAgree st) it tct = true) (h2 : List.all2 tabExtension st st' = true) :
    List.all2 (tabiAgree st') it tct = true := by
  exact all2_mono (fun _ _ h => tabi_agree_extension h h2) h1

@[rocq_alias iriswasm.inst_typing_extension]
theorem inst_typing_extension {s s' : StoreRecord} {i : Instance} {C : TContext}
    (hext : storeExtension s s' = true) (h : instTyping s i C = true) :
    instTyping s' i C = true := by
  obtain ⟨ts, fs, tbs, ms, gs⟩ := i
  obtain ⟨ts', tfs, tgs, tabsT, memsT, loc, lab, ret⟩ := C
  simp only [storeExtension, Bool.and_eq_true, decide_eq_true_eq] at hext
  obtain ⟨⟨⟨hf, ht⟩, hm⟩, hg⟩ := hext
  cases loc <;> cases lab <;> cases ret <;>
    simp only [instTyping, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨⟨⟨⟨h1, hf ▸ h2⟩, glob_extension_C h3 hg⟩, tab_extension_C h4 ht⟩, mem_extension_C h5 hm⟩

@[rocq_alias iriswasm.frame_typing_extension]
theorem frame_typing_extension {s s' : StoreRecord} {f : Frame} {C : TContext}
    (hext : storeExtension s s' = true) (h : FrameTyping s f C) : FrameTyping s' f C := by
  cases h with
  | frameTyping h1 h2 h3 => exact .frameTyping (inst_typing_extension hext h1) h2 h3

/-- Coq `reflexive f` for a boolean relation is `∀ x, f x x`. -/
@[rocq_alias iriswasm.reflexive_all2_same]
theorem reflexive_all2_same {X : Type} {f : X → X → Bool} (l : List X) (h : ∀ x, f x x = true) :
    List.all2 f l l = true := by
  induction l <;> simp [*]

@[rocq_alias iriswasm.all2_tab_extension_same]
theorem all2_tab_extension_same (t : List Tableinst) : List.all2 tabExtension t t = true := by
  exact reflexive_all2_same t fun x => by simp [tabExtension]

@[rocq_alias iriswasm.all2_mem_extension_same]
theorem all2_mem_extension_same (t : List Memory) : List.all2 memExtension t t = true := by
  exact reflexive_all2_same t fun x => by simp [memExtension]

@[rocq_alias iriswasm.all2_glob_extension_same]
theorem all2_glob_extension_same (t : List Global) : List.all2 globExtension t t = true := by
  exact reflexive_all2_same t fun ⟨m, v⟩ => by cases m <;> simp [globExtension]

@[rocq_alias iriswasm.lfilled_es_type_exists]
theorem lfilled_es_type_exists {k : Nat} {lh : Lholed} {es les : List AdministrativeInstruction}
    {s : StoreRecord} {C : TContext} {tf : FunctionType} (hlf : lfilled k lh es les = true)
    (h : ETyping s C les tf) : ∃ lab t1s t2s, ETyping s (updLabel C lab) es (.tf t1s t2s) := by
  have hind := (lfilled_Ind_Equivalent _ _ _ _).1 hlf
  induction hind generalizing C tf with
  | lfilledBase vs es es' _ =>
    obtain ⟨t1s, t2s⟩ := tf
    obtain ⟨a, H1, -⟩ := e_comp_weak h
    obtain ⟨b, -, H2⟩ := e_comp_weak H1
    exact ⟨C.label, _, _, H2⟩
  | lfilledRec _ vs n es' lh' es'' es LI _ hlf' ih =>
    obtain ⟨t1s, t2s⟩ := tf
    obtain ⟨a, H1, -⟩ := e_comp_weak h
    obtain ⟨b, -, H3⟩ := e_comp_weak H1
    obtain ⟨ts', ts2', -, -, H4, -⟩ := Label_typing H3
    obtain ⟨lab, t1s', t2s', H5⟩ := ih ((lfilled_Ind_Equivalent _ _ _ _).2 hlf') H4
    exact ⟨lab, t1s', t2s', H5⟩

@[rocq_alias iriswasm.store_extension_same]
theorem store_extension_same (s : StoreRecord) : storeExtension s s = true := by
  simp [storeExtension, all2_tab_extension_same, all2_mem_extension_same,
    all2_glob_extension_same]

@[rocq_alias iriswasm.store_extension_cl_typing]
theorem store_extension_cl_typing {s s' : StoreRecord} {cl : FunctionClosure} {tf : FunctionType}
    (hext : storeExtension s s' = true) (h : ClTyping s cl tf) : ClTyping s' cl tf := by
  cases h with
  | native h1 h2 h3 h4 => exact .native (inst_typing_extension hext h1) h2 h3 h4
  | host => exact .host

mutual
private theorem et_ext {s s' : StoreRecord} (hext : storeExtension s s' = true) :
    ∀ {C : TContext} {es : List AdministrativeInstruction} {tf : FunctionType},
      ETyping s C es tf → ETyping s' C es tf
  | _, _, _, .a h => .a h
  | _, _, _, .composition h1 h2 => .composition (et_ext hext h1) (et_ext hext h2)
  | _, _, _, .weakening h => .weakening (et_ext hext h)
  | _, _, _, .trap => .trap
  | _, _, _, .local h1 h2 => .local (st_ext hext h1) h2
  | _, _, _, .invoke h1 h2 => by
    simp only [storeExtension, Bool.and_eq_true, decide_eq_true_eq] at hext
    exact .invoke (hext.1.1.1 ▸ h1) (store_extension_cl_typing (by
      simp [storeExtension, hext.1.1.1, hext.1.1.2, hext.1.2, hext.2]) h2)
  | _, _, _, .label h1 h2 h3 => .label (et_ext hext h1) (et_ext hext h2) h3
  | _, _, _, .callHost h => .callHost h

private theorem st_ext {s s' : StoreRecord} (hext : storeExtension s s' = true) :
    ∀ {rs : Option (List ValueType)} {f : Frame} {es : List AdministrativeInstruction}
      {ts : List ValueType}, STyping s rs f es ts → STyping s' rs f es ts
  | _, _, _, _, .sTyping h1 h2 h3 h4 =>
    .sTyping (frame_typing_extension hext h1) h2 (et_ext hext h3) h4
end

private theorem all2_update {X : Type} {f : X → X → Bool} (hrefl : ∀ x, f x x = true)
    {l : List X} {n : Nat} {x x' : X} (h1 : l[n]? = some x) (h2 : f x x' = true) :
    List.all2 f l (updateListAt l n x') = true := by
  have hn : n < l.length := (List.getElem?_eq_some_iff.1 h1).1
  rw [← update_list_at_is_set_nth _ hn]
  induction l generalizing n with
  | nil => simp at hn
  | cons a l ih =>
    cases n with
    | zero => simp at h1; subst h1; simp [h2, reflexive_all2_same l hrefl]
    | succ n => simp at h1; simp [hrefl a, ih h1 (by simpa using hn)]

@[rocq_alias iriswasm.store_extension_e_typing]
theorem store_extension_e_typing {s s' : StoreRecord} {C : TContext}
    {es : List AdministrativeInstruction} {tf : FunctionType} (hst1 : StoreTyping s)
    (hst2 : StoreTyping s') (hext : storeExtension s s' = true) (h : ETyping s C es tf) :
    ETyping s' C es tf := by
  exact et_ext hext h

@[rocq_alias iriswasm.glob_extension_update_nth]
theorem glob_extension_update_nth {sglobs : List Global} {n : Nat} {g g' : Global}
    (h1 : sglobs[n]? = some g) (h2 : globExtension g g' = true) :
    List.all2 globExtension sglobs (updateListAt sglobs n g') = true := by
  exact all2_update (fun ⟨m, v⟩ => by cases m <;> simp [globExtension]) h1 h2

@[rocq_alias iriswasm.tc_reference_glob_type]
theorem tc_reference_glob_type {s : StoreRecord} {i : Instance} {C : TContext} {n m : Nat}
    {gt : GlobalType} {g : Global} (hit : instTyping s i C = true) (h1 : i.globs[n]? = some m)
    (h2 : s.globals[m]? = some g) (h3 : C.global[n]? = some gt) : globalAgree g gt = true := by
  have := all2_projection (instTyping_spec hit).2.2.1 h1 h3
  simp only [globalsAgree, Bool.and_eq_true, beq_iff_eq, h2, Option.map_some,
    Option.some.injEq] at this
  exact this.2

@[rocq_alias iriswasm.mem_extension_update_nth]
theorem mem_extension_update_nth {smems : List Memory} {n : Nat} {m m' : Memory}
    (h1 : smems[n]? = some m) (h2 : memExtension m m' = true) :
    List.all2 memExtension smems (updateListAt smems n m') = true := by
  exact all2_update (fun x => by simp [memExtension]) h1 h2

@[rocq_alias iriswasm.bytes_takefill_size]
theorem bytes_takefill_size (c : Byte) (l : Nat) (vs : Bytes) :
    (bytesTakefill c l vs).length = l := by
  exact length_bytesTakefill c l vs

@[rocq_alias iriswasm.bytes_replicate_size]
theorem bytes_replicate_size (n : Nat) (b : Byte) : (bytesReplicate n b).length = n := by
  induction n <;> simp [bytesReplicate, *]

@[rocq_alias iriswasm.div_le]
theorem div_le (a : Nat) {b : Nat} (h : b > 0) : a / b ≤ a := by
  exact Nat.div_le_self a b

/-- `P` is explicit: Lean cannot infer it by higher-order unification. -/
@[rocq_alias iriswasm.list_fold_left_rev_prop]
theorem list_fold_left_rev_prop {X Y : Type} (P : Y → Prop) {f : Y → X → Y} {l : List X}
    {a1 a2 : Y} (h : l.foldl f a1 = a2) (hp : P a2) (hn : ∀ a e a', P a' → f a e = a' → P a) :
    P a1 := by
  induction l generalizing a1 with
  | nil => exact (show a1 = a2 from h) ▸ hp
  | cons x l ih => exact hn a1 x _ (ih h) rfl

/-- `P`, `R` are explicit: Lean cannot infer them by higher-order unification. -/
@[rocq_alias iriswasm.list_fold_left_restricted_trans]
theorem list_fold_left_restricted_trans {X Y : Type} (P : Y → Prop) (R : Y → Y → Prop)
    {f : Y → X → Y} {l : List X} {a1 a2 : Y} (h : l.foldl f a1 = a2) (hp1 : P a1) (hp2 : P a2)
    (hf : ∀ a e a', P a → P a' → f a e = a' → R a a') (hrefl : ∀ a, P a → R a a)
    (htrans : ∀ a1 a2 a3, P a1 → P a2 → P a3 → R a1 a2 → R a2 a3 → R a1 a3)
    (hn : ∀ a e a', P a' → f a e = a' → P a) : R a1 a2 := by
  induction l generalizing a1 with
  | nil => exact (show a1 = a2 from h) ▸ hrefl _ hp1
  | cons x l ih =>
    have hp : P (f a1 x) := list_fold_left_rev_prop P h hp2 hn
    exact htrans _ _ _ hp1 hp hp2 (hf _ _ _ hp1 hp rfl) (ih h hp)

@[rocq_alias iriswasm.proj2_some]
def Proj2Some (acc : Nat × Option MemoryList) : Prop := ∃ m, acc.2 = some m

@[rocq_alias iriswasm.mem_type_proj2_preserve]
def MemTypeProj2Preserve (acc1 acc2 : Nat × Option MemoryList) : Prop :=
  ∃ m1 m2, acc1.2 = some m1 ∧ acc2.2 = some m2 ∧ m1.lengthMem = m2.lengthMem

@[rocq_alias iriswasm.mem_type_proj2_preserve_trans]
theorem mem_type_proj2_preserve_trans {a1 a2 a3 : Nat × Option MemoryList} (hp1 : Proj2Some a1)
    (hp2 : Proj2Some a2) (hp3 : Proj2Some a3) (h12 : MemTypeProj2Preserve a1 a2)
    (h23 : MemTypeProj2Preserve a2 a3) : MemTypeProj2Preserve a1 a3 := by
  obtain ⟨m1, m2, h1, h2, e1⟩ := h12
  obtain ⟨m2', m3, h2', h3, e2⟩ := h23
  rw [h2] at h2'; cases h2'
  exact ⟨m1, m3, h1, h3, e1.trans e2⟩

private theorem foldLefti_inv {A B : Type} (P : A → Prop) (f : Nat → A → B → A)
    (hf : ∀ k a b, P a → P (f k a b)) (xs : List B) (acc : A) (h : P acc) :
    P (foldLefti f xs acc) := by
  suffices ∀ k acc, P acc →
      P (xs.foldl (fun (k, acc) x => (k + 1, f k acc x)) (k, acc)).2 from this 0 acc h
  induction xs with
  | nil => intro k acc h; exact h
  | cons x xs ih => intro k acc h; exact ih (k + 1) (f k acc x) (hf _ _ _ h)

theorem memGrow_spec {m mem : Memory} {c : Nat} (h : memGrow m c = some mem) :
    mem.data = m.data.memGrow (c * pageSize) ∧
    mem.type = ⟨m.type.address, ⟨memSize m + c, m.type.limits.max⟩⟩ ∧
    memSize m + c ≤ m.type.address.pageLimit ∧
    ∀ n, m.type.limits.max = some n → memSize m + c ≤ n := by
  simp only [memGrow] at h
  split at h <;> rename_i hc
  · cases h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    refine ⟨rfl, rfl, hc.1, fun n hn => ?_⟩
    simpa [hn] using hc.2
  · contradiction

#rocq_ignore iriswasm.write_bytes_preserve_type "Core byte writes preserve byte length and the entire memory type"
theorem write_bytes_preserve_type {m : Memory} {pos : Nat} {str : Bytes} {m' : Memory}
    (h : writeBytes m pos str = some m') : lengthMem m = lengthMem m' ∧ m.type = m'.type := by
  simp only [writeBytes] at h
  split at h
  · rename_i dat hdat
    cases h
    have := foldLefti_inv
      (fun o : Option MemoryList => ∀ d : MemoryList, o = some d →
        d.lengthMem = m.data.lengthMem) _
      (fun k a b ha d hd => by
        cases a with
        | none => cases hd
        | some dat =>
          rw [MemoryList.memory_list_ax_length_constant_update _ _ _ _ hd.symm]
          exact ha _ rfl)
      str (some m.data) (fun _ hd => by cases hd; rfl) dat hdat
    exact ⟨this.symm, rfl⟩
  · cases h

@[rocq_alias iriswasm.mem_extension_store]
theorem mem_extension_store {m : Memory} {k : Nat} {off : StaticOffset} {v : Value} {tlen : Nat}
    {mem : Memory} (h : store m k off (bits v) tlen = some mem) : memExtension m mem = true := by
  simp only [store] at h
  split at h
  · obtain ⟨h1, h2⟩ := write_bytes_preserve_type h
    simp [memExtension, h1, h2]
  · cases h

#rocq_ignore iriswasm.mem_extension_grow_memory "Monotonicity of the declared minimum uses memory validity"
theorem mem_extension_grow_memory {m : Memory} {c : Nat} {mem : Memory}
    (ha : MemAgree m) (h : memGrow m c = some mem) : memExtension m mem = true := by
  obtain ⟨hd, ht, -⟩ := memGrow_spec h
  simp [memExtension, ht, lengthMem, hd, ← ha.min_eq]

@[rocq_alias iriswasm.store_memory_extension_store_typed]
theorem store_memory_extension_store_typed {s s' : StoreRecord} (hst : StoreTyping s)
    (hext : storeExtension s s' = true) (hf : s.funcs = s'.funcs) (ht : s.tables = s'.tables)
    (hm : ∀ m ∈ s'.mems, MemAgree m) : StoreTyping s' := by
  obtain ⟨hfs, hts, -⟩ := hst
  refine ⟨fun f hf' => ?_, fun t ht' => ?_, hm⟩
  · obtain ⟨tf, htf⟩ := hfs f (hf ▸ hf')
    exact ⟨tf, store_extension_cl_typing hext htf⟩
  · obtain ⟨h1, h2⟩ := hts t (ht ▸ ht')
    refine ⟨fun x hx => ?_, h2⟩
    have := h1 x hx
    cases x with
    | none => trivial
    | some n => simpa [TabclAgree, ← hf] using this

@[rocq_alias iriswasm.store_global_extension_store_typed]
theorem store_global_extension_store_typed {s s' : StoreRecord} (hst : StoreTyping s)
    (hext : storeExtension s s' = true) (hf : s.funcs = s'.funcs) (ht : s.tables = s'.tables)
    (hm : s.mems = s'.mems) : StoreTyping s' := by
  exact store_memory_extension_store_typed hst hext hf ht fun m hm' => hst.2.2 m (hm ▸ hm')


namespace TypePreservation

@[rocq_alias iriswasm.type_preservation.nth_error_map]
theorem nth_error_map {X Y : Type} {l : List X} {n : Nat} {f : X → Y} {fv : Y}
    (h : (l.map f)[n]? = some fv) : ∃ v, l[n]? = some v ∧ f v = fv := by
  simpa only [List.getElem?_map, Option.map_eq_some_iff] using h

end TypePreservation

@[rocq_alias iriswasm.nth_error_update_list_hit]
theorem nth_error_update_list_hit {X : Type} {l : List X} {n : Nat} (x : X) (h : n < l.length) :
    (updateListAt l n x)[n]? = some x := by
  rw [← update_list_at_is_set_nth _ h]; simp [h]

@[rocq_alias iriswasm.nth_error_update_list_others]
theorem nth_error_update_list_others {X : Type} {l : List X} {n m : Nat} (x : X) (hne : n ≠ m)
    (h : n < l.length) : (updateListAt l n x)[m]? = l[m]? := by
  rw [← update_list_at_is_set_nth _ h]; simp [hne]

@[rocq_alias iriswasm.Forall_update]
theorem Forall_update {X : Type} {f : X → Prop} {l : List X} {n : Nat} {x : X}
    (ha : ∀ y ∈ l, f y) (hf : f x) (hn : n < l.length) : ∀ y ∈ updateListAt l n x, f y := by
  rw [← update_list_at_is_set_nth _ hn]
  intro y hy
  rcases List.mem_or_eq_of_mem_set hy with h | rfl
  · exact ha y h
  · exact hf

@[rocq_alias iriswasm.store_typed_mem_agree]
theorem store_typed_mem_agree {s : StoreRecord} {n : Nat} {m : Memory} (hst : StoreTyping s)
    (h : s.mems[n]? = some m) : MemAgree m := by
  exact hst.2.2 m (List.mem_of_getElem? h)

@[rocq_alias iriswasm.store_mem_agree]
theorem store_mem_agree {s : StoreRecord} {n : Nat} {m : Memory} {k : Nat} {off : StaticOffset}
    {vs : Bytes} {tl : Nat} {mem : Memory} (hst : StoreTyping s) (hn : s.mems[n]? = some m)
    (hs : store m k off vs tl = some mem) (htl : tl > 0) : MemAgree mem := by
  have hm := store_typed_mem_agree hst hn
  simp only [store] at hs
  split at hs
  · obtain ⟨h1, h2⟩ := write_bytes_preserve_type hs
    unfold MemAgree at hm ⊢; rw [← h2, ← h1]; exact hm
  · cases hs

@[rocq_alias iriswasm.mem_grow_mem_agree]
theorem mem_grow_mem_agree {s : StoreRecord} {n : Nat} {m : Memory} {c : Nat} {mem : Memory}
    (hst : StoreTyping s) (hn : s.mems[n]? = some m) (hg : memGrow m c = some mem) :
    MemAgree mem := by
  obtain ⟨hd, ht, hcap, hmax⟩ := memGrow_spec hg
  have ha := store_typed_mem_agree hst hn
  have hv := (limitTyping_iff ..).1 ha.1
  refine ⟨(limitTyping_iff ..).2 ?_, ?_⟩
  · rw [ht]; exact ⟨hcap, fun i hi => ⟨hmax i hi, (hv.2 i hi).2⟩⟩
  · change mem.data.lengthMem = _
    rw [hd, ht]
    change lengthMem m + c * pageSize = (memSize m + c) * pageSize
    rw [← ha.min_eq, ha.2, Nat.add_mul]

private theorem et_pair {s : StoreRecord} {C : TContext} {e1 e2 : BasicInstruction}
    {t1s t2s : List ValueType} (h : ETyping s C [basic e1, basic e2] (.tf t1s t2s)) :
    ∃ t3s, BeTyping C [e1] (.tf t1s t3s) ∧ BeTyping C [e2] (.tf t3s t2s) := by
  obtain ⟨a, H1, H2⟩ := e_comp_weak (es1 := [basic e1]) (es2 := [basic e2]) h
  exact ⟨a, et_to_bet (by simp [EsIsBasic, EIsBasic]) H1, et_to_bet (by simp [EsIsBasic, EIsBasic]) H2⟩

private theorem et_triple {s : StoreRecord} {C : TContext} {e1 e2 e3 : BasicInstruction}
    {t1s t2s : List ValueType} (h : ETyping s C [basic e1, basic e2, basic e3] (.tf t1s t2s)) :
    ∃ t3s t4s, BeTyping C [e1] (.tf t1s t3s) ∧ BeTyping C [e2] (.tf t3s t4s) ∧
      BeTyping C [e3] (.tf t4s t2s) := by
  obtain ⟨a, H1, H2⟩ := e_comp_weak (es1 := [basic e1, basic e2]) (es2 := [basic e3]) h
  obtain ⟨b, H3, H4⟩ := et_pair H1
  exact ⟨b, a, H3, H4, et_to_bet (by simp [EsIsBasic, EIsBasic]) H2⟩

private theorem et_nil {s : StoreRecord} {C : TContext} {t1s t2s : List ValueType}
    (h : t1s = t2s) : ETyping s C [] (.tf t1s t2s) :=
  ety_a' (es := []) s trivial (bet_empty_of h)

private theorem et_const {s : StoreRecord} {C : TContext} {v : Value} {t1s t2s : List ValueType}
    (h : t2s = t1s ++ [typeof v]) : ETyping s C [basic (.const v)] (.tf t1s t2s) :=
  ety_a' s (by simp [EsIsBasic, EIsBasic]) (bet_const_of h)

private theorem lengthT_pos (t : ValueType) : lengthT t > 0 := by cases t <;> decide

private theorem lengthTp_pos (tp : PackedType) : lengthTp tp > 0 := by cases tp <;> decide

/-- The memory part of `store_extension_reduce` for an updated memory. -/
private theorem mem_update_ext {s : StoreRecord} {i : Nat} {m mem' : Memory} (hst : StoreTyping s)
    (hm : s.mems[i]? = some m) (he : memExtension m mem' = true) (ha : MemAgree mem') :
    storeExtension s (updSMem s (updateListAt s.mems i mem')) = true ∧
      StoreTyping (updSMem s (updateListAt s.mems i mem')) := by
  have hext : storeExtension s (updSMem s (updateListAt s.mems i mem')) = true := by
    simp only [storeExtension, updSMem, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨trivial, all2_tab_extension_same _⟩, mem_extension_update_nth hm he⟩,
      all2_glob_extension_same _⟩
  exact ⟨hext, store_memory_extension_store_typed hst hext rfl rfl
    (Forall_update hst.2.2 ha (List.getElem?_eq_some_iff.1 hm).1)⟩

@[rocq_alias iriswasm.reduce_inst_unchanged]
theorem reduce_inst_unchanged {s : StoreRecord} {f : Frame} {es : List AdministrativeInstruction}
    {s' : StoreRecord} {f' : Frame} {es' : List AdministrativeInstruction}
    (h : Reduce s f es s' f' es') : f.inst = f'.inst := by
  induction h
  all_goals first | rfl | (apply Eq.symm; assumption) | assumption

@[rocq_alias iriswasm.store_extension_reduce]
theorem store_extension_reduce {s : StoreRecord} {f : Frame} {es : List AdministrativeInstruction}
    {s' : StoreRecord} {f' : Frame} {es' : List AdministrativeInstruction} {C : TContext}
    {tf : FunctionType} {loc : List ValueType} {lab : List (List ValueType)}
    {ret : Option (List ValueType)} (hr : Reduce s f es s' f' es')
    (hit : instTyping s f.inst C = true)
    (h : ETyping s (updLabel (updLocalReturn C loc ret) lab) es tf) (hst : StoreTyping s) :
    storeExtension s s' = true ∧ StoreTyping s' := by
  induction hr generalizing C tf loc lab ret with
  | @setGlobal s f i v s' hsup =>
    obtain ⟨t1s, t2s⟩ := tf
    obtain ⟨a, H1, H2⟩ := et_pair h
    obtain rfl := BI_const_typing H1
    obtain ⟨g, t, hg, rfl, hmut, heq, -⟩ := Set_global_typing H2
    obtain ⟨-, hvt⟩ := concat_cancel_last heq
    simp only [supdateGlob, optionBind, sglobInd] at hsup
    split at hsup
    · cases hsup
    rename_i k hk
    simp only [supdateGlobS, Option.map_eq_some_iff] at hsup
    obtain ⟨g0, hg0, rfl⟩ := hsup
    have gagree := tc_reference_glob_type hit hk hg0 hg
    have hge : globExtension g0 ⟨g0.mut_, v⟩ = true := by
      obtain ⟨m0, v0⟩ := g0; obtain ⟨gm, gt⟩ := g
      cases m0 <;> cases gm <;> simp_all [globalAgree, isMut, globExtension]
    have hext : storeExtension s
        ⟨s.funcs, s.tables, s.mems, updateListAt s.globals k ⟨g0.mut_, v⟩⟩ = true := by
      simp only [storeExtension, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨⟨by simp, all2_tab_extension_same _⟩, all2_mem_extension_same _⟩,
        glob_extension_update_nth hg0 hge⟩
    exact ⟨hext, store_global_extension_store_typed hst hext rfl rfl rfl⟩
  | storeSuccess m _ _ hm hs =>
    exact mem_update_ext hst hm (mem_extension_store hs) (store_mem_agree hst hm hs (lengthT_pos _))
  | storePackedSuccess m _ _ _ hm hs =>
    exact mem_update_ext hst hm (mem_extension_store hs)
      (store_mem_agree hst hm hs (lengthTp_pos _))
  | growMemorySuccess m _ hm _ _ hg =>
    exact mem_update_ext hst hm (mem_extension_grow_memory (store_typed_mem_agree hst hm) hg)
      (mem_grow_mem_agree hst hm hg)
  | label es es' k lh _ hlf _ ih =>
    obtain ⟨lab', t1s, t2s, H⟩ := lfilled_es_type_exists hlf h
    exact ih (C := C) (loc := loc) (ret := ret) (lab := lab') (hit := hit) (h := H) (hst := hst)
  | @«local» s f es s' f' es' n f0 _ ih =>
    obtain ⟨t1s, t2s⟩ := tf
    obtain ⟨ts, -, hS, -⟩ := Local_typing h
    cases hS with
    | sTyping hF hC hE _ =>
    cases hF with
    | @frameTyping i tvs C' _ hit' hi htvs =>
    subst hC hi htvs
    exact ih (C := C') (loc := C'.local_ ++ f.locs.map typeof) (ret := some ts) (lab := C'.label)
      (tf := .tf [] ts) (hit := hit') (h := hE) (hst := hst)
  | _ => exact ⟨store_extension_same _, hst⟩

@[rocq_alias iriswasm.result_e_type]
theorem result_e_type {r : Result} {ts : List ValueType} (s : StoreRecord) (C : TContext)
    (h : resultTypesAgree ts r = true) : ETyping s C (resultToStack r) (.tf [] ts) := by
  cases r with
  | trap => exact .trap
  | values vs =>
    have hts : ts = vs.map typeof := by
      simp only [resultTypesAgree] at h
      induction ts generalizing vs with
      | nil => cases vs <;> simp_all [List.all2]
      | cons t ts ih =>
        cases vs with
        | nil => simp [List.all2] at h
        | cons v vs =>
          simp only [List.all2_cons, Bool.and_eq_true, typesAgree, beq_iff_eq] at h
          simp [h.1, ih vs h.2]
    subst hts
    exact ety_a' s (const_list_is_basic (v_to_e_is_const_list vs)) (Const_list_typing_empty C vs)

@[rocq_alias iriswasm.t_preservation_vs_type]
theorem t_preservation_vs_type {s : StoreRecord} {f : Frame} {es : List AdministrativeInstruction}
    {s' : StoreRecord} {f' : Frame} {es' : List AdministrativeInstruction} {C C' : TContext}
    {lab : List (List ValueType)} {ret : Option (List ValueType)} {t1s t2s : List ValueType}
    (hr : Reduce s f es s' f' es') (hst1 : StoreTyping s) (hst2 : StoreTyping s')
    (hit1 : instTyping s f.inst C = true) (hit2 : instTyping s' f.inst C' = true)
    (h : ETyping s (updLabel (updLocalReturn C (C.local_ ++ f.locs.map typeof) ret) lab) es
      (.tf t1s t2s)) :
    f.locs.map typeof = f'.locs.map typeof := by
  induction hr generalizing lab t1s t2s with
  | @setLocal f f' i v s hinst hlen hlocs =>
    obtain ⟨a, H1, H2⟩ := et_pair h
    obtain rfl := BI_const_typing H1
    obtain ⟨t, ht, heq, -⟩ := Set_local_typing H2
    obtain ⟨-, rfl⟩ := concat_cancel_last heq
    have hl := inst_t_context_local_empty hit1
    simp only [updLabel, updLocalReturn, hl, List.nil_append] at ht
    rw [hlocs, List.map_set]
    exact (set_nth_same_unchanged ht).symm
  | label es es' k lh _ hlf _ ih =>
    obtain ⟨lab', _, _, H⟩ := lfilled_es_type_exists hlf h
    exact ih (lab := lab') (hst1 := hst1) (hst2 := hst2) (hit1 := hit1) (hit2 := hit2) (h := H)
  | _ => rfl

@[rocq_alias iriswasm.inst_typing_func]
theorem inst_typing_func {s : StoreRecord} {i : Instance} {j : Nat} {C : TContext} {a : Nat}
    {x : FunctionType} (hit : instTyping s i C = true) (h1 : i.funcs[j]? = some a)
    (h2 : C.funcT[j]? = some x) : ∃ cl, s.funcs[a]? = some cl := by
  obtain ⟨-, H, -⟩ := instTyping_spec hit
  obtain ⟨y, -, hf⟩ := (all2_get H).2 j a h1
  simp only [functionsAgree, Bool.and_eq_true, decide_eq_true_eq] at hf
  exact ⟨_, List.getElem?_eq_getElem hf.1⟩

private theorem lfilled_preserve {s s' : StoreRecord} {Cb : TContext}
    {es es' : List AdministrativeInstruction}
    (hes : ∀ lab t1s t2s, ETyping s (updLabel Cb lab) es (.tf t1s t2s) →
      ETyping s' (updLabel Cb lab) es' (.tf t1s t2s))
    (hext : ∀ {C es tf}, ETyping s C es tf → ETyping s' C es tf)
    {k : Nat} {lh : Lholed} {les les' : List AdministrativeInstruction}
    (h1 : LfilledInd k lh es les) (h2 : LfilledInd k lh es' les') :
    ∀ {lab t1s t2s}, ETyping s (updLabel Cb lab) les (.tf t1s t2s) →
      ETyping s' (updLabel Cb lab) les' (.tf t1s t2s) := by
  induction h1 generalizing les' with
  | lfilledBase vs _ ea _ =>
    cases h2
    intro lab t1s t2s h
    obtain ⟨a, H1, H3⟩ := e_comp_weak h
    obtain ⟨b, H0, H2⟩ := e_comp_weak H1
    exact et_composition' (et_composition' (hext H0) (hes _ _ _ H2)) (hext H3)
  | lfilledRec k vs n es0 lh' ea _ LI _ _ ih =>
    cases h2 with
    | lfilledRec _ _ _ _ _ _ _ LI' _ h2' =>
    intro lab t1s t2s h
    obtain ⟨a, H1, H3⟩ := e_comp_weak h
    obtain ⟨b, H0, H2⟩ := e_comp_weak H1
    obtain ⟨ts, ts2', rfl, H4, H5, hn⟩ := Label_typing H2
    have H6 := ih (hes := hes) (les' := LI') (h2 := h2') (lab := [ts] ++ lab) H5
    exact et_composition' (et_composition' (hext H0)
      (et_weakening_empty_1 b (.label (hext H4) H6 hn))) (hext H3)

@[rocq_alias iriswasm.t_preservation_e]
theorem t_preservation_e {s : StoreRecord} {f : Frame} {es : List AdministrativeInstruction}
    {s' : StoreRecord} {f' : Frame} {es' : List AdministrativeInstruction} {C : TContext}
    {t1s t2s : List ValueType} {lab : List (List ValueType)} {ret : Option (List ValueType)}
    (hr : Reduce s f es s' f' es') (hst1 : StoreTyping s) (hst2 : StoreTyping s')
    (hit1 : instTyping s f.inst C = true) (hit2 : instTyping s' f.inst C = true)
    (h : ETyping s (updLabel (updLocalReturn C (C.local_ ++ f.locs.map typeof) ret) lab) es
      (.tf t1s t2s)) :
    ETyping s' (updLabel (updLocalReturn C (C.local_ ++ f'.locs.map typeof) ret) lab) es'
      (.tf t1s t2s) := by
  induction hr generalizing C ret lab t1s t2s with
  | simple hrs => exact t_simple_preservation hit1 h hrs
  | @block s f bt tn tm vs es hs hc hn =>
    obtain ⟨vs', rfl⟩ := const_es_exists hc
    obtain ⟨c, H1, H2⟩ := e_comp_weak h
    have hc' := Const_list_typing (et_to_bet (const_list_is_basic hc) H1)
    obtain ⟨ts, tn', tm', ht, rfl, rfl, H3⟩ :=
      Block_typing (et_to_bet (by simp [EsIsBasic, EIsBasic]) H2)
    rw [(instTyping_spec hit1).1] at hs
    cases Option.some.inj (hs.symm.trans ht)
    obtain ⟨rfl, hvs⟩ := concat_cancel_last_n hc'
      (by simpa only [List.length_map, v_to_e_size] using hn.symm)
    exact et_weakening_empty_1 _ (.label (.a (bet_weakening_empty_both _ .empty))
      (et_composition' (ety_a' s (const_list_is_basic hc)
        (by rw [hvs]; exact Const_list_typing_empty _ vs')) (.a H3)) rfl)
  | @loop s f bt tn tm vs es hs hc hn =>
    obtain ⟨vs', rfl⟩ := const_es_exists hc
    obtain ⟨c, H1, H2⟩ := e_comp_weak h
    have hc' := Const_list_typing (et_to_bet (const_list_is_basic hc) H1)
    obtain ⟨ts, tn', tm', ht, rfl, rfl, H3⟩ :=
      Loop_typing (et_to_bet (by simp [EsIsBasic, EIsBasic]) H2)
    rw [(instTyping_spec hit1).1] at hs
    cases Option.some.inj (hs.symm.trans ht)
    obtain ⟨rfl, hvs⟩ := concat_cancel_last_n hc'
      (by simpa only [List.length_map, v_to_e_size] using hn.symm)
    exact et_weakening_empty_1 _ (.label (ety_a' s (by simp [EsIsBasic, EIsBasic]) (.loop ht H3))
      (et_composition' (ety_a' s (const_list_is_basic hc)
        (by rw [hvs]; exact Const_list_typing_empty _ vs')) (.a H3)) rfl)
  | @call s f i a hi =>
    obtain ⟨ts, t1s', t2s', -, hfT, rfl, rfl⟩ :=
      Call_typing (et_to_bet (by simp [EsIsBasic, EIsBasic]) h)
    obtain ⟨cl, hcl⟩ := inst_typing_func hit1 hi hfT
    have htf := tc_func_reference1 hi hcl hit1 hfT
    exact .weakening (.invoke hcl (by rw [htf]; exact store_typed_cl_typed hcl hst1))
  | callIndirectSuccess cl _ hcl hty =>
    obtain ⟨a, H1, H2⟩ := et_pair h
    obtain rfl := BI_const_typing H1
    obtain ⟨tn, tm, ts, -, -, hT, heq, rfl⟩ := Call_indirect_typing H2
    obtain ⟨rfl, -⟩ := concat_cancel_last heq
    have htf := tc_func_reference2 hty hit1 hT
    exact .weakening (.invoke hcl (by rw [htf]; exact store_typed_cl_typed hcl hst1))
  | @invokeNative a cl tn tm ts' es0 ves vcs n m k zs s f f' i hcl hcleq hves hn hk ht1 ht2 hzs
      hfi hfl =>
    subst hves hcleq
    obtain ⟨b, H1, H2⟩ := e_comp_weak h
    obtain ⟨ts'', C', rfl, rfl, hitC, hB⟩ := Invoke_func_native_typing H2 hcl rfl
    have hb := Const_list_typing (et_to_bet (const_list_is_basic (v_to_e_is_const_list vcs)) H1)
    obtain ⟨rfl, htn⟩ := concat_cancel_last_n hb (by simp [hn, ht1])
    have hL : C'.local_ ++ f'.locs.map typeof = C'.local_ ++ tn ++ ts' := by
      rw [hfl, List.map_append, ← hzs, n_zeros_typing, ← htn, List.append_assoc]
    rw [← hL] at hB
    exact et_weakening_empty_1 _ (.local (.sTyping (.frameTyping hitC hfi rfl) rfl
      (.label (.a (bet_weakening_empty_both _ .empty)) (.a hB) ht2) (Or.inl rfl)) ht2)
  | @invokeHost a cl hh tn tm ves vcs m n s f hcl hcleq hves hn ht1 ht2 =>
    subst hves hcleq
    obtain ⟨b, H1, H2⟩ := e_comp_weak h
    obtain ⟨ts, rfl, rfl⟩ := Invoke_func_host_typing H2 hcl rfl
    have hb := Const_list_typing (et_to_bet (const_list_is_basic (v_to_e_is_const_list vcs)) H1)
    obtain ⟨rfl, -⟩ := concat_cancel_last_n hb (by simp [hn, ht1])
    exact et_weakening_empty_1 _ (.callHost (by rw [hn, ht1]))
  | getLocal hv =>
    obtain ⟨t, ht, rfl, -⟩ := Get_local_typing (et_to_bet (by simp [EsIsBasic, EIsBasic]) h)
    have hl := inst_t_context_local_empty hit1
    simp [updLabel, updLocalReturn, hl, hv] at ht
    exact et_const (by rw [ht])
  | setLocal _ _ _ =>
    obtain ⟨a, H1, H2⟩ := et_pair h
    obtain rfl := BI_const_typing H1
    obtain ⟨t, -, heq, -⟩ := Set_local_typing H2
    exact et_nil (concat_cancel_last heq).1
  | getGlobal hv =>
    obtain ⟨t, ht, rfl, -⟩ := Get_global_typing (et_to_bet (by simp [EsIsBasic, EIsBasic]) h)
    exact et_const (by rw [global_type_reference hit1 hv ht])
  | setGlobal _ =>
    obtain ⟨a, H1, H2⟩ := et_pair h
    obtain rfl := BI_const_typing H1
    obtain ⟨g, t, -, -, -, heq, -⟩ := Set_global_typing H2
    exact et_nil (concat_cancel_last heq).1
  | loadSuccess | loadPackedSuccess =>
    obtain ⟨a, H1, H2⟩ := et_pair h
    obtain rfl := BI_const_typing H1
    obtain ⟨_, ts, heq, rfl, -⟩ := Load_typing H2
    obtain ⟨rfl, -⟩ := concat_cancel_last heq
    exact et_const (by rw [typeof_deserialise])
  | storeSuccess | storePackedSuccess =>
    obtain ⟨a, b, H1, H2, H3⟩ := et_triple h
    obtain rfl := BI_const_typing H1
    obtain rfl := BI_const_typing H2
    obtain ⟨_, heq, -⟩ := Store_typing H3
    rw [List.append_assoc] at heq
    exact et_nil (List.append_inj' heq (by simp)).1
  | currentMemory _ m hi hm _ _ =>
    obtain ⟨mt, hmt, rfl⟩ := Current_memory_typing (et_to_bet (by simp [EsIsBasic, EIsBasic]) h)
    have hag := all2_projection (instTyping_spec hit1).2.2.2.2.1 hi hmt
    simp only [memiAgree, hm, memTyping, Bool.and_eq_true, beq_iff_eq] at hag
    apply et_const
    rw [← hag.2.1]
    cases m.type.address <;> rfl
  | growMemorySuccess | growMemoryFailure =>
    obtain ⟨a, H1, H2⟩ := et_pair h
    obtain rfl := BI_const_typing H1
    obtain ⟨_, ts, -, rfl, -⟩ := Grow_memory_typing H2
    apply et_const
    cases ‹AddressOperand› <;> rfl
  | @label s f es les s' f' es' les' k lh hr' hlf1 hlf2 ih =>
    obtain ⟨lab', _, _, H⟩ := lfilled_es_type_exists hlf1 h
    have hvs := t_preservation_vs_type (C := C) (ret := ret) (lab := lab') hr' hst1 hst2 hit1 hit2 H
    obtain ⟨hext, -⟩ := store_extension_reduce (loc := C.local_ ++ f.locs.map typeof) (ret := ret)
      (lab := lab') hr' hit1 H hst1
    rw [← hvs]
    exact lfilled_preserve (Cb := updLocalReturn C (C.local_ ++ f.locs.map typeof) ret)
      (fun lab0 a b H0 => by
        have := ih (C := C) (ret := ret) (lab := lab0) (t1s := a) (t2s := b) (hst1 := hst1)
          (hst2 := hst2) (hit1 := hit1) (hit2 := hit2) (h := H0)
        rwa [← hvs] at this)
      (fun H0 => store_extension_e_typing hst1 hst2 hext H0)
      ((lfilled_Ind_Equivalent _ _ _ _).1 hlf1) ((lfilled_Ind_Equivalent _ _ _ _).1 hlf2) h
  | @«local» s f es s' f' es' n f0 hr' ih =>
    obtain ⟨ts, rfl, hS, hn⟩ := Local_typing h
    cases hS with
    | sTyping hF hC hE _ =>
    cases hF with
    | @frameTyping i tvs C' _ hit' hi htvs =>
    subst hC hi htvs
    have hE' : ETyping s (updLabel (updLocalReturn C' (C'.local_ ++ f.locs.map typeof) (some ts))
        C'.label) es (.tf [] ts) := hE
    obtain ⟨hext, -⟩ := store_extension_reduce hr' hit' hE' hst1
    have hit'' := inst_typing_extension hext hit'
    have IH := ih (C := C') (ret := some ts) (lab := C'.label) (t1s := []) (t2s := ts)
      (hst1 := hst1) (hst2 := hst2) (hit1 := hit') (hit2 := hit'') (h := hE')
    exact et_weakening_empty_1 _ (.local (.sTyping
      (.frameTyping hit'' (reduce_inst_unchanged hr').symm rfl) rfl IH (Or.inl rfl)) hn)
  | _ => exact .trap

@[rocq_alias iriswasm.t_preservation]
theorem t_preservation {s : StoreRecord} {f : Frame} {es : List AdministrativeInstruction}
    {s' : StoreRecord} {f' : Frame} {es' : List AdministrativeInstruction} {ts : List ValueType}
    (hr : Reduce s f es s' f' es') (h : ConfigTyping s f es ts) : ConfigTyping s' f' es' ts := by
  cases h with
  | configTyping hst hS =>
  cases hS with
  | sTyping hF hC hE _ =>
  cases hF with
  | @frameTyping i tvs C1 _ hit hi htvs =>
  subst hC hi htvs
  have hE' : ETyping s (updLabel (updLocalReturn C1 (C1.local_ ++ f.locs.map typeof) none)
      C1.label) es (.tf [] ts) := hE
  obtain ⟨hext, hst'⟩ := store_extension_reduce hr hit hE' hst
  have hit' := inst_typing_extension hext hit
  exact .configTyping hst' (.sTyping (.frameTyping hit' (reduce_inst_unchanged hr).symm rfl) rfl
    (t_preservation_e hr hst hst' hit hit' hE') (Or.inr rfl))

end Wasm
