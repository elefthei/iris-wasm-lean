/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import Wasm.TypePreservation

/-! Port of `theories/type_progress.v`: the progress theorem.

Names also declared in `iris/helpers/prelude/first_instr.v` (`find_first_some`,
`first_instr_instr`, `first_instr`, `first_instr_const`, `starts_with_lfilled`,
`lfilled_implies_starts`, `first_instr_app`) or in `type_preservation.v` (`nth_error_map`) live in
`namespace Wasm.TypeProgress` and carry the alias `iriswasm.type_progress.<name>`.
Coq `decidable` via `pickable` becomes classical `Decidable`. -/

namespace Wasm

open AdministrativeInstruction (basic trap)

@[rocq_alias iriswasm.terminal_form]
def TerminalForm (es : List AdministrativeInstruction) : Prop :=
  constList es = true ∨ es = [trap]

@[rocq_alias iriswasm.reduce_trap_left]
theorem reduce_trap_left {vs : List AdministrativeInstruction} (hc : constList vs = true)
    (hne : vs ≠ []) : ReduceSimple (vs ++ [trap]) [trap] := by
  refine .trap (.base vs []) ?_ (by simp [lfilled, lfill, hc])
  cases vs with
  | nil => exact absurd rfl hne
  | cons a l => simp

@[rocq_alias iriswasm.v_e_trap]
theorem v_e_trap {vs es : List AdministrativeInstruction} (hc : constList vs = true)
    (h : vs ++ es = [trap]) : vs = [] ∧ es = [trap] := by
  cases vs with
  | nil => simpa using h
  | cons a l =>
    simp only [List.cons_append, List.cons.injEq] at h
    simp [h.1, constList, isConst] at hc

@[rocq_alias iriswasm.cat_split]
theorem cat_split {X : Type} {l l1 l2 : List X} (h : l = l1 ++ l2) :
    l1 = l.take l1.length ∧ l2 = l.drop l1.length := by
  subst h; simp

@[rocq_alias iriswasm.reduce_composition]
theorem reduce_composition {s : StoreRecord} {cs : List AdministrativeInstruction} {f : Frame}
    {es : List AdministrativeInstruction} (es0 : List AdministrativeInstruction) {s' : StoreRecord}
    {f' : Frame} {es' : List AdministrativeInstruction} (hc : constList cs = true)
    (h : Reduce s f es s' f' es') : Reduce s f (cs ++ es ++ es0) s' f' (cs ++ es' ++ es0) := by
  exact .label es es' 0 (.base cs es0) h (by simp [lfilled, lfill, hc])
    (by simp [lfilled, lfill, hc])

@[rocq_alias iriswasm.reduce_composition_right]
theorem reduce_composition_right {s : StoreRecord} {f : Frame} {es : List AdministrativeInstruction}
    (es0 : List AdministrativeInstruction) {s' : StoreRecord} {f' : Frame}
    {es' : List AdministrativeInstruction} (h : Reduce s f es s' f' es') :
    Reduce s f (es ++ es0) s' f' (es' ++ es0) := by
  simpa using reduce_composition (cs := []) es0 rfl h

@[rocq_alias iriswasm.reduce_composition_left]
theorem reduce_composition_left {s : StoreRecord} {cs : List AdministrativeInstruction} {f : Frame}
    {es : List AdministrativeInstruction} {s' : StoreRecord} {f' : Frame}
    {es' : List AdministrativeInstruction} (hc : constList cs = true)
    (h : Reduce s f es s' f' es') : Reduce s f (cs ++ es) s' f' (cs ++ es') := by
  simpa using reduce_composition [] hc h

@[rocq_alias iriswasm.lfilled0_empty]
theorem lfilled0_empty (es : List AdministrativeInstruction) :
    lfilled 0 (.base [] []) es es = true := by
  simp [lfilled, lfill, constList]

@[rocq_alias iriswasm.label_lfilled1]
theorem label_lfilled1 (n : Nat) (es es0 : List AdministrativeInstruction) :
    lfilled 1 (.rec_ [] n es0 (.base [] []) []) es [.label n es0 es] = true := by
  simp [lfilled, lfill, constList]

@[rocq_alias iriswasm.terminal_form_v_e]
theorem terminal_form_v_e {vs es : List AdministrativeInstruction} (hc : constList vs = true)
    (h : TerminalForm (vs ++ es)) : TerminalForm es := by
  rcases h with h | h
  · exact .inl (const_list_split h).2
  · exact .inr (v_e_trap hc h).2

@[rocq_alias iriswasm.terminal_trap]
theorem terminal_trap : TerminalForm [trap] := by
  exact .inr rfl

@[rocq_alias iriswasm.e_b_inverse]
theorem e_b_inverse {es : List AdministrativeInstruction} (h : EsIsBasic es) :
    toEList (toBList es) = es := by
  exact (e_b_elim rfl h).symm

@[rocq_alias iriswasm.typeof_append]
theorem typeof_append {ts : List ValueType} {t : ValueType} {vs : List Value}
    (h : vs.map typeof = ts ++ [t]) :
    ∃ v, vs = vs.take ts.length ++ [v] ∧ (vs.take ts.length).map typeof = ts ∧ typeof v = t := by
  obtain ⟨l1, l2, rfl, h1, h2⟩ := List.map_eq_append_iff.1 h
  obtain ⟨v, rfl, rfl⟩ := List.map_eq_singleton_iff.1 h2
  subst h1
  exact ⟨v, by simp, by simp, rfl⟩

#rocq_ignore iriswasm.invert_typeof_vcs "Ltac local to type_progress.v; proofs use rcases"

@[rocq_alias iriswasm.type_progress.nth_error_map]
theorem TypeProgress.nth_error_map {X Y : Type} {l : List X} {n : Nat} {f : X → Y} {fx : Y}
    (h : (l.map f)[n]? = some fx) : ∃ x, l[n]? = some x ∧ f x = fx := by
  simpa [List.getElem?_map] using h

@[rocq_alias iriswasm.func_context_store]
theorem func_context_store {s : StoreRecord} {i : Instance} {C : TContext} {j : Nat}
    {x : FunctionType} (hit : instTyping s i C = true) (hlen : j < C.funcT.length)
    (hn : C.funcT[j]? = some x) : ∃ a, i.funcs[j]? = some a := by
  obtain ⟨ts, fs, tbs, ms, gs⟩ := i
  obtain ⟨ts', tfs, tgs, tabsT, memsT, loc, lab, ret⟩ := C
  cases loc <;> cases lab <;> cases ret <;> simp [instTyping, and_assoc] at hit
  have := all2_size _ _ _ hit.2.1
  simp only at hlen ⊢
  exact ⟨_, List.getElem?_eq_getElem (by omega)⟩

@[rocq_alias iriswasm.glob_context_store]
theorem glob_context_store {s : StoreRecord} {i : Instance} {C : TContext} {j : Nat}
    {g : GlobalType} (hit : instTyping s i C = true) (hlen : j < C.global.length)
    (hn : C.global[j]? = some g) : sglob s i j ≠ none := by
  obtain ⟨ts, fs, tbs, ms, gs⟩ := i
  obtain ⟨ts', tfs, tgs, tabsT, memsT, loc, lab, ret⟩ := C
  cases loc <;> cases lab <;> cases ret <;> simp [instTyping, and_assoc] at hit
  have hl := all2_size _ _ _ hit.2.2.1
  simp only at hlen hn hl
  have hk : gs[j]? = some gs[j] := List.getElem?_eq_getElem (by omega)
  have := all2_projection hit.2.2.1 hk hn
  simp [globalsAgree] at this
  simp [sglob, sglobInd, optionBind, hk, this.1]

#rocq_ignore iriswasm.mem_context_store "Core resolves the selected memory rather than memory zero"
theorem mem_context_store {s : StoreRecord} {i : Instance} {C : TContext} {x : Nat} {mt : MemoryType}
    (hit : instTyping s i C = true) (hx : C.memory[x]? = some mt) :
    ∃ n m, i.memory[x]? = some n ∧ s.mems[n]? = some m ∧ memTyping m mt = true := by
  have hall := (instTyping_spec hit).2.2.2.2.1
  have hlen := all2_size _ _ _ hall
  obtain ⟨hx', _⟩ := List.getElem?_eq_some_iff.1 hx
  have hn := List.getElem?_eq_getElem (l := i.memory) (i := x) (hlen ▸ hx')
  have hag := all2_projection hall hn hx
  simp only [memiAgree, Bool.and_eq_true, decide_eq_true_eq] at hag
  have hm := List.getElem?_eq_getElem hag.1
  exact ⟨_, _, hn, hm, by simpa only [hm] using hag.2⟩

@[rocq_alias iriswasm.store_typing_stabaddr]
theorem store_typing_stabaddr {s : StoreRecord} {f : Frame} {C : TContext} {c a : Nat}
    (h : stabAddr s f c = some a) (hit : instTyping s f.inst C = true) (hst : StoreTyping s) :
    ∃ cl, s.funcs[a]? = some cl := by
  obtain ⟨locs, ⟨types, funcs, tab, mem, globs⟩⟩ := f
  simp only [stabAddr] at h
  cases tab with
  | nil => simp at h
  | cons ta _ =>
    simp only [stabIndex, optionBind] at h
    rcases ht : s.tables[ta]? with _ | t <;> simp [ht] at h
    rcases hd : t.entries.get? c with _ | x <;> simp [hd] at h
    have hd' : t.data[c]? = some x := by simpa only [Tableinst.data_getElem?] using hd
    subst h
    have := (hst.2.1 t (List.mem_of_getElem? ht)).1 _ (List.mem_of_getElem? hd')
    simp [TabclAgree] at this
    exact ⟨_, List.getElem?_eq_getElem this⟩

@[rocq_alias iriswasm.not_lf_br]
def NotLfBr (es : List AdministrativeInstruction) (n : Nat) : Prop :=
  ∀ k lh, ¬ lfilled n lh [basic (.br k)] es = true

@[rocq_alias iriswasm.not_lf_return]
def NotLfReturn (es : List AdministrativeInstruction) (n : Nat) : Prop :=
  ∀ lh, ¬ lfilled n lh [basic .return_] es = true

@[rocq_alias iriswasm.lf_composition]
theorem lf_composition {es : List AdministrativeInstruction} (es2 : List AdministrativeInstruction)
    {e0 : List AdministrativeInstruction} {lh : Lholed} {n : Nat} (h : lfilled n lh e0 es = true) :
    ∃ lh', lfilled n lh' e0 (es ++ es2) = true := by
  rw [lfilled_Ind_Equivalent] at h
  simp only [lfilled_Ind_Equivalent]
  cases h with
  | lfilledBase vs _ es' hc =>
    exact ⟨.base vs (es' ++ es2), by simpa using LfilledInd.lfilledBase vs e0 (es' ++ es2) hc⟩
  | lfilledRec k vs n0 es' lh' es'' _ LI hc h' =>
    exact ⟨.rec_ vs n0 es' lh' (es'' ++ es2),
      by simpa using LfilledInd.lfilledRec k vs n0 es' lh' (es'' ++ es2) _ _ hc h'⟩

@[rocq_alias iriswasm.lf_composition_left]
theorem lf_composition_left {cs es e0 : List AdministrativeInstruction} {lh : Lholed} {n : Nat}
    (hc : constList cs = true) (h : lfilled n lh e0 es = true) :
    ∃ lh', lfilled n lh' e0 (cs ++ es) = true := by
  rw [lfilled_Ind_Equivalent] at h
  simp only [lfilled_Ind_Equivalent]
  cases h with
  | lfilledBase vs _ es' hv =>
    exact ⟨.base (cs ++ vs) es',
      by simpa using LfilledInd.lfilledBase (cs ++ vs) e0 es' (const_list_concat hc hv)⟩
  | lfilledRec k vs n0 es' lh' es'' _ LI hv h' =>
    have := LfilledInd.lfilledRec k (cs ++ vs) n0 es' lh' es'' _ _ (const_list_concat hc hv) h'
    exact ⟨.rec_ (cs ++ vs) n0 es' lh' es'', by simpa using this⟩

@[rocq_alias iriswasm.nlfbr_right]
theorem nlfbr_right {es : List AdministrativeInstruction} {n : Nat}
    {es' : List AdministrativeInstruction} (h : NotLfBr (es ++ es') n) : NotLfBr es n := by
  intro k lh hc
  obtain ⟨lh', h'⟩ := lf_composition es' hc
  exact h k lh' h'

@[rocq_alias iriswasm.nlfret_right]
theorem nlfret_right {es : List AdministrativeInstruction} {n : Nat}
    {es' : List AdministrativeInstruction} (h : NotLfReturn (es ++ es') n) : NotLfReturn es n := by
  intro lh hc
  obtain ⟨lh', h'⟩ := lf_composition es' hc
  exact h lh' h'

@[rocq_alias iriswasm.nlfbr_left]
theorem nlfbr_left {es : List AdministrativeInstruction} {n : Nat}
    {cs : List AdministrativeInstruction} (hc : constList cs = true) (h : NotLfBr (cs ++ es) n) :
    NotLfBr es n := by
  intro k lh h'
  obtain ⟨lh', h''⟩ := lf_composition_left hc h'
  exact h k lh' h''

@[rocq_alias iriswasm.nlfret_left]
theorem nlfret_left {es : List AdministrativeInstruction} {n : Nat}
    {cs : List AdministrativeInstruction} (hc : constList cs = true)
    (h : NotLfReturn (cs ++ es) n) : NotLfReturn es n := by
  intro lh h'
  obtain ⟨lh', h''⟩ := lf_composition_left hc h'
  exact h lh' h''

#rocq_ignore iriswasm.type_progress.split_et_composition "Ltac used only inside type_progress.v"
#rocq_ignore iriswasm.type_progress.invert_e_typing "Ltac used only inside type_progress.v"
#rocq_ignore iriswasm.type_progress.auto_basic "Ltac used only inside type_progress.v"
#rocq_ignore iriswasm.solve_progress_cont "Ltac used only inside type_progress.v"
#rocq_ignore iriswasm.solve_progress "Ltac used only inside type_progress.v"

private theorem reduce_pre {s : StoreRecord} {f : Frame} (pre : List Value)
    {es : List AdministrativeInstruction} (h : ∃ s' f' es', Reduce s f es s' f' es') :
    ∃ s' f' es', Reduce s f (vToEList pre ++ es) s' f' es' :=
  let ⟨_, _, _, h⟩ := h
  ⟨_, _, _, reduce_composition_left (v_to_e_is_const_list pre) h⟩

@[rocq_alias iriswasm.t_progress_be]
theorem t_progress_be {C : TContext} {bes : List BasicInstruction} {ts1 ts2 : List ValueType}
    {vcs : List Value} {lab : List (List ValueType)} {ret : Option (List ValueType)}
    {s : StoreRecord} {f : Frame} (hst : StoreTyping s) (hit : instTyping s f.inst C = true)
    (htype : BeTyping (updLabel (updLocalReturn C (f.locs.map typeof) ret) lab) bes (.tf ts1 ts2))
    (hct : vcs.map typeof = ts1) (hbr : NotLfBr (toEList bes) 0)
    (hret : NotLfReturn (toEList bes) 0) :
    constList (toEList bes) = true ∨
    ∃ s' f' es', Reduce s f (vToEList vcs ++ toEList bes) s' f' es' := by
  suffices H : ∀ C0 bes tf, BeTyping C0 bes tf →
      updLabel (updLocalReturn C (f.locs.map typeof) ret) lab = C0 →
      ∀ ts1 ts2 (vcs : List Value), tf = .tf ts1 ts2 → vcs.map typeof = ts1 →
      NotLfBr (toEList bes) 0 → NotLfReturn (toEList bes) 0 →
      constList (toEList bes) = true ∨
      ∃ s' f' es', Reduce s f (vToEList vcs ++ toEList bes) s' f' es' from
    H _ _ _ htype rfl _ _ _ rfl hct hbr hret
  intro C0 bes tf htype hC0
  induction htype with
  | const => intros; exact .inl rfl
  | unop hop =>
    intro ts1 ts2 vcs htf hct _ _
    injection htf with h1 h2; subst h1 h2
    rcases vcs with _ | ⟨v, _ | ⟨_, _⟩⟩ <;> simp at hct
    exact .inr ⟨_, _, _, .simple (.unop (by simpa [typesAgree] using hct) ((unopTypeOK_iff ..).2 hop))⟩
  | @binop _ t op hop =>
    intro ts1 ts2 vcs htf hct _ _
    injection htf with h1 h2; subst h1 h2
    rcases vcs with _ | ⟨v1, _ | ⟨v2, _ | ⟨_, _⟩⟩⟩ <;> simp at hct
    have h1 : typesAgree t v1 = true := by simpa [typesAgree] using hct.1
    have h2 : typesAgree t v2 = true := by simpa [typesAgree] using hct.2
    have hok := (binopTypeOK_iff ..).2 hop
    rcases hb : appBinop op v1 v2 with _ | v
    · exact .inr ⟨_, _, _, .simple (.binopFailure h1 h2 hok hb)⟩
    · exact .inr ⟨_, _, _, .simple (.binopSuccess h1 h2 hok hb)⟩
  | @testop _ t op hi =>
    intro ts1 ts2 vcs htf hct _ _
    injection htf with h1 h2; subst h1 h2
    rcases vcs with _ | ⟨v, _ | ⟨_, _⟩⟩ <;> simp at hct
    subst hct
    cases v <;> cases op <;> simp [typeof, testopTypeOK, isIntT] at hi
    · exact .inr ⟨_, _, _, .simple .testopI32⟩
    · exact .inr ⟨_, _, _, .simple .testopI64⟩
    · exact .inr ⟨_, _, _, .simple .testopV128⟩
  | relop hop =>
    intro ts1 ts2 vcs htf hct _ _
    injection htf with h1 h2; subst h1 h2
    rcases vcs with _ | ⟨v1, _ | ⟨v2, _ | ⟨_, _⟩⟩⟩ <;> simp at hct
    exact .inr ⟨_, _, _, .simple (.relop (by simpa [typesAgree] using hct.1)
      (by simpa [typesAgree] using hct.2) ((relopTypeOK_iff ..).2 hop))⟩
  | convert hne hform =>
    intro ts1 ts2 vcs htf hct _ _
    injection htf with h1 h2; subst h1 h2
    rcases vcs with _ | ⟨v, _ | ⟨_, _⟩⟩ <;> simp at hct
    subst hct
    have hta : typesAgree (typeof v) v = true := by simp [typesAgree]
    rcases hcv : cvt _ _ v with _ | v'
    · exact .inr ⟨_, _, _, .simple (.convertFailure hta (by simp [convertCond, hne, hform]) hcv)⟩
    · exact .inr ⟨_, _, _, .simple (.convertSuccess hta (by simp [convertCond, hne, hform]) hcv)⟩
  | reinterpret hne hsize =>
    intro ts1 ts2 vcs htf hct _ _
    injection htf with h1 h2; subst h1 h2
    rcases vcs with _ | ⟨v, _ | ⟨_, _⟩⟩ <;> simp at hct
    exact .inr ⟨_, _, _, .simple (.reinterpret (by simp [typesAgree, hct])
      (by simpa [reinterpretCond, hne, Nat.beq_eq_true_eq] using hsize))⟩
  | @truncSat _ dst src sx hd hs =>
    intro ts1 ts2 vcs htf hct _ _
    injection htf with h1 h2; subst h1 h2
    rcases vcs with _ | ⟨v, _ | ⟨_, _⟩⟩ <;> simp at hct
    obtain ⟨w, hw⟩ := truncSat_total (v := v) sx hd (hct.symm ▸ hs)
    exact .inr ⟨_, _, _, .simple (.truncSat (by simp [typesAgree, hct]) hw)⟩
  | unreachable =>
    intro _ _ vcs _ _ _ _
    exact .inr (reduce_pre vcs ⟨_, _, _, .simple .unreachable⟩)
  | nop =>
    intro _ _ vcs _ _ _ _
    exact .inr (reduce_pre vcs ⟨_, _, _, .simple .nop⟩)
  | drop =>
    intro ts1 ts2 vcs htf hct _ _
    injection htf with h1 h2; subst h1 h2
    rcases vcs with _ | ⟨v, _ | ⟨_, _⟩⟩ <;> simp at hct
    exact .inr ⟨_, _, _, .simple .drop⟩
  | select =>
    intro ts1 ts2 vcs htf hct _ _
    injection htf with h1 h2; subst h1 h2
    rcases vcs with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | ⟨_, _⟩⟩⟩⟩ <;> simp at hct
    obtain ⟨-, -, h3⟩ := hct
    rcases v3 with n | _ | _ | _ <;> simp [typeof] at h3
    by_cases hn : n = Int.zero
    · exact .inr ⟨_, _, _, .simple (.selectFalse hn)⟩
    · exact .inr ⟨_, _, _, .simple (.selectTrue hn)⟩
  | vbitselect =>
    intro ts1 ts2 vcs htf hct _ _
    injection htf with h1 h2; subst h1 h2
    rcases vcs with _ | ⟨x, _ | ⟨y, _ | ⟨mask, _ | ⟨_, _⟩⟩⟩⟩ <;> simp at hct
    obtain ⟨hx, hy, hm⟩ := hct
    cases x <;> simp [typeof] at hx
    cases y <;> simp [typeof] at hy
    cases mask <;> simp [typeof] at hm
    exact .inr ⟨_, _, _, .simple .vbitselect⟩
  | @block _ bt _ _ _ hs _ =>
    intro ts1 ts2 vcs htf hct _ _
    injection htf with h1 h2; subst h1 h2 hC0
    exact .inr ⟨_, _, _, .block ((congrArg (expandBlockType · bt) (instTyping_spec hit).1).trans hs)
      (v_to_e_is_const_list vcs) (by simpa only [v_to_e_size, List.length_map] using congrArg List.length hct)⟩
  | @loop _ bt _ _ _ hs _ =>
    intro ts1 ts2 vcs htf hct _ _
    injection htf with h1 h2; subst h1 h2 hC0
    exact .inr ⟨_, _, _, .loop ((congrArg (expandBlockType · bt) (instTyping_spec hit).1).trans hs)
      (v_to_e_is_const_list vcs) (by simpa only [v_to_e_size, List.length_map] using congrArg List.length hct)⟩
  | ifWasm _ _ _ =>
    intro ts1 ts2 vcs htf hct _ _
    injection htf with h1 h2; subst h1 h2
    obtain ⟨v, hv, -, hvt⟩ := typeof_append hct
    rcases v with c | _ | _ | _ <;> simp [typeof] at hvt
    rw [hv, ← v_to_e_cat, List.append_assoc]
    refine .inr (reduce_pre _ ?_)
    by_cases hc : c = Int.zero
    · exact ⟨_, _, _, .simple (.ifFalse hc)⟩
    · exact ⟨_, _, _, .simple (.ifTrue hc)⟩
  | br _ _ =>
    intro _ _ _ _ _ hbr _
    exact absurd (lfilled0_empty _) (hbr _ _)
  | brIf _ _ =>
    intro ts1 ts2 vcs htf hct _ _
    injection htf with h1 h2; subst h1 h2
    obtain ⟨v, hv, -, hvt⟩ := typeof_append hct
    rcases v with c | _ | _ | _ <;> simp [typeof] at hvt
    rw [hv, ← v_to_e_cat, List.append_assoc]
    refine .inr (reduce_pre _ ?_)
    by_cases hc : c = Int.zero
    · exact ⟨_, _, _, .simple (.brIfFalse hc)⟩
    · exact ⟨_, _, _, .simple (.brIfTrue hc)⟩
  | @brTable _ i ins ts t1s t2s _ =>
    intro ts1 ts2 vcs htf hct _ _
    injection htf with h1 h2; subst h1 h2
    rw [← List.append_assoc] at hct
    obtain ⟨v, hv, -, hvt⟩ := typeof_append hct
    rcases v with c | _ | _ | _ <;> simp [typeof] at hvt
    rw [hv, ← v_to_e_cat, List.append_assoc]
    refine .inr (reduce_pre _ ?_)
    by_cases hlt : ins.length > Int.natOfUint c
    · exact ⟨_, _, _, .simple (.brTable hlt (List.getElem?_eq_getElem hlt))⟩
    · exact ⟨_, _, _, .simple (.brTableLength (by omega))⟩
  | return_ _ =>
    intro _ _ _ _ _ _ hret
    exact absurd (lfilled0_empty _) (hret _)
  | call hlen hn =>
    intro _ _ vcs _ _ _ _
    subst hC0
    obtain ⟨a, ha⟩ := func_context_store hit hlen hn
    exact .inr (reduce_pre vcs ⟨_, _, _, .call ha⟩)
  | @callIndirect _ i t1s t2s _ _ _ =>
    intro ts1 ts2 vcs htf hct _ _
    injection htf with h1 h2; subst h1 h2
    obtain ⟨v, hv, -, hvt⟩ := typeof_append hct
    rcases v with c | _ | _ | _ <;> simp [typeof] at hvt
    rw [hv, ← v_to_e_cat, List.append_assoc]
    refine .inr (reduce_pre _ ?_)
    rcases hsa : stabAddr s f (Int.natOfUint c) with _ | a
    · exact ⟨_, _, _, .callIndirectFailure2 hsa⟩
    · obtain ⟨cl, hcl⟩ := store_typing_stabaddr hsa hit hst
      by_cases hty : stypes s f.inst i = some (clType cl)
      · exact ⟨_, _, _, .callIndirectSuccess cl hsa hcl hty⟩
      · exact ⟨_, _, _, .callIndirectFailure1 a cl hsa hcl hty⟩
  | getLocal _ hn =>
    intro ts1 ts2 vcs htf hct _ _
    injection htf with h1 h2; subst h1 h2 hC0
    obtain rfl : vcs = [] := List.map_eq_nil_iff.1 hct
    simp only [updLabel, updLocalReturn] at hn
    obtain ⟨x, hx, -⟩ := TypeProgress.nth_error_map hn
    exact .inr ⟨_, _, _, .getLocal hx⟩
  | setLocal hlen _ =>
    intro ts1 ts2 vcs htf hct _ _
    injection htf with h1 h2; subst h1 h2 hC0
    rcases vcs with _ | ⟨v, _ | ⟨_, _⟩⟩ <;> simp at hct
    simp only [updLabel, updLocalReturn, List.length_map] at hlen
    exact .inr ⟨_, ⟨f.locs.set _ v, f.inst⟩, _, .setLocal rfl hlen rfl⟩
  | teeLocal _ _ =>
    intro ts1 ts2 vcs htf hct _ _
    injection htf with h1 h2; subst h1 h2
    rcases vcs with _ | ⟨v, _ | ⟨_, _⟩⟩ <;> simp at hct
    exact .inr ⟨_, _, _, .simple (.teeLocal rfl)⟩
  | getGlobal hlen hn =>
    intro ts1 ts2 vcs htf hct _ _
    injection htf with h1 h2; subst h1 h2 hC0
    obtain rfl : vcs = [] := List.map_eq_nil_iff.1 hct
    obtain ⟨g, hg, -⟩ := Option.map_eq_some_iff.1 hn
    have hne := glob_context_store hit hlen hg
    rcases hs : sglob s f.inst _ with _ | g'
    · exact absurd hs hne
    · exact .inr ⟨_, _, _, .getGlobal (v := g'.val) (by simp [sglobVal, hs])⟩
  | @setGlobal _ i g t hlen hg _ _ =>
    intro ts1 ts2 vcs htf hct _ _
    injection htf with h1 h2; subst h1 h2 hC0
    rcases vcs with _ | ⟨v, _ | ⟨_, _⟩⟩ <;> simp at hct
    have hne := glob_context_store hit hlen hg
    rcases hsu : supdateGlob s f.inst i v with _ | s'
    · exfalso
      rcases hk : sglobInd s f.inst i with _ | k <;>
        simp_all [supdateGlob, sglob, optionBind, supdateGlobS]
    · exact .inr ⟨_, _, _, .setGlobal hsu⟩
  | @load _ ma tpSx t mt hm hbounds _ =>
    intro ts1 ts2 vcs htf hct _ _
    injection htf with h1 h2; subst h1 h2 hC0
    rcases vcs with _ | ⟨v, _ | ⟨_, _⟩⟩ <;> simp at hct
    obtain ⟨k, rfl, -⟩ := AddressOperand.exists_of_type hct
    obtain ⟨n, m, hsi, hmm, -⟩ := mem_context_store hit hm
    rcases tpSx with _ | ⟨tp, sx⟩
    · rcases hl : load m k.unsigned ma.offset (lengthT t) with _ | bs
      · exact .inr ⟨_, _, _, .loadFailure (k := k) n m hsi hmm hl⟩
      · exact .inr ⟨_, _, _, .loadSuccess (k := k) n m hsi hmm hl⟩
    · have hp := packedTypeOK_of_bounds (a := ma.align) (tp := tp) (t := t) hbounds
      rcases hl : loadPacked sx m k.unsigned ma.offset (lengthTp tp) (lengthT t) with _ | bs
      · exact .inr ⟨_, _, _, .loadPackedFailure (k := k) n m hp hsi hmm hl⟩
      · exact .inr ⟨_, _, _, .loadPackedSuccess (k := k) n m hp hsi hmm hl⟩
  | @store _ ma tp t mt hm hbounds _ =>
    intro ts1 ts2 vcs htf hct _ _
    injection htf with h1 h2; subst h1 h2 hC0
    rcases vcs with _ | ⟨v1, _ | ⟨v, _ | ⟨_, _⟩⟩⟩ <;> simp at hct
    obtain ⟨h1, h2⟩ := hct
    obtain ⟨k, rfl, -⟩ := AddressOperand.exists_of_type h1
    have hta : typesAgree t v = true := by simp [typesAgree, h2]
    obtain ⟨n, m, hsi, hmm, -⟩ := mem_context_store hit hm
    rcases tp with _ | tp
    · rcases hl : store m k.unsigned ma.offset (bits v) (lengthT t) with _ | m'
      · exact .inr ⟨_, _, _, .storeFailure (k := k) n m hta hsi hmm hl⟩
      · exact .inr ⟨_, _, _, .storeSuccess (k := k) m hta hsi hmm hl⟩
    · have hp := packedTypeOK_of_bounds hbounds
      rcases hl : storePacked m k.unsigned ma.offset (bits v) (lengthTp tp) with _ | m'
      · exact .inr ⟨_, _, _, .storePackedFailure (k := k) n m hp hta hsi hmm hl⟩
      · exact .inr ⟨_, _, _, .storePackedSuccess (k := k) m hp hta hsi hmm hl⟩
  | currentMemory hm =>
    intro ts1 ts2 vcs htf hct _ _
    injection htf with h1 h2; subst h1 h2 hC0
    obtain rfl : vcs = [] := List.map_eq_nil_iff.1 hct
    obtain ⟨n, m, hsi, hmm, -⟩ := mem_context_store hit hm
    have hw := (store_typed_mem_agree hst hmm).wellSized
    exact .inr ⟨_, _, _, .currentMemory n m hsi hmm hw.pages_mul hw.pages_fit⟩
  | growMemory _ =>
    intro ts1 ts2 vcs htf hct _ _
    injection htf with h1 h2; subst h1 h2 hC0
    rcases vcs with _ | ⟨v, _ | ⟨_, _⟩⟩ <;> simp at hct
    obtain ⟨c, rfl, -⟩ := AddressOperand.exists_of_type hct
    exact .inr ⟨_, _, _, .growMemoryFailure (c := c)⟩
  | empty => intros; exact .inl rfl
  | composition h1 _ ih1 ih2 =>
    rename_i es e t1s t2s t3s
    intro ts1 ts2 vcs htf hct hbr hret
    injection htf with e1 e2; subst e1 e2
    rw [to_e_list_cat] at hbr hret
    rcases ih1 hC0 _ _ vcs rfl hct (nlfbr_right hbr) (nlfret_right hret) with hc | hr
    · obtain ⟨cs, hcs⟩ := const_es_exists hc
      obtain ⟨rfl, -⟩ := b_e_elim hcs
      have ht := Const_list_typing h1
      subst ht
      have hcb := e_b_inverse (const_list_is_basic (v_to_e_is_const_list cs))
      rw [hcb] at hbr hret
      rw [to_e_list_cat, hcb]
      rcases ih2 hC0 _ _ (vcs ++ cs) rfl (by simp [hct]) (nlfbr_left (v_to_e_is_const_list cs) hbr)
        (nlfret_left (v_to_e_is_const_list cs) hret) with hc2 | hr2
      · exact .inl (const_list_concat (v_to_e_is_const_list cs) hc2)
      · rw [← List.append_assoc, v_to_e_cat]
        exact .inr hr2
    · obtain ⟨s', f', es', hr⟩ := hr
      rw [to_e_list_cat, ← List.append_assoc]
      exact .inr ⟨_, _, _, reduce_composition_right _ hr⟩
  | weakening _ ih =>
    intro ts1 ts2 vcs htf hct hbr hret
    injection htf with e1 e2; subst e1 e2
    obtain ⟨l1, l2, rfl, -, hl2⟩ := List.map_eq_append_iff.1 hct
    rcases ih hC0 _ _ l2 rfl hl2 hbr hret with hc | hr
    · exact .inl hc
    · rw [← v_to_e_cat, List.append_assoc]
      exact .inr (reduce_pre l1 hr)

@[rocq_alias iriswasm.br_reduce]
def BrReduce (es : List AdministrativeInstruction) : Prop :=
  ∃ n lh, lfilled n lh [basic (.br n)] es = true

@[rocq_alias iriswasm.return_reduce]
def ReturnReduce (es : List AdministrativeInstruction) : Prop :=
  ∃ n lh, lfilled n lh [basic .return_] es = true

/-- Classical: Coq derives it from `pickable` enumeration of hole contexts. -/
@[rocq_alias iriswasm.br_reduce_decidable]
noncomputable def br_reduce_decidable (es : List AdministrativeInstruction) :
    Decidable (BrReduce es) := Classical.propDecidable _

/-- Classical: Coq derives it from `pickable` enumeration of hole contexts. -/
@[rocq_alias iriswasm.return_reduce_decidable]
noncomputable def return_reduce_decidable (es : List AdministrativeInstruction) :
    Decidable (ReturnReduce es) := Classical.propDecidable _

@[rocq_alias iriswasm.cat_abcd_a_bc_d]
theorem cat_abcd_a_bc_d {X : Type} (a b c d : List X) : a ++ b ++ c ++ d = a ++ (b ++ c) ++ d := by
  simp

private theorem et_single_basic {s : StoreRecord} {C : TContext} {b : BasicInstruction}
    {tf : FunctionType} (h : ETyping s C [basic b] tf) : BeTyping C [b] tf := by
  simpa [toBList, toBSingle] using et_to_bet (by simp [EsIsBasic, EIsBasic]) h

private theorem et_split3 {s : StoreRecord} {C : TContext} {vs : List AdministrativeInstruction}
    {x : AdministrativeInstruction} {es' : List AdministrativeInstruction} {t2 : List ValueType}
    (h : ETyping s C (vs ++ [x] ++ es') (.tf [] t2)) :
    ∃ t3 t4, ETyping s C vs (.tf [] t3) ∧ ETyping s C [x] (.tf t3 t4) := by
  obtain ⟨ts, t1s', t2s', t3s, h1, -, hvx, -⟩ := e_composition_typing h
  obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 h1.symm
  obtain ⟨ts', a, b, c, h2, -, hvs, hx⟩ := e_composition_typing hvx
  obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 h2.symm
  exact ⟨c, b, hvs, hx⟩

@[rocq_alias iriswasm.br_reduce_label_length]
theorem br_reduce_label_length {n k : Nat} {lh : Lholed} {es : List AdministrativeInstruction}
    {s : StoreRecord} {C : TContext} {ts2 : List ValueType}
    (h : lfilled n lh [basic (.br (n + k))] es = true) (ht : ETyping s C es (.tf [] ts2)) :
    C.label.length > k := by
  rw [lfilled_Ind_Equivalent] at h
  generalize hx : [basic (.br (n + k))] = x at h
  induction h generalizing k s C ts2 with
  | lfilledBase vs _ es' hc =>
    subst hx
    obtain ⟨_, _, -, hb⟩ := et_split3 ht
    obtain ⟨_, _, hlt, -, -⟩ := Break_typing (et_single_basic hb)
    omega
  | lfilledRec k' vs n0 es' lh' es'' _ LI hc _ ih =>
    obtain ⟨_, _, -, hb⟩ := et_split3 ht
    obtain ⟨ts, _, -, -, hLI, -⟩ := Label_typing hb
    have := @ih (k + 1) _ _ _ hLI (by rw [← hx, show k' + (k + 1) = k' + 1 + k by omega])
    simp [updLabel] at this
    omega

@[rocq_alias iriswasm.return_reduce_return_some]
theorem return_reduce_return_some {n : Nat} {lh : Lholed} {es : List AdministrativeInstruction}
    {s : StoreRecord} {C : TContext} {ts2 : List ValueType}
    (h : lfilled n lh [basic .return_] es = true) (ht : ETyping s C es (.tf [] ts2)) :
    C.return_ ≠ none := by
  rw [lfilled_Ind_Equivalent] at h
  generalize hx : [basic .return_] = x at h
  induction h generalizing s C ts2 with
  | lfilledBase vs _ es' hc =>
    subst hx
    obtain ⟨_, _, -, hb⟩ := et_split3 ht
    obtain ⟨_, _, -, hr⟩ := Return_typing (et_single_basic hb)
    simp [hr]
  | lfilledRec k' vs n0 es' lh' es'' _ LI hc _ ih =>
    obtain ⟨_, _, -, hb⟩ := et_split3 ht
    obtain ⟨ts, _, -, -, hLI, -⟩ := Label_typing hb
    simpa [updLabel] using ih hLI hx

@[rocq_alias iriswasm.br_reduce_extract_vs]
theorem br_reduce_extract_vs {n k : Nat} {lh : Lholed} {es : List AdministrativeInstruction}
    {s : StoreRecord} {C : TContext} {ts ts2 : List ValueType}
    (h : lfilled n lh [basic (.br (n + k))] es = true) (ht : ETyping s C es (.tf [] ts2))
    (hn : C.label[k]? = some ts) :
    ∃ vs lh', constList vs = true ∧
      lfilled n lh' (vs ++ [basic (.br (n + k))]) es = true ∧ vs.length = ts.length := by
  rw [lfilled_Ind_Equivalent] at h
  simp only [lfilled_Ind_Equivalent]
  generalize hx : [basic (.br (n + k))] = x at h
  induction h generalizing k s C ts ts2 with
  | lfilledBase vs _ es' hc =>
    subst hx
    obtain ⟨t3, t4, hvs, hb⟩ := et_split3 ht
    obtain ⟨ts0', ts0, -, hp, rfl⟩ := Break_typing (et_single_basic hb)
    have hts : ts0' = ts := by simp [plop2, hn] at hp; first | exact hp | exact hp.symm
    subst hts
    obtain ⟨vs', rfl⟩ := const_es_exists hc
    have hty := Const_list_typing (et_to_bet (const_list_is_basic hc) hvs)
    have hlen := congrArg List.length hty
    simp at hlen
    refine ⟨vToEList (vs'.drop (vs'.length - ts0'.length)),
      .base (vToEList (vs'.take (vs'.length - ts0'.length))) es', v_to_e_is_const_list _, ?_,
      by simp [v_to_e_size]; omega⟩
    have hsplit : vToEList vs' = vToEList (vs'.take (vs'.length - ts0'.length)) ++
        vToEList (vs'.drop (vs'.length - ts0'.length)) := by rw [v_to_e_cat, List.take_append_drop]
    rw [hsplit]
    simpa using LfilledInd.lfilledBase (vToEList (vs'.take (vs'.length - ts0'.length)))
      (vToEList (vs'.drop (vs'.length - ts0'.length)) ++ [basic (.br (0 + k))]) es'
      (v_to_e_is_const_list _)
  | lfilledRec k' vs n0 es' lh' es'' _ LI hc _ ih =>
    obtain ⟨_, _, -, hb⟩ := et_split3 ht
    obtain ⟨ts1, _, -, -, hLI, -⟩ := Label_typing hb
    obtain ⟨vs0, lh2, hc0, hf, hl⟩ := @ih (k + 1) _ _ ts _ hLI (by simpa [updLabel] using hn)
      (by rw [← hx, show k' + (k + 1) = k' + 1 + k by omega])
    exact ⟨vs0, .rec_ vs n0 es' lh2 es'', hc0,
      by simpa using LfilledInd.lfilledRec k' vs n0 es' lh2 es'' _ _ hc hf, hl⟩

@[rocq_alias iriswasm.return_reduce_extract_vs]
theorem return_reduce_extract_vs {n : Nat} {lh : Lholed} {es : List AdministrativeInstruction}
    {s : StoreRecord} {C : TContext} {ts ts2 : List ValueType}
    (h : lfilled n lh [basic .return_] es = true) (ht : ETyping s C es (.tf [] ts2))
    (hn : C.return_ = some ts) :
    ∃ vs lh', constList vs = true ∧
      lfilled n lh' (vs ++ [basic .return_]) es = true ∧ vs.length = ts.length := by
  rw [lfilled_Ind_Equivalent] at h
  simp only [lfilled_Ind_Equivalent]
  generalize hx : [basic .return_] = x at h
  induction h generalizing s C ts ts2 with
  | lfilledBase vs _ es' hc =>
    subst hx
    obtain ⟨t3, t4, hvs, hb⟩ := et_split3 ht
    obtain ⟨ts0', ts0, rfl, hr⟩ := Return_typing (et_single_basic hb)
    have hts : ts0' = ts := by rw [hn] at hr; exact (Option.some.inj hr).symm
    subst hts
    obtain ⟨vs', rfl⟩ := const_es_exists hc
    have hty := Const_list_typing (et_to_bet (const_list_is_basic hc) hvs)
    have hlen := congrArg List.length hty
    simp at hlen
    refine ⟨vToEList (vs'.drop (vs'.length - ts0'.length)),
      .base (vToEList (vs'.take (vs'.length - ts0'.length))) es', v_to_e_is_const_list _, ?_,
      by simp [v_to_e_size]; omega⟩
    have hsplit : vToEList vs' = vToEList (vs'.take (vs'.length - ts0'.length)) ++
        vToEList (vs'.drop (vs'.length - ts0'.length)) := by rw [v_to_e_cat, List.take_append_drop]
    rw [hsplit]
    simpa using LfilledInd.lfilledBase (vToEList (vs'.take (vs'.length - ts0'.length)))
      (vToEList (vs'.drop (vs'.length - ts0'.length)) ++ [basic .return_]) es'
      (v_to_e_is_const_list _)
  | lfilledRec k' vs n0 es' lh' es'' _ LI hc _ ih =>
    obtain ⟨_, _, -, hb⟩ := et_split3 ht
    obtain ⟨ts1, _, -, -, hLI, -⟩ := Label_typing hb
    obtain ⟨vs0, lh2, hc0, hf, hl⟩ := @ih _ _ ts _ hLI (by simpa [updLabel] using hn) hx
    exact ⟨vs0, .rec_ vs n0 es' lh2 es'', hc0,
      by simpa using LfilledInd.lfilledRec k' vs n0 es' lh2 es'' _ _ hc hf, hl⟩

@[rocq_alias iriswasm.le_add]
theorem le_add {n m : Nat} (h : n ≤ m) : ∃ k, m = n + k := by
  exact ⟨m - n, by omega⟩

@[rocq_alias iriswasm.s_typing_lf_br]
theorem s_typing_lf_br {s : StoreRecord} {rs : Option (List ValueType)} {f : Frame}
    {es : List AdministrativeInstruction} {ts : List ValueType} (h : STyping s rs f es ts) :
    ∀ n lh k, lfilled n lh [basic (.br k)] es = true → k < n := by
  intro n lh k hf
  obtain ⟨hft, rfl, ht, -⟩ := h
  obtain ⟨hit, -, -⟩ := hft
  rcases Nat.lt_or_ge k n with hk | hk
  · exact hk
  · obtain ⟨j, rfl⟩ := le_add hk
    have := br_reduce_label_length hf ht
    simp [updReturn, updLocal, inst_t_context_label_empty hit] at this

@[rocq_alias iriswasm.s_typing_lf_return]
theorem s_typing_lf_return {s : StoreRecord} {f : Frame} {es : List AdministrativeInstruction}
    {ts : List ValueType} (h : STyping s none f es ts) : ∀ n, NotLfReturn es n := by
  intro n lh hf
  obtain ⟨hft, rfl, ht, -⟩ := h
  exact return_reduce_return_some hf ht (by simp [updReturn])

namespace TypeProgress

@[rocq_alias iriswasm.type_progress.find_first_some]
def findFirstSome {A : Type} : List (Option A) → Option A
  | [] => none
  | some e :: _ => some e
  | none :: q => findFirstSome q

@[rocq_alias iriswasm.type_progress.first_instr_instr]
def firstInstrInstr (e : AdministrativeInstruction) : Option (AdministrativeInstruction × Nat) :=
  match e with
  | .basic (.const _) => none
  | .label _ _ LI =>
    match findFirstSome (LI.map firstInstrInstr) with
    | some (e', i) => some (e', i + 1)
    | none => some (e, 0)
  | .local _ _ LI =>
    match findFirstSome (LI.map firstInstrInstr) with
    | some (e', i) => some (e', i + 1)
    | none => some (e, 0)
  | _ => some (e, 0)

@[rocq_alias iriswasm.type_progress.first_instr]
def firstInstr (es : List AdministrativeInstruction) : Option (AdministrativeInstruction × Nat) :=
  findFirstSome (es.map firstInstrInstr)

private theorem firstInstr_cons (e : AdministrativeInstruction)
    (es : List AdministrativeInstruction) :
    firstInstr (e :: es) = (firstInstrInstr e).or (firstInstr es) := by
  simp only [firstInstr, List.map_cons]
  cases firstInstrInstr e <;> simp [findFirstSome]

private theorem firstInstrInstr_label (n : Nat) (es LI : List AdministrativeInstruction) :
    firstInstrInstr (.label n es LI) = some ((firstInstr LI).elim (.label n es LI, 0)
      fun p => (p.1, p.2 + 1)) := by
  rw [firstInstrInstr]; simp only [firstInstr]; split <;> simp_all

private theorem firstInstrInstr_local (n : Nat) (f : Frame) (LI : List AdministrativeInstruction) :
    firstInstrInstr (.local n f LI) = some ((firstInstr LI).elim (.local n f LI, 0)
      fun p => (p.1, p.2 + 1)) := by
  rw [firstInstrInstr]; simp only [firstInstr]; split <;> simp_all

@[rocq_alias iriswasm.type_progress.first_instr_const]
theorem first_instr_const {vs : List AdministrativeInstruction}
    (es : List AdministrativeInstruction)
    (hvs : constList vs = true) : firstInstr (vs ++ es) = firstInstr es := by
  induction vs with
  | nil => rfl
  | cons a l ih =>
    simp only [constList, List.all_cons, Bool.and_eq_true] at hvs
    have ha : firstInstrInstr a = none := by
      match a, hvs.1 with
      | .basic (.const _), _ => simp [firstInstrInstr]
    rw [List.cons_append, firstInstr_cons, ha, Option.none_or]
    exact ih hvs.2

@[rocq_alias iriswasm.type_progress.first_instr_app]
theorem first_instr_app {e : List AdministrativeInstruction} {a : AdministrativeInstruction × Nat}
    (es' : List AdministrativeInstruction) (h : firstInstr e = some a) :
    firstInstr (e ++ es') = some a := by
  induction e with
  | nil => simp [firstInstr, findFirstSome] at h
  | cons x l ih =>
    rw [List.cons_append, firstInstr_cons]
    rw [firstInstr_cons] at h
    cases hx : firstInstrInstr x <;> simp_all

@[rocq_alias iriswasm.type_progress.starts_with_lfilled]
theorem starts_with_lfilled {e : AdministrativeInstruction} {i : Nat}
    {es : List AdministrativeInstruction} {k : Nat} {lh : Lholed}
    {les : List AdministrativeInstruction} (h1 : firstInstr es = some (e, i))
    (h2 : lfilled k lh es les = true) : firstInstr les = some (e, i + k) := by
  rw [lfilled_Ind_Equivalent] at h2
  induction h2 generalizing i with
  | lfilledBase vs _ es' hc =>
    rw [List.append_assoc, first_instr_const _ hc]
    simpa using first_instr_app es' h1
  | lfilledRec k' vs n0 es' lh' es'' _ LI hc _ ih =>
    rw [List.append_assoc, first_instr_const _ hc, List.singleton_append, firstInstr_cons,
      firstInstrInstr_label, ih h1]
    simp; omega

@[rocq_alias iriswasm.type_progress.lfilled_implies_starts]
theorem lfilled_implies_starts {k : Nat} {lh : Lholed} {e : AdministrativeInstruction}
    {es : List AdministrativeInstruction} (hl : ∀ n es' LI, e ≠ .label n es' LI)
    (hloc : ∀ n es' LI, e ≠ .local n es' LI) (hc : isConst e = true → False)
    (h : lfilled k lh [e] es = true) : firstInstr es = some (e, k) := by
  rw [lfilled_Ind_Equivalent] at h
  have he : firstInstrInstr e = some (e, 0) := by
    cases e with
    | basic b => cases b <;> simp_all [firstInstrInstr, isConst]
    | label => exact absurd rfl (hl _ _ _)
    | «local» => exact absurd rfl (hloc _ _ _)
    | _ => simp [firstInstrInstr]
  generalize hx : [e] = x at h
  induction h with
  | lfilledBase vs _ es' hc =>
    subst hx
    rw [List.append_assoc, first_instr_const _ hc]
    simp [firstInstr_cons, he]
  | lfilledRec k' vs n0 es' lh' es'' _ LI hc _ ih =>
    rw [List.append_assoc, first_instr_const _ hc, List.singleton_append, firstInstr_cons,
      firstInstrInstr_label, ih hx]
    simp

end TypeProgress

open TypeProgress

private theorem prefix_progress {s : StoreRecord} {f : Frame}
    {cs es : List AdministrativeInstruction} (hc : constList cs = true)
    (h : TerminalForm es ∨ ∃ s' f' es', Reduce s f es s' f' es') :
    TerminalForm (cs ++ es) ∨ ∃ s' f' es', Reduce s f (cs ++ es) s' f' es' := by
  rcases h with (h | rfl) | ⟨s', f', es', h⟩
  · exact .inl (.inl (const_list_concat hc h))
  · by_cases hcs : cs = []
    · subst hcs; exact .inl terminal_trap
    · exact .inr ⟨s, f, _, .simple (reduce_trap_left hc hcs)⟩
  · exact .inr ⟨_, _, _, reduce_composition_left hc h⟩

private theorem lfilled_label_rec {n0 : Nat} {lh : Lholed}
    {es0 es e0s : List AdministrativeInstruction}
    (n : Nat) (hf : lfilled n0 lh es0 es = true) :
    lfilled (n0 + 1) (.rec_ [] n e0s lh []) es0 [.label n e0s es] = true := by
  rw [lfilled_Ind_Equivalent] at hf ⊢
  simpa using LfilledInd.lfilledRec n0 [] n e0s lh [] _ _ rfl hf

@[rocq_alias iriswasm.t_progress_e]
theorem t_progress_e {s : StoreRecord} {C C' : TContext} {f : Frame} {vcs : List Value}
    {es : List AdministrativeInstruction} {tf : FunctionType} {ts1 ts2 : List ValueType}
    {lab : List (List ValueType)} {ret : Option (List ValueType)}
    (ht : ETyping s C es tf) (htf : tf = .tf ts1 ts2)
    (hC : C = updLabel (updLocalReturn C' (f.locs.map typeof) ret) lab)
    (hit : instTyping s f.inst C' = true) (hct : vcs.map typeof = ts1) (hst : StoreTyping s)
    (hbr : ∀ n lh k, lfilled n lh [basic (.br k)] es = true → k < n)
    (hret : ∀ n, NotLfReturn es n)
    (hch : ∀ tf h vcs n, firstInstr es = some (.callHost tf h vcs, n) → False) :
    TerminalForm (vToEList vcs ++ es) ∨
    ∃ s' f' es', Reduce s f (vToEList vcs ++ es) s' f' es' := by
  refine ETyping.rec
    (motive_1 := fun C es (tf : FunctionType) _ => ∀ (f : Frame) (C' : TContext) (vcs : List Value)
      (ts1 ts2 : List ValueType) (lab : List (List ValueType)) (ret : Option (List ValueType)),
      tf = .tf ts1 ts2 → C = updLabel (updLocalReturn C' (f.locs.map typeof) ret) lab →
      instTyping s f.inst C' = true → vcs.map typeof = ts1 → StoreTyping s →
      (∀ n lh k, lfilled n lh [basic (.br k)] es = true → k < n) →
      (∀ n, NotLfReturn es n) →
      (∀ tf h vcs n, firstInstr es = some (.callHost tf h vcs, n) → False) →
      TerminalForm (vToEList vcs ++ es) ∨
      ∃ s' f' es', Reduce s f (vToEList vcs ++ es) s' f' es')
    (motive_2 := fun _ f es ts _ => StoreTyping s →
      (∀ n lh k, lfilled n lh [basic (.br k)] es = true → k < n) →
      (∀ n, NotLfReturn es n) →
      (∀ tf h vcs n, firstInstr es = some (.callHost tf h vcs, n) → False) →
      (constList es = true ∧ es.length = ts.length) ∨ es = [trap] ∨
      ∃ s' f' es', Reduce s f es s' f' es')
    ?a ?comp ?weak ?trap ?loc ?inv ?lab ?ch ?st ht f C' vcs ts1 ts2 lab ret htf hC hit hct hst hbr
    hret hch
  case a =>
    intro C bes tf hb f C' vcs ts1 ts2 lab ret htf hC hit hct hst hbr hret _
    subst htf hC
    rcases t_progress_be hst hit hb hct (fun k lh h => absurd (hbr 0 lh k h) (Nat.not_lt_zero _))
      (hret 0) with h | h
    · exact .inl (.inl (const_list_concat (v_to_e_is_const_list _) h))
    · exact .inr h
  case comp =>
    intro C es e t1s t2s t3s h1 _ ih1 ih2 f C' vcs ts1 ts2 lab ret htf hC hit hct hst hbr hret hch
    injection htf with e1 e2; subst e1 e2
    rcases ih1 f C' vcs _ t2s lab ret rfl hC hit hct hst
      (fun n lh k h => let ⟨lh', h'⟩ := lf_composition [e] h; hbr n lh' k h')
      (fun n => nlfret_right (hret n))
      (fun tf h vcs n hf => hch tf h vcs n (first_instr_app [e] hf)) with
      (hc | htrap) | ⟨s', f', es', hr⟩
    · obtain ⟨-, hc2⟩ := const_list_split hc
      obtain ⟨esv, rfl⟩ := const_es_exists hc2
      have hty := Const_list_typing (et_to_bet (const_list_is_basic hc2) h1)
      subst hty
      have hcv := v_to_e_is_const_list esv
      rcases ih2 f C' (vcs ++ esv) _ _ lab ret rfl hC hit (by simp [hct]) hst
        (fun n lh k h => let ⟨lh', h'⟩ := lf_composition_left hcv h; hbr n lh' k h')
        (fun n => nlfret_left hcv (hret n))
        (fun tf h vcs n hf => hch tf h vcs n (by rw [first_instr_const _ hcv]; exact hf)) with
        (hc' | ht') | hr'
      · rw [← List.append_assoc, v_to_e_cat]
        exact .inl (.inl hc')
      · obtain ⟨h0, rfl⟩ := extract_list1 ht'
        rw [← v_to_e_cat] at h0
        simp [vToEList] at h0
        obtain ⟨rfl, rfl⟩ := h0
        exact .inl (.inr rfl)
      · rw [← List.append_assoc, v_to_e_cat]
        exact .inr hr'
    · obtain ⟨h0, rfl⟩ := v_e_trap (v_to_e_is_const_list _) htrap
      rw [h0]
      exact .inr ⟨s, f, [trap], .simple (.trap (.base [] [e]) (by simp)
        (by simp [lfilled, lfill, constList]))⟩
    · rw [← List.append_assoc]
      exact .inr ⟨_, _, _, reduce_composition_right [e] hr⟩
  case weak =>
    intro C es ts t1s t2s _ ih f C' vcs ts1 ts2 lab ret htf hC hit hct hst hbr hret hch
    injection htf with e1 e2; subst e1 e2
    obtain ⟨l1, l2, rfl, -, hl2⟩ := List.map_eq_append_iff.1 hct
    rw [← v_to_e_cat, List.append_assoc]
    exact prefix_progress (v_to_e_is_const_list l1)
      (ih f C' l2 _ _ lab ret rfl hC hit hl2 hst hbr hret hch)
  case trap =>
    intro C tf f C' vcs _ _ _ _ _ _ _ _ _ _ _ _
    exact prefix_progress (v_to_e_is_const_list vcs) (.inl terminal_trap)
  case loc =>
    intro C n f0 es ts hs hlen ih f C' vcs ts1 ts2 lab ret htf hC hit hct hst hbr hret hch
    injection htf with e1 e2; subst e1 e2
    obtain rfl : vcs = [] := List.map_eq_nil_iff.1 hct
    right
    by_cases hrr : ReturnReduce es
    · obtain ⟨n0, lh, hf⟩ := hrr
      obtain ⟨hft, hCC, het, -⟩ := hs
      obtain ⟨vs, lh', hcv, hfv, hlv⟩ := return_reduce_extract_vs hf het (by subst hCC; rfl)
      exact ⟨s, f, vs, .simple (.return_ n0 lh' hcv (hlv.trans hlen) hfv)⟩
    · rcases ih hst (s_typing_lf_br hs) (fun n0 lh hf => hrr ⟨n0, lh, hf⟩)
        (fun tf h vcs n0 hf => hch tf h vcs (n0 + 1)
          (by rw [firstInstr_cons, firstInstrInstr_local, hf]; rfl)) with
        ⟨hcl, hlen'⟩ | rfl | ⟨s', f', es', hr⟩
      · exact ⟨s, f, es, .simple (.localConst hcl (hlen'.trans hlen))⟩
      · exact ⟨s, f, [trap], .simple .localTrap⟩
      · exact ⟨s', f, [.local n f' es'], .local hr⟩
  case inv =>
    intro a C cl tf hcl hclt f C' vcs ts1 ts2 lab ret htf _ _ hct _ _ _ _
    subst htf
    right
    cases hclt with
    | native _ htf' _ _ =>
      subst htf'
      exact ⟨s, f, _, .invokeNative (f' := ⟨vcs ++ nZeros _, _⟩) _ ts1 _ vcs vcs.length
        _ _ _ hcl rfl rfl rfl rfl (by rw [← hct, List.length_map]) rfl rfl rfl rfl⟩
    | host =>
      exact ⟨s, f, _, .invokeHost _ ts2.length vcs.length hcl rfl rfl rfl
        (by rw [← hct, List.length_map]) rfl⟩
  case lab =>
    intro C e0s es ts t2s n _ hes hlen _ ihes f C' vcs ts1 ts2 lab ret htf hC hit hct hst hbr
      hret hch
    injection htf with e1 e2; subst e1 e2
    obtain rfl : vcs = [] := List.map_eq_nil_iff.1 hct
    right
    by_cases hbrr : BrReduce es
    · obtain ⟨n0, lh, hf⟩ := hbrr
      obtain ⟨vs, lh', hcv, hfv, hlv⟩ :=
        br_reduce_extract_vs (k := 0) (ts := ts) hf hes (by simp [updLabel])
      exact ⟨s, f, _, .simple (.br n0 lh' hcv (hlv.trans hlen) hfv)⟩
    · subst hC
      rcases ihes f C' [] [] t2s ([ts] ++ lab) ret rfl rfl hit rfl hst
        (fun n0 lh k hf => by
          have := hbr (n0 + 1) _ k (lfilled_label_rec n hf)
          rcases Nat.lt_or_ge k n0 with h | h
          · exact h
          · exfalso
            obtain rfl : k = n0 := Nat.le_antisymm (Nat.lt_succ_iff.1 this) h
            exact hbrr ⟨k, lh, hf⟩)
        (fun n0 lh hf => hret (n0 + 1) _ (lfilled_label_rec n hf))
        (fun tf h vcs n0 hf => hch tf h vcs (n0 + 1)
          (by rw [firstInstr_cons, firstInstrInstr_label, hf]; rfl)) with
        (hc | ht) | ⟨s', f', es', hr⟩
      · exact ⟨s, f, es, .simple (.labelConst hc)⟩
      · have ht' : es = [trap] := ht
        subst ht'
        exact ⟨s, f, [trap], .simple .labelTrap⟩
      · exact ⟨s', f', [.label n e0s es'], .label es es' 1 (.rec_ [] n e0s (.base [] []) []) hr
          (label_lfilled1 n es e0s) (label_lfilled1 n es' e0s)⟩
  case ch =>
    intro C t1s t2s h vs _ f C' vcs ts1 ts2 lab ret _ _ _ _ _ _ _ hch
    exact (hch (.tf t1s t2s) h vs 0 (by rw [firstInstr_cons]; simp [firstInstrInstr, firstInstr,
      findFirstSome])).elim
  case st =>
    intro f es rs ts C C0 hft hCC het _ ih hst hbr hret hch
    cases hft with
    | frameTyping hit' hfi hfl =>
      rename_i i tvs C1
      have hloc := inst_t_context_local_empty hit'
      rcases ih f C1 [] [] ts C1.label rs rfl
        (by subst hCC hfl; cases C1; simp_all [updReturn, updLocal, updLabel, updLocalReturn])
        (by rw [hfi]; exact hit') rfl hst hbr hret hch with (hc | ht) | hr
      · refine .inl ⟨hc, ?_⟩
        obtain ⟨esv, rfl⟩ := const_es_exists hc
        have := Const_list_typing (et_to_bet (const_list_is_basic hc) het)
        simp [this, v_to_e_size]
      · exact .inr (.inl ht)
      · exact .inr (.inr hr)

@[rocq_alias iriswasm.t_progress]
theorem t_progress {s : StoreRecord} {f : Frame} {es : List AdministrativeInstruction}
    {ts : List ValueType} (h : ConfigTyping s f es ts) :
    TerminalForm es ∨ (∃ tf h vcs n, firstInstr es = some (.callHost tf h vcs, n)) ∨
    ∃ s' f' es', Reduce s f es s' f' es' := by
  obtain ⟨hst, hs⟩ := h
  by_cases hch : ∃ tf h vcs n, firstInstr es = some (.callHost tf h vcs, n)
  · exact .inr (.inl hch)
  have hs' := hs
  obtain ⟨hft, hCC, het, -⟩ := hs
  cases hft with
  | frameTyping hit' hfi hfl =>
    rename_i i tvs C1
    have hloc := inst_t_context_local_empty hit'
    rcases t_progress_e (vcs := []) het rfl (C' := C1) (f := f) (ret := none) (lab := C1.label)
      (by subst hCC hfl; cases C1; simp_all [updReturn, updLocal, updLabel, updLocalReturn])
      (by rw [hfi]; exact hit') rfl hst (s_typing_lf_br hs') (s_typing_lf_return hs')
      (fun tf h vcs n hf => hch ⟨tf, h, vcs, n, hf⟩) with h | h
    · exact .inl h
    · exact .inr (.inr h)

end Wasm
