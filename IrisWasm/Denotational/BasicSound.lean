import IrisWasm.Denotational.Observation

namespace IrisWasm.Denotational

open Wasm

/-- Put back the operands of the redex before lifting it under the unused stack and tail. -/
private theorem reflect_emit (used : List Value) {left : List Value} {e : AdministrativeInstruction}
    {out tail : Expr} {σ σ₁ σ' : State} {r : Front} (h : Runs (emit left out tail) σ₁ r σ')
    (step : Reduce σ.1 ⟨σ.2.1, σ.2.2⟩ (vToEList used.reverse ++ [e])
      σ₁.1 ⟨σ₁.2.1, σ₁.2.2⟩ out) :
    Represents (vToEList (used ++ left).reverse ++ e :: tail) σ r σ' := by
  obtain ⟨rfl, rfl⟩ := runs_ret.mp h
  simpa [Represents, vToEList, List.append_assoc] using wrap_reduce left.reverse tail step

private theorem reflect_args (vs : List Value) (n : Nat) {e : AdministrativeInstruction}
    {out tail : Expr} {σ σ₁ σ' : State} {r : Front} (h : Runs (emit (vs.drop n) out tail) σ₁ r σ')
    (step : Reduce σ.1 ⟨σ.2.1, σ.2.2⟩ (vToEList (vs.take n).reverse ++ [e])
      σ₁.1 ⟨σ₁.2.1, σ₁.2.2⟩ out) :
    Represents (vToEList vs.reverse ++ e :: tail) σ r σ' := by
  simpa only [List.take_append_drop] using reflect_emit (vs.take n) h step

/-- Split away a malformed operand shape. Only the matching redex has a leaf. -/
local macro "operands" h:ident : tactic =>
  `(tactic| (simp only [basicLayer] at $h:ident; split at $h:ident <;>
    try exact False.elim (runs_stuck $h)))

local macro "leaf" args:term:max h:ident : tactic =>
  `(tactic| apply reflect_emit $args $h)

private theorem reflect_read {α : Type} {x y : α} {σ σ' : State}
    (h : Yields (pure (x, σ)) (y, σ')) : y = x ∧ σ' = σ := by
  simpa only [yields_ret, Prod.mk.injEq] using h

local macro "request" h:ident " as " x:ident st:ident hx:ident : tactic =>
  `(tactic| (obtain ⟨$x, $st, $hx, $h⟩ := runs_vis.mp $h; simp only [handle, withMemory] at $hx:ident))

local macro "readReply" hx:ident : tactic =>
  `(tactic| (obtain ⟨he, hs⟩ := reflect_read $hx; subst_vars))

local macro "lookup" hx:ident : tactic =>
  `(tactic| (split at $hx:ident <;> try exact False.elim (yields_stuck $hx)))

local macro "arity" h:ident : tactic =>
  `(tactic| (simp only [withArgs] at $h:ident; split at $h:ident <;>
    try exact False.elim (runs_stuck $h)))

private theorem args_length {n : Nat} {vs : List Value} (h : n ≤ vs.length) :
    (vs.take n).reverse.length = n := by simp [List.length_take, Nat.min_eq_left h]

theorem invoke_sound {a vs tail σ σ' r} (h : Runs (invokeLayer a vs tail) σ r σ') :
    Represents (vToEList vs.reverse ++ .invoke a :: tail) σ r σ' := by
  rcases σ with ⟨s, locs, inst⟩
  unfold invokeLayer at h
  request h as cl st hc
  lookup hc
  readReply hc
  split at h
  · arity h
    apply reflect_args _ _ h
    exact .invokeNative _ _ _ _ _ _ _ _ (by assumption) rfl rfl (args_length (by assumption))
      rfl rfl rfl rfl rfl rfl
  · arity h
    apply reflect_args _ _ h
    exact .invokeHost _ _ _ (by assumption) rfl rfl (args_length (by assumption)) rfl rfl

theorem basic_sound {b : BasicInstruction} {vs : List Value} {tail : Expr} {k : List Value → Layer}
    {σ σ' : State} {r : Front} (hn : ∀ v, b ≠ .const v)
    (h : Runs (basicLayer b vs tail k) σ r σ') :
    Represents (vToEList vs.reverse ++ .basic b :: tail) σ r σ' := by
  rcases σ with ⟨s, locs, inst⟩
  cases b with
  | const v => exact False.elim (hn v rfl)
  | nop => leaf [] h; exact .simple .nop
  | unreachable => leaf [] h; exact .simple .unreachable
  | drop => operands h; leaf [_] h; exact .simple .drop
  | unop =>
    operands h
    split at h
    · rename_i hok
      simp only [Bool.and_eq_true] at hok
      obtain ⟨ht, hop⟩ := hok
      leaf [_] h; exact .simple (.unop ht hop)
    · exact False.elim (runs_stuck h)
  | relop =>
    operands h
    split at h
    · rename_i hok
      simp only [Bool.and_eq_true] at hok
      leaf [_, _] h; exact .simple (.relop hok.1.1 hok.1.2 hok.2)
    · exact False.elim (runs_stuck h)
  | teeLocal => operands h; leaf [_] h; exact .simple (.teeLocal rfl)
  | binop t op =>
    operands h
    rename_i v2 v1 ws
    split at h
    · rename_i hok
      simp only [Bool.and_eq_true] at hok
      obtain ⟨⟨h1, h2⟩, hop⟩ := hok
      cases he : appBinop op v1 v2 <;> simp only [he, resultCode] at h <;> leaf [_, _] h
      · exact .simple (.binopFailure h1 h2 hop he)
      · exact .simple (.binopSuccess h1 h2 hop he)
    · exact False.elim (runs_stuck h)
  | testop =>
    operands h <;> leaf [_] h
    · exact .simple .testopI32
    · exact .simple .testopI64
    · exact .simple .testopV128
  | vbitselect => operands h; leaf [_, _, _] h; exact .simple .vbitselect
  | select =>
    operands h
    split at h <;> leaf [_, _, _] h
    · exact .simple (.selectFalse (by assumption))
    · exact .simple (.selectTrue (by assumption))
  | if_ =>
    operands h
    split at h <;> leaf [_] h
    · exact .simple (.ifFalse (by assumption))
    · exact .simple (.ifTrue (by assumption))
  | brIf =>
    operands h
    split at h <;> leaf [_] h
    · exact .simple (.brIfFalse (by assumption))
    · exact .simple (.brIfTrue (by assumption))
  | brTable iss i =>
    operands h
    rename_i c ws
    by_cases hl : Wasm.Int.natOfUint c < iss.length
    · rw [List.getElem?_eq_getElem hl] at h
      leaf [_] h
      exact .simple (.brTable hl (List.getElem?_eq_getElem hl))
    · have hl' := Nat.le_of_not_gt hl
      rw [List.getElem?_eq_none hl'] at h
      leaf [_] h
      exact .simple (.brTableLength hl')
  | cvtop t2 op t1 sx =>
    operands h
    rename_i v ws
    split at h <;> try exact False.elim (runs_stuck h)
    split at h
    · split at h <;> try exact False.elim (runs_stuck h)
      cases he : cvt t2 sx v <;> simp only [he, resultCode] at h <;> leaf [_] h
      · exact .simple (.convertFailure (by assumption) (by assumption) he)
      · exact .simple (.convertSuccess (by assumption) (by assumption) he)
    · split at h <;> try exact False.elim (runs_stuck h)
      leaf [_] h; exact .simple (.reinterpret (by assumption) (by assumption))
    · exact False.elim (runs_stuck h)
    · split at h
      · leaf [_] h; exact .simple (.truncSat (by assumption) (by assumption))
      · exact False.elim (runs_stuck h)
    · exact False.elim (runs_stuck h)
  | block bt es | loop bt es =>
    simp only [basicLayer, runs_withBlockType] at h
    obtain ⟨⟨ins, outs⟩, hb, h⟩ := h
    arity h
    apply reflect_args _ _ h
    first
    | apply Reduce.block hb (v_to_e_is_const_list _)
    | apply Reduce.loop hb (v_to_e_is_const_list _)
    simpa [vToEList] using args_length (by assumption : ins.length ≤ vs.length)
  | br =>
    obtain ⟨rfl, rfl⟩ := runs_ret.mp h
    exact ⟨by simp [ofVal, vfill, List.append_assoc], rfl⟩
  | return_ =>
    obtain ⟨rfl, rfl⟩ := runs_ret.mp h
    exact ⟨by simp [ofVal, sfill, List.append_assoc], rfl⟩
  | call =>
    simp only [basicLayer] at h
    request h as a st ha
    lookup ha; readReply ha
    leaf [] h; exact .call (by assumption)
  | getLocal =>
    simp only [basicLayer] at h
    request h as v st hv
    lookup hv; readReply hv
    leaf [] h; exact .getLocal (by assumption)
  | getGlobal =>
    simp only [basicLayer] at h
    request h as v st hv
    lookup hv; readReply hv
    leaf [] h; exact .getGlobal (by assumption)
  | setLocal =>
    operands h
    request h as u st hu
    lookup hu; readReply hu
    leaf [_] h; exact .setLocal rfl (by assumption) rfl
  | setGlobal =>
    operands h
    request h as u st hu
    lookup hu; readReply hu
    leaf [_] h; exact .setGlobal (by assumption)
  | callIndirect i =>
    operands h
    rename_i n ws
    request h as oa st ha
    readReply ha
    cases he : stabAddr s ⟨locs, inst⟩ (Wasm.Int.natOfUint n) <;> simp only [he] at h
    · leaf [_] h; exact .callIndirectFailure2 he
    · request h as cl st hc
      lookup hc; readReply hc
      request h as ot st ht
      readReply ht
      split at h <;> leaf [_] h
      · exact .callIndirectSuccess _ he (by assumption) (by assumption)
      · exact .callIndirectFailure1 _ _ he (by assumption) (by assumption)
  | currentMemory =>
    simp only [basicLayer] at h
    request h as n st hn'
    lookup hn'; lookup hn'
    split at hn' <;> try exact False.elim (yields_stuck hn')
    rename_i hs
    readReply hn'
    leaf [] h; exact .currentMemory _ _ (by assumption) (by assumption) hs.1 hs.2
  | growMemory =>
    operands h
    split at h <;> try exact False.elim (runs_stuck h)
    rename_i d hd
    obtain rfl := AddressOperand.ofValue?_eq_some.mp hd
    request h as n st hg
    repeat' (split at hg <;> try (readReply hg; leaf [_] h; exact .growMemoryFailure))
    obtain ⟨ok, hg⟩ := yields_br.mp hg
    cases ok <;> readReply hg <;> leaf [_] h
    · exact .growMemoryFailure
    · exact .growMemorySuccess _ (by assumption) (by assumption) rfl (by assumption) (by assumption)
  | load t pack ma =>
    operands h
    split at h <;> try exact False.elim (runs_stuck h)
    rename_i addr hv
    obtain rfl := AddressOperand.ofValue?_eq_some.mp hv
    split at h <;> try exact False.elim (runs_stuck h)
    request h as v st hv
    lookup hv; lookup hv
    rename_i m hm
    readReply hv
    rcases pack with _ | ⟨tp, sx⟩
    · cases he : load m addr.unsigned ma.offset (lengthT t) <;>
        simp only [he, Option.map_none, Option.map_some, resultCode] at h <;> leaf [_] h
      · exact .loadFailure _ _ (by assumption) hm he
      · exact .loadSuccess _ _ (by assumption) hm he
    · cases he : loadPacked sx m addr.unsigned ma.offset (lengthTp tp) (lengthT t) <;>
        simp only [he, Option.map_none, Option.map_some, resultCode] at h <;> leaf [_] h
      · exact .loadPackedFailure _ _ (by assumption) (by assumption) hm he
      · exact .loadPackedSuccess _ _ (by assumption) (by assumption) hm he
  | store t pack ma =>
    operands h
    split at h <;> try exact False.elim (runs_stuck h)
    rename_i addr hv
    obtain rfl := AddressOperand.ofValue?_eq_some.mp hv
    split at h <;> try exact False.elim (runs_stuck h)
    rename_i hok
    simp only [Bool.and_eq_true] at hok
    obtain ⟨ht, hp⟩ := hok
    request h as ok st hw
    lookup hw; lookup hw
    cases pack <;> split at hw <;> readReply hw <;> leaf [_, _] h
    · exact .storeFailure _ _ (by assumption) (by assumption) (by assumption) (by assumption)
    · exact .storeSuccess _ (by assumption) (by assumption) (by assumption) (by assumption)
    · exact .storePackedFailure _ _ hp ht (by assumption) (by assumption) (by assumption)
    · exact .storePackedSuccess _ hp ht (by assumption) (by assumption) (by assumption)

end IrisWasm.Denotational
