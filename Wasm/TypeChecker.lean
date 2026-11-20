/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import Wasm.Typing

/-! Port of `theories/type_checker.v`: the executable Wasm type checker. -/

namespace Wasm

#rocq_ignore iriswasm.checker_type_aux_beq "deriving DecidableEq"
#rocq_ignore iriswasm.checker_type_aux_eq_dec "deriving DecidableEq"
#rocq_ignore iriswasm.checker_type_aux_eqb "deriving DecidableEq"
#rocq_ignore iriswasm.eqchecker_type_auxP "deriving DecidableEq"
#rocq_ignore iriswasm.checker_type_aux_eqMixin "deriving DecidableEq"
#rocq_ignore iriswasm.checker_type_aux_eqType "deriving DecidableEq"
#rocq_ignore iriswasm.checker_type_eq_dec "deriving DecidableEq"
#rocq_ignore iriswasm.checker_type_eqb "deriving DecidableEq"
#rocq_ignore iriswasm.eqchecker_typeP "deriving DecidableEq"
#rocq_ignore iriswasm.checker_type_eqMixin "deriving DecidableEq"
#rocq_ignore iriswasm.checker_type_eqType "deriving DecidableEq"

@[rocq_alias iriswasm.checker_type_aux]
inductive CheckerTypeAux where
  | any
  | some : ValueType → CheckerTypeAux
  deriving DecidableEq, Repr, Inhabited

@[rocq_alias iriswasm.checker_type]
inductive CheckerType where
  | topType : List CheckerTypeAux → CheckerType
  | type : List ValueType → CheckerType
  | bot
  deriving DecidableEq, Repr, Inhabited

@[rocq_alias iriswasm.to_ct_list]
def toCtList (ts : List ValueType) : List CheckerTypeAux := ts.map .some

@[rocq_alias iriswasm.ct_compat]
def ctCompat (t1 t2 : CheckerTypeAux) : Bool :=
  match t1 with
  | .any => true
  | .some vt1 =>
    match t2 with
    | .any => true
    | .some vt2 => vt1 == vt2

@[rocq_alias iriswasm.ct_list_compat]
def ctListCompat (l1 l2 : List CheckerTypeAux) : Bool := List.all2 ctCompat l1 l2

@[rocq_alias iriswasm.ct_suffix]
def ctSuffix (ts ts' : List CheckerTypeAux) : Bool :=
  decide (ts.length ≤ ts'.length) && ctListCompat (ts'.drop (ts'.length - ts.length)) ts

@[rocq_alias iriswasm.consume]
def consume (t : CheckerType) (cons : List CheckerTypeAux) : CheckerType :=
  match t with
  | .type ts =>
    if ctSuffix cons (toCtList ts)
    then .type (ts.take (ts.length - cons.length))
    else .bot
  | .topType cts =>
    if ctSuffix cons cts
    then .topType (cts.take (cts.length - cons.length))
    else if ctSuffix cts cons then .topType [] else .bot
  | _ => .bot

@[rocq_alias iriswasm.produce]
def produce (t1 t2 : CheckerType) : CheckerType :=
  match t1, t2 with
  | .topType ts, .type ts' => .topType (ts ++ toCtList ts')
  | .type ts, .type ts' => .type (ts ++ ts')
  | .type _, .topType ts => .topType ts
  | .topType _, .topType ts => .topType ts
  | _, _ => .bot

@[rocq_alias iriswasm.type_update]
def typeUpdate (currType : CheckerType) (cons : List CheckerTypeAux) (prods : CheckerType) :
    CheckerType :=
  produce (consume currType cons) prods

@[rocq_alias iriswasm.select_return_top]
def selectReturnTop (ts : List CheckerTypeAux) (cta1 cta2 : CheckerTypeAux) : CheckerType :=
  match cta1, cta2 with
  | _, .any => .topType (ts.take (ts.length - 3) ++ [cta1])
  | .any, _ => .topType (ts.take (ts.length - 3) ++ [cta2])
  | .some t1, .some t2 =>
    if t1 == t2 then .topType (ts.take (ts.length - 3) ++ [.some t1]) else .bot

@[rocq_alias iriswasm.type_update_select]
def typeUpdateSelect (t : CheckerType) : CheckerType :=
  match t with
  | .type ts =>
    if decide (3 ≤ ts.length) && ts[ts.length - 2]? == ts[ts.length - 3]?
    then consume (.type ts) [.any, .some .i32]
    else .bot
  | .topType ts =>
    match ts.length with
    | 0 => .topType [.any]
    | 1 => typeUpdate (.topType ts) [.some .i32] (.topType [.any])
    | 2 => consume (.topType ts) [.some .i32]
    | _ =>
      match ts[ts.length - 2]?, ts[ts.length - 3]? with
      | some tsAt2, some tsAt3 =>
        typeUpdate (.topType ts) [.any, .any, .some .i32] (selectReturnTop ts tsAt2 tsAt3)
      | _, _ => .bot
  | .bot => .bot

@[rocq_alias iriswasm.same_lab_h]
def sameLabH (iss : List Nat) (labC : List (List ValueType)) (ts : List ValueType) :
    Option (List ValueType) :=
  match iss with
  | [] => some ts
  | i :: iss' =>
    if labC.length ≤ i then none
    else
      match labC[i]? with
      | none => none
      | some xx => if xx == ts then sameLabH iss' labC xx else none

@[rocq_alias iriswasm.same_lab]
def sameLab (iss : List Nat) (labC : List (List ValueType)) : Option (List ValueType) :=
  match iss with
  | [] => none
  | i :: iss' =>
    if labC.length ≤ i then none
    else
      match labC[i]? with
      | some xx => sameLabH iss' labC xx
      | none => none

@[rocq_alias iriswasm.c_types_agree]
def cTypesAgree (ct : CheckerType) (ts' : List ValueType) : Bool :=
  match ct with
  | .type ts => ts == ts'
  | .topType ts => ctSuffix ts (toCtList ts')
  | .bot => false

@[rocq_alias iriswasm.is_int]
def isInt (t : ValueType) : Bool :=
  match t with
  | .i32 | .i64 => true
  | .f32 | .f64 => false

@[rocq_alias iriswasm.is_float]
def isFloat (t : ValueType) : Bool :=
  match t with
  | .i32 | .i64 => false
  | .f32 | .f64 => true

mutual
/-- Coq `check_single`. Coq's local `b_e_type_checker` (a `fold_left` of `check_single`) is
expressed through the mutually defined `check`, which is `fold_left` by structural recursion
(see `check_eq_foldl`). -/
@[rocq_alias iriswasm.check_single]
def checkSingle (C : TContext) (ts : CheckerType) (be : BasicInstruction) : CheckerType :=
  if ts == .bot then .bot
  else
  match be with
  | .const v => typeUpdate ts [] (.type [typeof v])
  | .unop t op =>
    match op with
    | .i _ => if isInt t then typeUpdate ts [.some t] (.type [t]) else .bot
    | .f _ => if isFloat t then typeUpdate ts [.some t] (.type [t]) else .bot
  | .binop t op =>
    match op with
    | .i _ => if isInt t then typeUpdate ts [.some t, .some t] (.type [t]) else .bot
    | .f _ => if isFloat t then typeUpdate ts [.some t, .some t] (.type [t]) else .bot
  | .testop t _ =>
    if isIntT t then typeUpdate ts [.some t] (.type [.i32]) else .bot
  | .relop t op =>
    match op with
    | .i _ => if isInt t then typeUpdate ts [.some t, .some t] (.type [.i32]) else .bot
    | .f _ => if isFloat t then typeUpdate ts [.some t, .some t] (.type [.i32]) else .bot
  | .cvtop t1 .convert t2 sx =>
    if convertCond t1 t2 sx then typeUpdate ts [.some t2] (.type [t1]) else .bot
  | .cvtop t1 .reinterpret t2 sxo =>
    if t1 != t2 && lengthT t1 == lengthT t2 && sxo == none
    then typeUpdate ts [.some t2] (.type [t1])
    else .bot
  | .unreachable => typeUpdate ts [] (.topType [])
  | .nop => ts
  | .drop => typeUpdate ts [.any] (.type [])
  | .select => typeUpdateSelect ts
  | .block (.tf tn tm) es =>
    if cTypesAgree (check (updLabel C ([tm] ++ C.label)) es (.type tn)) tm
    then typeUpdate ts (toCtList tn) (.type tm)
    else .bot
  | .loop (.tf tn tm) es =>
    if cTypesAgree (check (updLabel C ([tn] ++ C.label)) es (.type tn)) tm
    then typeUpdate ts (toCtList tn) (.type tm)
    else .bot
  | .if_ (.tf tn tm) es1 es2 =>
    if cTypesAgree (check (updLabel C ([tm] ++ C.label)) es1 (.type tn)) tm
        && cTypesAgree (check (updLabel C ([tm] ++ C.label)) es2 (.type tn)) tm
    then typeUpdate ts (toCtList (tn ++ [.i32])) (.type tm)
    else .bot
  | .br i =>
    if i < C.label.length then
      match C.label[i]? with
      | some xx => typeUpdate ts (toCtList xx) (.topType [])
      | none => .bot
    else .bot
  | .brIf i =>
    if i < C.label.length then
      match C.label[i]? with
      | some xx => typeUpdate ts (toCtList (xx ++ [.i32])) (.type xx)
      | none => .bot
    else .bot
  | .brTable iss i =>
    match sameLab (iss ++ [i]) C.label with
    | none => .bot
    | some tls => typeUpdate ts (toCtList (tls ++ [.i32])) (.topType [])
  | .return_ =>
    match C.return_ with
    | none => .bot
    | some tls => typeUpdate ts (toCtList tls) (.topType [])
  | .call i =>
    if i < C.funcT.length then
      match C.funcT[i]? with
      | none => .bot
      | some (.tf tn tm) => typeUpdate ts (toCtList tn) (.type tm)
    else .bot
  | .callIndirect i =>
    if 1 ≤ C.table.length && i < C.typesT.length then
      match C.typesT[i]? with
      | none => .bot
      | some (.tf tn tm) => typeUpdate ts (toCtList (tn ++ [.i32])) (.type tm)
    else .bot
  | .getLocal i =>
    if i < C.local_.length then
      match C.local_[i]? with
      | none => .bot
      | some xx => typeUpdate ts [] (.type [xx])
    else .bot
  | .setLocal i =>
    if i < C.local_.length then
      match C.local_[i]? with
      | none => .bot
      | some xx => typeUpdate ts [.some xx] (.type [])
    else .bot
  | .teeLocal i =>
    if i < C.local_.length then
      match C.local_[i]? with
      | none => .bot
      | some xx => typeUpdate ts [.some xx] (.type [xx])
    else .bot
  | .getGlobal i =>
    if i < C.global.length then
      match C.global[i]? with
      | none => .bot
      | some xx => typeUpdate ts [] (.type [xx.t])
    else .bot
  | .setGlobal i =>
    if i < C.global.length then
      match C.global[i]? with
      | none => .bot
      | some xx => if isMut xx then typeUpdate ts [.some xx.t] (.type []) else .bot
    else .bot
  | .load t tpSx a _ =>
    if C.memory != [] && loadStoreTBounds a (optionProjl tpSx) t
    then typeUpdate ts [.some .i32] (.type [t])
    else .bot
  | .store t tp a _ =>
    if C.memory != [] && loadStoreTBounds a tp t
    then typeUpdate ts [.some .i32, .some t] (.type [])
    else .bot
  | .currentMemory =>
    if C.memory != [] then typeUpdate ts [] (.type [.i32]) else .bot
  | .growMemory =>
    if C.memory != [] then typeUpdate ts [.some .i32] (.type [.i32]) else .bot

/-- Coq `check C es ts := fold_left (check_single C) es ts`. -/
@[rocq_alias iriswasm.check]
def check (C : TContext) (es : List BasicInstruction) (ts : CheckerType) : CheckerType :=
  match es with
  | [] => ts
  | e :: es' => check C es' (checkSingle C ts e)
end

theorem check_eq_foldl (C : TContext) (es : List BasicInstruction) (ts : CheckerType) :
    check C es ts = es.foldl (checkSingle C) ts := by
  induction es generalizing ts with
  | nil => simp [check]
  | cons e es ih => simp [check, ih]

@[rocq_alias iriswasm.collect_at_inds]
def collectAtInds {A : Type} (l : List A) (ns : List Nat) : List A :=
  match ns with
  | n :: ns' =>
    match l[n]? with
    | some x => x :: collectAtInds l ns'
    | none => collectAtInds l ns'
  | [] => []

@[rocq_alias iriswasm.b_e_type_checker]
def bETypeChecker (C : TContext) (es : List BasicInstruction) (tf : FunctionType) : Bool :=
  match tf with
  | .tf tn tm => cTypesAgree (es.foldl (checkSingle C) (.type tn)) tm

end Wasm
