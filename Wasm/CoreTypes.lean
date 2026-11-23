import Std

/-! Core 3.0 recursive type groups, substitution and matching (SpecTec 1.2, 2.1 and 2.2). -/

namespace Wasm.CoreTypes

inductive AbsHeap where
  | any | eq | i31 | struct_ | array | none | func | nofunc | exn | noexn | extern_ | noextern | bot
  deriving DecidableEq, Repr

inductive Heap (U : Type) where
  | abs (type : AbsHeap)
  | use (type : U)
  deriving DecidableEq, Repr

structure Ref (U : Type) where
  nullable : Bool
  heap : Heap U
  deriving DecidableEq, Repr

inductive Val (U : Type) where
  | i32 | i64 | f32 | f64 | v128 | bot
  | ref (type : Ref U)
  deriving DecidableEq, Repr

inductive Storage (U : Type) where
  | i8 | i16
  | val (type : Val U)
  deriving DecidableEq, Repr

structure Field (U : Type) where
  isMutable : Bool
  storage : Storage U
  deriving DecidableEq, Repr

inductive Composite (U : Type) where
  | struct_ (fields : List (Field U))
  | array (field : Field U)
  | func (params results : List (Val U))
  deriving DecidableEq, Repr

structure Sub (U : Type) where
  isFinal : Bool
  supers : List U
  body : Composite U
  deriving DecidableEq, Repr

abbrev RecGroup (U : Type) := List (Sub U)

/-- A rolled binder distinguishes its own variables from all free uses. -/
inductive Scope (U : Type) where
  | bound (index : Nat)
  | free (type : U)
  deriving DecidableEq, Repr

/-- A projection of a closed group. Only references to *earlier* groups are nested values. -/
inductive Defined where
  | proj (group : List (Sub (Scope Defined))) (index : Nat)

namespace Defined

local macro "decCtor " h:ident : tactic =>
  `(tactic| refine @decidable_of_iff _ _ (($h ..).to_iff.symm) ?_)

-- Lean's stock nested BEq derivation is partial. Decide structural equality on the finite syntax.
mutual
  def decEq (a b : Defined) : Decidable (a = b) :=
    match a, b with
    | .proj g i, .proj g' j =>
      if h : i = j then
        letI := withPtrEqDecEq withPtrEq (fun _ _ _ _ ↦ rfl) g g' fun _ ↦ decGroup g g'
        decidable_of_iff (g = g') (by simp [proj.injEq, h])
      else isFalse fun e ↦ h (proj.inj e).2
  termination_by structural a
  private def decGroup (a b : RecGroup (Scope Defined)) : Decidable (a = b) :=
    match a, b with
    | [], [] => isTrue rfl
    | [], _ :: _ | _ :: _, [] => isFalse (by intro h; cases h)
    | x :: xs, y :: ys => by
      letI := decSub x y; letI := decGroup xs ys; decCtor List.cons.injEq; infer_instance
  termination_by structural a
  private def decSub (a b : Sub (Scope Defined)) : Decidable (a = b) :=
    match a, b with
    | ⟨_, ps, c⟩, ⟨_, qs, d⟩ => by
      letI := decScopes ps qs; letI := decComposite c d; decCtor Sub.mk.injEq; infer_instance
  termination_by structural a
  private def decScopes (a b : List (Scope Defined)) : Decidable (a = b) :=
    match a, b with
    | [], [] => isTrue rfl
    | [], _ :: _ | _ :: _, [] => isFalse (by intro h; cases h)
    | x :: xs, y :: ys => by
      letI := decScope x y; letI := decScopes xs ys; decCtor List.cons.injEq; infer_instance
  termination_by structural a
  private def decScope (a b : Scope Defined) : Decidable (a = b) := by
    cases a <;> cases b <;> first
      | (decCtor Scope.bound.injEq; infer_instance)
      | (decCtor Scope.free.injEq; apply decEq)
      | exact isFalse (by intro h; cases h)
  termination_by structural a
  private def decComposite (a b : Composite (Scope Defined)) : Decidable (a = b) := by
    cases a <;> cases b <;> first
      | (decCtor Composite.struct_.injEq; apply decFields)
      | (decCtor Composite.array.injEq; apply decField)
      | (decCtor Composite.func.injEq; exact @instDecidableAnd _ _ (decVals _ _) (decVals _ _))
      | exact isFalse (by intro h; cases h)
  termination_by structural a
  private def decFields (a b : List (Field (Scope Defined))) : Decidable (a = b) :=
    match a, b with
    | [], [] => isTrue rfl
    | [], _ :: _ | _ :: _, [] => isFalse (by intro h; cases h)
    | x :: xs, y :: ys => by
      letI := decField x y; letI := decFields xs ys; decCtor List.cons.injEq; infer_instance
  termination_by structural a
  private def decField (a b : Field (Scope Defined)) : Decidable (a = b) :=
    match a, b with
    | ⟨_, s⟩, ⟨_, t⟩ => by letI := decStorage s t; decCtor Field.mk.injEq; infer_instance
  termination_by structural a
  private def decStorage (a b : Storage (Scope Defined)) : Decidable (a = b) := by
    cases a <;> cases b <;> first
      | (decCtor Storage.val.injEq; apply decVal)
      | exact isTrue rfl
      | exact isFalse (by intro h; cases h)
  termination_by structural a
  private def decVals (a b : List (Val (Scope Defined))) : Decidable (a = b) :=
    match a, b with
    | [], [] => isTrue rfl
    | [], _ :: _ | _ :: _, [] => isFalse (by intro h; cases h)
    | x :: xs, y :: ys => by
      letI := decVal x y; letI := decVals xs ys; decCtor List.cons.injEq; infer_instance
  termination_by structural a
  private def decVal (a b : Val (Scope Defined)) : Decidable (a = b) := by
    cases a <;> cases b <;> first
      | (decCtor Val.ref.injEq; apply decRef)
      | exact isTrue rfl
      | exact isFalse (by intro h; cases h)
  termination_by structural a
  private def decRef (a b : Ref (Scope Defined)) : Decidable (a = b) :=
    match a, b with
    | ⟨_, h⟩, ⟨_, k⟩ => by letI := decHeap h k; decCtor Ref.mk.injEq; infer_instance
  termination_by structural a
  private def decHeap (a b : Heap (Scope Defined)) : Decidable (a = b) := by
    cases a <;> cases b <;> first
      | (decCtor Heap.abs.injEq; infer_instance)
      | (decCtor Heap.use.injEq; apply decScope)
      | exact isFalse (by intro h; cases h)
  termination_by structural a
end

instance : DecidableEq Defined := decEq

end Defined

variable {m : Type → Type} [Monad m] {U V : Type}

/-- Capture-free type-use substitution, lifted through all composite bodies. -/
def Heap.substM (f : U → m V) : Heap U → m (Heap V)
  | .abs a => pure (.abs a)
  | .use u => .use <$> f u

def Ref.substM (f : U → m V) (r : Ref U) : m (Ref V) :=
  return ⟨r.nullable, ← r.heap.substM f⟩

def Val.substM (f : U → m V) : Val U → m (Val V)
  | .i32 => pure .i32 | .i64 => pure .i64 | .f32 => pure .f32 | .f64 => pure .f64
  | .v128 => pure .v128 | .bot => pure .bot | .ref r => .ref <$> r.substM f

def Storage.substM (f : U → m V) : Storage U → m (Storage V)
  | .i8 => pure .i8 | .i16 => pure .i16 | .val v => .val <$> v.substM f

def Field.substM (f : U → m V) (field : Field U) : m (Field V) :=
  return ⟨field.isMutable, ← field.storage.substM f⟩

def Composite.substM (f : U → m V) : Composite U → m (Composite V)
  | .struct_ fs => .struct_ <$> fs.mapM (Field.substM f)
  | .array field => .array <$> field.substM f
  | .func ps rs => return .func (← ps.mapM (Val.substM f)) (← rs.mapM (Val.substM f))

def Sub.substM (f : U → m V) (s : Sub U) : m (Sub V) :=
  return ⟨s.isFinal, ← s.supers.mapM f, ← s.body.substM f⟩

/-- `$rollrt`: only this group's indices become bound. Earlier uses are substituted separately. -/
def rollUse (base count i : Nat) : Scope Nat :=
  if base ≤ i && i < base + count then .bound (i - base) else .free i

def roll (base : Nat) (g : RecGroup Nat) : RecGroup (Scope Nat) :=
  let f := rollUse base g.length
  g.map fun s ↦ Id.run (s.substM (m := Id) f)

/-- Combine rolling and substitution in one traversal; no index in a later group is in scope. -/
def closeGroup (prior : Array Defined) (g : RecGroup Nat) : Option (RecGroup (Scope Defined)) :=
  let f := rollUse prior.size g.length
  g.mapM (Sub.substM fun i ↦ match f i with
    | .bound j => some (.bound j)
    | .free j => .free <$> prior[j]?)

def Scope.openIn (group : RecGroup (Scope Defined)) : Scope Defined → Option Defined :=
  let count := group.length
  fun
    | .free d => some d
    | .bound j => if j < count then some (.proj group j) else none

/-- `$unrolldt`: replace the selected body's bound variables, never descend into imported groups. -/
def Defined.unroll : Defined → Option (Sub Defined)
  | .proj g i => do (← g[i]?).substM (Scope.openIn g)

def Defined.expand (d : Defined) : Option (Composite Defined) := Sub.body <$> d.unroll

/-- `Deftype_sub/super` follows only declared parents. A local parent precedes its child;
    following an external parent descends strictly into a finite, previously closed group. -/
private def follows (target : Defined) (g : RecGroup (Scope Defined)) (i : Nat) : Bool :=
  if Defined.proj g i = target then true else
    match _hs : g[i]? with
    | none => false
    | some s =>
      match _hp : s.supers with
      | [.bound j] => if _ : j < i then follows target g j else false
      | [.free (.proj p j)] => follows target p j
      | _ => false
termination_by (sizeOf g, i)
decreasing_by
  · apply Prod.Lex.right; assumption
  · apply Prod.Lex.left
    have hm := List.sizeOf_lt_of_mem (List.mem_of_getElem? _hs)
    rcases s with ⟨_, ps, _⟩; dsimp at _hp; subst ps
    simp +arith at hm; omega

def Defined.matches (a b : Defined) : Bool :=
  match a with | .proj g i => follows b g i

/-- Reflexivity of closed projections and declared supertype edges (2.2 `Deftype_sub`). -/
inductive DefinedSub : Defined → Defined → Prop where
  | refl (d : Defined) : DefinedSub d d
  | bound {g : RecGroup (Scope Defined)} {i j : Nat} {s t} :
      g[i]? = some s → s.supers = [.bound j] → j < i →
      DefinedSub (.proj g j) t → DefinedSub (.proj g i) t
  | free {g : RecGroup (Scope Defined)} {i : Nat} {s d t} :
      g[i]? = some s → s.supers = [.free d] → DefinedSub d t → DefinedSub (.proj g i) t

private theorem follows_sound {t g i} : follows t g i = true → DefinedSub (.proj g i) t := by
  induction g, i using follows.induct t with
  | case1 g i h => subst t; exact fun _ ↦ .refl _
  | case2 | case4 | case6 => rw [follows]; grind
  | case3 g i hn s hs j hp hj ih =>
    rw [follows]; intro h; apply DefinedSub.bound hs hp hj; apply ih; grind
  | case5 g i hn s hs pg j hp ih =>
    rw [follows]; intro h; apply DefinedSub.free hs hp; apply ih; grind

theorem Defined.matches_iff {d t : Defined} : d.matches t = true ↔ DefinedSub d t := by
  constructor
  · cases d; exact follows_sound
  · intro h
    induction h with
    | refl d => cases d; simp only [Defined.matches]; rw [follows]; simp
    | bound hs hp hj _ ih => simp only [Defined.matches] at ih ⊢; rw [follows]; grind
    | @free g i s d t hs hp _ ih => cases d; simp only [Defined.matches] at ih ⊢; rw [follows]; grind

def Composite.kind : Composite U → AbsHeap
  | .struct_ _ => .struct_ | .array _ => .array | .func .. => .func

def Defined.kind : Defined → Option AbsHeap
  | .proj g i => (fun s ↦ s.body.kind) <$> g[i]?

def AbsHeap.matches (a b : AbsHeap) : Bool :=
  a == b || match a, b with
    | .bot, _ => true
    | .none, .any | .none, .eq | .none, .i31 | .none, .struct_ | .none, .array => true
    | .i31, k | .struct_, k | .array, k => k == .eq || k == .any
    | .eq, .any | .nofunc, .func | .noexn, .exn | .noextern, .extern_ => true
    | _, _ => false

def Heap.matches : Heap Defined → Heap Defined → Bool
  | .abs a, .abs b => a.matches b
  | .use a, .use b => a.matches b
  | .use d, .abs b => d.kind.any (·.matches b)
  | .abs a, .use d => a == .bot || d.kind.any fun k ↦ match a, k with
    | .none, .struct_ | .none, .array | .nofunc, .func => true
    | _, _ => false

def Ref.matches (a b : Ref Defined) : Bool :=
  (!a.nullable || b.nullable) && a.heap.matches b.heap

def Val.matches : Val Defined → Val Defined → Bool
  | .bot, _ => true
  | .ref a, .ref b => a.matches b
  | a, b => a == b

def resultMatches : List (Val Defined) → List (Val Defined) → Bool
  | [], [] => true
  | a :: as, b :: bs => a.matches b && resultMatches as bs
  | _, _ => false

def Storage.matches : Storage Defined → Storage Defined → Bool
  | .val a, .val b => a.matches b
  | .i8, .i8 | .i16, .i16 => true
  | _, _ => false

def Field.matches (a b : Field Defined) : Bool :=
  a.isMutable == b.isMutable && a.storage.matches b.storage &&
    (!b.isMutable || b.storage.matches a.storage)

private def fieldsMatch : List (Field Defined) → List (Field Defined) → Bool
  | _, [] => true
  | a :: as, b :: bs => a.matches b && fieldsMatch as bs
  | [], _ :: _ => false

def Composite.matches : Composite Defined → Composite Defined → Bool
  | .struct_ as, .struct_ bs => fieldsMatch as bs
  | .array a, .array b => a.matches b
  | .func ap ar, .func bp br => resultMatches bp ap && resultMatches ar br
  | _, _ => false

def Sub.validParent (s : Sub (Scope Defined)) (g : RecGroup (Scope Defined)) (i : Nat) : Bool :=
  match s.supers with
  | [] => true
  | [p] => Id.run do
    if let .bound j := p then if j ≥ i then return false
    let some parent := p.openIn g | return false
    let some t := parent.unroll | return false
    if t.isFinal then return false
    let some body := s.body.substM (Scope.openIn g) | return false
    return body.matches t.body
  | _ => false

/-- `$rolldt` plus `Rectype_ok`: the whole group is in scope for bodies but not for super edges. -/
def validateGroup (prior : Array Defined) (raw : RecGroup Nat) : Option (Array Defined) := do
  let g ← closeGroup prior raw
  go g 0 g prior
where
  go (g : RecGroup (Scope Defined)) (i : Nat) (rest : RecGroup (Scope Defined)) (acc : Array Defined) :
      Option (Array Defined) :=
    match rest with
    | [] => some acc
    | s :: ss =>
      if s.validParent g i then go g (i+1) ss (acc.push (.proj g i)) else none

def validateGroups (groups : List (RecGroup Nat)) : Option (Array Defined) :=
  groups.foldlM validateGroup #[]

def closeVal (types : Array Defined) (t : Val Nat) : Option (Val Defined) :=
  t.substM fun i ↦ types[i]?

def closeRef (types : Array Defined) (t : Ref Nat) : Option (Ref Defined) :=
  t.substM fun i ↦ types[i]?

/-- The immediate keeps a type index until the module type vector is available. -/
inductive BlockType (V : Type) where
  | result (type : Option V)
  | index (type : Nat)
  deriving DecidableEq, Repr

structure Signature where
  params : List (Val Defined)
  results : List (Val Defined)
  deriving DecidableEq

inductive BlockType.Valid (types : Array Defined) : BlockType (Val Nat) → Signature → Prop where
  | empty : Valid types (.result none) ⟨[], []⟩
  | result {v w} : closeVal types v = some w → Valid types (.result (some v)) ⟨[], [w]⟩
  | index {i d ps rs} : types[i]? = some d → d.expand = some (.func ps rs) →
      Valid types (.index i) ⟨ps, rs⟩

def BlockType.resolve (types : Array Defined) : BlockType (Val Nat) → Option Signature
  | .result none => some ⟨[], []⟩
  | .result (some v) => do return ⟨[], [← closeVal types v]⟩
  | .index i => do
    let d ← types[i]?
    let some (.func ps rs) := d.expand | none
    return ⟨ps, rs⟩

theorem BlockType.resolve_iff {types bt s} : bt.resolve types = some s ↔ Valid types bt s := by
  constructor
  · intro h
    cases bt with
    | result v =>
      cases v with
      | none => cases h; exact .empty
      | some v =>
        cases hv : closeVal types v with
        | none => simp [resolve, hv] at h
        | some w => simp [resolve, hv] at h; subst s; exact .result hv
    | index i =>
      cases hd : types[i]? with
      | none => simp [resolve, hd] at h
      | some d =>
        cases he : d.expand with
        | none => simp [resolve, hd, he] at h
        | some c =>
          cases c <;> simp [resolve, hd, he] at h
          subst s; exact .index hd he
  · intro h
    cases h with
    | empty => rfl
    | result hv => simp [resolve, hv]
    | index hd he => simp [resolve, hd, he]

/-- Runtime entry needs only the arities. An inline result tag is not validated by a raw step. -/
def BlockType.arities (types : Array Defined) : BlockType (Val Nat) → Option (Nat × Nat)
  | .result none => some (0, 0)
  | .result (some _) => some (0, 1)
  | bt@(.index _) => (bt.resolve types).map fun s ↦ (s.params.length, s.results.length)

theorem BlockType.Valid.arities_eq {types bt s} (h : Valid types bt s) :
    bt.arities types = some (s.params.length, s.results.length) := by
  cases h with
  | empty | result => rfl
  | index hd he => simp [arities, resolve, hd, he]

end Wasm.CoreTypes
