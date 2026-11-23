import IrisWasm.Denotational.Basic
import IrisWasm.Logrel.IrisLogrel

/-! One syntax-directed Wasm reduction boundary, before handling store and frame operations. -/

namespace IrisWasm.Denotational

open Wasm

abbrev Layer := WasmProg Front

/-- Reuse the instruction tail in the usual closed-fragment case. -/
def remaining (es : Expr) : Expr → Expr
  | [] => es
  | e :: rest => es ++ e :: rest

@[simp] theorem remaining_eq (es rest : Expr) : remaining es rest = es ++ rest := by
  cases rest <;> simp [remaining]

def finish (vs : List Value) : Layer := pure (.done (.immV vs.reverse))

def trapLayer (vs : List Value) (tail : Expr) : Layer :=
  if vs = [] ∧ tail = [] then pure (.done .trapV)
  else .br (.trim vs.length tail.length) fun p ↦
    pure (.next (vToEList (vs.reverse.take p.val.1) ++
      .trap :: tail.drop (tail.length - p.val.2)))

def invokeLayer (a : Funcaddr) (vs : List Value) (tail : Expr) : Layer :=
  .vis (.closureAt a) fun
    | .funcNative inst (.tf ins outs) ts body => withArgs ins.length vs fun left args ↦
      emit left [.local outs.length ⟨args ++ nZeros ts, inst⟩ [.label outs.length [] (toEList body)]] tail
    | .funcHost (.tf ins outs) h => withArgs ins.length vs fun left args ↦
      emit left [.callHost (.tf ins outs) h args] tail

/-- A catch takes its operands from the innermost base, not from a bypassed label. -/
def catchValues (vs : List Value) (tail : Expr) (n : Nat) (ws : List Value) (cont : Expr) : Layer :=
  if n ≤ ws.length then emit vs (vToEList (ws.drop (ws.length - n)) ++ cont) tail else .stuck

def labelFront (n : Nat) (cont : Expr) (vs : List Value) (tail : Expr) : Front → Layer
  | .next b => emit vs [.label n cont b] tail
  | .done (.immV ws) => emit vs (vToEList ws) tail
  | .done .trapV => emit vs [.trap] tail
  | .done (.brV vh) =>
    match vhDecrease (.rec_ vs.reverse n cont vh tail) with
    | some vh' => pure (.done (.brV vh'))
    | none => catchValues vs tail n (getBaseL vh) cont
  | .done (.retV sh) => pure (.done (.retV (.rec_ vs.reverse n cont sh tail)))
  | .done (.callHostV tf h args lh) =>
    pure (.done (.callHostV tf h args (.label vs.reverse n cont lh tail)))

def localFront (n : Nat) (f f' : Frame) (vs : List Value) (tail : Expr) : Front → Layer
  | .next b => emit vs [.local n f' b] tail
  | .done (.immV ws) => if ws.length = n then emit vs (vToEList ws) tail else .stuck
  | .done .trapV => emit vs [.trap] tail
  | .done (.brV _) => .stuck
  | .done (.retV sh) => catchValues vs tail n (simpleGetBaseL sh) []
  | .done (.callHostV tf h args lh) =>
    pure (.done (.callHostV tf h args (.local vs.reverse n f lh tail)))

/-- `vs` is top first; `rest` is still present at a boundary. Only constants enter `k`. -/
def frag (es : Expr) (vs : List Value) (rest : Expr) (k : List Value → Layer) : Layer :=
  match es with
  | [] => k vs
  | .basic b :: es => basicLayer b vs (remaining es rest) (fun ws ↦ frag es ws rest k)
  | .trap :: es => trapLayer vs (remaining es rest)
  | .invoke a :: es => invokeLayer a vs (remaining es rest)
  | .callHost tf h args :: es =>
    pure (.done (.callHostV tf h args (.base vs.reverse (remaining es rest))))
  | .label n cont body :: es =>
    frag body [] [] finish >>= labelFront n cont vs (remaining es rest)
  | .local n f body :: es => .vis (.swapFrame f) fun caller ↦
    frag body [] [] finish >>= fun r ↦ .vis (.swapFrame caller) fun inner ↦
      localFront n f inner vs (remaining es rest) r
termination_by sizeOf es
decreasing_by all_goals simp_wf; omega

def layer (es : Expr) : Layer := frag es [] [] finish

theorem frag_append (p q : Expr) (vs : List Value) (tail : Expr) (k : List Value → Layer) :
    frag (p ++ q) vs tail k = frag p vs (q ++ tail) (fun ws ↦ frag q ws tail k) := by
  induction p generalizing vs with
  | nil => simp [frag]
  | cons e p ih => cases e <;> simp only [List.cons_append, frag, remaining_eq, List.append_assoc, ih]

/-- Peeling a prefix of constants is not a small step. -/
theorem frag_consts (ws vs : List Value) (es tail : Expr) (k : List Value → Layer) :
    frag (vToEList ws ++ es) vs tail k = frag es (ws.reverse ++ vs) tail k := by
  induction ws generalizing vs with
  | nil => simp [vToEList]
  | cons v ws ih =>
    simpa [vToEList, frag, basicLayer] using ih (v :: vs)

end IrisWasm.Denotational
