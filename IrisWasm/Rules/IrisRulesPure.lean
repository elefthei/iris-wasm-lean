/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Language.IrisWpDef
import IrisWasm.Helpers.Prelude.FirstInstr
import IrisWasm.Helpers.IrisWasmDeterm

/-! Port of `theories/iris/rules/iris_rules_pure.v`.

Every rule is one pure `ReduceSimple` step; all go through the shared `wp_simple_step`, which
replays the Coq proof script (`wp_lift_atomic_step` + `only_one_reduction`). -/

namespace IrisWasm

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm

set_option linter.unusedSimpArgs false

variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF} {f0 : Frame}

/-- One deterministic pure step `es ↦ es'` to a value, framing `↪[frame] f0` through. -/
theorem wp_simple_step {es es' : Expr} {v : Val} (hred : ReduceSimple es es')
    (hnv : toVal es = none := by simp [toVal, mergeValuesList, toValInstr, mergeValues, valNotValCombine, valCombine])
    (hv : toVal es' = some v := by simp [toVal, mergeValuesList, toValInstr, mergeValues, valNotValCombine, valCombine])
    (hgrow : ∀ i, firstInstr es ≠ some (.basic .growMemory, i) := by
      simp [firstInstr_cons, firstInstrInstr])
    (htrap : ∀ i, firstInstr es ≠ some (.trap, i) := by
      simp [firstInstr_cons, firstInstrInstr]) :
    ⊢ iprop(↪[frame] f0 -∗ ▷ Φ v -∗ WP es @ s ; E {{ w, Φ w ∗ ↪[frame] f0 }}) := by
  let := @WasmG.invGS hlc GF _
  iintro Hf HΦ
  iapply IrisWp.wp_lift_atomic_step (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS) hnv f0
  iintro %σ %ns %obs %obs' %nt Hσ !>
  rcases σ with ⟨ws, locs, inst⟩
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact ⟨[], es', (ws, locs, inst), [], .simple hred, rfl, rfl⟩
  iintro !> %e₂ %σ₂ %eₜ %Hstep Hcr
  rcases σ₂ with ⟨ws', locs', inst'⟩
  obtain ⟨H, rfl, rfl⟩ := Hstep
  have : (ws, Frame.mk locs inst, es') = (ws', ⟨locs', inst'⟩, e₂) := by
    rcases reduce_det (.simple hred) H with h | ⟨i, h⟩ | ⟨i, -, -, h, -⟩
    · exact h
    · exact absurd h (hgrow i)
    · exact absurd h (htrap i)
  cases this
  imodintro
  iframe
  isplitl
  · ipureintro; exact hv
  · simp; exact .rfl

@[rocq_alias iriswasm.wp_unop]
theorem wp_unop {v v' : Value} {t : ValueType} {op : Unop} (h : appUnop op v = v') :
    ⊢ iprop(↪[frame] f0 -∗ ▷ Φ (.immV [v']) -∗
      WP ([.basic (.const v), .basic (.unop t op)] : Expr) @ s ; E
        {{ v, Φ v ∗ ↪[frame] f0 }}) := by
  subst h; exact wp_simple_step .unop

@[rocq_alias iriswasm.wp_binop]
theorem wp_binop {v1 v2 v : Value} {t : ValueType} {op : Binop} (h : appBinop op v1 v2 = some v) :
    ⊢ iprop(↪[frame] f0 -∗ ▷ Φ (.immV [v]) -∗
      WP ([.basic (.const v1), .basic (.const v2), .basic (.binop t op)] : Expr) @ s ; E
        {{ v, Φ v ∗ ↪[frame] f0 }}) :=
  wp_simple_step (.binopSuccess h)

@[rocq_alias iriswasm.wp_binop_failure]
theorem wp_binop_failure {v1 v2 : Value} {t : ValueType} {op : Binop}
    (h : appBinop op v1 v2 = none) :
    ⊢ iprop(▷ Φ .trapV -∗ ↪[frame] f0 -∗
      WP ([.basic (.const v1), .basic (.const v2), .basic (.binop t op)] : Expr) @ s ; E
        {{ v, Φ v ∗ ↪[frame] f0 }}) := by
  iintro HΦ Hf
  iapply (wp_simple_step (s := s) (E := E) (Φ := Φ) (f0 := f0) (.binopFailure h)) $$ Hf HΦ

@[rocq_alias iriswasm.wp_relop]
theorem wp_relop {v1 v2 : Value} {b : Bool} {t : ValueType} {op : Relop}
    (h : appRelop op v1 v2 = b) :
    ⊢ iprop(↪[frame] f0 -∗ ▷ Φ (.immV [.int32 (wasmBool b)]) -∗
      WP ([.basic (.const v1), .basic (.const v2), .basic (.relop t op)] : Expr) @ s ; E
        {{ v, Φ v ∗ ↪[frame] f0 }}) := by
  subst h; exact wp_simple_step .relop

@[rocq_alias iriswasm.wp_testop_i32]
theorem wp_testop_i32 {v : I32} {b : Bool} {op : Testop} (h : appTestopI op v = b) :
    ⊢ iprop(↪[frame] f0 -∗ ▷ Φ (.immV [.int32 (wasmBool b)]) -∗
      WP ([.basic (.const (.int32 v)), .basic (.testop .i32 op)] : Expr) @ s ; E
        {{ v, Φ v ∗ ↪[frame] f0 }}) := by
  subst h; exact wp_simple_step .testopI32

@[rocq_alias iriswasm.wp_testop_i64]
theorem wp_testop_i64 {v : I64} {b : Bool} {op : Testop} (h : appTestopI op v = b) :
    ⊢ iprop(↪[frame] f0 -∗ ▷ Φ (.immV [.int32 (wasmBool b)]) -∗
      WP ([.basic (.const (.int64 v)), .basic (.testop .i64 op)] : Expr) @ s ; E
        {{ v, Φ v ∗ ↪[frame] f0 }}) := by
  subst h; exact wp_simple_step .testopI64

@[rocq_alias iriswasm.wp_cvtop_convert]
theorem wp_cvtop_convert {v v' : Value} {t1 t2 : ValueType} {sx : Option Sx}
    (h : cvt t2 sx v = some v') (ht : typesAgree t1 v = true) :
    ⊢ iprop(↪[frame] f0 -∗ ▷ Φ (.immV [v']) -∗
      WP ([.basic (.const v), .basic (.cvtop t2 .convert t1 sx)] : Expr) @ s ; E
        {{ v, Φ v ∗ ↪[frame] f0 }}) :=
  wp_simple_step (.convertSuccess ht h)

@[rocq_alias iriswasm.wp_cvtop_convert_failure]
theorem wp_cvtop_convert_failure {v : Value} {t1 t2 : ValueType} {sx : Option Sx}
    (h : cvt t2 sx v = none) (ht : typesAgree t1 v = true) :
    ⊢ iprop(↪[frame] f0 -∗ ▷ Φ .trapV -∗
      WP ([.basic (.const v), .basic (.cvtop t2 .convert t1 sx)] : Expr) @ s ; E
        {{ v, Φ v ∗ ↪[frame] f0 }}) :=
  wp_simple_step (.convertFailure ht h)

@[rocq_alias iriswasm.wp_cvtop_reinterpret]
theorem wp_cvtop_reinterpret {v v' : Value} {t1 t2 : ValueType}
    (h : wasmDeserialise (bits v) t2 = v') (ht : typesAgree t1 v = true) :
    ⊢ iprop(↪[frame] f0 -∗ ▷ Φ (.immV [v']) -∗
      WP ([.basic (.const v), .basic (.cvtop t2 .reinterpret t1 none)] : Expr) @ s ; E
        {{ v, Φ v ∗ ↪[frame] f0 }}) := by
  subst h
  exact wp_simple_step (.reinterpret ht)

@[rocq_alias iriswasm.wp_unreachable]
theorem wp_unreachable :
    ⊢ iprop(↪[frame] f0 -∗ ▷ Φ .trapV -∗
      WP ([.basic .unreachable] : Expr) @ s ; E {{ v, Φ v ∗ ↪[frame] f0 }}) :=
  wp_simple_step .unreachable

@[rocq_alias iriswasm.wp_nop]
theorem wp_nop :
    ⊢ iprop(↪[frame] f0 -∗ ▷ Φ (.immV []) -∗
      WP ([.basic .nop] : Expr) @ s ; E {{ v, Φ v ∗ ↪[frame] f0 }}) :=
  wp_simple_step .nop

@[rocq_alias iriswasm.wp_drop]
theorem wp_drop {v : Value} :
    ⊢ iprop(↪[frame] f0 -∗ ▷ Φ (.immV []) -∗
      WP ([.basic (.const v), .basic .drop] : Expr) @ s ; E {{ w, Φ w ∗ ↪[frame] f0 }}) :=
  wp_simple_step .drop

@[rocq_alias iriswasm.wp_select_false]
theorem wp_select_false {n : I32} {v1 v2 : Value} (h : n = Int.zero) :
    ⊢ iprop(↪[frame] f0 -∗ ▷ Φ (.immV [v2]) -∗
      WP ([.basic (.const v1), .basic (.const v2), .basic (.const (.int32 n)), .basic .select] : Expr)
        @ s ; E {{ w, Φ w ∗ ↪[frame] f0 }}) :=
  wp_simple_step (.selectFalse h)

@[rocq_alias iriswasm.wp_select_true]
theorem wp_select_true {n : I32} {v1 v2 : Value} (h : n ≠ Int.zero) :
    ⊢ iprop(↪[frame] f0 -∗ ▷ Φ (.immV [v1]) -∗
      WP ([.basic (.const v1), .basic (.const v2), .basic (.const (.int32 n)), .basic .select] : Expr)
        @ s ; E {{ w, Φ w ∗ ↪[frame] f0 }}) :=
  wp_simple_step (.selectTrue h)

end IrisWasm
