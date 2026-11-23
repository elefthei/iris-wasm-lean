/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import IrisWasm.Rules.IrisRulesPure
import IrisWasm.Rules.IrisRulesStructural
import IrisWasm.Rules.IrisRulesControl
import IrisWasm.Rules.IrisRulesResources
import IrisWasm.Rules.IrisRulesTrap
import IrisWasm.Rules.IrisRulesBind

/-! Port of `theories/iris/examples/stack/function/stack_common.v`. -/

namespace IrisWasm.Examples.Stack

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm

/-- `{{{{ P }}}} es {{{{ v, Q }}}}` (and `… @ E …`): persistent Hoare quadruple of the stack
examples, `□ ∀ Φ, P -∗ (∀ v, Q -∗ Φ v) -∗ WP es @ NotStuck ; E {{ v, Φ v }}`. -/
syntax:50 "{{{{ " term " }}}} " term:max " {{{{ " ident ", " term " }}}}" : term
syntax:50 "{{{{ " term " }}}} " term:max " @ " term:max " {{{{ " ident ", " term " }}}}" : term

macro_rules
  | `({{{{ $P }}}} $es {{{{ $v, $Q }}}}) =>
    `(iprop(□ ∀ Φ, $P -∗ (∀ $v:ident : Val, $Q -∗ Φ $v) -∗
        WP ($es : Expr) @ Stuckness.NotStuck ; ⊤ {{ Φ }}))
  | `({{{{ $P }}}} $es @ $E {{{{ $v, $Q }}}}) =>
    `(iprop(□ ∀ Φ, $P -∗ (∀ $v:ident : Val, $Q -∗ Φ $v) -∗
        WP ($es : Expr) @ Stuckness.NotStuck ; $E {{ Φ }}))

@[rocq_alias iriswasm.i32const]
def i32const (n : _root_.Int) : BasicInstruction := .const (.int32 (Wasm.Int.intOfZ n))

@[rocq_alias iriswasm.value_of_int]
def valueOfInt (n : _root_.Int) : Value := .int32 (Wasm.Int.intOfZ n)

@[rocq_alias iriswasm.u32const]
def u32const (n : Nat) : BasicInstruction := .const (.int32 (Wasm.Int.intOfZ (n : _root_.Int)))

@[rocq_alias iriswasm.value_of_uint]
def valueOfUint (n : Nat) : Value := .int32 (Wasm.Int.intOfZ (n : _root_.Int))

/-! Some useful constants -/

@[rocq_alias iriswasm.two14]
def two14 : Nat := 16384

@[rocq_alias iriswasm.two16]
def two16 : Nat := 65536

@[rocq_alias iriswasm.two32]
def two32 : Nat := 4294967296

@[rocq_alias iriswasm.ffff0000]
def ffff0000 : Nat := 4294901760

section pointsTo
variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF]

@[rocq_alias iriswasm.points_to_i32]
def pointsToI32 (n i : Nat) (v : I32) : IProp GF := iprop(
  ∃ a b c d, n ↦[wm][ i ] a ∗ n ↦[wm][ i + 1 ] b ∗
    n ↦[wm][ i + 2 ] c ∗ n ↦[wm][ i + 3 ] d ∗
    ⌜serialiseI32 v = [a, b, c, d]⌝)

end pointsTo

/-- `n ↦[i32][ k ] v`: the little-endian bytes of the `i32` value `v` at offset `k` of
memory `n`. -/
notation:50 n:51 " ↦[i32][ " k " ] " v:51 => pointsToI32 n k v

@[rocq_alias iriswasm.u32_modulus]
theorem u32_modulus : Wasm.Int.modulus 32 = 4294967296 := by decide

@[rocq_alias iriswasm.of_nat_to_nat_plus]
theorem of_nat_to_nat_plus (a b : Nat) : a + b = a + b := rfl

@[rocq_alias iriswasm.drop_is_nil]
theorem drop_is_nil {A : Type} (n : Nat) (s : List A) : s.drop n = [] → n ≥ s.length := by
  intro h; have := congrArg List.length h; simp at this; omega

@[rocq_alias iriswasm.in_take]
theorem in_take {A : Type} (n : Nat) (s : List A) (x : A) : x ∈ s.take n → x ∈ s :=
  List.mem_of_mem_take

@[rocq_alias iriswasm.two16_div_i32]
theorem two16_div_i32 : (two16 : _root_.Int) ∣ Wasm.Int.modulus 32 := ⟨65536, by decide⟩

@[rocq_alias iriswasm.wasm_int_signed]
theorem wasm_int_signed (x : _root_.Int) :
    -2147483648 ≤ x ∧ x ≤ 2147483647 → Wasm.Int.signed (Wasm.Int.repr (w := 32) x) = x := by
  intro h; simp only [Wasm.Int.signed, Wasm.Int.repr]
  rw [BitVec.toInt_ofInt]; apply Int.bmod_eq_of_le <;> simp <;> omega

@[rocq_alias iriswasm.wasm_int_unsigned]
theorem wasm_int_unsigned (x : _root_.Int) :
    0 ≤ x ∧ x ≤ 4294967295 → Wasm.Int.unsigned (Wasm.Int.repr (w := 32) x) = x := by
  intro h; simp only [Wasm.Int.unsigned, Wasm.Int.repr]
  rw [BitVec.toNat_ofInt]; simp; omega

@[rocq_alias iriswasm.value_of_int_repr]
theorem value_of_int_repr (a : I32) : ∃ v, Value.int32 a = valueOfInt v :=
  ⟨a.toInt, by simp [valueOfInt]⟩

@[rocq_alias iriswasm.value_of_uint_repr]
theorem value_of_uint_repr (a : I32) : ∃ v, Value.int32 a = valueOfUint v :=
  ⟨a.toNat, by simp [valueOfUint]⟩

@[rocq_alias iriswasm.div_mod_i32]
theorem div_mod_i32 (v : Nat) :
    let k := Wasm.Int.nOfUint (Wasm.Int.intOfZ (w := 32) (v : _root_.Int))
    65536 ∣ v → 65536 ∣ k := by
  intro k h; simp only [k, Wasm.Int.nOfUint, Wasm.Int.intOfZ, Wasm.Int.repr, BitVec.ofInt_natCast,
    BitVec.toNat_ofNat]
  exact (Nat.dvd_mod_iff (by decide : 65536 ∣ 2^32)).2 h

@[rocq_alias iriswasm.int_of_Z_mod]
theorem int_of_Z_mod (v : Nat) :
    Wasm.Int.intOfZ (w := 32) (v : _root_.Int) =
      Wasm.Int.intOfZ (w := 32)
        ((Wasm.Int.zModModulus 32 (v : _root_.Int)).toNat : _root_.Int) := by
  simp only [Wasm.Int.intOfZ, Wasm.Int.repr, Wasm.Int.zModModulus, Wasm.Int.modulus]
  have : ((v : _root_.Int) % 2 ^ 32).toNat = v % 2 ^ 32 := by omega
  rw [this, BitVec.ofInt_natCast, BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq; simp

section Stack
variable {hlc : HasLC} {GF : BundledGFunctors} [WasmG hlc GF]

set_option warn.classDefReducibility false in
attribute [local instance] WasmG.invGS

@[rocq_alias iriswasm.points_to_i32_eq]
theorem points_to_i32_eq (n1 i1 : Nat) (v1 : I32) (n2 i2 : Nat) (v2 : I32) :
    n1 = n2 → i1 = i2 → v1 = v2 → ⊢ (n1 ↦[i32][ i1 ] v1 -∗ n2 ↦[i32][ i2 ] v2 : IProp GF) := by
  intro h1 h2 h3; subst h1 h2 h3; iintro H; iexact H

@[rocq_alias iriswasm.points_to_wm_eq]
theorem points_to_wm_eq (n1 : Nat) (b1 : Byte) (k1 n2 : Nat) (b2 : Byte) (k2 : Nat) :
    n1 = n2 → b1 = b2 → k1 = k2 → ⊢ (n1 ↦[wm][ k1 ] b1 -∗ n2 ↦[wm][ k2 ] b2 : IProp GF) := by
  intro h1 h2 h3; subst h1 h2 h3; iintro H; iexact H

@[rocq_alias iriswasm.points_to_wms_eq]
theorem points_to_wms_eq (n1 : Nat) (l1 : Bytes) (k1 n2 : Nat) (l2 : Bytes) (k2 : Nat) :
    n1 = n2 → l1 = l2 → k1 = k2 → ⊢ (n1 ↦[wms][ k1 ] l1 -∗ n2 ↦[wms][ k2 ] l2 : IProp GF) := by
  intro h1 h2 h3; subst h1 h2 h3; iintro H; iexact H

@[rocq_alias iriswasm.i32_wms]
theorem i32_wms (n i : Nat) (v : I32) :
    (n ↦[i32][ i ] v : IProp GF) ⊣⊢ n ↦[wms][ i ] serialiseI32 v := by
  obtain ⟨a, b, c, d, h⟩ : ∃ a b c d, serialiseI32 v = [a, b, c, d] := by
    have hl : (serialiseI32 v).length = 4 := length_encodeInt ..
    match serialiseI32 v, hl with
    | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩
  rw [h]
  unfold pointsToI32 memBlockAtPos
  show _ ⊣⊢ (iprop(n ↦[wm][ i ] a ∗ n ↦[wm][ i + 1 ] b ∗ n ↦[wm][ i + 2 ] c ∗
      n ↦[wm][ i + 3 ] d ∗ emp) : IProp GF)
  constructor
  · iintro ⟨%a', %b', %c', %d', Ha, Hb, Hc, Hd, %he⟩
    rw [h] at he
    cases he
    iframe
  · iintro ⟨Ha, Hb, Hc, Hd, -⟩
    iexists a, b, c, d
    iframe
    ipureintro
    exact h

/-- The `isStack v l n` predicate describes a stack starting at location `v`, containing the
mathematical stack `l`, at memory `n`, of size 1 page. The first cell `v` points to the current top
cell of the stack, so the maximum number of elements the stack could contain is 16383. -/
@[rocq_alias iriswasm.isStack]
def isStack (v : Nat) (l : List I32) (n : Nat) : IProp GF :=
  let stP := v + l.length * 4
  iprop(⌜two16 ∣ v⌝ ∗ ⌜0 ≤ v ∧ v ≤ ffff0000⌝ ∗ ⌜l.length < two14⌝ ∗
    n ↦[i32][ v ] (Wasm.Int.repr (stP : _root_.Int)) ∗
    ([∗list] i ↦ w ∈ l, n ↦[i32][ stP - 4 * i ] w) ∗
    ∃ bs : Bytes, ⌜bs.length = two16 - 4 - l.length * 4⌝ ∗ n ↦[wms][ stP + 4 ] bs)

@[rocq_alias iriswasm.stk]
def stk : String := "STACK"

@[rocq_alias iriswasm.stkN]
def stkN : Namespace := ndot nroot stk

/-! stack module invariant -/

@[rocq_alias iriswasm.N_divide_dec]
def N_divide_dec (a b : Nat) : Decidable (a ∣ b) := inferInstance

@[rocq_alias iriswasm.multiples_upto]
inductive MultiplesUpto : Nat → Nat → List Nat → Prop where
  | baseNil (n : Nat) : n > 0 → MultiplesUpto n 0 []
  | ind (n m : Nat) (l : List Nat) : MultiplesUpto n m l → MultiplesUpto n (m + n) (m :: l)

@[rocq_alias iriswasm.multiples_upto_nil]
theorem multiples_upto_nil (n m : Nat) (l : List Nat) : MultiplesUpto n m l → n > 0 := by
  intro h; induction h <;> assumption

@[rocq_alias iriswasm.multiples_upto_le]
theorem multiples_upto_le (n m : Nat) (l : List Nat) : m > 0 → MultiplesUpto n m l → n ≤ m := by
  intro _ h; cases h <;> omega

@[rocq_alias iriswasm.le_mul]
theorem le_mul (x n : Nat) : 2 ≤ x → 0 < n → n < x * n := by
  intro h1 h2; have := Nat.mul_le_mul_right n h1; omega

@[rocq_alias iriswasm.lt_mul]
theorem lt_mul (x n : Nat) : x * n < n → x = 0 := by
  intro h; rcases x with _ | x; rfl; rw [Nat.succ_mul] at h; omega

@[rocq_alias iriswasm.multiples_upto_div]
theorem multiples_upto_div (n m : Nat) (l : List Nat) : MultiplesUpto n m l → n ∣ m := by
  intro h; induction h with
  | baseNil => exact Nat.dvd_zero _
  | ind m l _ ih => exact Nat.dvd_add ih (Nat.dvd_refl n)

@[rocq_alias iriswasm.multiples_upto_in_lt]
theorem multiples_upto_in_lt (n m : Nat) (l : List Nat) (i : Nat) :
    MultiplesUpto n m l → i ∈ l → i < m := by
  intro h; induction h with
  | baseNil => simp
  | ind m l h ih =>
    have := multiples_upto_nil _ _ _ h
    intro hi; rcases List.mem_cons.1 hi with rfl | hi; omega; have := ih hi; omega

@[rocq_alias iriswasm.multiples_upto_in_div]
theorem multiples_upto_in_div (n m : Nat) (l : List Nat) (i : Nat) :
    MultiplesUpto n m l → i ∈ l → n ∣ i := by
  intro h; induction h with
  | baseNil => simp
  | ind m l h ih =>
    intro hi; rcases List.mem_cons.1 hi with rfl | hi
    · exact multiples_upto_div _ _ _ h
    · exact ih hi

@[rocq_alias iriswasm.times_lt]
theorem times_lt (n1 n2 n3 : Nat) : n1 * n3 < n2 * n3 → n1 < n2 := Nat.lt_of_mul_lt_mul_right

@[rocq_alias iriswasm.times_lt_plus]
theorem times_lt_plus (x x0 n : Nat) : n > 0 → x * n < x0 * n + n → x ≤ x0 := by
  intro _ h; rw [← Nat.succ_mul] at h; have := Nat.lt_of_mul_lt_mul_right h; omega

@[rocq_alias iriswasm.Nat2N_le_inj]
theorem Nat2N_le_inj (n1 n2 : Nat) : n1 ≤ n2 ↔ n1 ≤ n2 := .rfl

@[rocq_alias iriswasm.Nat2N_lt_inj]
theorem Nat2N_lt_inj (n1 n2 : Nat) : n1 < n2 ↔ n1 < n2 := .rfl

@[rocq_alias iriswasm.N2Nat_le_inj]
theorem N2Nat_le_inj (n1 n2 : Nat) : n1 ≤ n2 ↔ n1 ≤ n2 := .rfl

@[rocq_alias iriswasm.N2Nat_lt_inj]
theorem N2Nat_lt_inj (n1 n2 : Nat) : n1 < n2 ↔ n1 < n2 := .rfl

@[rocq_alias iriswasm.multiples_upto_in]
theorem multiples_upto_in (n m : Nat) (l : List Nat) (i : Nat) :
    MultiplesUpto n m l → i < m → n ∣ i → i ∈ l := by
  intro h; induction h with
  | baseNil => omega
  | ind m l h ih =>
    intro hlt hdiv
    by_cases hi : i = m
    · simp [hi]
    · refine List.mem_cons_of_mem _ (ih ?_ hdiv)
      obtain ⟨a, rfl⟩ := hdiv; obtain ⟨b, rfl⟩ := multiples_upto_div _ _ _ h
      have hn := multiples_upto_nil _ _ _ h
      have : a ≤ b := times_lt_plus a b n hn (by rw [Nat.mul_comm a, Nat.mul_comm b]; omega)
      have : n * a ≠ n * b := hi
      have : a ≠ b := fun e => this (e ▸ rfl)
      have := Nat.mul_lt_mul_of_pos_left (show a < b by omega) hn; omega

@[rocq_alias iriswasm.stackModuleInv]
def stackModuleInv (isStack : Nat → List I32 → IProp GF) (nextStackAddrIs : Nat → IProp GF) :
    IProp GF := iprop(
  ∃ nextStack : Nat, ⌜pageSize ∣ nextStack⌝ ∗ nextStackAddrIs nextStack ∗
    ∃ l : List Nat, ⌜MultiplesUpto pageSize nextStack l⌝ ∗
      [∗list] s ∈ l, ∃ stk, isStack s stk)

@[rocq_alias iriswasm.validate_stack]
def validateStack (x : Immediate) : List BasicInstruction :=
  [ .getLocal x,
    i32const 65536,
    .binop .i32 (.i (.rem .u)),
    .if_ (.result none) [.unreachable] [] ]

@[rocq_alias iriswasm.is_stack_divide]
theorem is_stack_divide (v : Nat) (s : List I32) (n : Nat) :
    (isStack v s n : IProp GF) ⊢ ⌜(65536 : _root_.Int) ∣ (v : _root_.Int)⌝ := by
  unfold isStack
  iintro ⟨%h, -⟩
  ipureintro
  exact Int.natCast_dvd_natCast.2 h

@[rocq_alias iriswasm.stack_pure]
theorem stack_pure (v : Nat) (s : List I32) (n : Nat) :
    ⊢ (isStack v s n -∗
      ⌜two16 ∣ v⌝ ∗ ⌜0 ≤ v ∧ v ≤ ffff0000⌝ ∗ ⌜s.length < two14⌝ ∗ isStack v s n : IProp GF) := by
  simp only [isStack]
  iintro ⟨%h1, %h2, %h3, H⟩
  iframe H
  ipureintro
  exact ⟨h1, h2, h3, h1, h2, h3⟩

private theorem wp_wand_s {s : Stuckness} {E : CoPset} {e : Expr} {Φ Ψ : Val → IProp GF} :
    WP e @ s ; E {{ Φ }} ⊢ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s ; E {{ Ψ }} :=
  IrisWp.wp_wand (fun f => iprop(↪[frame] f)) (ι := wasmIrisGS)

private theorem rem_two16_eq_zero (v : Nat) :
    Wasm.Int.intOfZ (w := 32) (v : _root_.Int) % Wasm.Int.intOfZ 65536 = Wasm.Int.zero ↔
      65536 ∣ v := by
  simp only [Wasm.Int.intOfZ, Wasm.Int.repr, Wasm.Int.zero, BitVec.ofInt_natCast,
    ← BitVec.toNat_inj, BitVec.toNat_umod, BitVec.toNat_ofNat]
  simp only [show ((65536 : _root_.Int)) = ((65536 : Nat) : _root_.Int) from rfl,
    BitVec.ofInt_natCast, BitVec.toNat_ofNat]
  rw [Nat.mod_mod_of_dvd _ (by decide : 65536 ∣ 2 ^ 32)]
  omega

/-- The `get_local x; i32.const 65536; i32.rem_u` prefix of `validate_stack x`. -/
private theorem wp_validate_stack_prefix (v : Nat) (f : Frame) (E : CoPset) (x : Nat)
    (Φ : Val → IProp GF) (hlocs : f.locs[x]? = some (valueOfUint v)) :
    ⊢ (↪[frame] f -∗
      (↪[frame] f -∗ WP ([.basic (.const (.int32
          (Wasm.Int.intOfZ (w := 32) (v : _root_.Int) % Wasm.Int.intOfZ 65536))),
        .basic (.if_ (.result none) [.unreachable] [])] : Expr) @ E {{ Φ }}) -∗
      WP (toEList (validateStack x) : Expr) @ E {{ Φ }} : IProp GF) := by
  iintro Hf Hk
  rw [show (toEList (validateStack x) : Expr) = [.basic (.getLocal x)] ++
    [.basic (i32const 65536), .basic (.binop .i32 (.i (.rem .u))),
      .basic (.if_ (.result none) [.unreachable] [])] from rfl]
  iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV [valueOfUint v]⌝ ∗ ↪[frame] f))
  isplitr
  · iintro ⟨%h, -⟩; cases h
  isplitl [Hf]
  · iapply wp_get_local _ _ _ _ (fun w => iprop(⌜w = .immV [valueOfUint v]⌝)) _ hlocs $$ [] Hf
    inext; ipureintro; rfl
  iintro %w ⟨%hw, Hf⟩
  subst hw
  rw [show (ofVal (.immV [valueOfUint v]) ++ [.basic (i32const 65536),
      .basic (.binop .i32 (.i (.rem .u))), .basic (.if_ (.result none) [.unreachable] [])] : Expr) =
    [.basic (.const (valueOfUint v)), .basic (.const (.int32 (Wasm.Int.intOfZ 65536))),
      .basic (.binop .i32 (.i (.rem .u)))] ++ [.basic (.if_ (.result none) [.unreachable] [])]
    from rfl]
  iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV [.int32
    (Wasm.Int.intOfZ (w := 32) (v : _root_.Int) % Wasm.Int.intOfZ 65536)]⌝ ∗ ↪[frame] f))
  isplitr
  · iintro ⟨%h, -⟩; cases h
  isplitl [Hf]
  · have hb : appBinop (.i (.rem .u)) (valueOfUint v) (.int32 (Wasm.Int.intOfZ 65536)) =
        some (.int32 (Wasm.Int.intOfZ (w := 32) (v : _root_.Int) % Wasm.Int.intOfZ 65536)) := by
      simp [valueOfUint, appBinop, appBinopI, Wasm.Int.iremU]; decide
    iapply wp_binop (t := .i32) rfl rfl .i32Agree hb $$ Hf
    inext; ipureintro; rfl
  iintro %w ⟨%hw, Hf⟩
  subst hw
  rw [show (ofVal (.immV [.int32 (Wasm.Int.intOfZ (w := 32) (v : _root_.Int) %
      Wasm.Int.intOfZ 65536)]) ++ [.basic (.if_ (.result none) [.unreachable] [])] : Expr) =
    [.basic (.const (.int32 (Wasm.Int.intOfZ (w := 32) (v : _root_.Int) %
      Wasm.Int.intOfZ 65536))), .basic (.if_ (.result none) [.unreachable] [])] from rfl]
  iapply Hk $$ Hf

@[rocq_alias iriswasm.is_stack_valid]
theorem is_stack_valid (v : Nat) (s : List I32) (n : Nat) (f : Frame) (E : CoPset) (x : Nat) :
    (iprop(⌜f.locs[x]? = some (valueOfUint v)⌝ ∗ isStack v s n ∗ ↪[frame] f) : IProp GF) ⊢
    WP (toEList (validateStack x) : Expr) @ E
      {{ w, ⌜w = .immV []⌝ ∗ isStack v s n ∗ ↪[frame] f }} := by
  iintro ⟨%hlocs, Hstack, Hf⟩
  icases stack_pure v s n $$ Hstack with ⟨%hdiv, -, -, Hstack⟩
  iapply wp_wand_s (Φ := fun w => iprop((⌜w = .immV []⌝ ∗ isStack v s n) ∗ ↪[frame] f))
    $$ [Hstack Hf]
  · iapply wp_validate_stack_prefix v f E x _ hlocs $$ Hf
    iintro Hf
    iapply wp_if_false ((rem_two16_eq_zero v).2 hdiv) $$ Hf
    iintro !> Hf
    rw [show ([.basic (.block (.result none) [])] : Expr) = [] ++ [.basic (.block (.result none) [])]
      from rfl]
    iapply wp_block (bt := .result none) (vs := []) rfl rfl rfl rfl rfl $$ Hf
    iintro !> Hf
    iapply wp_label_value (Φ := fun w => iprop(⌜w = .immV []⌝ ∗ isStack v s n)) (by rfl) $$ Hf
    inext; iframe; ipureintro; rfl
  · iintro %w ⟨⟨%hw, Hs⟩, Hf⟩
    iframe
    ipureintro; exact hw

@[rocq_alias iriswasm.check_stack_valid]
theorem check_stack_valid (v : Nat) (f : Frame) (E : CoPset) (x : Nat) :
    (iprop(⌜f.locs[x]? = some (valueOfUint v)⌝ ∗ ↪[frame] f) : IProp GF) ⊢
    WP (toEList (validateStack x) : Expr) @ E
      {{ w, (⌜w = .trapV⌝ ∨ ⌜w = .immV []⌝ ∗ ⌜65536 ∣ v⌝) ∗ ↪[frame] f }} := by
  iintro ⟨%hlocs, Hf⟩
  iapply wp_validate_stack_prefix v f E x _ hlocs $$ Hf
  iintro Hf
  by_cases hr : Wasm.Int.intOfZ (w := 32) (v : _root_.Int) % Wasm.Int.intOfZ 65536 =
    Wasm.Int.zero
  · iapply wp_if_false hr $$ Hf
    iintro !> Hf
    rw [show ([.basic (.block (.result none) [])] : Expr) = [] ++ [.basic (.block (.result none) [])]
      from rfl]
    iapply wp_block (bt := .result none) (vs := []) rfl rfl rfl rfl rfl $$ Hf
    iintro !> Hf
    iapply wp_label_value
      (Φ := fun w => iprop(⌜w = .trapV⌝ ∨ ⌜w = .immV []⌝ ∗ ⌜65536 ∣ v⌝)) (by rfl) $$ Hf
    inext; iright; isplitr
    · ipureintro; rfl
    · ipureintro; exact (rem_two16_eq_zero v).1 hr
  · iapply wp_if_true hr $$ Hf
    iintro !> Hf
    rw [show ([.basic (.block (.result none) [.unreachable])] : Expr) =
      [] ++ [.basic (.block (.result none) [.unreachable])] from rfl]
    iapply wp_block (bt := .result none) (vs := []) (m := 0) rfl rfl rfl rfl rfl $$ Hf
    iintro !> Hf
    iapply wp_wand_s (Φ := fun w => iprop(⌜w = .trapV⌝ ∗ ↪[frame] f)) $$ [Hf]
    · rw [show ([.label 0 [] ([] ++ toEList [.unreachable])] : Expr) =
          [] ++ [.label 0 [] [.basic .unreachable]] ++ [] from rfl]
      iapply IrisRulesTrap.wp_label_trap _ _ _ [] _ _ [] _ _ rfl $$ Hf
      iintro Hf
      iapply wp_unreachable (Φ := fun w => iprop(⌜w = .trapV⌝)) $$ Hf
      inext; ipureintro; rfl
    · iintro %w ⟨%hw, Hf⟩
      iframe
      ileft; ipureintro; exact hw

@[rocq_alias iriswasm.validate_stack_bound]
def validateStackBound (x : Immediate) : List BasicInstruction :=
  [ .getLocal x,
    .load .i32 none ⟨0, 0, 0⟩,
    .drop ]

/-- An `i32` address below `2^32` survives the `i32` round trip. -/
private theorem addr_eq (a : Nat) (h : a < 4294967296) :
    Wasm.Int.nOfUint (Wasm.Int.intOfZ (w := 32) (a : _root_.Int)) + 0 = a := by
  simp [Wasm.Int.nOfUint, Wasm.Int.intOfZ, Wasm.Int.repr, BitVec.ofInt_natCast]
  omega

private theorem bits_int32 (c : I32) : bits (.int32 c) = serialiseI32 c := rfl

private theorem set_self {s : List I32} {j : Nat} {sv : I32} (h : s[j]? = some sv) :
    s.set j sv = s := by
  rw [List.getElem?_eq_some_iff] at h
  obtain ⟨h, rfl⟩ := h
  simp

@[rocq_alias iriswasm.stack_load_0]
theorem stack_load_0 (v : Nat) (s : List I32) (n : Nat) (f : Frame) (E : CoPset) :
    ⊢ (⌜f.inst.memory[0]? = some n⌝ -∗ isStack v s n -∗ ↪[frame] f -∗
      WP ([.basic (.const (valueOfUint v)), .basic (.load .i32 none ⟨0, 0, 0⟩)] : Expr) @ E
        {{ w, ⌜w = .immV [valueOfUint (v + s.length * 4)]⌝ ∗ isStack v s n ∗ ↪[frame] f }}
      : IProp GF) := by
  simp only [isStack]
  iintro %hmem ⟨%hdiv, %hvb, %hlen, Hv, Hl, Hb⟩ Hf
  have e := addr_eq v (by simp [ffff0000] at hvb; omega)
  ihave Hv := (i32_wms n v _).1 $$ Hv
  ihave Hv := points_to_wms_eq n _ v n _ _ rfl rfl e.symm $$ Hv
  rw [show valueOfUint v = .int32 (Wasm.Int.intOfZ (v : _root_.Int)) from rfl]
  iapply wp_wand_s (Φ := fun w => iprop((⌜w = .immV [valueOfUint (v + s.length * 4)]⌝ ∗
      n ↦[wms][ Wasm.Int.nOfUint (Wasm.Int.intOfZ (w := 32) (v : _root_.Int)) + 0 ]
        bits (.int32 (Wasm.Int.repr ((v + s.length * 4 : Nat) : _root_.Int)))) ∗ ↪[frame] f))
    $$ [Hv Hf]
  · iapply wp_load (x := 0) (fun w => iprop(⌜w = .immV [valueOfUint (v + s.length * 4)]⌝)) _ _ .i32
      (.int32 (Wasm.Int.repr ((v + s.length * 4 : Nat) : _root_.Int))) 0 0
      (.i32 (Wasm.Int.intOfZ (v : _root_.Int))) n f rfl hmem
    isplitr
    · inext; ipureintro; rfl
    rw [bits_int32]
    isplitl [Hf]
    · iexact Hf
    · iexact Hv
  · iintro %w ⟨⟨%hw, Hv⟩, Hf⟩
    rw [bits_int32]
    ihave Hv := points_to_wms_eq n _ _ n _ v rfl rfl e $$ Hv
    ihave Hv := (i32_wms n v _).2 $$ Hv
    iframe
    ipureintro
    exact ⟨hw, hdiv, hvb, hlen⟩

@[rocq_alias iriswasm.is_stack_bound_valid]
theorem is_stack_bound_valid (v : Nat) (s : List I32) (n : Nat) (f : Frame) (E : CoPset)
    (x : Nat) :
    (iprop(⌜f.inst.memory[0]? = some n⌝ ∗ ⌜f.locs[x]? = some (valueOfUint v)⌝ ∗
      isStack v s n ∗ ↪[frame] f) : IProp GF) ⊢
    WP (toEList (validateStackBound x) : Expr) @ E
      {{ w, ⌜w = .immV []⌝ ∗ isStack v s n ∗ ↪[frame] f }} := by
  iintro ⟨%hmem, %hlocs, Hs, Hf⟩
  rw [show (toEList (validateStackBound x) : Expr) = [.basic (.getLocal x)] ++
    [.basic (.load .i32 none ⟨0, 0, 0⟩), .basic .drop] from rfl]
  iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV [valueOfUint v]⌝ ∗ ↪[frame] f))
  isplitr
  · iintro ⟨%h, -⟩; cases h
  isplitl [Hf]
  · iapply wp_get_local _ _ _ _ (fun w => iprop(⌜w = .immV [valueOfUint v]⌝)) _ hlocs $$ [] Hf
    inext; ipureintro; rfl
  iintro %w ⟨%hw, Hf⟩
  subst hw
  rw [show (ofVal (.immV [valueOfUint v]) ++
      [.basic (.load .i32 none ⟨0, 0, 0⟩), .basic .drop] : Expr) =
    [.basic (.const (valueOfUint v)), .basic (.load .i32 none ⟨0, 0, 0⟩)] ++
      [.basic .drop] from rfl]
  iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV [valueOfUint (v + s.length * 4)]⌝ ∗
    isStack v s n ∗ ↪[frame] f))
  isplitr
  · iintro ⟨%h, -⟩; cases h
  isplitl [Hs Hf]
  · iapply stack_load_0 v s n f E $$ [] Hs Hf
    ipureintro; exact hmem
  iintro %w ⟨%hw, Hs, Hf⟩
  subst hw
  rw [show (ofVal (.immV [valueOfUint (v + s.length * 4)]) ++ [.basic .drop] : Expr) =
    [.basic (.const (valueOfUint (v + s.length * 4))), .basic .drop] from rfl]
  iapply wp_wand_s (Φ := fun w => iprop(⌜w = .immV []⌝ ∗ ↪[frame] f)) $$ [Hf]
  · iapply wp_drop (Φ := fun w => iprop(⌜w = .immV []⌝)) $$ Hf
    inext; ipureintro; rfl
  · iintro %w ⟨%hw, Hf⟩
    iframe
    ipureintro; exact hw

/-- `validate_stack_bound` traps as soon as the `i32` load at `v` is out of bounds. -/
private theorem fail_bound_aux {aw : AddrType} (v n : Nat) (f : Frame) (E : CoPset)
    (x len : Nat) (es : Expr)
    (hmem : f.inst.memory[0]? = some n) (hlocs : f.locs[x]? = some (valueOfUint v))
    (hk : Wasm.Int.nOfUint (Wasm.Int.intOfZ (w := 32) (v : _root_.Int)) + 4 > len) :
    ⊢ (↪[frame] f -∗ n ↦[wmlength] (aw, len) -∗
      WP (toEList (validateStackBound x) ++ es : Expr) @ E
        {{ w, ⌜w = .trapV⌝ ∗ n ↦[wmlength] (aw, len) ∗ ↪[frame] f }} : IProp GF) := by
  iintro Hf Hlen
  rw [show (toEList (validateStackBound x) ++ es : Expr) = [.basic (.getLocal x)] ++
    ([.basic (.load .i32 none ⟨0, 0, 0⟩), .basic .drop] ++ es) from rfl]
  iapply wp_seq _ _ _ (fun w => iprop(⌜w = .immV [valueOfUint v]⌝ ∗ ↪[frame] f))
  isplitr
  · iintro ⟨%h, -⟩; cases h
  isplitl [Hf]
  · iapply wp_get_local _ _ _ _ (fun w => iprop(⌜w = .immV [valueOfUint v]⌝)) _ hlocs $$ [] Hf
    inext; ipureintro; rfl
  iintro %w ⟨%hw, Hf⟩
  subst hw
  rw [show (ofVal (.immV [valueOfUint v]) ++
      ([.basic (.load .i32 none ⟨0, 0, 0⟩), .basic .drop] ++ es) : Expr) =
    [.basic (.const (valueOfUint v)), .basic (.load .i32 none ⟨0, 0, 0⟩)] ++
      ([.basic .drop] ++ es)
    from rfl]
  rw [show valueOfUint v = .int32 (Wasm.Int.intOfZ (v : _root_.Int)) from rfl]
  iapply (wandIff_equiv (wp_wasm_empty_ctx _ E _ _)).2
  iapply wp_seq_can_trap_ctx _ E _ (fun _ => iprop(⌜False⌝)) _ _ 0 (.base [] [])
    (fun f' => iprop(⌜f' = f⌝ ∗ n ↦[wmlength] (aw, len))) f
  isplitr
  · iintro %h; exact h.elim
  isplitr
  · iintro %f' ⟨Hf', %hf, Hlen'⟩
    subst hf
    iframe
    ipureintro; rfl
  isplitl [Hf]
  · iexact Hf
  isplitl [Hlen]
  · iintro Hf
    iapply wp_wand_s (Φ := fun w => iprop((⌜w = .trapV⌝ ∗ n ↦[wmlength] (aw, len)) ∗ ↪[frame] f))
      $$ [Hf Hlen]
    · iapply wp_load_failure (aw := aw) (x := 0) (fun w => iprop(⌜w = .trapV⌝)) _ _ 0 0
        (.i32 (Wasm.Int.intOfZ (v : _root_.Int))) n f .i32 len hmem
        (by simpa only [AddressOperand.unsigned, lengthT, Nat.add_zero] using hk)
      isplitr
      · inext; ipureintro; rfl
      isplitl [Hf]
      · iexact Hf
      · iexact Hlen
    · iintro %w ⟨⟨%hw, Hlen⟩, Hf⟩
      isplitr
      · ileft; ipureintro; exact hw
      iexists f
      iframe
      ipureintro; rfl
  · iintro %w %f0 ⟨%h, -⟩; exact h.elim

#rocq_ignore iriswasm.check_stack_bound_valid "The bounds check preserves memory metadata at either width"
theorem check_stack_bound_valid {aw : AddrType} (v n : Nat) (f : Frame) (E : CoPset)
    (x len : Nat) (s : List I32) :
    let k := Wasm.Int.nOfUint (Wasm.Int.intOfZ (w := 32) (v : _root_.Int))
    (iprop(⌜f.inst.memory[0]? = some n⌝ ∗ ⌜f.locs[x]? = some (valueOfUint v)⌝ ∗
      ↪[frame] f ∗ n ↦[wmlength] (aw, len) ∗ (⌜k < len⌝ -∗ isStack v s n)) : IProp GF) ⊢
    WP (toEList (validateStackBound x) : Expr) @ E
      {{ w, (⌜w = .trapV⌝ ∨ ⌜w = .immV []⌝ ∗ ⌜k < len⌝ ∗ isStack v s n) ∗
        n ↦[wmlength] (aw, len) ∗ ↪[frame] f }} := by
  intro k
  iintro ⟨%hmem, %hlocs, Hf, Hlen, Hs⟩
  by_cases hk : k + 4 > len
  · iapply wp_wand_s (Φ := fun w => iprop(⌜w = .trapV⌝ ∗ n ↦[wmlength] (aw, len) ∗ ↪[frame] f))
      $$ [Hf Hlen]
    · have h := fail_bound_aux (GF := GF) (aw := aw) v n f E x len [] hmem hlocs hk
      rw [List.append_nil] at h
      iapply h $$ Hf Hlen
    · iintro %w ⟨%hw, Hlen, Hf⟩
      iframe
      ileft; ipureintro; exact hw
  · ispecialize Hs $$ []
    · ipureintro; omega
    iapply wp_wand_s (Φ := fun w => iprop(⌜w = .immV []⌝ ∗ isStack v s n ∗ ↪[frame] f))
      $$ [Hs Hf]
    · iapply is_stack_bound_valid v s n f E x
      iframe
      ipureintro; exact ⟨hmem, hlocs⟩
    · iintro %w ⟨%hw, Hs, Hf⟩
      iframe
      iright
      iframe
      ipureintro; exact ⟨hw, by omega⟩

#rocq_ignore iriswasm.fail_stack_bound_valid "The failed load preserves memory metadata at either width"
theorem fail_stack_bound_valid {aw : AddrType} (v n : Nat) (f : Frame) (E : CoPset)
    (x len : Nat) (es : Expr) :
    let k := Wasm.Int.nOfUint (Wasm.Int.intOfZ (w := 32) (v : _root_.Int));
    ⊢ (⌜f.inst.memory[0]? = some n⌝ ∗ ⌜f.locs[x]? = some (valueOfUint v)⌝ ∗ ⌜k ≥ len⌝ ∗
      ↪[frame] f ∗ n ↦[wmlength] (aw, len) -∗
      WP (toEList (validateStackBound x) ++ es : Expr) @ E
        {{ w, ⌜w = .trapV⌝ ∗ n ↦[wmlength] (aw, len) ∗ ↪[frame] f }} : IProp GF) := by
  intro k
  iintro ⟨%hmem, %hlocs, %hk, Hf, Hlen⟩
  iapply fail_bound_aux v n f E x len es hmem hlocs (by omega) $$ Hf Hlen

@[rocq_alias iriswasm.stack_load_0_alt]
theorem stack_load_0_alt (v : Nat) (s : List I32) (n : Nat) (f : Frame) (E : CoPset) (k : Nat) :
    ⊢ (⌜f.inst.memory[0]? = some n⌝ -∗ ⌜k = v + s.length * 4⌝ -∗ isStack v s n -∗
      ↪[frame] f -∗
      WP ([.basic (.const (valueOfUint v)), .basic (.load .i32 none ⟨0, 0, 0⟩)] : Expr) @ E
        {{ w, ⌜w = .immV [valueOfUint k]⌝ ∗ isStack v s n ∗ ↪[frame] f }}
      : IProp GF) := by
  iintro %hmem %hk Hs Hf
  subst hk
  iapply stack_load_0 v s n f E $$ [] Hs Hf
  ipureintro; exact hmem

@[rocq_alias iriswasm.stack_load_j]
theorem stack_load_j (v : Nat) (s : List I32) (n : Nat) (f : Frame) (E : CoPset) (j : Nat)
    (sv : I32) :
    ⊢ (⌜f.inst.memory[0]? = some n⌝ -∗ ⌜s[j]? = some sv⌝ -∗ ⌜0 ≤ j ∧ j < s.length⌝ -∗
      isStack v s n -∗ ↪[frame] f -∗
      WP ([.basic (.const (valueOfUint (v + s.length * 4 - 4 * j))),
          .basic (.load .i32 none ⟨0, 0, 0⟩)] : Expr) @ E
        {{ w, ⌜w = .immV [.int32 sv]⌝ ∗ isStack v s n ∗ ↪[frame] f }}
      : IProp GF) := by
  simp only [isStack]
  iintro %hmem %hsv %hj ⟨%hdiv, %hvb, %hlen, Hv, Hl, Hb⟩ Hf
  have e := addr_eq (v + s.length * 4 - 4 * j) (by simp [ffff0000, two14] at hvb hlen; omega)
  icases BigSepL.bigSepL_insert_acc (PROP := IProp GF)
      (Φ := fun i w => iprop(n ↦[i32][ v + s.length * 4 - 4 * i ] w)) hsv $$ Hl with ⟨Hj, Hl⟩
  ihave Hj := (i32_wms n _ _).1 $$ Hj
  ihave Hj := points_to_wms_eq n _ _ n _ _ rfl rfl e.symm $$ Hj
  rw [show valueOfUint (v + s.length * 4 - 4 * j) =
    .int32 (Wasm.Int.intOfZ ((v + s.length * 4 - 4 * j : Nat) : _root_.Int)) from rfl]
  iapply wp_wand_s (Φ := fun w => iprop((⌜w = .immV [.int32 sv]⌝ ∗
      n ↦[wms][ Wasm.Int.nOfUint (Wasm.Int.intOfZ (w := 32)
        ((v + s.length * 4 - 4 * j : Nat) : _root_.Int)) + 0 ] bits (.int32 sv)) ∗ ↪[frame] f))
    $$ [Hj Hf]
  · iapply wp_load (x := 0) (fun w => iprop(⌜w = .immV [.int32 sv]⌝)) _ _ .i32 (.int32 sv) 0 0
      (.i32 (Wasm.Int.intOfZ ((v + s.length * 4 - 4 * j : Nat) : _root_.Int))) n f rfl hmem
    isplitr
    · inext; ipureintro; rfl
    rw [bits_int32]
    isplitl [Hf]
    · iexact Hf
    · iexact Hj
  · iintro %w ⟨⟨%hw, Hj⟩, Hf⟩
    rw [bits_int32]
    ihave Hj := points_to_wms_eq n _ _ n _ _ rfl rfl e $$ Hj
    ihave Hj := (i32_wms n _ _).2 $$ Hj
    ihave Hl := Hl $$ %sv Hj
    rw [set_self hsv]
    iframe
    ipureintro
    exact ⟨hw, hdiv, hvb, hlen⟩

@[rocq_alias iriswasm.stack_load_j_alt]
theorem stack_load_j_alt (v : Nat) (s : List I32) (n : Nat) (f : Frame) (E : CoPset) (j k : Nat)
    (sv : I32) :
    ⊢ (⌜f.inst.memory[0]? = some n⌝ -∗ ⌜k = v + s.length * 4 - 4 * j⌝ -∗ ⌜s[j]? = some sv⌝ -∗
      ⌜0 ≤ j ∧ j < s.length⌝ -∗ isStack v s n -∗ ↪[frame] f -∗
      WP ([.basic (.const (valueOfUint k)), .basic (.load .i32 none ⟨0, 0, 0⟩)] : Expr) @ E
        {{ w, ⌜w = .immV [.int32 sv]⌝ ∗ isStack v s n ∗ ↪[frame] f }}
      : IProp GF) := by
  iintro %hmem %hk %hsv %hj Hs Hf
  subst hk
  iapply stack_load_j v s n f E j sv $$ [] [] [] Hs Hf
  · ipureintro; exact hmem
  · ipureintro; exact hsv
  · ipureintro; exact hj

@[rocq_alias iriswasm.stack_store_j]
theorem stack_store_j (v : Nat) (s : List I32) (n : Nat) (f : Frame) (E : CoPset) (j : Nat)
    (sv v0 : I32) :
    ⊢ (⌜f.inst.memory[0]? = some n⌝ -∗ ⌜s[j]? = some sv⌝ -∗ ⌜0 ≤ j ∧ j < s.length⌝ -∗
      isStack v s n -∗ ↪[frame] f -∗
      WP ([.basic (.const (valueOfUint (v + s.length * 4 - 4 * j))),
          .basic (.const (.int32 v0)), .basic (.store .i32 none ⟨0, 0, 0⟩)] : Expr) @ E
        {{ w, ⌜w = .immV []⌝ ∗ isStack v (s.set j v0) n ∗ ↪[frame] f }}
      : IProp GF) := by
  simp only [isStack, List.length_set]
  iintro %hmem %hsv %hj ⟨%hdiv, %hvb, %hlen, Hv, Hl, Hb⟩ Hf
  have e := addr_eq (v + s.length * 4 - 4 * j) (by simp [ffff0000, two14] at hvb hlen; omega)
  icases BigSepL.bigSepL_insert_acc (PROP := IProp GF)
      (Φ := fun i w => iprop(n ↦[i32][ v + s.length * 4 - 4 * i ] w)) hsv $$ Hl with ⟨Hj, Hl⟩
  ihave Hj := (i32_wms n _ _).1 $$ Hj
  ihave Hj := points_to_wms_eq n _ _ n _ _ rfl rfl e.symm $$ Hj
  rw [show valueOfUint (v + s.length * 4 - 4 * j) =
    .int32 (Wasm.Int.intOfZ ((v + s.length * 4 - 4 * j : Nat) : _root_.Int)) from rfl]
  iapply wp_wand_s (Φ := fun w => iprop((⌜w = .immV []⌝ ∗
      n ↦[wms][ Wasm.Int.nOfUint (Wasm.Int.intOfZ (w := 32)
        ((v + s.length * 4 - 4 * j : Nat) : _root_.Int)) + 0 ] bits (.int32 v0)) ∗ ↪[frame] f))
    $$ [Hj Hf]
  · iapply wp_store (x := 0) (fun w => iprop(⌜w = .immV []⌝)) _ _ .i32
      (.int32 v0) (serialiseI32 sv) 0 0
      (.i32 (Wasm.Int.intOfZ ((v + s.length * 4 - 4 * j : Nat) : _root_.Int))) n f rfl
      (length_encodeInt ..) hmem
    isplitr
    · inext; ipureintro; rfl
    isplitl [Hf]
    · iexact Hf
    · iexact Hj
  · iintro %w ⟨⟨%hw, Hj⟩, Hf⟩
    rw [bits_int32]
    ihave Hj := points_to_wms_eq n _ _ n _ _ rfl rfl e $$ Hj
    ihave Hj := (i32_wms n _ _).2 $$ Hj
    ihave Hl := Hl $$ %v0 Hj
    iframe
    ipureintro
    exact ⟨hw, hdiv, hvb, hlen⟩

@[rocq_alias iriswasm.stack_store_j_alt]
theorem stack_store_j_alt (v : Nat) (s : List I32) (n : Nat) (f : Frame) (E : CoPset)
    (j k : Nat) (sv v0 : I32) :
    ⊢ (⌜f.inst.memory[0]? = some n⌝ -∗ ⌜k = v + s.length * 4 - 4 * j⌝ -∗ ⌜s[j]? = some sv⌝ -∗
      ⌜0 ≤ j ∧ j < s.length⌝ -∗ isStack v s n -∗ ↪[frame] f -∗
      WP ([.basic (.const (valueOfUint k)), .basic (.const (.int32 v0)),
          .basic (.store .i32 none ⟨0, 0, 0⟩)] : Expr) @ E
        {{ w, ⌜w = .immV []⌝ ∗ isStack v (s.set j v0) n ∗ ↪[frame] f }}
      : IProp GF) := by
  iintro %hmem %hk %hsv %hj Hs Hf
  subst hk
  iapply stack_store_j v s n f E j sv v0 $$ [] [] [] Hs Hf
  · ipureintro; exact hmem
  · ipureintro; exact hsv
  · ipureintro; exact hj

#rocq_ignore iriswasm.positive_add "ssrnat tail-recursive addition; no counterpart for Lean `Nat`"
#rocq_ignore iriswasm.nat_of_bin_to_N "ssrnat/N bridge; `N` and `nat` are both `Nat` in Lean"

@[rocq_alias iriswasm.divide_and_multiply]
theorem divide_and_multiply (a b : Nat) : b > 0 → b ∣ a → a / b * b = a := by
  intro _ h; exact Nat.div_mul_cancel h

@[rocq_alias iriswasm.div_lt]
theorem div_lt (a b c : Nat) : a < b → c > 0 → c ∣ a → c ∣ b → a / c < b / c := by
  intro h hc ha hb
  obtain ⟨x, rfl⟩ := ha; obtain ⟨y, rfl⟩ := hb
  rw [Nat.mul_div_cancel_left _ hc, Nat.mul_div_cancel_left _ hc]
  exact Nat.lt_of_mul_lt_mul_left h

@[rocq_alias iriswasm.stackAll]
def stackAll {A : Type} : List A → (A → IProp GF) → IProp GF
  | [], _ => iprop(True)
  | a :: s, Φ => iprop(Φ a ∗ stackAll s Φ)

@[rocq_alias iriswasm.stackAll2]
def stackAll2 {A : Type} : List A → List A → (A → A → IProp GF) → IProp GF
  | [], [], _ => iprop(True)
  | a1 :: s1, a2 :: s2, Ψ => iprop(Ψ a1 a2 ∗ stackAll2 s1 s2 Ψ)
  | _, _, _ => iprop(False)

@[rocq_alias iriswasm.stackAll_app]
theorem stackAll_app {A : Type} (s s' : List A) (Φ : A → IProp GF) :
    ⊢ (stackAll (s ++ s') Φ ∗-∗ stackAll s Φ ∗ stackAll s' Φ : IProp GF) := by
  induction s with
  | nil =>
    simp only [List.nil_append, stackAll]
    isplit
    · iintro H; iframe
    · iintro ⟨-, H⟩; iexact H
  | cons a s ih =>
    simp only [List.cons_append, stackAll]
    isplit
    · iintro ⟨Ha, H⟩
      ihave ⟨H1, H2⟩ := (wandIff_equiv ih).1 $$ H
      iframe
    · iintro ⟨⟨Ha, H1⟩, H2⟩
      iframe
      iapply (wandIff_equiv ih).2
      iframe

end Stack

end IrisWasm.Examples.Stack
