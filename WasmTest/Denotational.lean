import IrisWasm.Denotational.Run
import Wasm.ModuleValidation

/-! Concrete observations at native CTree reduction and host boundaries. -/

namespace WasmTest.Denotational

open Wasm IrisWasm IrisWasm.Denotational CTree Relation

private abbrev emptyStore : StoreRecord := ⟨[], [], [], []⟩
private abbrev emptyInst : Instance := ⟨[], [], [], [], []⟩
private abbrev val32 (x : I32) := Value.int32 x
private abbrev const32 (x : I32) := AdministrativeInstruction.basic (.const (val32 x))

private abbrev AtCut (i : Nat) (c d : Cfg) :=
  ∃ t : Tree Cfg, Iterate (trans .tau) i (cutAfter i c) t ∧ Yields t d

private theorem cut_zero {c d : Cfg} : AtCut 0 c d ↔ d = c :=
  (exact_cut_next_iff 0 c d).trans (iterate_zero_iff.trans eq_comm)

private theorem cut_succ {i : Nat} {c d : Cfg} : AtCut (i+1) c d ↔ ∃ b, Next c b ∧ AtCut i b d := by
  rw [AtCut, exact_cut_next_iff, iterate_succ_iff]
  simp only [AtCut, exact_cut_next_iff]

private theorem cut_one {c d : Cfg} : AtCut 1 c d ↔ Next c d := by simp [cut_succ, cut_zero]

private theorem value_no_next (v : Val) (σ : State) (d : Cfg) : ¬ Next (ofVal v, σ) d := by
  intro h
  have hn := val_head_stuck _ _ _ _ _ _ (round_next_iff.1 h)
  rw [to_of_val] at hn; contradiction

private theorem cut_no_run {i : Nat} {c : Cfg} (h : ∀ d, ¬ AtCut i c d) (t : Tree (Val × State)) :
    ¬ Iterate (trans .tau) i (denote c) t := by
  rintro ht; obtain ⟨d, hd, _⟩ := (denote_steps_next_iff i c t).1 ht
  exact h d ((exact_cut_next_iff i c d).2 hd)

section NativeEntry

private def callee := { emptyInst with funcs := [0] }
private def nativeBody : List BasicInstruction := [.getLocal 0, .getLocal 1]
private def nativeState : State :=
  ({ emptyStore with funcs := [.funcNative callee (.tf [.i32] [.i32, .i64]) [.i64] nativeBody] },
    [val32 99], emptyInst)
private def entering : Cfg := ([const32 5, const32 23, .invoke 0], nativeState)
private def entered : Cfg :=
  ([const32 5, .local 2 ⟨[val32 23, .int64 0], callee⟩ [.label 2 [] (toEList nativeBody)]], nativeState)

#guard runCut 1 entering == some entered
#guard runCut 5 entering == some ([const32 5, const32 23, .basic (.const (.int64 0))], nativeState)

theorem native_entry_cut : AtCut 1 entering entered :=
  (runCut_sound (c := entering) (n := 1) (d := entered) (by decide +kernel)).1

end NativeEntry

section ConversionDomain

private def converting (v : Value) (dst : ValueType) (op : Cvtop) (sx : Option Sx) (σ : State) : Cfg :=
  ([.basic (.const v), .basic (.cvtop dst op (typeof v) sx)], σ)

theorem convert_trap_iff {src dst : ValueType} {sx : Option Sx} {v : Value} {σ σ' : State} :
    Next ([.basic (.const v), .basic (.cvtop dst .convert src sx)], σ) ([.trap], σ') ↔
      typesAgree src v ∧ convertCond dst src sx ∧ cvt dst sx v = none ∧ σ' = σ := by
  change Runs (layer _) σ (.next [.trap]) σ' ↔ _
  cases ht : typesAgree src v <;> cases ho : convertCond dst src sx <;> cases hc : cvt dst sx v <;>
    simp [layer, frag, basicLayer, ht, ho, hc, resultCode, emit, vToEList, eq_comm]

/-- Reinterpretation cannot zero-extend: no primitive successor exists, not even a trap. -/
theorem no_width_changing_reinterpret (x : I32) (σ : State) (d : Cfg) :
    ¬ AtCut 1 (converting (.int32 x) .f64 .reinterpret none σ) d := by
  rw [cut_one]
  intro h
  change Runs (layer _) _ (.next d.1) d.2 at h
  simp [converting, layer, frag, basicLayer, typeof, typesAgree, reinterpretCond, lengthT] at h

private def noMem : State := (emptyStore, [], emptyInst)
#guard runCut 1 (converting (.int64 1) .i32 .convert (some .s) noMem) == none
#guard runCut 1 (converting (.float32 ⟨0x7fc00000⟩) .i32 .convert none noMem) == none
#guard runCut 1 (converting (.float32 ⟨0x7fc00000⟩) .i32 .convert (some .s) noMem) ==
  some ([.trap], noMem)
#guard runCut 1 (converting (.float32 ⟨0x80000000⟩) .i32 .reinterpret none noMem) ==
  some ([const32 0x80000000], noMem)

end ConversionDomain

section TruncSat

private def satStep (sx : Sx) (operand expected : Value) : Bool :=
  let σ : State := (emptyStore, [], emptyInst)
  let op := BasicInstruction.cvtop (typeof expected) .truncSat (typeof operand) (some sx)
  runCut 1 ([.basic (.const operand), .basic op], σ) == some ([.basic (.const expected)], σ)

#guard satStep .s (.float32 ⟨0xcf000001⟩) (.int32 0x80000000)
#guard satStep .s (.float32 ⟨0x4f000000⟩) (.int32 0x7fffffff)
#guard satStep .u (.float32 ⟨0xbf800000⟩) (.int32 0)
#guard satStep .s (.float64 ⟨0x7ff0000000000001⟩) (.int32 0)
#guard satStep .u (.float64 ⟨0x41f0000000000000⟩) (.int32 0xffffffff)
#guard satStep .s (.float32 ⟨0xbfc00000⟩) (.int64 0xffffffffffffffff)
#guard satStep .u (.float32 ⟨0x5f800000⟩) (.int64 0xffffffffffffffff)
#guard satStep .s (.float64 ⟨0xc3e0000000000001⟩) (.int64 0x8000000000000000)
#guard satStep .s (.float64 ⟨0x43e0000000000000⟩) (.int64 0x7fffffffffffffff)
#guard satStep .u (.float64 ⟨0xbff0000000000000⟩) (.int64 0)
#guard satStep .u (.float64 ⟨0xfff8000000001234⟩) (.int64 0)

end TruncSat

theorem sign_extension_step (s : StoreRecord) (f : Frame) :
    Reduce s f [const32 0x12340080, .basic (.unop .i32 (.extendS .i8))] s f
      [const32 0xffffff80] := .simple (.unop rfl rfl)

private def unaryCut (x : Value) (t : ValueType) (op : Unop) : Option Cfg :=
  runCut 1 ([.basic (.const x), .basic (.unop t op)], emptyStore, [], emptyInst)

#guard unaryCut (.int64 0x123480000000) .i64 (.extendS .i32) ==
  some ([.basic (.const (.int64 0xffffffff80000000))], emptyStore, [], emptyInst)
#guard unaryCut (.int32 0) .i64 (.extendS .i8) == none
#guard unaryCut (.float64 ⟨0⟩) .f64 (.i .clz) == none

section Locals

private abbrev σlocal (x : I32) : State := (emptyStore, [val32 x], emptyInst)
private abbrev setGet : Cfg := ([const32 7, .basic (.setLocal 0), .basic (.getLocal 0)], σlocal 0)
private abbrev afterSet : Cfg := ([.basic (.getLocal 0)], σlocal 7)
private abbrev afterGet : Cfg := ([const32 7], σlocal 7)

private theorem set_next (d : Cfg) : Next setGet d ↔ d = afterSet := by
  rcases d with ⟨es, σ⟩
  change Runs (layer _) _ (.next es) σ ↔ _
  simp [afterSet, σlocal, layer, frag, basicLayer, emit, handle, vToEList]

private theorem get_next (d : Cfg) : Next afterSet d ↔ d = afterGet := by
  rcases d with ⟨es, σ⟩
  change Runs (layer _) _ (.next es) σ ↔ _
  simp [afterGet, σlocal, layer, frag, basicLayer, emit, handle, and_assoc, vToEList]

example (d : Cfg) : AtCut 0 setGet d ↔ d = setGet := cut_zero
example (d : Cfg) : AtCut 1 setGet d ↔ d = afterSet := cut_one.trans (set_next d)

#guard runCut 2 setGet == some afterGet
#guard runCut 3 setGet == none

#guard match runUntil 1 setGet with
  | (d, .budget) => d == afterSet
  | _ => false
#guard match runUntil 2 setGet with
  | (d, .boundary (.immV [v])) => d == afterGet && v == val32 7
  | _ => false

private def frames : Nat → IrisWasm.Expr
  | 0 => []
  | n+1 => [.local 0 ⟨[], emptyInst⟩ (frames n)]

#guard framesFit (frames 1024) 1024 && !framesFit (frames 1025) 1024
#guard framesFit [.label 0 (frames 1025) [], .basic .nop] 0
#guard match (runUntil 0 (frames 1025, σlocal 0)).2 with
  | .frameLimit => true
  | _ => false

private theorem read_back (d : Cfg) : AtCut 2 setGet d ↔ d = afterGet := by
  rw [cut_succ]; simp [set_next, cut_one, get_next]

example : ∃ t : Tree Cfg, Iterate (trans .tau) 2 (cutAfter 2 setGet) t ∧
    Yields t afterGet ∧ Yields (round afterGet) (.done (.immV [val32 7]), σlocal 7) := by
  obtain ⟨t, ht, hd⟩ := (read_back _).2 rfl
  exact ⟨t, ht, hd, ofVal_runs (.immV [val32 7]) _⟩

example (t : Tree (Val × State)) : ¬ Iterate (trans .tau) 3 (denote setGet) t := by
  apply cut_no_run _ t
  intro d h
  obtain ⟨b, hb, h⟩ := cut_succ.1 h
  obtain rfl := (set_next b).1 hb
  obtain ⟨b, hb, h⟩ := cut_succ.1 h
  obtain rfl := (get_next b).1 hb
  exact value_no_next (.immV [val32 7]) _ d (cut_one.1 h)

end Locals

section Traps

private abbrev surroundedTrap : IrisWasm.Expr := [const32 7, .trap, .basic .nop]

private theorem trap_next (σ : State) (d : Cfg) : Next (surroundedTrap, σ) d ↔
    d = ([.trap], σ) ∨ d = ([const32 7, .trap], σ) ∨ d = ([.trap, .basic .nop], σ) := by
  rcases d with ⟨es, σ'⟩
  change Runs (layer surroundedTrap) σ (.next es) σ' ↔ _
  simp only [surroundedTrap, const32, layer, frag, basicLayer, remaining, trapLayer,
    List.cons_ne_nil, false_and, ite_false, runs_br, runs_ret]
  constructor
  · rintro ⟨⟨⟨a, b⟩, ha, hb, hlt⟩, h, rfl⟩
    change a ≤ 1 at ha
    change b ≤ 1 at hb
    change a + b < 2 at hlt
    have cases : a = 0 ∧ b = 0 ∨ a = 1 ∧ b = 0 ∨ a = 0 ∧ b = 1 := by omega
    rcases cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases h <;> simp [vToEList]
  · rintro (h | h | h) <;> cases h
    · exact ⟨⟨(0, 0), by decide⟩, rfl, rfl⟩
    · exact ⟨⟨(1, 0), by decide⟩, rfl, rfl⟩
    · exact ⟨⟨(0, 1), by decide⟩, rfl, rfl⟩

example (σ : State) (d : Cfg) : AtCut 1 (surroundedTrap, σ) d ↔
    d = ([.trap], σ) ∨ d = ([const32 7, .trap], σ) ∨ d = ([.trap, .basic .nop], σ) :=
  cut_one.trans (trap_next σ d)

private theorem last_trim {vs : List Value} {tail : IrisWasm.Expr} (hlen : vs.length + tail.length = 1)
    (σ : State) (d : Cfg) : Runs (trapLayer vs tail) σ (.next d.1) d.2 ↔ d = ([.trap], σ) := by
  rcases d with ⟨es, σ'⟩
  have ne : ¬ (vs = [] ∧ tail = []) := by rintro ⟨rfl, rfl⟩; contradiction
  simp only [trapLayer, ne, ite_false, runs_br, runs_ret]
  constructor
  · rintro ⟨⟨⟨a, b⟩, _, _, hlt⟩, h, rfl⟩
    have hz : a = 0 ∧ b = 0 := by change a + b < vs.length + tail.length at hlt; omega
    obtain ⟨rfl, rfl⟩ := hz
    simpa [vToEList] using h
  · rintro h; cases h
    exact ⟨⟨(0, 0), Nat.zero_le _, Nat.zero_le _, by omega⟩, by simp [vToEList], rfl⟩

private theorem near_trap (σ : State) (d : Cfg) {es : IrisWasm.Expr}
    (h : es = [const32 7, .trap] ∨ es = [.trap, .basic .nop]) :
    Next (es, σ) d ↔ d = ([.trap], σ) := by
  change Runs (layer es) σ (.next d.1) d.2 ↔ _
  rcases h with rfl | rfl <;> simp only [const32, layer, frag, basicLayer, remaining] <;>
    exact last_trim (by decide) σ d

example (σ : State) : AtCut 1 (surroundedTrap, σ) ([.trap], σ) ∧
    AtCut 2 (surroundedTrap, σ) ([.trap], σ) := by
  constructor
  · exact cut_one.2 ((trap_next _ _).2 (.inl rfl))
  · exact cut_succ.2 ⟨_, (trap_next _ _).2 (.inr (.inl rfl)),
      cut_one.2 ((near_trap _ _ (.inl rfl)).2 rfl)⟩

example (σ : State) (t : Tree (Val × State)) :
    ¬ Iterate (trans .tau) 3 (denote (surroundedTrap, σ)) t := by
  apply cut_no_run _ t
  intro d h
  obtain ⟨b, hb, h⟩ := cut_succ.1 h
  obtain ⟨c, hc, h⟩ := cut_succ.1 h
  rcases (trap_next _ _).1 hb with rfl | rfl | rfl
  · exact value_no_next .trapV σ c hc
  · obtain rfl := (near_trap _ _ (.inl rfl)).1 hc
    exact value_no_next .trapV σ d (cut_one.1 h)
  · obtain rfl := (near_trap _ _ (.inr rfl)).1 hc
    exact value_no_next .trapV σ d (cut_one.1 h)

end Traps

section GrowMemory

private abbrev zeroMaxMem : Memory := ⟨MemoryList.memMake 0 0, ⟨.i32, ⟨0, some 0⟩⟩⟩
private abbrev σmem : State :=
  ({ emptyStore with mems := [zeroMaxMem] }, [], { emptyInst with memory := [0] })
private abbrev growCfg (δ : I32) (σ : State) : Cfg := ([const32 δ, .basic (.growMemory 0)], σ)
private abbrev growResult (x : I32) : Cfg := ([const32 x], σmem)

example (d : Cfg) : AtCut 1 (growCfg 0 σmem) d ↔ d = growResult 0 ∨ d = growResult int32MinusOne := by
  rw [cut_one]
  rcases d with ⟨es, σ'⟩
  change Runs (layer _) σmem (.next es) σ' ↔ _
  have h : handle (.growPages 0 (.i32 0)) σmem = .br .grow (fun ok ↦
      if ok then pure (val32 0, σmem) else pure (val32 int32MinusOne, σmem)) := rfl
  simp only [layer, frag, basicLayer, AddressOperand.ofValue?, runs_vis, h, ClosedProg.toTree_br, yields_br]
  simp [emit, vToEList, growResult, Bool.exists_bool, or_and_right, exists_or, and_assoc]
  grind

example (d : Cfg) : AtCut 1 (growCfg 1 σmem) d ↔ d = growResult int32MinusOne := by
  rw [cut_one]
  rcases d with ⟨es, σ'⟩
  change Runs (layer _) σmem (.next es) σ' ↔ _
  have h : handle (.growPages 0 (.i32 1)) σmem = pure (val32 int32MinusOne, σmem) := rfl
  simp only [layer, frag, basicLayer, AddressOperand.ofValue?, runs_vis, h]
  simp [emit, vToEList, growResult, and_assoc]

example (x : I32) : Yields (round (growResult x)) (.done (.immV [val32 x]), σmem) :=
  ofVal_runs (.immV [val32 x]) _

-- The store still has its memory; only the instance's memory index is missing.
private abbrev missingIndex : Cfg := growCfg 0 (σmem.1, [], emptyInst)

example : AtCut 1 missingIndex ([const32 int32MinusOne], missingIndex.2) :=
  cut_one.2 (round_next_iff.2 ⟨.growMemoryFailure (c := .i32 0), rfl, rfl⟩)

#guard runCut 1 missingIndex == some ([const32 int32MinusOne], missingIndex.2)
#guard runCut 1 ([.basic .drop], σmem) == none

example (σ : State) (l : Label HostCallE) (t : Tree (Val × State)) :
    ¬ trans l (denote ([.basic .drop], σ)) t := by
  intro ht
  rw [denote.eq_1] at ht
  obtain ⟨⟨r, σ'⟩, hr, _⟩ := trans_bind_pure (pure_pure_finite (round_finite _)) ht
  change Runs (layer _) _ r σ' at hr
  simp [layer, frag, basicLayer] at hr

end GrowMemory

section Loop

private abbrev loopInstr := AdministrativeInstruction.basic (.loop (.result none) [.br 0])
private abbrev loopStart (σ : State) : Cfg := ([loopInstr], σ)
private abbrev loopLabel (σ : State) : Cfg := ([.label 0 [loopInstr] [.basic (.br 0)]], σ)

private theorem enter_loop (σ : State) (d : Cfg) : Next (loopStart σ) d ↔ d = loopLabel σ := by
  rcases d with ⟨es, σ'⟩
  change Runs (layer _) _ (.next es) σ' ↔ _
  simp [loopLabel, loopInstr, layer, frag, basicLayer, withBlockType, withArgs, emit, vToEList, toEList]

private theorem repeat_loop (σ : State) (d : Cfg) : Next (loopLabel σ) d ↔ d = loopStart σ := by
  obtain ⟨store, locs, inst⟩ := σ
  rcases d with ⟨es, σ'⟩
  change Runs (layer _) _ (.next es) σ' ↔ _
  simp [loopStart, layer, frag, basicLayer, labelFront, vhDecrease, catchValues, emit, vToEList,
    and_assoc]

private theorem cycles (n : Nat) (σ : State) (d : Cfg) :
    Iterate Next (2*n) (loopStart σ) d ↔ d = loopStart σ := by
  induction n with
  | zero => exact iterate_zero_iff.trans eq_comm
  | succ n ih =>
    rw [Nat.mul_succ, iterate_succ_iff]
    simp only [enter_loop, exists_eq_left]
    rw [iterate_succ_iff]
    simpa only [repeat_loop, exists_eq_left] using ih

example (σ : State) (d : Cfg) : AtCut 1 (loopStart σ) d ↔ d = loopLabel σ :=
  cut_one.trans (enter_loop σ d)

example (σ : State) (d : Cfg) : AtCut 2 (loopStart σ) d ↔ d = loopStart σ :=
  (exact_cut_next_iff ..).trans (cycles 1 σ d)

private theorem cycle_boundary (n : Nat) (σ : State) (t : Tree (Val × State)) :
    Iterate (trans .tau) (2*n) (denote (loopStart σ)) t ↔ t = denote (loopStart σ) := by
  rw [denote_steps_next_iff]; simp [cycles]

example (n : Nat) (σ : State) :
    Iterate (trans .tau) (2*n) (denote (loopStart σ)) (denote (loopStart σ)) :=
  (cycle_boundary ..).2 rfl

example {n : Nat} {σ σ' : State} {t u : Tree (Val × State)} {v : Val}
    (h : Iterate (trans .tau) (2*n) (denote (loopStart σ)) t) : ¬ trans (.val (v, σ')) t u := by
  rw [(cycle_boundary ..).1 h, denote_val_iff]
  have hn := val_head_stuck _ _ _ _ _ _ (round_next_iff.1 ((enter_loop σ _).2 rfl))
  simp [hn]

end Loop

section Start

private def counter : Wasm.Module :=
  { (default : Wasm.Module) with
    globals := [⟨⟨.mut, .i32⟩, [.const (val32 0)]⟩]
    exports := [⟨[], .global (.globalidx 0)⟩] }

private def failingStart : Wasm.Module :=
  { (default : Wasm.Module) with
    types := [.tf [] []]
    imports := [⟨[], [], .global ⟨.mut, .i32⟩⟩]
    funcs := [⟨.typeidx 0, [], [.const (val32 73), .setGlobal 0, .unreachable]⟩]
    start := some ⟨.funcidx 0⟩ }

/-- After linking, the trapping start updates the imported object, not the second instance's copy. -/
private def afterStart : Option (Value × Value) := do
  let _ ← (validateModule counter).toOption
  let sig ← (validateModule failingStart).toOption
  let (s, first, exports) := interpAllocModule emptyStore counter [] [val32 0]
  let (s, second, _) := interpAllocModule s counter [] [val32 0]
  let [exported] := exports | none
  let .global (.globalidx g) := exported.desc | none
  let [.glob gt] := sig.imports | none
  guard (globalsAgree s.globals g gt)
  let (s, i, _) := interpAllocModule s failingStart [exported.desc] []
  let ⟨.funcidx k⟩ ← failingStart.start
  let addr ← i.funcs[k]?
  let (endCfg, .boundary .trapV) := runUntil 16 ([.invoke addr], s, [], emptyInst) | none
  let s := endCfg.2.1
  return (← sglobVal s first 0, ← sglobVal s second 0)

theorem trapping_start_preserves_imported_write : afterStart = some (val32 73, val32 0) := by
  decide +kernel

/-- With no global at the import address, linking supplies no store/instance/start triple. -/
theorem missing_global_cannot_start (s : StoreRecord) (result) :
    ¬ Instantiate s failingStart [.global (.globalidx s.globals.length)] result := by
  obtain ⟨⟨s', i, es⟩, start⟩ := result
  rintro ⟨_, _, _, _, _, _, _, links, _⟩
  cases links with
  | cons head _ => cases head with | glob _ _ _ bound _ _ => exact Nat.lt_irrefl _ bound

end Start

section Host

private abbrev inner : Frame := ⟨[val32 9], emptyInst⟩
private abbrev saved : Llholed := .local [] 1 inner (.base [] []) []
private abbrev request (tf : FunctionType) (h : Hostfuncidx) : Cfg :=
  ([.local 1 inner [.callHost tf h []]], σlocal 0)

example (tf : FunctionType) (h : Hostfuncidx) :
    ∃ t : Tree Cfg, Iterate (trans .tau) 0 (cutAfter 0 (request tf h)) t ∧
      Yields t (request tf h) ∧ Yields (round (request tf h)) (.done (.callHostV tf h [] saved), σlocal 0) :=
  ⟨_, .rfl _, trans_ret _, ofVal_runs (.callHostV tf h [] saved) _⟩

example (tf : FunctionType) (h : Hostfuncidx) (t : Tree (Val × State)) :
    ¬ trans .tau (denote (request tf h)) t := by
  intro ht
  obtain ⟨d, hd, _⟩ := denote_tau_next_iff.1 ht
  exact value_no_next (.callHostV tf h [] saved) _ d hd

private abbrev replyStore : StoreRecord := { emptyStore with globals := [⟨.immut, val32 1⟩] }
private abbrev replyState : State := (replyStore, [val32 0], emptyInst)
private abbrev resumeLocal : Cfg := ([.local 1 inner [.basic (.getLocal 0)]], replyState)
private abbrev innerRead : Cfg := ([.local 1 inner [const32 9]], replyState)
private abbrev exitLocal : Cfg := ([const32 9], replyState)

example (tf : FunctionType) (h : Hostfuncidx) :
    replyStore ≠ emptyStore ∧
    trans (.obs (tf, h, []) (replyStore, [.basic (.getLocal 0)])) (denote (request tf h)) (denote resumeLocal) ∧
    trans .tau (denote resumeLocal) (denote innerRead) ∧
    trans .tau (denote innerRead) (denote exitLocal) ∧
    Yields (denote exitLocal) (.immV [val32 9], replyState) := by
  refine ⟨by decide, denote_host_iff.2 ⟨saved, to_of_val (.callHostV tf h [] saved), rfl⟩,
    denote_tau_next_iff.2 ⟨innerRead, ?_, rfl⟩, denote_tau_next_iff.2 ⟨exitLocal, ?_, rfl⟩,
    denote_val_iff.2 ⟨to_of_val (.immV [val32 9]), trivial, rfl, rfl⟩⟩
  · change Runs (layer _) _ (.next _) _
    simp [layer, frag, basicLayer, localFront, emit, handle, and_assoc, vToEList, inner]
  · change Runs (layer _) _ (.next _) _
    simp [layer, frag, basicLayer, finish, localFront, emit, handle, and_assoc, vToEList]

end Host

end WasmTest.Denotational
