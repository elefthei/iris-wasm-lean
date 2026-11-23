/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import Iris.ProgramLogic.Adequacy
import IrisWasm.Examples.IrisRobustExample

/-! Port of `theories/iris/examples/iris_robust_example_adequacy.v`: host-level adequacy of the
robust load-store-example, via iris-lean's `wp_adequacy` for the host language. -/

namespace IrisWasm.Examples

open Iris Iris.BI Iris.ProgramLogic Iris.Std Wasm IrisWasm Language.Notation
open scoped Iris.Std.PartialMap

@[rocq_alias iriswasm.adv_module_record]
class AdvModuleRecord where
  advModule : Module
  noStart : advModule.start = none
  restrictions : ModuleRestrictions advModule
  elemBounds : ModuleElemBoundCheckGmap ∅ [] advModule
  dataBounds : ModuleDataBoundCheckGmap ∅ [] advModule

@[rocq_alias iriswasm.S]
def S : StoreRecord := ⟨[], [], [], [⟨.mut, xx 0⟩]⟩

@[rocq_alias iriswasm.V]
def V (vs : ModuleExport) : ViStore :=
  insert (insert (∅ : ViStore) 1 ⟨[0x00#8], .global (.globalidx 0)⟩) 0 vs

@[rocq_alias iriswasm.M]
def M (advModule : Module) : List Module := [advModule, lseModule]

section adequacy

/- The table and memory limit heaps still share their `Option Nat` instance. -/
variable (GF : BundledGFunctors) [InvGpreS GF] [NaInvG GF]
  [genHeapPreS Nat FunctionClosure GF NatMap] [genHeapPreS (Nat × Nat) Funcelem GF NatPairMap]
  [genHeapPreS Nat Nat GF NatMap] [genHeapPreS Nat (Option Nat) GF NatMap]
  [genHeapPreS Nat (AddrType × Nat × Nat) GF NatMap]
  [genHeapPreS (Nat × Nat) Byte GF NatPairMap] [genHeapPreS Nat Global GF NatMap]
  [genHeapPreS Unit Frame GF UnitMapF] [genHeapPreS Nat ModuleExport GF NatMap]
  [genHeapPreS Nat Module GF NatMap] [genHeapPreS Nat HostAction GF NatMap]

include GF

#rocq_ignore iriswasm.ex_adequacy "The ghost signature includes the typed memory metadata heap"
theorem ex_adequacy [AdvModuleRecord] (he' : HostExpr) (S' : StoreRecord) (V' : ViStore)
    (M' : List Module) (HA' : List HostAction) (F : Frame) (vs : ModuleExport)
    (hmodtyping : ModuleTyping AdvModuleRecord.advModule [] lseFuncImpts)
    (hstep : ([((advLseInstantiate 0, []) : HostExpr)],
        ((S, V vs, M AdvModuleRecord.advModule, [], emptyFrame) : HostState)) -·->ₜₚ*
      ([he'], ((S', V', M', HA', F) : HostState))) :
    ∀ v, hostToVal he' = some v → v = .trapHV ∨ v = .immHV [xx 42] := by
  intro v hv
  have hadeq := wp_adequacy (GF := GF) .NotStuck ((advLseInstantiate 0, []) : HostExpr)
    ((S, V vs, M AdvModuleRecord.advModule, [], emptyFrame) : HostState)
    (fun v => v = .trapHV ∨ v = .immHV [xx 42]) ?_
  · cases IrisHost.of_to_val _ _ hv
    exact hadeq.adequate_result [] _ v hstep
  intro inst κs
  imod genHeap_init (∅ : NatMap FunctionClosure) with ⟨%Gfunc, Hfunc, -⟩
  imod genHeap_init (∅ : NatPairMap Funcelem) with ⟨%Gtab, Htab, -⟩
  imod genHeap_init (∅ : NatMap Nat) with ⟨%Gtabsize, Htabsize, -⟩
  imod genHeap_init (∅ : NatMap (Option Nat)) with ⟨%Gtablimit, Htablimit, -⟩
  imod genHeap_init (∅ : NatPairMap Byte) with ⟨%Gmem, Hmem, -⟩
  imod genHeap_init (∅ : NatMap (AddrType × Nat × Nat)) with ⟨%Gmemsize, Hmemsize, -⟩
  imod genHeap_init (∅ : NatMap (Option Nat)) with ⟨%Gmemlimit, Hmemlimit, -⟩
  imod genHeap_init (∅ : NatMap Global) with ⟨%Gglob, Hglob, -⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Unit) (V := Frame) (H := UnitMapF)
    with ⟨%γframe, Hframe⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := ModuleExport) (H := NatMap)
    with ⟨%γvis, Hvis⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := Module) (H := NatMap)
    with ⟨%γms, Hms⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := HostAction) (H := NatMap)
    with ⟨%γhas, Hhas⟩
  imod NonAtomicInvariant.alloc (GF := GF) with ⟨%p, Hna⟩
  letI wasmG : WasmG .hasLC GF :=
    { invGS := inst, funcHs := Gfunc, tabHs := Gtab, tabsizeHs := Gtabsize,
      tablimitHs := Gtablimit, memHs := Gmem, memsizeHs := Gmemsize, memlimitHs := Gmemlimit,
      globHs := Gglob, locsHs := inferInstance, frameGName := γframe }
  letI : HvisG GF := { genG := inferInstance, visGName := γvis }
  letI : HmsG GF := { genG := inferInstance, msGName := γms }
  letI : HasG GF := { genG := inferInstance, haGName := γhas }
  letI : LogrelNaInvs GF := { logrelNais := p }
  imod ghost_map_insert (γ := γframe) () emptyFrame (get?_empty _) $$ Hframe with ⟨Hframe, Hf⟩
  imod ghost_map_insert (γ := γvis) 1 (⟨[0x00#8], .global (.globalidx 0)⟩ : ModuleExport)
    (get?_empty _) $$ Hvis with ⟨Hvis, Hv1⟩
  imod ghost_map_insert (γ := γvis) 0 vs (by rw [get?_insert_ne (by decide), get?_empty])
    $$ Hvis with ⟨Hvis, Hv0⟩
  imod ghost_map_insert (γ := γms) 1 lseModule (get?_empty _) $$ Hms with ⟨Hms, Hm1⟩
  imod ghost_map_insert (γ := γms) 0 AdvModuleRecord.advModule
    (by rw [get?_insert_ne (by decide), get?_empty]) $$ Hms with ⟨Hms, Hm0⟩
  imod genHeap_alloc (GF := GF) (L := Nat) (V := Global) (l := 0) (v := ⟨.mut, xx 0⟩) (get?_empty _)
    $$ Hglob with ⟨Hglob, Hg, -⟩
  imodintro
  iexists (fun σ _ => hostStateInterp σ), (fun _ => iprop(True))
  isplitl [Hfunc Htab Htabsize Htablimit Hmem Hmemsize Hmemlimit Hglob Hvis Hms Hhas Hframe]
  · have hfuncs : gmapOfList S.funcs = (∅ : NatMap FunctionClosure) := rfl
    have htab : gmapOfTable S.tables = ∅ := rfl
    have hmem : gmapOfMemory S.mems = ∅ := rfl
    have hglob : gmapOfList S.globals = insert (∅ : NatMap Global) 0 ⟨.mut, xx 0⟩ := rfl
    have hms : gmapOfList (M AdvModuleRecord.advModule) =
        insert (insert (∅ : NatMap Module) 1 lseModule) 0 AdvModuleRecord.advModule := rfl
    have hhas : gmapOfList ([] : List HostAction) = ∅ := rfl
    have hmemsize : gmapOfList (S.mems.map memLengthMeta) = ∅ := rfl
    have htabsize : gmapOfList (S.tables.map tabSize) = ∅ := rfl
    have hmemlimit : gmapOfList (S.mems.map (·.type.limits.max)) = ∅ := rfl
    have htablimit : gmapOfList (S.tables.map (·.maxOpt)) = ∅ := rfl
    simp only [hostStateInterp, hfuncs, htab, hmem, hglob, hms, hhas, hmemsize, htabsize,
      hmemlimit, htablimit, V]
    iframe
  · ihave H := instantiate_lse AdvModuleRecord.advModule 0 (xx 0) hmodtyping
      AdvModuleRecord.noStart AdvModuleRecord.restrictions AdvModuleRecord.elemBounds
      AdvModuleRecord.dataBounds rfl
    iapply H $$ [Hf Hg Hm0 Hm1 Hna Hv1 Hv0]
    · simp only [frameOwn, modsOwn, visOwn]
      iframe
    · iintro %w (%h | %h)
      · ipureintro; exact .inl h
      · ipureintro; exact .inr h

end adequacy

/-- The concrete functor list of Coq's `lse_adequacy` (`#[invΣ; na_invΣ; gen_heapΣ …]`); heaps
sharing key and value types share a functor, and so do the meta-data maps of heaps sharing
their key type. -/
def lseAdequacyGF : BundledGFunctors
  | 0 => ⟨InvMapF⟩
  | 1 => ⟨constOF CoPsetDisjL⟩
  | 2 => ⟨constOF (DisjointLeibnizSet PosSet)⟩
  | 3 => ⟨Auth.AuthURF (constOF Credit)⟩
  | 4 => ⟨NaInvF⟩
  | 5 => ⟨constOF MetaUR⟩
  | 6 => ⟨constOF (HeapView Nat (Agree (DiscreteO GName)) NatMap)⟩
  | 7 => ⟨constOF (HeapView (Nat × Nat) (Agree (DiscreteO GName)) NatPairMap)⟩
  | 8 => ⟨constOF (HeapView Unit (Agree (DiscreteO GName)) UnitMapF)⟩
  | 9 => ⟨constOF (HeapView Nat (Agree (DiscreteO FunctionClosure)) NatMap)⟩
  | 10 => ⟨constOF (HeapView (Nat × Nat) (Agree (DiscreteO Funcelem)) NatPairMap)⟩
  | 11 => ⟨constOF (HeapView Nat (Agree (DiscreteO Nat)) NatMap)⟩
  | 12 => ⟨constOF (HeapView Nat (Agree (DiscreteO (Option Nat))) NatMap)⟩
  | 13 => ⟨constOF (HeapView (Nat × Nat) (Agree (DiscreteO Byte)) NatPairMap)⟩
  | 14 => ⟨constOF (HeapView Nat (Agree (DiscreteO Global)) NatMap)⟩
  | 15 => ⟨constOF (HeapView Unit (Agree (DiscreteO Frame)) UnitMapF)⟩
  | 16 => ⟨constOF (HeapView Nat (Agree (DiscreteO ModuleExport)) NatMap)⟩
  | 17 => ⟨constOF (HeapView Nat (Agree (DiscreteO Module)) NatMap)⟩
  | 18 => ⟨constOF (HeapView Nat (Agree (DiscreteO HostAction)) NatMap)⟩
  | 19 => ⟨constOF (HeapView Nat (Agree (DiscreteO (AddrType × Nat × Nat))) NatMap)⟩
  | _ => ⟨constOF Unit⟩

instance : InvGpreS lseAdequacyGF where
  toWsatGpreS := ⟨⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩⟩
  toLcGpreS := ⟨⟨3, rfl⟩⟩

instance : NaInvG lseAdequacyGF := ⟨⟨4, rfl⟩⟩

instance : genHeapPreS Nat FunctionClosure lseAdequacyGF NatMap :=
  ⟨⟨⟨9, rfl⟩⟩, ⟨⟨6, rfl⟩⟩, ⟨5, rfl⟩⟩
instance : genHeapPreS (Nat × Nat) Funcelem lseAdequacyGF NatPairMap :=
  ⟨⟨⟨10, rfl⟩⟩, ⟨⟨7, rfl⟩⟩, ⟨5, rfl⟩⟩
instance : genHeapPreS Nat Nat lseAdequacyGF NatMap := ⟨⟨⟨11, rfl⟩⟩, ⟨⟨6, rfl⟩⟩, ⟨5, rfl⟩⟩
instance : genHeapPreS Nat (Option Nat) lseAdequacyGF NatMap := ⟨⟨⟨12, rfl⟩⟩, ⟨⟨6, rfl⟩⟩, ⟨5, rfl⟩⟩
instance : genHeapPreS (Nat × Nat) Byte lseAdequacyGF NatPairMap :=
  ⟨⟨⟨13, rfl⟩⟩, ⟨⟨7, rfl⟩⟩, ⟨5, rfl⟩⟩
instance : genHeapPreS Nat Global lseAdequacyGF NatMap := ⟨⟨⟨14, rfl⟩⟩, ⟨⟨6, rfl⟩⟩, ⟨5, rfl⟩⟩
instance : genHeapPreS Unit Frame lseAdequacyGF UnitMapF := ⟨⟨⟨15, rfl⟩⟩, ⟨⟨8, rfl⟩⟩, ⟨5, rfl⟩⟩
instance : genHeapPreS Nat ModuleExport lseAdequacyGF NatMap :=
  ⟨⟨⟨16, rfl⟩⟩, ⟨⟨6, rfl⟩⟩, ⟨5, rfl⟩⟩
instance : genHeapPreS Nat Module lseAdequacyGF NatMap := ⟨⟨⟨17, rfl⟩⟩, ⟨⟨6, rfl⟩⟩, ⟨5, rfl⟩⟩
instance : genHeapPreS Nat HostAction lseAdequacyGF NatMap :=
  ⟨⟨⟨18, rfl⟩⟩, ⟨⟨6, rfl⟩⟩, ⟨5, rfl⟩⟩
instance : genHeapPreS Nat (AddrType × Nat × Nat) lseAdequacyGF NatMap :=
  ⟨⟨⟨19, rfl⟩⟩, ⟨⟨6, rfl⟩⟩, ⟨5, rfl⟩⟩

@[rocq_alias iriswasm.lse_adequacy]
theorem lse_adequacy [AdvModuleRecord] (he' : HostExpr) (S' : StoreRecord) (V' : ViStore)
    (M' : List Module) (HA' : List HostAction) (F : Frame) (vs : ModuleExport)
    (hmodtyping : ModuleTyping AdvModuleRecord.advModule [] lseFuncImpts)
    (hstep : ([((advLseInstantiate 0, []) : HostExpr)],
        ((S, V vs, M AdvModuleRecord.advModule, [], emptyFrame) : HostState)) -·->ₜₚ*
      ([he'], ((S', V', M', HA', F) : HostState))) :
    ∀ v, hostToVal he' = some v → v = .trapHV ∨ v = .immHV [xx 42] := by
  exact ex_adequacy lseAdequacyGF he' S' V' M' HA' F vs hmodtyping hstep

end IrisWasm.Examples
