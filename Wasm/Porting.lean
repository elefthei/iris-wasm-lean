/-
Copyright (c) The Iris-Wasm Lean port contributors
Released under MIT license as described in the file LICENSE.
Authors: Iris-Wasm Lean port contributors
-/
import Iris.Std.RocqPorting
import Wasm.Numerics

/-! Coq files of `theories/` deliberately not ported. -/

#rocq_ignore_file iriswasm "binary_format_parser.v" "binary format parser is not used by the Iris layer"
#rocq_ignore_file iriswasm "binary_format_printer.v" "binary format printer is not used by the Iris layer"
#rocq_ignore_file iriswasm "binary_format_spec.v" "binary format is not used by the Iris layer"
#rocq_ignore_file iriswasm "binary_format_tests.v" "binary format is not used by the Iris layer"
#rocq_ignore_file iriswasm "binary_parser_types.v" "binary format is not used by the Iris layer"
#rocq_ignore_file iriswasm "leb128.v" "binary format is not used by the Iris layer"
#rocq_ignore_file iriswasm "leb128_tests.v" "binary format is not used by the Iris layer"
#rocq_ignore_file iriswasm "interpreter.v" "the executable interpreter is not used by the Iris layer"
#rocq_ignore_file iriswasm "interpreter_func.v" "the executable interpreter is not used by the Iris layer"
#rocq_ignore_file iriswasm "interpreter_func_sound.v" "the executable interpreter is not used by the Iris layer"
#rocq_ignore_file iriswasm "interpreter_sound.v" "the executable interpreter is not used by the Iris layer"
#rocq_ignore_file iriswasm "pp.v" "pretty printing"
#rocq_ignore_file iriswasm "bytes_pp.v" "pretty printing"
#rocq_ignore_file iriswasm "ansi.v" "pretty printing"
#rocq_ignore_file iriswasm "check_toks.v" "text format tokens are not used by the Iris layer"
#rocq_ignore_file iriswasm "extraction.v" "Coq extraction"
#rocq_ignore_file iriswasm "floats.v" "CompCert float glue; floats are Lean Float/Float32 bit patterns"
#rocq_ignore_file iriswasm "array.v" "only used by the unused data_vec record"
#rocq_ignore_file iriswasm "host.v" "only imported by the interpreter"
#rocq_ignore_file iriswasm "memory.v" "packed memory interface; datatypes use MemoryList directly"
#rocq_ignore_file iriswasm "pickability.v" "pickability is replaced by classical Decidable"
#rocq_ignore_file iriswasm "datatypes_properties.v" "eqType machinery is replaced by deriving DecidableEq"

/-! ## Base-file declarations not covered by their Lean port -/

/-! ### `common.v`: Ltac automation (Lean uses `omega`, `simp`, `deriving DecidableEq`, `induction`) -/

#rocq_ignore iriswasm.set_eq "Ltac; Lean uses `generalize h : t = x`"
#rocq_ignore iriswasm.lias_simpl "Ltac preprocessing for `lia`; Lean uses `omega`"
#rocq_ignore iriswasm.lias "Ltac wrapper around `lia`; Lean uses `omega`"
#rocq_ignore iriswasm.rewrite_by "Ltac; Lean uses `rw [show a = b by omega]`"
#rocq_ignore iriswasm.remove_bools_options "Ltac case-splitting bools/options; Lean uses `split`/`simp`"
#rocq_ignore iriswasm.decidable_equality_step "Ltac for decidable equality; replaced by `deriving DecidableEq`"
#rocq_ignore iriswasm.decidable_equality "Ltac for decidable equality; replaced by `deriving DecidableEq`"
#rocq_ignore iriswasm.efold "Ltac `fold` helper; Lean uses `simp only`/`unfold`"
#rocq_ignore iriswasm.decide_equality_injection "Ltac for decidable equality; replaced by `deriving DecidableEq`"
#rocq_ignore iriswasm.decidable_equality_using "Ltac for decidable equality; replaced by `deriving DecidableEq`"
#rocq_ignore iriswasm.count_cases "Ltac meta-programming for rect' principles; Lean generates nested recursors"
#rocq_ignore iriswasm.is_reducible "Ltac meta-programming for rect' principles; Lean generates nested recursors"
#rocq_ignore iriswasm.rect'_type_projection "Ltac building strong induction principles; Lean's nested inductives provide them"
#rocq_ignore iriswasm.rect'_type "Ltac building strong induction principles; Lean's nested inductives provide them"
#rocq_ignore iriswasm.rect'_type_list "Ltac building strong induction principles; Lean's nested inductives provide them"
#rocq_ignore iriswasm.rect'_type_option "Ltac building strong induction principles; Lean's nested inductives provide them"
#rocq_ignore iriswasm.rect'_build_projection "Ltac building strong induction principles; Lean's nested inductives provide them"
#rocq_ignore iriswasm.rect'_build "Ltac building strong induction principles; Lean's nested inductives provide them"
#rocq_ignore iriswasm.rect'_build_list "Ltac building strong induction principles; Lean's nested inductives provide them"
#rocq_ignore iriswasm.rect'_build_option "Ltac building strong induction principles; Lean's nested inductives provide them"
#rocq_ignore iriswasm.is_variable "Ltac meta-programming helper of the rect' tactics"

/-! ### `bytes.v`, `datatypes.v`, `memory_list.v`, `list_extra.v` -/

#rocq_ignore iriswasm.EqDec_byte "ITree EqDec instance; `Wasm.Byte = BitVec 8` has DecidableEq"
#rocq_ignore iriswasm.Byte_Index.Index "member of the unported array.v index module Byte_Index"
#rocq_ignore iriswasm.Byte_Index.Value "member of the unported array.v index module Byte_Index"
#rocq_ignore iriswasm.Byte_Index.index_eqb "member of the unported array.v index module Byte_Index"
#rocq_ignore iriswasm.list_memoryMixin "memory.v packed interface (unported); laws are Wasm.MemoryList.memory_list_ax_*"
#rocq_ignore iriswasm.list_memoryClass "memory.v packed interface (unported); laws are Wasm.MemoryList.memory_list_ax_*"
#rocq_ignore iriswasm.those_aux "Local; replaced by Wasm.thoseAux (plain list accumulator)"
#rocq_ignore iriswasm.those0_None "Local proof helper of those_those0; Lean proves it via Wasm.thoseAux_eq"
#rocq_ignore iriswasm.those_aux_None "Local proof helper of those_those0; Lean proves it via Wasm.thoseAux_eq"
#rocq_ignore iriswasm.cons_app "`a :: l = [a] ++ l` is `rfl`; Lean rewrites with `List.cons_append`"
#rocq_ignore iriswasm.those_those0_gen "Local proof helper of those_those0; Lean proves it via Wasm.thoseAux_eq"

/-! ### `numerics.v`: Flocq parameters and internals of `Wasm_float` -/

#rocq_ignore iriswasm.Wasm_float.FloatSize.compare "Flocq comparison; IEEE comparisons are MixinOf.eq/lt/gt/le/ge"
#rocq_ignore iriswasm.Wasm_float.FloatSize.cmp "Flocq comparison; IEEE comparisons are MixinOf.eq/lt/gt/le/ge"
#rocq_ignore iriswasm.Wasm_float.FloatSize.eq_dec "Flocq comparison; IEEE comparisons are MixinOf.eq/lt/gt/le/ge"
#rocq_ignore iriswasm.Wasm_float.FloatSize32.prec "Flocq format parameter; Lean Float32/Float are IEEE binary32/64"
#rocq_ignore iriswasm.Wasm_float.FloatSize32.emax "Flocq format parameter; Lean Float32/Float are IEEE binary32/64"
#rocq_ignore iriswasm.Wasm_float.FloatSize32.prec_gt_0 "Flocq format parameter; Lean Float32/Float are IEEE binary32/64"
#rocq_ignore iriswasm.Wasm_float.FloatSize32.Hmax "Flocq format parameter; Lean Float32/Float are IEEE binary32/64"
#rocq_ignore iriswasm.Wasm_float.FloatSize32.prec_gt_2 "Flocq format parameter; Lean Float32/Float are IEEE binary32/64"
#rocq_ignore iriswasm.Wasm_float.FloatSize32.default_nan "NaN payload canonicalisation is not modelled; payloads follow the hardware (see Wasm.wasmDemote)"
#rocq_ignore iriswasm.Wasm_float.FloatSize64.prec "Flocq format parameter; Lean Float32/Float are IEEE binary32/64"
#rocq_ignore iriswasm.Wasm_float.FloatSize64.emax "Flocq format parameter; Lean Float32/Float are IEEE binary32/64"
#rocq_ignore iriswasm.Wasm_float.FloatSize64.prec_gt_0 "Flocq format parameter; Lean Float32/Float are IEEE binary32/64"
#rocq_ignore iriswasm.Wasm_float.FloatSize64.Hmax "Flocq format parameter; Lean Float32/Float are IEEE binary32/64"
#rocq_ignore iriswasm.Wasm_float.FloatSize64.prec_gt_2 "Flocq format parameter; Lean Float32/Float are IEEE binary32/64"
#rocq_ignore iriswasm.Wasm_float.FloatSize64.default_nan "NaN payload canonicalisation is not modelled; payloads follow the hardware (see Wasm.wasmDemote)"
#rocq_ignore iriswasm.Wasm_float.Make.eqb "eqType plumbing; F32/F64 derive DecidableEq on bit patterns"
#rocq_ignore iriswasm.Wasm_float.Make.eqbP "eqType plumbing; F32/F64 derive DecidableEq on bit patterns"
#rocq_ignore iriswasm.Wasm_float.Make.is_nan "Flocq-level helper of Wasm_float.Make; Lean Float/Float32 builtins implement the ops (instMixinOfF32/F64)"
#rocq_ignore iriswasm.Wasm_float.Make.sign "Flocq-level helper of Wasm_float.Make; Lean Float/Float32 builtins implement the ops (instMixinOfF32/F64)"
#rocq_ignore iriswasm.Wasm_float.Make.is_zero "Flocq-level helper of Wasm_float.Make; Lean Float/Float32 builtins implement the ops (instMixinOfF32/F64)"
#rocq_ignore iriswasm.Wasm_float.Make.is_infinity "Flocq-level helper of Wasm_float.Make; Lean Float/Float32 builtins implement the ops (instMixinOfF32/F64)"
#rocq_ignore iriswasm.Wasm_float.Make.pos_infinity "Flocq-level helper of Wasm_float.Make; Lean Float/Float32 builtins implement the ops (instMixinOfF32/F64)"
#rocq_ignore iriswasm.Wasm_float.Make.neg_infinity "Flocq-level helper of Wasm_float.Make; Lean Float/Float32 builtins implement the ops (instMixinOfF32/F64)"
#rocq_ignore iriswasm.Wasm_float.Make.neg_zero "Flocq-level helper of Wasm_float.Make; Lean Float/Float32 builtins implement the ops (instMixinOfF32/F64)"
#rocq_ignore iriswasm.Wasm_float.Make.opp "Flocq-level helper of Wasm_float.Make; Lean Float/Float32 builtins implement the ops (instMixinOfF32/F64)"
#rocq_ignore iriswasm.Wasm_float.Make.normalise "Flocq-level helper of Wasm_float.Make; Lean Float/Float32 builtins implement the ops (instMixinOfF32/F64)"
#rocq_ignore iriswasm.Wasm_float.Make.sqrt "Flocq-level helper of Wasm_float.Make; Lean Float/Float32 builtins implement the ops (instMixinOfF32/F64)"
#rocq_ignore iriswasm.Wasm_float.Make.ZofB_param "Flocq-level helper of Wasm_float.Make; Lean Float/Float32 builtins implement the ops (instMixinOfF32/F64)"
#rocq_ignore iriswasm.Wasm_float.Make.div_down "Flocq-level helper of Wasm_float.Make; Lean Float/Float32 builtins implement the ops (instMixinOfF32/F64)"
#rocq_ignore iriswasm.Wasm_float.Make.div_up "Flocq-level helper of Wasm_float.Make; Lean Float/Float32 builtins implement the ops (instMixinOfF32/F64)"
#rocq_ignore iriswasm.Wasm_float.Make.div_near "Flocq-level helper of Wasm_float.Make; Lean Float/Float32 builtins implement the ops (instMixinOfF32/F64)"
#rocq_ignore iriswasm.Wasm_float.Make.ceilo "Flocq-level helper of Wasm_float.Make; Lean Float/Float32 builtins implement the ops (instMixinOfF32/F64)"
#rocq_ignore iriswasm.Wasm_float.Make.flooro "Flocq-level helper of Wasm_float.Make; Lean Float/Float32 builtins implement the ops (instMixinOfF32/F64)"
#rocq_ignore iriswasm.Wasm_float.Make.trunco "Flocq-level helper of Wasm_float.Make; Lean Float/Float32 builtins implement the ops (instMixinOfF32/F64)"
#rocq_ignore iriswasm.Wasm_float.Make.nearesto "Flocq-level helper of Wasm_float.Make; Lean Float/Float32 builtins implement the ops (instMixinOfF32/F64)"
#rocq_ignore iriswasm.Wasm_float.Make.trunco_is_ZofB "Flocq-level helper of Wasm_float.Make; Lean Float/Float32 builtins implement the ops (instMixinOfF32/F64)"
#rocq_ignore iriswasm.Wasm_float.Make.BofZ "Flocq-level helper of Wasm_float.Make; Lean Float/Float32 builtins implement the ops (instMixinOfF32/F64)"
#rocq_ignore iriswasm.Wasm_float.Make.BofZ_normalise "Flocq-level helper of Wasm_float.Make; Lean Float/Float32 builtins implement the ops (instMixinOfF32/F64)"
#rocq_ignore iriswasm.Wasm_float.Make.floatify "Flocq-level helper of Wasm_float.Make; Lean Float/Float32 builtins implement the ops (instMixinOfF32/F64)"
#rocq_ignore iriswasm.Wasm_float.Make.ceil "Flocq-level helper of Wasm_float.Make; Lean Float/Float32 builtins implement the ops (instMixinOfF32/F64)"
#rocq_ignore iriswasm.Wasm_float.Make.floor "Flocq-level helper of Wasm_float.Make; Lean Float/Float32 builtins implement the ops (instMixinOfF32/F64)"
#rocq_ignore iriswasm.Wasm_float.Make.trunc "Flocq-level helper of Wasm_float.Make; Lean Float/Float32 builtins implement the ops (instMixinOfF32/F64)"
#rocq_ignore iriswasm.Wasm_float.Make.nearest "Flocq-level helper of Wasm_float.Make; Lean Float/Float32 builtins implement the ops (instMixinOfF32/F64)"
#rocq_ignore iriswasm.Wasm_float.Make.set_sign "Flocq-level helper of Wasm_float.Make; Lean Float/Float32 builtins implement the ops (instMixinOfF32/F64)"
#rocq_ignore iriswasm.Wasm_float.Make.set_sign_sign "Flocq-level helper of Wasm_float.Make; Lean Float/Float32 builtins implement the ops (instMixinOfF32/F64)"
#rocq_ignore iriswasm.Wasm_float.Make.set_sign_opp "Flocq-level helper of Wasm_float.Make; Lean Float/Float32 builtins implement the ops (instMixinOfF32/F64)"
#rocq_ignore iriswasm.Wasm_float.Make.to_int_range "Flocq-level helper of Wasm_float.Make; Lean Float/Float32 builtins implement the ops (instMixinOfF32/F64)"
#rocq_ignore iriswasm.Wasm_float.Make.canonical_pl "NaN payload canonicalisation is not modelled; payloads follow the hardware (see Wasm.wasmDemote)"
#rocq_ignore iriswasm.Wasm_float.Make.is_canonical "NaN payload canonicalisation is not modelled; payloads follow the hardware (see Wasm.wasmDemote)"
#rocq_ignore iriswasm.Wasm_float.Make.pl_arithmetic "NaN payload canonicalisation is not modelled; payloads follow the hardware (see Wasm.wasmDemote)"
#rocq_ignore iriswasm.Wasm_float.Make.pl_arithmetic_is_nan "NaN payload canonicalisation is not modelled; payloads follow the hardware (see Wasm.wasmDemote)"
#rocq_ignore iriswasm.Wasm_float.Make.is_arithmetic "NaN payload canonicalisation is not modelled; payloads follow the hardware (see Wasm.wasmDemote)"
#rocq_ignore iriswasm.Wasm_float.Make.is_arithmetic_is_nan "NaN payload canonicalisation is not modelled; payloads follow the hardware (see Wasm.wasmDemote)"
#rocq_ignore iriswasm.Wasm_float.Make.canonical_pl_arithmetic "NaN payload canonicalisation is not modelled; payloads follow the hardware (see Wasm.wasmDemote)"
#rocq_ignore iriswasm.Wasm_float.Make.canonical_pl_is_arithmetic "NaN payload canonicalisation is not modelled; payloads follow the hardware (see Wasm.wasmDemote)"
#rocq_ignore iriswasm.Wasm_float.Make.canonical_nan "NaN payload canonicalisation is not modelled; payloads follow the hardware (see Wasm.wasmDemote)"
#rocq_ignore iriswasm.Wasm_float.Make.is_canonical_nan_disj "NaN payload canonicalisation is not modelled; payloads follow the hardware (see Wasm.wasmDemote)"
#rocq_ignore iriswasm.Wasm_float.Make.unspec_canonical_nan "NaN payload canonicalisation is not modelled; payloads follow the hardware (see Wasm.wasmDemote)"
#rocq_ignore iriswasm.Wasm_float.Make.make_arithmetic "NaN payload canonicalisation is not modelled; payloads follow the hardware (see Wasm.wasmDemote)"
#rocq_ignore iriswasm.Wasm_float.Make.make_arithmetic_arithmetic "NaN payload canonicalisation is not modelled; payloads follow the hardware (see Wasm.wasmDemote)"
#rocq_ignore iriswasm.Wasm_float.Make.make_arithmetic_nan "NaN payload canonicalisation is not modelled; payloads follow the hardware (see Wasm.wasmDemote)"
#rocq_ignore iriswasm.Wasm_float.Make.unspec_nan_pl "NaN payload canonicalisation is not modelled; payloads follow the hardware (see Wasm.wasmDemote)"
#rocq_ignore iriswasm.Wasm_float.Make.unspec_arithmetic_nan_pl "NaN payload canonicalisation is not modelled; payloads follow the hardware (see Wasm.wasmDemote)"
#rocq_ignore iriswasm.Wasm_float.Make.unspec_arithmetic_nan_pl_canonical "NaN payload canonicalisation is not modelled; payloads follow the hardware (see Wasm.wasmDemote)"
#rocq_ignore iriswasm.Wasm_float.Make.unspec_arithmetic_nan_pl_nan "NaN payload canonicalisation is not modelled; payloads follow the hardware (see Wasm.wasmDemote)"
#rocq_ignore iriswasm.Wasm_float.Make.unspec_arithmetic_nan "NaN payload canonicalisation is not modelled; payloads follow the hardware (see Wasm.wasmDemote)"
#rocq_ignore iriswasm.Wasm_float.Make.unspec_nan_nan "NaN payload canonicalisation is not modelled; payloads follow the hardware (see Wasm.wasmDemote)"
#rocq_ignore iriswasm.Wasm_float.Make.unspec_nan "NaN payload canonicalisation is not modelled; payloads follow the hardware (see Wasm.wasmDemote)"
#rocq_ignore iriswasm.Wasm_float.Make.nans "NaN payload canonicalisation is not modelled; payloads follow the hardware (see Wasm.wasmDemote)"
#rocq_ignore iriswasm.Wasm_float.Make.nans_is_nan "NaN payload canonicalisation is not modelled; payloads follow the hardware (see Wasm.wasmDemote)"
#rocq_ignore iriswasm.Wasm_float.Make.normalise_unit_test "Coq unit test of a Flocq rounding helper; WasmTest/Numerics.lean checks the Lean ops"
#rocq_ignore iriswasm.Wasm_float.Make.ceil_unit_test_1 "Coq unit test of a Flocq rounding helper; WasmTest/Numerics.lean checks the Lean ops"
#rocq_ignore iriswasm.Wasm_float.Make.ceil_unit_test_2 "Coq unit test of a Flocq rounding helper; WasmTest/Numerics.lean checks the Lean ops"
#rocq_ignore iriswasm.Wasm_float.Make.floor_unit_test_1 "Coq unit test of a Flocq rounding helper; WasmTest/Numerics.lean checks the Lean ops"
#rocq_ignore iriswasm.Wasm_float.Make.floor_unit_test_2 "Coq unit test of a Flocq rounding helper; WasmTest/Numerics.lean checks the Lean ops"
#rocq_ignore iriswasm.Wasm_float.Make.trunc_unit_test_1 "Coq unit test of a Flocq rounding helper; WasmTest/Numerics.lean checks the Lean ops"
#rocq_ignore iriswasm.Wasm_float.Make.trunc_unit_test_2 "Coq unit test of a Flocq rounding helper; WasmTest/Numerics.lean checks the Lean ops"
#rocq_ignore iriswasm.Wasm_float.Make.nearest_unit_test_1 "Coq unit test of a Flocq rounding helper; WasmTest/Numerics.lean checks the Lean ops"
#rocq_ignore iriswasm.Wasm_float.Make.nearest_unit_test_2 "Coq unit test of a Flocq rounding helper; WasmTest/Numerics.lean checks the Lean ops"
#rocq_ignore iriswasm.Wasm_float.Make.nearest_unit_test_3 "Coq unit test of a Flocq rounding helper; WasmTest/Numerics.lean checks the Lean ops"
#rocq_ignore iriswasm.Wasm_float.Make.nearest_unit_test_4 "Coq unit test of a Flocq rounding helper; WasmTest/Numerics.lean checks the Lean ops"

-- The Wasm float operations of `Wasm_float.Make` are the `MixinOf` fields (instances F32/F64).
attribute [rocq_alias iriswasm.Wasm_float.Make.pos_zero] Wasm.Float.MixinOf.zero
attribute [rocq_alias iriswasm.Wasm_float.Make.fadd] Wasm.Float.MixinOf.add
attribute [rocq_alias iriswasm.Wasm_float.Make.fsub] Wasm.Float.MixinOf.sub
attribute [rocq_alias iriswasm.Wasm_float.Make.fmul] Wasm.Float.MixinOf.mul
attribute [rocq_alias iriswasm.Wasm_float.Make.fdiv] Wasm.Float.MixinOf.div
attribute [rocq_alias iriswasm.Wasm_float.Make.fmin] Wasm.Float.MixinOf.min
attribute [rocq_alias iriswasm.Wasm_float.Make.fmax] Wasm.Float.MixinOf.max
attribute [rocq_alias iriswasm.Wasm_float.Make.fcopysign] Wasm.Float.MixinOf.copysign
attribute [rocq_alias iriswasm.Wasm_float.Make.fabs] Wasm.Float.MixinOf.abs
attribute [rocq_alias iriswasm.Wasm_float.Make.fneg] Wasm.Float.MixinOf.neg
attribute [rocq_alias iriswasm.Wasm_float.Make.fsqrt] Wasm.Float.MixinOf.sqrt
attribute [rocq_alias iriswasm.Wasm_float.Make.fceil] Wasm.Float.MixinOf.ceil
attribute [rocq_alias iriswasm.Wasm_float.Make.ffloor] Wasm.Float.MixinOf.floor
attribute [rocq_alias iriswasm.Wasm_float.Make.ftrunc] Wasm.Float.MixinOf.trunc
attribute [rocq_alias iriswasm.Wasm_float.Make.fnearest] Wasm.Float.MixinOf.nearest
attribute [rocq_alias iriswasm.Wasm_float.Make.ui32_trunc] Wasm.Float.MixinOf.ui32Trunc
attribute [rocq_alias iriswasm.Wasm_float.Make.si32_trunc] Wasm.Float.MixinOf.si32Trunc
attribute [rocq_alias iriswasm.Wasm_float.Make.ui64_trunc] Wasm.Float.MixinOf.ui64Trunc
attribute [rocq_alias iriswasm.Wasm_float.Make.si64_trunc] Wasm.Float.MixinOf.si64Trunc
attribute [rocq_alias iriswasm.Wasm_float.Make.convert_ui32] Wasm.Float.MixinOf.convertUi32
attribute [rocq_alias iriswasm.Wasm_float.Make.convert_si32] Wasm.Float.MixinOf.convertSi32
attribute [rocq_alias iriswasm.Wasm_float.Make.convert_ui64] Wasm.Float.MixinOf.convertUi64
attribute [rocq_alias iriswasm.Wasm_float.Make.convert_si64] Wasm.Float.MixinOf.convertSi64

/-! ### `stdpp_aux.v` (plan step 4.1: only lemmas Lean callers need are ported) -/

#rocq_ignore iriswasm.N_nat_bin "N/nat bridge; N and nat are both Nat in Lean"
#rocq_ignore iriswasm.nat_bin "N/nat bridge; N and nat are both Nat in Lean"
#rocq_ignore iriswasm.take_all_alt "unused; core List.take_length / List.take_of_length_le"
#rocq_ignore iriswasm.map_fmap "stdpp/mathcomp bridge: list fmap is List.map, statement is rfl"
#rocq_ignore iriswasm.nth_error_lookup "stdpp/mathcomp bridge: nth_error and !! are both l[i]?, statement is rfl"
#rocq_ignore iriswasm.fmap_split "proof helper of iris_wasm_lang_properties.v; core List.map_eq_append_iff gives the split"
#rocq_ignore iriswasm.fmap_insert_set_nth "stdpp/mathcomp bridge: <[i:=v]> and set_nth both translate to List.set, statement is rfl"
#rocq_ignore iriswasm.repeat_lookup "core List.getElem?_replicate (+ List.getElem?_replicate_of_lt) by simp"
#rocq_ignore iriswasm.repeat_lookup_None "unused; core List.getElem?_replicate"
#rocq_ignore iriswasm.seq_map_fmap "stdpp/mathcomp bridge: seq.map and fmap are both List.map, statement is rfl"
#rocq_ignore iriswasm.repeat_lookup_Some "core List.getElem?_replicate by simp"
#rocq_ignore iriswasm.zip_lookup_Some "core List.getElem?_zip_eq_some (length hypothesis unnecessary)"
#rocq_ignore iriswasm.zip_lookup_Some_inv "core List.getElem?_zip_eq_some (mp direction)"
#rocq_ignore iriswasm.fmap_fmap_lookup "core List.getElem?_map applied to congrArg (·[i]?) of the hypothesis"
#rocq_ignore iriswasm.skipn_is_drop_n "stdpp/mathcomp bridge: both drops are List.drop, statement is rfl"
#rocq_ignore iriswasm.nth_error_none_fmap "core List.getElem?_map + Option.map_none"
#rocq_ignore iriswasm.rcons_eq "unused; core List.append_inj'"
#rocq_ignore iriswasm.elem_of_app_l "proof helper of iris_wasm_lang_properties.v; List.mem_append with Decidable.em"
#rocq_ignore iriswasm.app_eq_singleton "core List.append_eq_singleton_iff (disjuncts swapped)"
#rocq_ignore iriswasm.list_insert_destruct "core List.set_eq_take_append_cons_drop"
#rocq_ignore iriswasm.update_list_at_insert "stdpp/mathcomp bridge: update_list_at and <[n:=x]> both translate to List.set, statement is rfl"
#rocq_ignore iriswasm.update_trivial "core List.set_getElem_self (with List.getElem?_eq_some_iff)"
#rocq_ignore iriswasm.update_twice "unused; core List.set_set"
#rocq_ignore iriswasm.length_update "core List.length_set (no bound needed)"
#rocq_ignore iriswasm.lookup_seq_nth "stdpp/mathcomp bridge: seq.nth vs !!, only used inside stdpp_aux.v"
#rocq_ignore iriswasm.ncons_fmap "ssreflect ncons bridge, only used inside stdpp_aux.v"
#rocq_ignore iriswasm.set_nth_read "set_nth translates to List.set; core List.getElem?_set_self (needs i < length)"
#rocq_ignore iriswasm.set_nth_ncons "ssreflect ncons bridge, only used inside stdpp_aux.v"
#rocq_ignore iriswasm.set_nth_write "set_nth translates to List.set; core List.set_set"
#rocq_ignore iriswasm.update_ne "core List.getElem?_set_ne"
#rocq_ignore iriswasm.those_nil "unused"
#rocq_ignore iriswasm.those_not_nil "unused"
#rocq_ignore iriswasm.separate1 "`a :: … :: l = [a, …] ++ l` is rfl; Lean rewrites with List.cons_append"
#rocq_ignore iriswasm.separate2 "`a :: … :: l = [a, …] ++ l` is rfl; Lean rewrites with List.cons_append"
#rocq_ignore iriswasm.separate3 "`a :: … :: l = [a, …] ++ l` is rfl; Lean rewrites with List.cons_append"
#rocq_ignore iriswasm.separate4 "`a :: … :: l = [a, …] ++ l` is rfl; Lean rewrites with List.cons_append"
#rocq_ignore iriswasm.separate5 "`a :: … :: l = [a, …] ++ l` is rfl; Lean rewrites with List.cons_append"
#rocq_ignore iriswasm.separate6 "`a :: … :: l = [a, …] ++ l` is rfl; Lean rewrites with List.cons_append"
#rocq_ignore iriswasm.separate7 "`a :: … :: l = [a, …] ++ l` is rfl; Lean rewrites with List.cons_append"
#rocq_ignore iriswasm.separate8 "`a :: … :: l = [a, …] ++ l` is rfl; Lean rewrites with List.cons_append"
#rocq_ignore iriswasm.separate9 "`a :: … :: l = [a, …] ++ l` is rfl; Lean rewrites with List.cons_append"

attribute [rocq_alias iriswasm.list_fmap_app] List.map_append
attribute [rocq_alias iriswasm.fmap_update_list_at] List.map_set
attribute [rocq_alias iriswasm.set_nth_fmap] List.map_set
attribute [rocq_alias iriswasm.take_fmap] List.map_take
attribute [rocq_alias iriswasm.lookup_snoc] List.getElem?_concat_length
