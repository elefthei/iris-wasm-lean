import Wasm.Binary

namespace WasmTest.Core3
open Wasm Wasm.Binary

private def parse {α : Type} (p : Reader α) (bs : Array UInt8) :=
  (complete p (ByteArray.mk bs).toByteSlice).toOption

-- Both terminal sign extension and the maximum encoded length matter; minimality does not.
theorem nonminimal_u32 : parse u32 #[0x81, 0x80, 0x80, 0x80, 0] = some 1 := by decide +kernel
#guard parse u32 #[0xff, 0xff, 0xff, 0xff, 0x10] == none
#guard parse u32 #[0x80, 0x80, 0x80, 0x80, 0x80, 0] == none
theorem max_type_index : parse s33 #[0xff, 0xff, 0xff, 0xff, 0x0f] = some 0xffffffff := by
  decide +kernel
theorem min_i32 : parse i32 #[0x80, 0x80, 0x80, 0x80, 0x78] = some 0x80000000 := by
  decide +kernel
#guard parse i32 #[0x80, 0x80, 0x80, 0x80, 0x08] == none
theorem negative_i64 : parse i64 #[0x80, 0x7f] = some (-128) := by decide +kernel
#guard parse (fixedBits 4) #[0x01, 0x00, 0x80, 0x7f] == some 0x7f800001
#guard parse name #[3, 0xe2, 0x82, 0xac] == some "€"
#guard parse name #[3, 0xed, 0xa0, 0x80] == none

#guard parse memArg #[0x42, 0x01, 0x81, 0x80, 0x80, 0x80, 0x10] == some ⟨1, 2, 2^32+1⟩
#guard parse memArg #[0x80, 0x01, 0] == none
#guard parse numericInstr #[0x43, 0x01, 0, 0x80, 0x7f] == some (.const (.float32 ⟨0x7f800001⟩))
#guard parse numericInstr #[0x7d] == some (.binop .i64 (.i .sub))
#guard parse numericInstr #[0xa7] == some (.cvtop .i32 .convert .i64 none)
#guard parse numericInstr #[0xfc, 0x87, 0] == some (.cvtop .i64 .truncSat .f64 (some .u))
#guard parse numericInstr #[0xfc, 0x08] == none
#guard parse numericInstr #[0xc5] == none

theorem decode_extend_s :
    [0xc0, 0xc1, 0xc2, 0xc3, 0xc4].map (fun b => parse numericInstr #[b]) =
      [some (.unop .i32 (.extendS .i8)), some (.unop .i32 (.extendS .i16)),
       some (.unop .i64 (.extendS .i8)), some (.unop .i64 (.extendS .i16)),
       some (.unop .i64 (.extendS .i32))] := by decide +kernel

theorem decode_trunc_sat :
    (List.range 8).map (fun n => parse numericInstr #[0xfc, n.toUInt8]) =
      ([ValueType.i32, .i64].flatMap fun dst => [ValueType.f32, .f64].flatMap fun src =>
        [Sx.s, .u].map fun sx => some (.cvtop dst .truncSat src (some sx))) := by decide +kernel

-- A typed self-reference uses index 0 inside its own group; it does not require an earlier type.
#guard (parse typeSection #[1, 0x4e, 1, 0x5f, 1, 0x63, 0, 0]).any fun groups =>
  (CoreTypes.validateGroups groups.toList).isSome
-- Multiple supertypes are a validation failure, not a decoding failure.
#guard (parse typeSection #[3, 0x50, 0, 0x5f, 0, 0x50, 0, 0x5f, 0,
    0x4f, 2, 0, 1, 0x5f, 0]).any fun groups =>
  (CoreTypes.validateGroups groups.toList).isNone
#guard parse refType #[0x64, 0xff, 0x00] == some ⟨false, .use 127⟩
#guard parse refType #[0x63, 0xf0, 0x7f] == none -- abstract heap tags must use one byte
#guard parse fieldType #[0x77, 2] == none
#guard parse blockType #[0x80, 0] == some (.index 0)
#guard parse blockType #[0x40] == some (.result none)

private def blockSignature (sectionBytes immediate : Array UInt8) :
    Option CoreTypes.Signature := do
  let groups ← parse typeSection sectionBytes
  let types ← CoreTypes.validateGroups groups.toList
  (← parse blockType immediate).resolve types

-- Struct 0 and function 1 are in the same recursive group. The result refers back to struct 0.
private def controlTypes : Array UInt8 := #[1, 0x4e, 2, 0x5f, 0, 0x60, 2, 0x7e, 0x7f, 2, 0x7b, 0x64, 0]

theorem indexed_block_signature :
    (blockSignature controlTypes #[0x81, 0]).any (fun s =>
      s.params == [.i64, .i32] && match s.results with
      | [.v128, .ref ⟨false, .use d⟩] => d.expand == some (.struct_ [])
      | _ => false) = true := by decide +kernel

#guard (blockSignature controlTypes #[0]).isNone -- valid index, but not a function type
#guard (blockSignature controlTypes #[2]).isNone
theorem inline_block_signature :
    blockSignature #[0] #[0x40] = some ⟨[], []⟩ ∧
    blockSignature #[0] #[0x7f] = some ⟨[], [.i32]⟩ ∧
    blockSignature #[0] #[0x63, 0] = none := by decide +kernel

theorem decode_variable_indices :
    [0x20, 0x21, 0x22, 0x23, 0x24].map (fun tag => parse variableInstr #[tag, 0x80, 0x01]) =
      [some (.getLocal 128), some (.setLocal 128), some (.teeLocal 128),
       some (.getGlobal 128), some (.setGlobal 128)] := by decide +kernel

#guard (parse variableInstr #[0x20, 0x80]).isNone

-- The raw block rule uses the arity, even when validation of the inline reference would fail.
theorem raw_inline_result_arity :
    (parse blockType #[0x63, 0]).bind (·.arities #[]) = some (0, 1) ∧
    (parse blockType #[0]).bind (·.arities #[]) = none := by decide +kernel

theorem global_initializer_type (types : Array CoreTypes.Defined) :
    (parse externType #[3, 0x63, 0, 0]).bind (·.close types) =
      (types[0]?).map (fun d => .global_ false (.ref ⟨true, .use d⟩)) := by
  have decoded : parse externType #[3, 0x63, 0, 0] = some (.global_ false (.ref ⟨true, .use 0⟩)) := by
    decide +kernel
  rw [decoded]
  change (CoreTypes.closeVal types (.ref ⟨true, .use 0⟩)).map _ = _
  cases h : types[0]? <;> simp [CoreTypes.closeVal, CoreTypes.Val.substM, CoreTypes.Ref.substM,
    CoreTypes.Heap.substM, h]

private def interfaceMatch (actual required : Array UInt8) : Option Bool := do
  -- A non-final function type followed by a final, nominal subtype of the same signature.
  let groups ← parse typeSection #[2, 0x50,0,0x60,0,0, 0x4f,1,0,0x60,0,0]
  let env ← CoreTypes.validateGroups groups.toList
  let a ← (← parse externType actual).close env
  let b ← (← parse externType required).close env
  return a.matches b

theorem nominal_import_variance :
    interfaceMatch #[0,1] #[0,0] = some true ∧ interfaceMatch #[0,0] #[0,1] = some false ∧
    interfaceMatch #[4,0,1] #[4,0,0] = some false ∧ interfaceMatch #[4,0,1] #[4,0,1] = some true ∧
    interfaceMatch #[3,0x64,1,0] #[3,0x63,0,0] = some true ∧
    interfaceMatch #[3,0x64,1,1] #[3,0x63,0,1] = some false := by cbv

theorem table_import_variance :
    interfaceMatch #[1,0x64,1,4,2] #[1,0x64,1,4,1] = some true ∧
    interfaceMatch #[1,0x64,1,4,2] #[1,0x63,0,4,1] = some false ∧
    interfaceMatch #[1,0x64,1,4,2] #[1,0x64,1,0,1] = some false := by cbv

#guard ((parse externType #[2, 4, 0x81, 0x80, 4]).bind (·.close #[])).isSome
#guard ((parse externType #[2, 0, 0x81, 0x80, 4]).bind (·.close #[])).isNone
#guard parse externType #[4, 1, 0] == none
#guard parse externType #[2, 6, 0] == none
#guard (Limits.mk 2 (some 4)).matches ⟨1, none⟩
#guard !(Limits.mk 2 none).matches ⟨1, some 4⟩
#guard !(Limits.mk 0 (some 7)).matches ⟨0, some 5⟩

theorem byte_respects_window :
    ((byte *> byte).run ((ByteArray.mk #[0x61, 0x62]).toByteSlice 0 1)).toOption.isNone := by
  decide

private def functionBody := codeBody valType (structuredExpr numVecType numericPayload)

theorem compressed_locals_limit :
    parse functionBody #[8,1,0xff,0xff,0xff,0xff,0x0f,0x7f,0x0b] =
      some (#[(2^32-1, .i32)], []) ∧
    parse functionBody #[10,2,0xff,0xff,0xff,0xff,0x0f,0x7f,1,0x7e,0x0b] = none := by
  decide +kernel

#guard (parse functionBody #[3,0,0x41,0x80,0,0x0b]).isNone -- immediate crosses the body window
#guard (parse functionBody #[3,0,0x0b,0x0b]).isNone -- bytes remain after the function's end

private def inventory (body : Array UInt8) : Option (Array Section) :=
  let header := #[0, 0x61, 0x73, 0x6d, 1, 0, 0, 0]
  (foldSections ⟨header ++ body⟩ #[] fun seen kind ↦ do
    let _ ← u32
    return seen.push kind).toOption

#guard inventory #[13, 1, 0, 0, 3, 1, 65, 255, 6, 1, 0, 12, 1, 0, 10, 1, 0] ==
  some #[.tags, .globals, .dataCount, .code]
#guard inventory #[6, 1, 0, 13, 1, 0] == none
#guard inventory #[1, 1, 0, 1, 1, 0] == none
#guard inventory #[1, 1, 0x81, 0] == none -- length continuation cannot borrow from next section
#guard inventory #[1, 2, 0, 0] == none -- unconsumed byte inside a section
#guard inventory #[0, 2, 1, 0xff] == none -- custom data starts with a valid UTF-8 name

end WasmTest.Core3
