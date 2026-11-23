import Wasm.TypeMatching

namespace WasmTest.RecursiveTypes

open Wasm.CoreTypes

private def refAt (i : Nat) : Val Nat := .ref ⟨true, .use i⟩
private def refAbs (a : AbsHeap) : Val Nat := .ref ⟨true, .abs a⟩
private def constField {U} (t : Val U) : Field U := ⟨false, .val t⟩
private def emptyStruct : Wasm.CoreTypes.Sub Nat := ⟨false, [], .struct_ []⟩

-- Node ($1) points at Edges ($2); Edges holds Nodes. Node extends Object ($0).
private def nodeAndEdges (base : Nat) : RecGroup Nat :=
  [⟨false, [base - 1], .struct_ [constField (refAt (base + 1))]⟩,
   ⟨true, [], .array (constField (refAt base))⟩]

private def object : Defined := .proj [⟨false, [], .struct_ []⟩] 0
private def rolledPair : RecGroup (Scope Defined) :=
  [⟨false, [.free object], .struct_ [constField (.ref ⟨true, .use (.bound 1)⟩)]⟩,
   ⟨true, [], .array (constField (.ref ⟨true, .use (.bound 0)⟩))⟩]
private def node : Defined := .proj rolledPair 0
private def edges : Defined := .proj rolledPair 1

theorem mutual_group_closes :
    validateGroups [[emptyStruct], nodeAndEdges 1] = some #[object, node, edges] := by decide

theorem mutual_projections_expand :
    node.unroll = some ⟨false, [object], .struct_ [constField (.ref ⟨true, .use edges⟩)]⟩ ∧
    edges.expand = some (.array (constField (.ref ⟨true, .use node⟩))) := by decide

-- An unrelated earlier declaration changes every source index, not the closed pair's identity.
theorem closed_identity_ignores_module_indices :
    (validateGroups [[⟨true, [], .func [] []⟩], [emptyStruct], nodeAndEdges 2]).bind
      (fun types ↦ types[2]?) = some node := by decide

private def markedNode : Wasm.CoreTypes.Sub Nat :=
  ⟨true, [1], .struct_ [constField (refAt 2), ⟨true, .i8⟩]⟩

theorem declared_ancestors_and_prefix :
    (validateGroups [[emptyStruct], nodeAndEdges 1, [markedNode]]).bind (fun types ↦ do
      let marked ← types[3]?
      return marked.matches node && marked.matches object && !node.matches marked &&
        !marked.matches edges) = some true := by cbv

-- The child's own recursive reference refines its parent's recursive field. The nominal
-- edge is available inside the group while checking the structurally covariant bodies.
theorem recursive_field_refines_itself :
    (validateGroups [[⟨false, [], .struct_ [constField (refAt 0)]⟩,
                      ⟨true, [0], .struct_ [constField (refAt 1)]⟩]]).isSome = true := by cbv

theorem final_parent_rejected :
    validateGroups [[{emptyStruct with isFinal := true}], [{emptyStruct with supers := [0]}]] =
      none := by decide

theorem forward_or_cyclic_parent_rejected :
    validateGroups [[{emptyStruct with supers := [1]}, {emptyStruct with supers := [0]}]] = none ∧
    validateGroups [[{emptyStruct with supers := [0]}]] = none := by decide

theorem invalid_scope_and_multiple_parents_rejected :
    validateGroups [[⟨true, [], .func [] [refAt 1]⟩], [emptyStruct]] = none ∧
    validateGroups [[emptyStruct, emptyStruct, {emptyStruct with supers := [0, 1]}]] = none := by
  decide

private def functionPair (ap ar bp br : AbsHeap) : List (RecGroup Nat) :=
  [[⟨false, [], .func [refAbs ap] [refAbs ar]⟩, ⟨true, [0], .func [refAbs bp] [refAbs br]⟩]]

theorem function_variance :
    (validateGroups (functionPair .eq .any .any .eq)).isSome = true ∧
    validateGroups (functionPair .any .any .eq .eq) = none ∧
    validateGroups (functionPair .eq .eq .any .any) = none := by decide

private def arrayPair (m n : Bool) (x y : Storage Nat) : List (RecGroup Nat) :=
  [[⟨false, [], .array ⟨m, x⟩⟩, ⟨true, [0], .array ⟨n, y⟩⟩]]

theorem mutable_and_packed_fields_invariant :
    (validateGroups (arrayPair false false (.val (refAbs .any)) (.val (refAbs .eq)))).isSome = true ∧
    validateGroups (arrayPair true true (.val (refAbs .any)) (.val (refAbs .eq))) = none ∧
    validateGroups (arrayPair true true .i8 .i16) = none ∧
    validateGroups (arrayPair false true .i8 .i8) = none := by decide

theorem struct_cannot_remove_fields :
    validateGroups [[⟨false, [], .struct_ [⟨true, .i8⟩]⟩, {emptyStruct with supers := [0]}]] =
      none := by decide

theorem heap_hierarchies_and_nullability :
    (Ref.mk false (.abs .none)).matches ⟨true, .use node⟩ = true ∧
    (Ref.mk true (.use node)).matches ⟨false, .abs .any⟩ = false ∧
    (Heap.use edges).matches (.abs .eq) = true ∧ (Heap.use edges).matches (.abs .func) = false ∧
    (Heap.abs .noextern).matches (.abs .extern_) = true ∧
    (Heap.abs .noexn).matches (.abs .exn) = true ∧
    (Heap.abs .nofunc).matches (.use node) = false ∧
    (Heap.abs .none).matches (.abs .bot) = false := by decide

theorem numeric_vector_signature (required : List (Val Defined)) :
    resultMatches [.v128, .i32] required = true ↔ required = [.v128, .i32] := by
  rcases required with _ | ⟨a, _ | ⟨b, _ | ⟨c, cs⟩⟩⟩ <;> simp [resultMatches, Val.matches] <;> grind

theorem mutual_group_typing : ValidGroups #[] [[emptyStruct], nodeAndEdges 1] #[object, node, edges] :=
  validateGroups_iff.mp mutual_group_closes

end WasmTest.RecursiveTypes
