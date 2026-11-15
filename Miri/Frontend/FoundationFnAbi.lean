import Miri.Frontend.FoundationAbi

/-! Exact pass-mode material for the supported scalar/array subset of ordinary
Rust ABI on explicit x86_64 targets. Source: pinned rustc_ty_utils/src/abi.rs
`arg_attrs_for_rust_scalar` and rustc_target/src/callconv/mod.rs `ArgAbi::new`,
`adjust_for_rust_abi`, `cast_to_maybe_noundef`, revision
8144389c895da997dbdecaa635e41d6a50be6ffd.

This is a parametric component, not a document-to-interpreter FnAbi bridge:
physical identities still require a validated document-local type/layout registry.
It never allocates identities or copies precomputed compiler ABI answers. -/
namespace Miri.Frontend.Foundation

private def attributes (bits : Nat) (extension : Input.ArgumentExtensionKind := .none)
    (size : Nat := 0) (align : Option Nat := none) : Input.AbiAttributes :=
  ⟨bits, size, align, extension⟩

/-- Every accepted scalar is initialized; accepted arrays have neither padding
nor unions. Thus the exact-sized integer aggregate cast preserves NoUndef. -/
def rustPassMode (target : Target) (architecture : String) (isReturn : Bool)
    (ty : ConcreteType) : Except String Input.AbiPassMode := do
  let shape ← rustModeShape target architecture isReturn ty
  let empty : Input.AbiPassMode := ⟨.ignore, #[], none, none, none, none⟩
  match shape with
  | .ignore => return empty
  | .direct extendBool =>
    -- Raw pointers have no dereferenceable pointee and retain the full valid
    -- range. FnPtr excludes null in its scalar layout: NoUndef | NonNull.
    let bits := match ty with | .functionPointer .. => 144 | _ => 128
    return { empty with kind := .direct, attributes := #[attributes bits
      (if extendBool then .zeroExtend else .none)] }
  | .integerCast size =>
    let register : Input.AbiRegister := ⟨.integer, size * 8, none⟩
    let cast : Input.AbiCastTarget := ⟨#[], none, register, size, false, attributes 128⟩
    return { empty with kind := .cast, castTarget := some cast, padI32Count := some 0 }
  | .indirect =>
    let layout ← layoutOf target ty
    -- NoAlias | CapturesAddress | NonNull | NoUndef | NoFree.
    return { empty with
      kind := .indirect
      attributes := #[attributes 670 Input.ArgumentExtensionKind.none layout.size (some layout.align)]
      indirectMode := some .pointer }

/-- IDs supplied here must already name this concrete type and its *physical*
layout in the same executable registry. Size/alignment checks alone cannot
establish this association. No registry validation or provenance claim is made
by this data structure or by `rustFunctionAbiComponent`. -/
structure AbiTypeBinding where
  type : ConcreteType
  typeId : Input.TypeId
  layoutId : Input.LayoutId

private def rustArgument (target : Target) (architecture : String) (isReturn : Bool)
    (binding : AbiTypeBinding) : Except String Input.AbiArgument := do
  return ⟨binding.typeId, binding.layoutId,
    ← rustPassMode target architecture isReturn binding.type⟩

/-- Parametric construction for a nonvariadic ordinary Rust item, without
track_caller, virtual receiver adjustment, extra arguments or deduced pointer
attributes. The caller must establish those signature facts and the binding
associations above; this API is not sufficient evidence for interpreter import. -/
def rustFunctionAbiComponent (target : Target) (architecture : String)
    (unwind : RustUnwindFacts) (arguments : Array AbiTypeBinding)
    (result : AbiTypeBinding) : Except String Input.FunctionAbi := do
  let ret ← rustArgument target architecture true result
  let args ← arguments.mapM (rustArgument target architecture false)
  return {
    arguments := args
    returnValue := ret
    callingConvention := ⟨.rust, none, none, none⟩
    canUnwind := rustCanUnwind unwind
    cVariadic := false
    fixedCount := arguments.size
  }

end Miri.Frontend.Foundation
