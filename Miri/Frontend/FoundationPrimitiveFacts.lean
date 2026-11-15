import Miri.Frontend.FoundationPhysicalRegistry

/-! Compiler leaves for the closed physical subset, computed from structure.
Pinned rustc sources: ty/util.rs::{is_trivially_freeze,is_trivially_unpin,
needs_drop_components_with_async,struct_tail_raw}; ty/sty.rs::{builtin_deref,
discriminant_ty,ptr_metadata_ty_or_tail,is_like_maybe_dangling};
ty/inhabitedness/mod.rs::OpSemInhabitedness::is_inhabited_ty.
All supported leaves are inhabited, Sized, Freeze and both Unpin traits;
arrays recurse and the only supported tuple is empty. No trait solver fallback
is taken. Region/parameter/inference flags are absent by construction.
Hashing, nominal definitions and projection catalogs are intentionally absent. -/
namespace Miri.Frontend.Foundation

/-- Check the entire supported domain before assigning any compiler answer. -/
def primitiveFactsDomain (ty : ConcreteType) : Except String Unit := go 1024 ty
where
  go (fuel : Nat) (ty : ConcreteType) : Except String Unit := do
    let .succ fuel := fuel | throw "primitive compiler facts recursion exhausted"
    match ty with
    | .primitive "bool" "" | .primitive "char" "" => pure ()
    | .primitive "int" name =>
      unless #["i8", "i16", "i32", "i64", "i128", "isize"].contains name do
        throw "unsupported signed compiler facts"
    | .primitive "uint" name =>
      unless #["u8", "u16", "u32", "u64", "u128", "usize"].contains name do
        throw "unsupported unsigned compiler facts"
    | .array element _ => go fuel element
    | .tuple fields =>
      unless fields.isEmpty do throw "nonempty tuple compiler facts unsupported"
    | _ => throw "unsupported primitive compiler facts"

/-- IDs must be provided by the physical registry: self, unit metadata, and u8
(the pinned discriminant type for every supported non-enum shape). -/
def primitiveCompilerFacts (ty : ConcreteType) (self unit u8 : Nat) :
    Except String Input.TypeCompilerFacts := do
  primitiveFactsDomain ty
  return {
    typingEnvironment := "fully_monomorphized"
    booleanQueries := #[
      ("is_unsafe_cell", false), ("has_erasable_regions", false),
      ("is_c_void", false), ("is_simd", false), ("is_box", false),
      ("is_global_box", false), ("is_dynamic", false), ("is_too_generic", false),
      ("is_monomorphic", true), ("is_monomorphic_enough", true),
      ("is_like_maybe_dangling", false), ("is_freeze", true),
      ("is_unpin", true), ("is_unsafe_unpin", true), ("needs_drop", false),
      ("opsem_inhabited", true), ("is_sized", true)]
    typeQueries := #[
      ("normalized", some self), ("metadata_tail", some self),
      ("pointer_metadata_type", some unit), ("discriminant_type", some u8),
      ("builtin_deref_explicit", none), ("builtin_deref_implicit", none),
      ("boxed_type", none), ("unsafe_binder_erased", none)]
    discriminants := some ⟨false, none, #[]⟩ }

namespace PhysicalTypeRegistry

/-- Attach derived compiler leaves to all currently demanded rows. The only
additional demands are the exact unit and u8 query result types. Re-run after
adding more rows; no answer for an unsupported type is fabricated. -/
def withPrimitiveFacts (r : PhysicalTypeRegistry) : Except String PhysicalTypeRegistry := do
  let (r, unit) ← r.intern (.tuple #[])
  let (r, u8) ← r.intern (.primitive "uint" "u8")
  let mut nodes := r.types
  for i in [:r.types.size] do
    let some entry := r.registry.entries[i]? | throw "compiler fact type identity absent"
    let (node, _) ← r.lookup i
    let facts ← primitiveCompilerFacts entry.type i unit u8
    if h : i < nodes.size then
      nodes := nodes.set i { node with compilerFacts := some facts }
    else
      throw "compiler fact destination identity absent"
  return { r with types := nodes }

end PhysicalTypeRegistry
end Miri.Frontend.Foundation
