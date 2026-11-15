import Miri.Frontend.FoundationLayout

/-! Physical rows computed from finite target material. The constructors follow
pinned rustc_abi/layout/simple.rs::scalar and layout.rs::layout_of_array_like.
Empty tuples use layout_of_univariant_biased with no fields and default repr:
rustc_ty_utils/src/layout.rs::layout_of_uncached maps tuples to univariant;
its empty-field alignment is aggregate_align and its seed is zero.
Thin pointer layout follows rustc_ty_utils/src/layout.rs's Ref/RawPtr branch:
Primitive::Pointer(AddressSpace::ZERO), a full raw range or reference start 1.
These are representation facts and supply no dereferenceability, allocation,
provenance or borrow permission evidence.
They supply no compiler boolean-query catalog or nominal type facts. -/
namespace Miri.Frontend.Foundation

private def memoryBackend : Input.BackendRepr :=
  ⟨.memory, some true, none, none, none, none, none, none, none⟩

private def singleVariant : Input.VariantsLayout :=
  ⟨.single, some 0, none, none, none, #[]⟩

private def baseLayout (size align seed : Nat) (fields : Input.FieldShape)
    (offsets : Input.LayoutFieldOffsets) (backend : Input.BackendRepr)
    (niche : Option Input.NicheLayout) : Input.Layout := {
  maxReprAlignBytes := none, reprC := false, uninhabited := false,
  largestNiche := niche, randomizationSeed := seed, kind := .layout,
  sizeBytes := some size, abiAlignBytes := some align,
  unadjustedAbiAlignBytes := some align, fieldOffsetsBytes := offsets,
  fields := some fields, variantsLayout := some singleVariant,
  backendRepresentation := some backend, variantsKind := some .single,
  backendReprKind := some backend.kind, variants := none, backendRepr := none }

/-- Structural primitive tags preserve pointer-sized type identity while the
physical primitive tag is always a fixed-width integer, as required by the
existing runtime converter. -/
def physicalIntegerKind (name : String) : Except String MIR.IntegerKind :=
  match name with
  | "i8" => pure .i8 | "u8" => pure .u8
  | "i16" => pure .i16 | "u16" => pure .u16
  | "i32" => pure .i32 | "u32" => pure .u32
  | "i64" => pure .i64 | "u64" => pure .u64
  | "i128" => pure .i128 | "u128" => pure .u128
  | "isize" => pure .isize | "usize" => pure .usize
  | _ => throw "unsupported physical integer tag"

private def scalarLayout (size align : Nat) (signed : Bool) (last : Nat) :
    Except String Input.Layout := do
  let tag ← physicalIntegerKind s!"{if signed then "i" else "u"}{size * 8}"
  let primitive : Input.PrimitiveLayout :=
    ⟨.integer, size, some (.known tag), some signed, none, none⟩
  let scalar : Input.ScalarLayout := ⟨.initialized, primitive, some (0, last)⟩
  let niche := if last == 2 ^ (size * 8) - 1 then none
    else some (Input.NicheLayout.mk 0 primitive (0, last))
  let rotated := UInt64.ofNat ((last % 2^64) / 2^16 + (last % 2^16) * 2^48)
  let seed := (UInt64.ofNat size + UInt64.ofNat ((if signed then 1 else 2) * 2^32) + rotated).toNat
  return baseLayout size align seed ⟨.primitive, 0, none, none, #[], #[]⟩
    (.explicit #[]) ⟨.scalar, none, some scalar, none, none, none, none, none, none⟩ niche

/-- Exact supported physical layouts; unsupported shapes and missing complete
material remain errors. Recursion and object bounds use the same checked query
as size/alignment construction. No rustc process or answer cache is consulted. -/
def physicalLayoutOfRuntime (target : ABI.RuntimeTargetDataLayout) (ty : ConcreteType) :
    Except String Input.Layout := do
  let _ ← layoutOfRuntime target ty
  go 1024 ty
where
  go (fuel : Nat) (ty : ConcreteType) : Except String Input.Layout := do
    let .succ fuel := fuel | throw "physical layout recursion exhausted"
    let basic ← layoutOfRuntime target ty
    match ty with
    | .primitive kind _name =>
      let signed := kind == "int"
      let last := if kind == "bool" then 1 else if kind == "char" then 0x10ffff
        else 2 ^ (basic.size * 8) - 1
      scalarLayout basic.size basic.align signed last
    | .array element count =>
      let elem ← go fuel element
      let some stride := elem.sizeBytes | throw "physical element size absent"
      let seed := (UInt64.ofNat elem.randomizationSeed + UInt64.ofNat count).toNat
      return baseLayout basic.size basic.align seed
        ⟨.array, count, none, some stride, #[], #[]⟩ (.arrayFormula stride count)
        memoryBackend (if count == 0 then none else elem.largestNiche)
    | .tuple elements =>
      unless elements.isEmpty do throw "nonempty physical tuple unsupported"
      let align ← target.aggregateAlign.bytes.mapError toString
      return baseLayout 0 align.toNat 0 ⟨.arbitrary, 0, none, none, #[], #[]⟩
        (.explicit #[]) memoryBackend none
    | .pointer kind _ =>
      let info ← pointerKindInfo kind
      let first := if info.region.isSome then 1 else 0
      let last := 2 ^ (basic.size * 8) - 1
      let primitive : Input.PrimitiveLayout :=
        ⟨.pointer, basic.size, none, none, none, some 0⟩
      let scalar : Input.ScalarLayout := ⟨.initialized, primitive, some (first, last)⟩
      let niche := if first == 0 then none else some (Input.NicheLayout.mk 0 primitive (first, last))
      let rotate (n : Nat) := UInt64.ofNat ((n % 2^64) / 2^16 + (n % 2^16) * 2^48)
      let seed := (UInt64.ofNat basic.size + UInt64.ofNat (4 * 2^32) + rotate first + rotate last).toNat
      return baseLayout basic.size basic.align seed ⟨.primitive, 0, none, none, #[], #[]⟩
        (.explicit #[]) ⟨.scalar, none, some scalar, none, none, none, none, none, none⟩ niche

def physicalLayoutOf (target : Target) (ty : ConcreteType) : Except String Input.Layout := do
  physicalLayoutOfRuntime (← runtimeTargetOfTarget target) ty

/-- Build a row from already interned child and length identities. The caller
must bind those IDs in its document-local pools; no compiler facts are invented. -/
def physicalTypeNode (ty : ConcreteType) (id layoutId : Nat)
    (arrayReferences : Option (Nat × Nat) := none)
    (pointeeReference : Option Nat := none) : Except String Input.TypeNode := do
  let (shape, display) ← match ty with
    | .primitive "bool" "" => pure (Input.TypeShape.bool, "bool")
    | .primitive "char" "" => pure (Input.TypeShape.char, "char")
    | .primitive "int" name =>
      unless #["i8", "i16", "i32", "i64", "i128", "isize"].contains name do
        throw "invalid signed primitive name"
      pure (.int (.known (← physicalIntegerKind name)), name)
    | .primitive "uint" name =>
      unless #["u8", "u16", "u32", "u64", "u128", "usize"].contains name do
        throw "invalid unsigned primitive name"
      pure (.uint (.known (← physicalIntegerKind name)), name)
    | .array _ count =>
      let some (element, length) := arrayReferences | throw "array pool identities absent"
      pure (.array element length ⟨count, true⟩, s!"foundation-array-{id}")
    | .tuple elements =>
      unless elements.isEmpty do throw "nonempty physical tuple unsupported"
      pure (.tuple #[], "()")
    | .pointer kind _ =>
      let info ← pointerKindInfo kind
      let some pointee := pointeeReference | throw "pointer pointee identity absent"
      match info.region with
      | none => pure (.rawPointer pointee info.mutability, s!"foundation-pointer-{id}")
      | some region => pure (.reference pointee info.mutability region, s!"foundation-reference-{id}")
    | _ => throw "unsupported physical type shape"
  return { id, layoutId, shape, display }

end Miri.Frontend.Foundation
