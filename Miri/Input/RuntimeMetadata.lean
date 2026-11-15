import Miri.Input.Model
import Miri.Input.TypeArena
import Miri.Input.TypeArenaWorld
import Miri.Input.GenericInstantiationWorld
import Miri.Input.WorldNormalization
import Miri.Input.SequenceLayoutMaterial
import Miri.ABI.Layout
import Miri.Input.StructLayoutMaterial
import Miri.Input.CoroutineSourceInstantiation

/-! Compiler adapters and runtime metadata must come from the same export:
pool IDs are compilation-local. -/
namespace Miri.Input
open Miri.ABI

inductive RuntimeMetadataError where
  | missing (path : String)
  | unsupported (path : String)
  | invalid (path message : String)
  | duplicateType (id : TypeId)
  | unknownType (id : TypeId)
  deriving DecidableEq, Repr
instance : ToString RuntimeMetadataError where
  toString e := reprStr e

namespace RuntimeMetadata

abbrev Result := Except RuntimeMetadataError

def require (value : Option A) (path : String) : Result A :=
  match value with | some value => pure value | none => throw (.missing path)
def u64 (n : Nat) (path : String) : Result UInt64 :=
  if n < 2^64 then pure (UInt64.ofNat n) else throw (.invalid path "u64 overflow")
def u32 (n : Nat) (path : String) : Result UInt32 :=
  if n < 2^32 then pure (UInt32.ofNat n) else throw (.invalid path "u32 overflow")
def u128 (n : Nat) (path : String) : Result U128 :=
  if n < 2^128 then pure (BitVec.ofNat 128 n) else throw (.invalid path "u128 overflow")
def size (n : Nat) : Result Size := Size.ofBytes <$> u64 n "size"
def alignment (n : Nat) : Result Align := do
  if n == 0 then throw (.invalid "alignment" "zero alignment")
  (Align.fromBytes (← u64 n "alignment")).mapError (fun e => .invalid "alignment" (toString e))

def integer : MIR.IntegerKind → Result Integer
  | .i8 | .u8 => pure .I8
  | .i16 | .u16 => pure .I16
  | .i32 | .u32 => pure .I32
  | .i64 | .u64 => pure .I64
  | .i128 | .u128 => pure .I128
  | .isize | .usize => throw (.unsupported "pointer-sized integer primitive tag")
def float : FloatTypeTag → Result ABI.Float
  | .f16 => pure .F16 | .f16b => pure .F16B | .f32 => pure .F32
  | .f64 => pure .F64 | .f128 => pure .F128 | .ppcf128 => pure .PpcF128

def primitive (target : RuntimeTargetDataLayout) (source : PrimitiveLayout) : Result Primitive := do
  let expected ← size source.sizeBytes
  match source.kind with
  | .integer =>
    let kind ← require source.integerKind "primitive.integer_kind"
    let .known kind := kind
    let integer ← integer kind
    if integer.size != expected then throw (.invalid "integer" "tag/size mismatch")
    return .Int integer (← require source.signed "primitive.signed")
  | .float =>
    let f ← float (← require source.floatKind "primitive.float_kind")
    if f.size != expected then throw (.invalid "float" "tag/size mismatch")
    return .Float f
  | .pointer =>
    let space : AddressSpace := ⟨← u32 (← require source.addressSpace "primitive.address_space") "address space"⟩
    let pointerSize ← (target.pointerSizeIn space).mapError (fun e => .invalid "pointer" (toString e))
    if pointerSize != expected then throw (.invalid "pointer" "target/primitive size mismatch")
    return .Pointer space

def scalar (target : RuntimeTargetDataLayout) (source : ScalarLayout) : Result ABI.Scalar := do
  let value ← primitive target source.primitive
  match source.kind with
  | .initialized =>
    let (first,last) ← require source.validRange "scalar.valid_range"
    let range : WrappingRange := ⟨← u128 first "range.start", ← u128 last "range.end"⟩
    let width ← size source.primitive.sizeBytes
    let _ ← (range.isFullFor width).mapError (fun e => .invalid "scalar range" (reprStr e))
    return .Initialized (value := value) (validRange := range)
  | .union => return .Union (value := value)

def backend (target : RuntimeTargetDataLayout) (source : Input.BackendRepr) : Result ABI.BackendRepr := do
  match source.kind with
  | .scalar => return .Scalar (← scalar target (← require source.scalar "backend.scalar"))
  | .scalarPair =>
    let a ← scalar target (← require source.first "backend.first")
    let b ← scalar target (← require source.second "backend.second")
    return .ScalarPair (a := a) (b := b) (bOffset := ← size (← require source.secondOffsetBytes "backend.second_offset"))
  | .memory => return .Memory (sized := ← require source.sized "backend.sized")
  | .simdVector | .scalableSimdVector =>
    let element ← scalar target (← require source.element "backend.element")
    let count ← (BackendLaneCount.new (← u64 (← require source.laneCount "backend.lane_count") "lane count"))
      |>.mapError (fun e => .invalid "lane count" (reprStr e))
    if source.kind == .simdVector then return .SimdVector (element := element) (count := count)
    let vectors ← require source.vectorCount "backend.vector_count"
    if vectors == 0 || vectors > 8 then throw (.invalid "vector count" "outside 1..=8")
    return .SimdScalableVector (element := element) (count := count)
      (numberOfVectors := ⟨UInt8.ofNat vectors⟩)

def fields (source : FieldShape) : Result FieldsShape := do
  let result ← match source.kind with
    | .primitive =>
      if source.fieldCount != 0 then throw (.invalid "primitive fields" "nonzero field count")
      pure .Primitive
    | .union =>
      if (← require source.offsetBytes "union.offset_bytes") != 0 then
        throw (.invalid "union" "nonzero offset")
      pure (.Union source.fieldCount)
    | .array => pure (.Array (← size (← require source.strideBytes "array.stride"))
        (← u64 source.fieldCount "array count"))
    | .arbitrary =>
      if source.fieldCount != source.offsetsBytes.size then throw (.invalid "fields" "count mismatch")
      pure (.Arbitrary (← source.offsetsBytes.mapM size) source.memoryOrder)
  result.validate.mapError (fun e => .invalid "fields" (reprStr e))
  pure result

def niche (target : RuntimeTargetDataLayout) (source : Option NicheLayout) : Result (Option Niche) := do
  let some source := source | return none
  let value ← primitive target source.primitive
  let range : WrappingRange := ⟨← u128 source.validRange.1 "niche.start", ← u128 source.validRange.2 "niche.end"⟩
  let width ← value.size target |>.mapError (fun e => .invalid "niche size" (toString e))
  let _ ← range.isFullFor width |>.mapError (fun e => .invalid "niche range" (reprStr e))
  return some ⟨← size source.offsetBytes, value, range⟩

def encoding (source : Input.TagEncoding) : Result ABI.TagEncoding := do
  match source.kind with
  | .direct => pure .Direct
  | .niche =>
    let (first,last) ← require source.nicheVariants "tag.niche_variants"
    if first > last then throw (.invalid "niche variants" "reversed range")
    return .Niche (← require source.untaggedVariant "tag.untagged_variant") first last
      (← u128 (← require source.nicheStart "tag.niche_start") "niche start")

private def variant (target : RuntimeTargetDataLayout) (source : Input.LayoutVariant) : Result ABI.VariantLayout := do
  if source.fields.kind != .arbitrary then throw (.invalid "variant fields" "not arbitrary")
  let offsets ← source.fieldOffsetsBytes.mapM size
  let memoryOrder := source.fields.memoryOrder
  if source.fields.offsetsBytes != source.fieldOffsetsBytes then throw (.invalid "variant offsets" "duplicate metadata mismatch")
  if source.fields.fieldCount != offsets.size then throw (.invalid "variant fields" "count mismatch")
  (FieldsShape.Arbitrary offsets memoryOrder).validate.mapError (fun e => .invalid "variant fields" (reprStr e))
  return {
    size := ← size source.sizeBytes, backendRepr := ← backend target source.backendRepr,
    fieldOffsets := offsets, fieldsInMemoryOrder := memoryOrder,
    largestNiche := ← niche target source.largestNiche, uninhabited := source.uninhabited }

def variants (target : RuntimeTargetDataLayout) (source : VariantsLayout) : Result ABI.Variants := do
  match source.kind with
  | .empty => pure .Empty
  | .single => return .Single (← require source.variantIndex "variant index")
  | .multiple =>
    let mut values := #[]
    for source in source.variants do
      if source.variantIndex != values.size then throw (.invalid "variants" "noncontiguous source indices")
      values := values.push (← variant target source)
    return .Multiple (← scalar target (← require source.tag "variants.tag"))
      (← encoding (← require source.tagEncoding "variants.tag_encoding"))
      (← require source.tagFieldIndex "variants.tag_field_index") values

def layout (target : RuntimeTargetDataLayout) (source : Input.Layout) : Result LayoutData := do
  let maxAlign ← source.maxReprAlignBytes.mapM alignment
  let fields ← fields (← require source.fields "layout.fields")
  source.fieldOffsetsBytes.validate (← require source.fields "layout.fields")
    |>.mapError (fun message => .invalid "field offsets" message)
  match source.fieldOffsetsBytes with
  | .explicit offsets =>
    let duplicateOffsets ← offsets.mapM size
    for index in List.range fields.count do
      let offset ← fields.offset index |>.mapError (fun e => .invalid "field offset" (reprStr e))
      if duplicateOffsets[index]? != some offset then throw (.invalid "field offsets" "mismatch")
  | .arrayFormula _ _ => pure ()
  let variants ← variants target (← require source.variantsLayout "layout.variants")
  let uninhabited := source.uninhabited
  if variants == .Empty && !uninhabited then throw (.invalid "empty variants" "inhabited layout")
  return {
    fields, variants, backendRepr := ← backend target (← require source.backendRepresentation "layout.backend"),
    largestNiche := ← niche target source.largestNiche, uninhabited,
    align := .new (← alignment (← require source.abiAlignBytes "layout.align")),
    size := ← size (← require source.sizeBytes "layout.size"), maxReprAlign := maxAlign,
    unadjustedAbiAlign := ← alignment (← require source.unadjustedAbiAlignBytes "layout.unadjusted_align"),
    reprC := source.reprC, randomizationSeed := ← u64 source.randomizationSeed "seed" }


private def pointerSpec (source : TargetPointerSpec) : Result PointerSpec := do
  return ⟨← size source.pointerSizeBytes, ← alignment source.pointerAlignBytes,
    ← size source.pointerOffsetBytes, source.isFat⟩

def importTarget (source : TargetDataLayoutEvidence) : Result RuntimeTargetDataLayout := do
  let endian ← match source.endian with
    | "little" => pure Endian.little | "big" => pure .big
    | _ => throw (.unsupported "target endian")
  let width ← match source.pointerWidthBits with
    | 16 => pure PointerWidth.w16 | 32 => pure .w32 | 64 => pure .w64
    | _ => throw (.unsupported "target pointer width")
  let base : TargetDataLayout := ⟨endian, width⟩
  let objectBound ← require source.objectSizeBoundBytes "object bound"
  if (← u64 objectBound "object bound") != base.objSizeBound then
    throw (.invalid "object bound" "target arithmetic view mismatch")
  let vectors ← source.vectorAlign.mapM fun (width, align) => do
    pure (← size width, ← alignment align)
  let spaces ← source.addressSpaceInfo.mapM fun entry => do
    pure (AddressSpace.mk (← u32 entry.addressSpace "address space"),
      ← pointerSpec entry.spec)
  let cEnum ← match source.cEnumMinSize with
    | "I8" => pure Integer.I8 | "I16" => pure .I16 | "I32" => pure .I32
    | "I64" => pure .I64 | "I128" => pure .I128
    | _ => throw (.unsupported "C enum min size")
  let result : RuntimeTargetDataLayout := {
    base, i1Align := ← alignment source.i1AlignBytes,
    i8Align := ← alignment source.i8AlignBytes,
    i16Align := ← alignment source.i16AlignBytes,
    i32Align := ← alignment source.i32AlignBytes,
    i64Align := ← alignment source.i64AlignBytes,
    i128Align := ← alignment source.i128AlignBytes,
    f16Align := ← alignment source.f16AlignBytes,
    f32Align := ← alignment source.f32AlignBytes,
    f64Align := ← alignment source.f64AlignBytes,
    f128Align := ← alignment source.f128AlignBytes,
    aggregateAlign := ← alignment source.aggregateAlignBytes,
    vectorAlign := vectors,
    defaultAddressSpace := ⟨← u32 source.defaultAddressSpace "default address space"⟩,
    defaultAddressSpacePointerSpec := ← pointerSpec source.defaultAddressSpacePointerSpec,
    addressSpaceInfo := spaces,
    instructionAddressSpace := ⟨← u32 source.instructionAddressSpace "instruction address space"⟩,
    cEnumMinSize := cEnum }
  result.validate.mapError (fun e => .invalid "target" (toString e))
  return result


end RuntimeMetadata

private def rawLayoutBudget (types layouts : Nat) (definitions : Array DefinitionId) : Nat :=
  3 * (types + layouts + definitions.foldl (fun total definition => total + match definition.genericTemplate with
    | none => 1
    | some template => 1 + StructLayoutMaterial.termFuel template.typeExpression +
      template.fields.foldl (fun total field => total + StructLayoutMaterial.termFuel field.expression) 0) 1)

/-- Immutable compiler tables and target semantics. -/
structure RuntimeMetadata where
  source : ImportDocument
  target : RuntimeTargetDataLayout
  /-- Raw syntax traversal budget, computed once; contains no query answer. -/
  materialLayoutFuel : Nat
  /-- Immutable validation/index evidence tied to the exact raw source prefix. -/
  checkedMaterial : Option (TypeArena.CheckedMaterial source.types source.typeConstants
    source.definitions source.predicates target.pointerSize.bytes.toNat) := none
  /-- Checked once at import. Dependence on the exact source prevents retaining
  this certificate when replacing its type table. It carries no runtime cache. -/
  denseTypes : Option (PLift (TypeArena.isDense source.types = true)) := none

namespace RuntimeMetadata

def ofDocument (document : ImportDocument) : Result RuntimeMetadata := do
  let target ← importTarget (← require document.runtimeTargetDataLayout "runtime_target_data_layout")
  let mut seen : Std.HashSet TypeId := {}
  for node in document.types do
    if seen.contains node.id then throw (.duplicateType node.id)
    seen := seen.insert node.id
  if dense : TypeArena.isDense document.types = true then
    let checked ← (TypeArena.CheckedMaterial.create document.types document.typeConstants
      document.definitions document.predicates target.pointerSize.bytes.toNat).mapError (fun e => .invalid "material prefix" e)
    return {
      source := document
      target := target
      checkedMaterial := some checked
      materialLayoutFuel := rawLayoutBudget document.types.size document.layouts.size document.definitions,
      denseTypes := some ⟨dense⟩ }
  else throw (.invalid "compiler type ID" "material type IDs are not dense row positions")

def node (metadata : RuntimeMetadata) (id : TypeId) : Result TypeNode := do
  if metadata.denseTypes.isNone then
    (TypeArena.validateMaterial metadata.source.types).mapError (.invalid "type arena")
  let value ← require metadata.source.types[id]? "source type; constructed types require execution universe"
  unless value.id == id do throw (.invalid "type arena" "source type row/index mismatch")
  pure value

structure LayoutNormalization (m : Type → Type) where
  resolve : Nat → Nat → GenericSubstitution.Term → m TypeId

section EffectfulSourceLayouts
variable {m : Type → Type} [Monad m] [MonadStateOf TypeArena.World m]
  [MonadExceptOf String m] [MonadLiftT (Except String) m]
  [MonadLiftT TypeArena.WorldM m]

private def lift {m : Type → Type} [Monad m] [MonadExceptOf String m] (result : Except String α) : m α :=
  match result with | .ok value => pure value | .error error => throw error

private def worldAdt (id : TypeId) : m (AdtDeclaration.Material × GenericSubstitution.DefinitionTemplate ×
    GenericSubstitution.DefinitionIdentity × Array MIR.GenericArg × Option AdtShape) := do
  let world ← get
  let (identity, args, shape) ← match ← lift (world.lookupType id) with
    | .material node => match node.shape with
      | .adt data => do
        let some definition := world.definitions[data.definition]? | throw "layout ADT definition absent"
        pure (⟨definition.crateIndex,definition.index⟩,data.args,some data)
      | _ => throw "layout source type is not an ADT"
    | .constructed (.adt identity args) => pure (identity,args,none)
    | _ => throw "layout constructed type is not an ADT"
  let reference ← lift (world.definitionRef identity)
  let some definition := world.definitions[reference]? | throw "layout ADT declaration absent"
  let some declaration := definition.adtDeclaration | throw "layout raw ADT declaration absent"
  let some template := definition.genericTemplate | throw "layout raw ADT field template absent"
  lift (declaration.validate template)
  unless args.size == template.parameters.size do throw "layout ADT generic argument arity mismatch"
  for (parameter,arg) in template.parameters.zip args do
    let sort : GenericSubstitution.ArgSort := match arg with
      | .Type _ => .type | .Lifetime _ => .region | .Const _ => .constant
    unless parameter == sort do throw "layout ADT generic argument sort mismatch"
  if let some shape := shape then
    unless shape.kind == declaration.kind && shape.representation == declaration.representation do
      throw "layout ADT material differs from raw declaration attributes"
    unless shape.variants.size == declaration.variantCount do
      throw "layout ADT variant domain differs from raw declaration"
    let materialFields := shape.variants.foldl (fun fields variant =>
      fields ++ variant.fields.map (fun field => (variant.index,field.index))) #[]
    unless materialFields == declaration.fields.map (fun field => (field.variantIndex,field.fieldIndex)) do
      throw "layout ADT field domain differs from raw declaration"
  pure (declaration,template,identity,args,shape)

open TypeArena in
private def worldAdtField (normalization : Option (LayoutNormalization m)) (fuel : Nat)
    (id variant index : Nat) : m TypeId := do
  let world ← get
  let (declaration,_,identity,args,_) ← worldAdt id
  unless variant < declaration.variantCount && declaration.fields.any (fun field =>
      field.variantIndex == variant && field.fieldIndex == index) do
    throw "constructed ADT field index absent"
  let term ← lift (GenericInstantiationWorld.instantiateFieldTerm world fuel identity args variant index)
  match normalization with
  | some context => context.resolve (fuel * (fuel + 1)) fuel term
  | none => GenericInstantiationWorld.resolveType fuel term

open TypeArena in
private def worldConstructor (id : TypeId) : m Constructor := do
  let world ← get
  match ← lift (world.lookupType id) with
  | .constructed key => pure key
  | .material node =>
    let some key ← lift (world.materialKey node) | throw "layout source constructor has no universe key"
    pure key

open TypeArena in
/-- layout.rs975-987 and rustc_type_ir/ty_kind/closure.rs138-173,250-281:
closure fields are the actual capture tuple's fields. The raw generic header
checks the parent prefix and synthetic suffix before selecting upvars. -/
private def worldClosureFields (id : TypeId) : m (Array TypeId) := do
  let (owner,arguments,suffix) ← match ← worldConstructor id with
    | .closure owner arguments => pure (owner,arguments,3)
    | .coroutineClosure owner arguments => pure (owner,arguments,4)
    | _ => throw "capture fields require a closure constructor"
  let world ← get
  let reference ← lift (world.definitionRef owner)
  let some definition := world.definitions[reference]? | throw "capture field owner absent"
  let some path := definition.rawPath | throw "capture field raw generic header absent"
  unless path.components.back?.any (·.kind == "closure") do
    throw "capture field raw owner is not a closure"
  let header ← lift (DefinitionPath.requireGenerics path)
  unless header.parameters.size == arguments.size &&
      header.parentParameterCount + suffix == arguments.size do
    throw "capture field canonical synthetic scope mismatch"
  for (sort,argument) in header.parameters.zip arguments do
    let actual : GenericSubstitution.ArgSort := match argument with
      | .Type _ => .type | .Const _ => .constant | .Lifetime _ => .region
    unless sort == actual do throw "capture field generic argument sort mismatch"
  let some (MIR.GenericArg.Type captures) := arguments[header.parentParameterCount + 2]?
    | throw "capture field tuple argument absent"
  let .tuple fields ← worldConstructor captures | throw "capture field upvars are not a tuple"
  pure fields

private def worldArrayCount (target : RuntimeTargetDataLayout) (length : TypeConstantId)
      (identity : ArrayConstructor) : m UInt64 := do
    let world ← get
    lift (SequenceLayoutMaterial.arrayCount
      (fun id => do
        match ← world.lookupType id with
        | .material node => pure (node.shapeMetadata.unsignedKind == some (.known .usize))
        | .constructed (.integer false .usize) => pure true
        | _ => pure false)
      world.lookupConstant target.pointerSize.bytes.toNat length identity)

/-- A canonical layout demand consumes the exact rustc LayoutData exported for
this material type. The execution World verifies its identity; locally interned
types cannot borrow a numeric row from the immutable compiler prefix. -/
def layoutEffectfulInWorld (normalization : LayoutNormalization m) (metadata : RuntimeMetadata) (id : TypeId) : m (TyAndLayout TypeId) := do
  let _ := normalization
  let actual ← match ← lift ((← get).lookupType id) with
    | .material node => pure node
    | .constructed constructor =>
      throw s!"constructed type {id} ({reprStr constructor}) has no rustc canonical layout result"
  let some original := metadata.source.types[id]?
    | throw "canonical layout type is absent from rustc export"
  unless actual.id == id && actual.layoutId == original.layoutId &&
      (← lift ((← get).materialKey actual)) == (← lift ((← get).materialKey original)) do
    throw "canonical layout type differs from rustc export"
  let some seed := metadata.source.layouts[original.layoutId]?
    | throw "rustc canonical layout result is absent"
  let result ← lift ((layout metadata.target seed).mapError toString)
  pure ⟨id,result⟩

end EffectfulSourceLayouts

private def pureLayoutNormalization : LayoutNormalization TypeArena.WorldM :=
  {resolve := WorldNormalization.resolveNormalizedTerm ()}

def layoutInWorld (metadata : RuntimeMetadata) (id : TypeId) : TypeArena.WorldM (TyAndLayout TypeId) :=
  layoutEffectfulInWorld (pureLayoutNormalization) metadata id

def resolveLayout (target : RuntimeTargetDataLayout) (_types : Array TypeNode)
    (layouts : Array Input.Layout) (id : LayoutId) (_definitions : Array DefinitionId)
    (_constants : Array MIR.TypeConst) (_predicates : Array VtablePredicate) : Result LayoutData := do
  let source ← require layouts[id]? "compiler layout ID out of bounds"
  layout target source

/-- Decode rustc's exact material layout for scalar-wire width validation.
The closure owns only immutable source arrays; it keeps no query memo. -/
def scalarStorageQuery (target : RuntimeTargetDataLayout) (types : Array TypeNode)
    (layouts : Array Input.Layout) (_definitions : Array DefinitionId)
    (_constants : Array MIR.TypeConst) (_predicates : Array VtablePredicate) : Result (TypeId → Result Nat) := do
  pure fun id => do
    let node ← require types[id]? "scalar storage type ID out of bounds"
    let source ← require layouts[node.layoutId]? "scalar storage rustc layout result absent"
    let value ← layout target source
    pure value.size.bytes.toNat

/-- ID-free standalone adapter. Decoder captures scalarStorageQuery once for
all scalar-wire checks, rather than rebuilding the checked prefix per value. -/
def scalarStorageSize (target : RuntimeTargetDataLayout) (types : Array TypeNode)
    (layouts : Array Input.Layout) (definitions : Array DefinitionId)
    (constants : Array MIR.TypeConst) (predicates : Array VtablePredicate) (id : TypeId) : Result Nat := do
  (← scalarStorageQuery target types layouts definitions constants predicates) id

def lookup (metadata : RuntimeMetadata) (id : TypeId) : Result (TyAndLayout TypeId) := do
  unless id < metadata.source.types.size do
    throw (.unsupported "constructed type layout requires the execution-owned universe")
  let source ← metadata.node id
  let seed ← require metadata.source.layouts[source.layoutId]? "compiler layout seed"
  return ⟨id, ← layout metadata.target seed⟩

/-- Pure source-constant access. Constructed constants belong to the execution
universe and must be obtained through its checked lookup. -/
def typeConstant (metadata : RuntimeMetadata) (id : TypeConstantId) : Result MIR.TypeConst :=
  require metadata.source.typeConstants[id]? "source type constant; constructed constants require execution universe"

/-- This is an explicit diagnostic inventory, not an execution-readiness test. -/
def obligations (metadata : RuntimeMetadata) : Array (TypeId × RuntimeMetadataError) :=
  metadata.source.types.filterMap fun node => match metadata.lookup node.id with
    | .error e => some (node.id,e) | .ok _ => none

def findKind (metadata : RuntimeMetadata) (kind : TypeShapeKind) : Result (TyAndLayout TypeId) := do
  let nodes := metadata.source.types.filter (·.shapeKind == kind)
  if nodes.size != 1 then throw (.unsupported "ambiguous or absent type-kind lookup")
  let value ← require nodes[0]? "type kind"
  metadata.lookup value.id

/-- Canonical primitive lookup compares the compiler integer tag, rather than
choosing an arbitrary member of the broad `int`/`uint` shape category. -/
def integerLayout (metadata : RuntimeMetadata) (kind : MIR.IntegerKind) : Result (TyAndLayout TypeId) := do
  let nodes := metadata.source.types.filter fun node =>
    node.shapeMetadata.signedKind == some (.known kind) || node.shapeMetadata.unsignedKind == some (.known kind)
  unless nodes.size == 1 do throw (.unsupported "ambiguous or absent exact integer type")
  let value ← require nodes[0]? "integer type"
  metadata.lookup value.id

/-- Pinned `TyAbiInterface::ty_and_layout_field` maps every `str` field
request to `tcx.types.u8`. The source query ignores the field index; a unique
canonical U8 identity supplies its exact type and layout. -/
private def stringElementLayout (metadata : RuntimeMetadata) : Result (TyAndLayout TypeId) := do
  let nodes := metadata.source.types.filter fun node =>
    node.shapeKind == .uint &&
      node.shapeMetadata.unsignedKind == some (.known .u8)
  unless nodes.size == 1 do throw (.unsupported "ambiguous or absent exact string element type")
  let value ← require nodes[0]? "string element type"
  metadata.lookup value.id

/-- Source Ty::new_tup identity from the exact ordered compiler element IDs.
No size, display spelling, or first-match heuristic establishes a tuple type. -/
def tupleLayout (metadata : RuntimeMetadata) (elements : Array TypeId) : Result (TyAndLayout TypeId) := do
  let mut candidates := #[]
  for node in metadata.source.types do
    if node.shapeKind == .tuple then
      let .tuple ids := node.shape | throw (.invalid "tuple type" "shape mismatch")
      if ids == elements then candidates := candidates.push node.id
  unless candidates.size == 1 do throw (.unsupported "ambiguous or absent exact tuple type")
  metadata.lookup (← require candidates[0]? "tuple type")

def overflowTupleLayout (metadata : RuntimeMetadata) (element : TyAndLayout TypeId) : Result (TyAndLayout TypeId) := do
  let boolean ← metadata.findKind .bool
  metadata.tupleLayout #[element.ty,boolean.ty]

private def projectionParents (metadata : RuntimeMetadata) (id : TypeId) : Result (Array ProjectionParent) := do
  let node ← metadata.node id
  let some facts := node.compilerFacts | return #[]
  let some queries := facts.projectionQueries | return #[]
  unless queries.typingEnvironment == "fully_monomorphized" do
    throw (.invalid "projection query" "typing environment mismatch")
  pure queries.parents
/-- Import the exact rustc contextual LayoutData by LayoutId. It contains no
type identities and requires no local layout reconstruction or World cache. -/
def layoutById (metadata : RuntimeMetadata) (id : Nat) : Result LayoutData := do
  let source ← require metadata.source.layouts[id]? "compiler layout ID out of bounds"
  layout metadata.target source

private def projectionLayout (metadata : RuntimeMetadata) (id : TypeId) (layoutId : LayoutId) :
    Result (TyAndLayout TypeId) := do
  return ⟨id,← metadata.layoutById layoutId⟩

/-- Source type relationships are read from typed compiler payloads, never
from display/debug strings. ADT field selection uses the selected variant. -/
def field (metadata : RuntimeMetadata) (parent : TyAndLayout TypeId) (index : Nat) :
    Result (TyAndLayout TypeId) := do
  let node ← metadata.node parent.ty
  for record in ← projectionParents metadata parent.ty do
    let queried ← projectionLayout metadata parent.ty record.layoutId
    if queried == parent then
      -- Pinned rustc TyAbiInterface::ty_and_layout_field returns the same
      -- element TyAndLayout for every array/slice/str index. The row at zero
      -- is rustc's concrete result for this whole query family.
      let sourceIndex := if node.shapeKind == .str || node.shapeKind == .slice ||
          node.shapeKind == .array then 0 else index
      let source ← require (record.fields.find? (·.index == sourceIndex))
        s!"compiler projection field: parent={parent.ty}, shape={reprStr node.shapeKind}, index={index}, source_index={sourceIndex}, variants={reprStr parent.layout.variants}"
      let id := source.typeId
      let _ ← metadata.node id
      return ← projectionLayout metadata id source.layoutId
  throw (.unsupported "missing exact rustc contextual field layout result")

/-- Reconstructs precisely `LayoutData::for_variant` in pinned
rustc_abi/layout/simple.rs:158–185. Missing uninhabited-variant compiler queries
remain obligations instead of fabricated field metadata. -/
def forVariant (metadata : RuntimeMetadata) (parent : TyAndLayout TypeId) (index : Nat) :
    Result (TyAndLayout TypeId) := do
  let _ ← metadata.node parent.ty
  for record in ← projectionParents metadata parent.ty do
    if record.variant == some index then
      let canonical ← metadata.lookup parent.ty
      unless canonical == parent do
        match parent.layout.variants with
        | .Single actual =>
          if actual == index then return parent
          throw (.invalid "compiler variant projection" "cannot apply for_variant twice to a selected parent")
        | _ => throw (.invalid "compiler variant projection" "parent differs from exact rustc layout")
      return ← projectionLayout metadata parent.ty record.layoutId
  throw (.unsupported "missing exact rustc contextual variant layout result")

def pointee (metadata : RuntimeMetadata) (parent : TyAndLayout TypeId) :
    Result (TyAndLayout TypeId) := do
  let node ← metadata.node parent.ty
  match node.shape with
  | .rawPointer pointee _ | .reference pointee .. => metadata.lookup pointee
  | _ => throw (.unsupported "non-pointer pointee query")

/-- Boundary adapter preserves missing compiler metadata as explicit failures. -/
def queries (metadata : RuntimeMetadata) : LayoutQueries TypeId := {
  field := fun parent index => (metadata.field parent index).mapError (fun _ => .missingField index)
  variant := fun parent index => (metadata.forVariant parent index).mapError (fun _ => .missingVariant index)
  pointee := fun parent => (metadata.pointee parent).mapError (fun _ => .missingPointee) }

/-- Read-only constructor classification; this operation never interns a type. -/
def shapeKindInWorld (_metadata : RuntimeMetadata) (id : TypeId) : TypeArena.WorldM TypeShapeKind := do
  lift ((← get).shapeKind id)

def packedAlignInWorld (_metadata : RuntimeMetadata) (id : TypeId) : TypeArena.WorldM (Option Align) := do
  let world ← get
  let packed ← match ← lift (world.lookupType id) with
    | .material node => match node.shape with
      | .adt data => pure data.representation.packBytes
      | _ => pure none
    | .constructed (.adt ..) => do
      let (declaration,_,_,_,_) ← worldAdt id
      pure declaration.representation.packBytes
    | _ => pure none
  lift (packed.mapM (fun value => (alignment value).mapError toString))

/-- Raw coroutine source selection in the execution-owned type universe. -/
private def coroutineSourceInWorld (metadata : RuntimeMetadata) (id : TypeId) :
    TypeArena.WorldM CoroutineSourceInstantiation.Result := do
  let world ← get
  let fuel := metadata.materialLayoutFuel + 3 * (world.constructedTypes.size + world.constructedConstants.size)
  let some coverage := metadata.source.coroutineCoverage | throw "coroutine source catalog absent"
  let term ← lift (GenericInstantiationWorld.ofType world fuel id)
  lift (CoroutineSourceInstantiation.instantiate coverage.genericSources fuel term)

section EffectfulFields
variable {m : Type → Type} [Monad m] [MonadStateOf TypeArena.World m]
  [MonadExceptOf String m] [MonadLiftT (Except String) m]
  [MonadLiftT TypeArena.WorldM m]

private def coroutineFieldTypeEffectful (normalization : LayoutNormalization m) (metadata : RuntimeMetadata) (id variant index : Nat) :
    m TypeId := do
  let source ← coroutineSourceInWorld metadata id
  let term ← lift (source.stateField variant index)
  let world ← get
  let fuel := metadata.materialLayoutFuel + 3 * (world.constructedTypes.size + world.constructedConstants.size)
  normalization.resolve (fuel * (fuel + 1)) fuel term

/-- Constructor field selection may instantiate and intern raw ADT field types
in the same execution universe. The requested variant is explicit. -/
def fieldTypeEffectfulInWorld (normalization : LayoutNormalization m) (_metadata : RuntimeMetadata) (id variant index : Nat) : m TypeId := do
  let world ← get
  let fuel := _metadata.materialLayoutFuel + 3 * (world.constructedTypes.size + world.constructedConstants.size)
  match ← lift (world.lookupType id) with
  | .material node => match node.shape with
    | .coroutine .. => coroutineFieldTypeEffectful normalization _metadata id variant index
    | .closure .. | .coroutineClosure .. => do
      let fields ← worldClosureFields id
      let some field := fields[index]? | throw "capture field index absent"
      pure field
    | .adt .. =>
      worldAdtField (some normalization) fuel id variant index
    | .tuple elements =>
      let some field := elements[index]? | throw "source tuple field index absent"
      pure field
    | .array element .. | .slice element => pure element
    | .str => TypeArena.World.internType (.integer false .u8)
    | .patternType base _ =>
      unless index == 0 do throw "source pattern has only its base field"
      pure base
    | _ => throw "source type field constructor is not implemented"
  | .constructed key => match key with
    | .coroutine .. => coroutineFieldTypeEffectful normalization _metadata id variant index
    | .closure .. | .coroutineClosure .. => do
      let fields ← worldClosureFields id
      let some field := fields[index]? | throw "capture field index absent"
      pure field
    | .adt .. =>
      worldAdtField (some normalization) fuel id variant index
    | .tuple elements =>
      let some field := elements[index]? | throw "constructed tuple field index absent"
      pure field
    | .array element _ | .slice element => pure element
    | .str => TypeArena.World.internType (.integer false .u8)
    | .patternType base _ =>
      unless index == 0 do throw "constructed pattern has only its base field"
      pure base
    | _ => throw "constructed type field constructor is not implemented"

end EffectfulFields

def fieldTypeInWorld (metadata : RuntimeMetadata) (id variant index : Nat) : TypeArena.WorldM TypeId :=
  fieldTypeEffectfulInWorld (pureLayoutNormalization) metadata id variant index

private def exactTypeInWorld (id : TypeId) (key : String) : TypeArena.WorldM TypeId := do
  let source ← match ← lift ((← get).lookupType id) with
    | .material node => pure node
    | .constructed _ => throw s!"constructed type has no exact rustc {key} result"
  let some facts := source.compilerFacts | throw s!"rustc {key} result absent"
  unless facts.typingEnvironment == "fully_monomorphized" do
    throw s!"rustc {key} result has a different typing environment"
  let some (_,some result) := facts.typeQueries.find? (·.1 == key)
    | throw s!"rustc {key} result absent"
  let _ ← lift ((← get).lookupType result)
  pure result

def metadataTailInWorld (_metadata : RuntimeMetadata) (id : TypeId) : TypeArena.WorldM TypeId :=
  exactTypeInWorld id "metadata_tail"

def pointerMetadataTypeInWorld (_metadata : RuntimeMetadata) (id : TypeId) : TypeArena.WorldM TypeId :=
  exactTypeInWorld id "pointer_metadata_type"

section EffectfulProjection
variable {m : Type → Type} [Monad m] [MonadStateOf TypeArena.World m]
  [MonadExceptOf String m] [MonadLiftT (Except String) m]
  [MonadLiftT TypeArena.WorldM m]

def fieldLayoutForEffectfulInWorld (_normalization : LayoutNormalization m) (metadata : RuntimeMetadata)
    (parent : TyAndLayout TypeId) (index : Nat) : m (TyAndLayout TypeId) := do
  let actual ← match ← lift ((← get).lookupType parent.ty) with
    | .material node => pure node
    | .constructed _ => throw "constructed type has no rustc contextual field layout result"
  let some original := metadata.source.types[parent.ty]?
    | throw "contextual field layout type is absent from rustc export"
  unless actual.id == parent.ty && actual.layoutId == original.layoutId &&
      (← lift ((← get).materialKey actual)) == (← lift ((← get).materialKey original)) do
    throw "contextual field layout type differs from rustc export"
  lift ((metadata.field parent index).mapError toString)

def fieldLayoutEffectfulInWorld (normalization : LayoutNormalization m) (metadata : RuntimeMetadata) (id index : Nat) :
    m (TyAndLayout TypeId) := do
  let parent ← layoutEffectfulInWorld normalization metadata id
  fieldLayoutForEffectfulInWorld normalization metadata parent index

end EffectfulProjection

def fieldLayoutForInWorld (metadata : RuntimeMetadata) (parent : TyAndLayout TypeId) (index : Nat) :
    TypeArena.WorldM (TyAndLayout TypeId) :=
  fieldLayoutForEffectfulInWorld (pureLayoutNormalization) metadata parent index

def fieldLayoutInWorld (metadata : RuntimeMetadata) (id index : Nat) : TypeArena.WorldM (TyAndLayout TypeId) :=
  fieldLayoutEffectfulInWorld (pureLayoutNormalization) metadata id index

/-- Raw nominal attributes; no physical layout or fields are computed. -/
def adtDeclarationInWorld (_metadata : RuntimeMetadata) (id : TypeId) :
    TypeArena.WorldM AdtDeclaration.Material := do
  let (declaration,_,_,_,_) ← worldAdt id
  pure declaration

/-- Pinned ty/layout.rs803-850 and rustc_abi/layout/simple.rs132-185.
Multiple variants are projected directly from the supplied source layout.
Single/Empty canonical enums can reconstruct pruned variants from raw ADT
field counts; applying a different variant to an already selected Multiple
layout is rejected. Contextual LayoutIds never stand in for this operation. -/
def variantLayoutInWorld (metadata : RuntimeMetadata) (parent : TyAndLayout TypeId) (index : Nat) :
    TypeArena.WorldM (TyAndLayout TypeId) := do
  let actual ← match ← lift ((← get).lookupType parent.ty) with
    | .material node => pure node
    | .constructed _ => throw "constructed type has no rustc contextual variant layout result"
  let some original := metadata.source.types[parent.ty]?
    | throw "contextual variant layout type is absent from rustc export"
  unless actual.id == parent.ty && actual.layoutId == original.layoutId &&
      (← lift ((← get).materialKey actual)) == (← lift ((← get).materialKey original)) do
    throw "contextual variant layout type differs from rustc export"
  lift ((metadata.forVariant parent index).mapError toString)

/-- Canonical source Value extraction, never a summarized normalized answer. -/
def arrayCountInWorld (metadata : RuntimeMetadata) (id : TypeId) : TypeArena.WorldM UInt64 := do
  let world ← get
  let (length, identity) ← match ← lift (world.lookupType id) with
    | .material node => match node.shape with
      | .array _ length identity => pure (length,identity)
      | _ => throw "array count source is not an array"
    | .constructed (.array _ length) =>
      let value ← lift (world.lookupConstant length)
      let .Value _ tree := value | throw "array length requires source constant evaluation"
      let some (Miri.MIR.ValTreeNode.Leaf bits _) := tree.nodes[tree.root]?
        | throw "array length source value is not a scalar"
      pure (length,⟨bits,true⟩)
    | _ => throw "array count constructor is not an array"
  worldArrayCount metadata.target length identity

end RuntimeMetadata
end Miri.Input
