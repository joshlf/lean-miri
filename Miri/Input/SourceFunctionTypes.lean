import Miri.Input.SourceSignatureTypes

/-! Function-item types are declaration identities, not executable instances.
Pinned rustc_ty_utils/layout.rs FnDef uses LayoutData::unit(cx,true);
rustc_abi/layout/simple.rs::unit specifies i8 alignment and seed zero. -/
namespace Miri.Input.SourceFunctionTypes
open SourceTypes

/-- Demand a function-item type from its complete source argument recipe.
No instance, MIR body, ABI result, or allocation identity is created. -/
def internSource (initial : SourceCompilerWorld.World) (reference : TypeRef)
    (bindings : Array (Option Concrete)) (constantBindings : Array (Option Nat)) :
    Except String (SourceCompilerWorld.World × TypeId) := do
  let some source := initial.canonical.sourceMaterial | throw "Unsupported FnDef source unavailable"
  let some physical := source.physical | throw "Unsupported FnDef type expressions unavailable"
  let some abi := source.abi | throw "Unsupported FnDef declarations unavailable"
  let some (.functionDefinition definition arguments) := physical.types[reference]?
    | throw "Unsupported source type is not a function definition"
  let some declaration := physical.definitions[definition]? | throw "Invalid FnDef source definition"
  unless declaration.kind == "fn" || declaration.kind == "assoc_fn" do throw "Invalid FnDef declaration category"
  let [header] := (abi.functions.filter (·.definition == declaration.raw)).toList
    | throw "Unsupported FnDef signature absent/ambiguous"
  let parameters ← SourceDeclarations.fullParameters source.genericLayers declaration.raw
  unless parameters.size == arguments.size do throw "Invalid FnDef complete argument count"
  let mut world := initial
  let mut canonical : Array MIR.GenericArg := #[]
  let mut types := #[]
  let mut constants := #[]
  for (parameter,argument) in parameters.zip arguments do
    match parameter,argument with
    | .typeParameter,.type reference =>
      let type ← instantiate physical bindings constantBindings reference
      let (updated,id) ← SourcePhysical.intern world type
      world := updated
      canonical := canonical.push (.Type id)
      types := types.push (some type); constants := constants.push none
    | .region,.lifetime region =>
      let value ← match region with
        | .static => pure MIR.Region.Static
        | .erased => pure MIR.Region.Erased
        | _ => throw "Unsupported FnDef argument region substitution"
      canonical := canonical.push (.Lifetime value)
      types := types.push none; constants := constants.push none
    | .constParameter,.constant (.value typeRef bits bytes) =>
      let type ← instantiate physical bindings constantBindings typeRef
      match type with
      | .primitive kind _ =>
        unless #["bool","char","int","uint"].contains kind do throw "Unsupported FnDef const scalar kind"
      | _ => throw "Unsupported FnDef const scalar type"
      let (updated,id) ← SourcePhysical.intern world type
      let some node := updated.canonical.types[id]? | throw "Invalid FnDef const scalar type"
      let some layout := updated.canonical.layouts[node.layoutId]? | throw "Invalid FnDef const scalar layout"
      unless layout.sizeBytes == some bytes do throw "Invalid FnDef const scalar width"
      let (updated,value) ← SourceCompilerWorld.internScalarConstant updated id bits bytes
      world := updated
      canonical := canonical.push (.Const value)
      types := types.push none; constants := constants.push (some bits)
    | _,_ => throw "Unsupported FnDef generic argument recipe"
  let signature := header.signature
  let mut inputs := #[]
  for reference in signature.inputs do
    let (updated,id) ← SourceSignatureTypes.intern world types constants signature.boundVariables reference
    world := updated; inputs := inputs.push id
  let (updated,output) ← SourceSignatureTypes.intern world types constants signature.boundVariables signature.output
  world := updated
  let (updated,boundVariables) ← SourceSignatureTypes.boundVariables world signature.boundVariables
  world := updated
  let (updated,definition) ← SourceCompilerWorld.internDefinition world declaration.raw
  world := updated
  let target ← SourcePhysical.target world
  let align := (← target.i8Align.bytes.mapError toString).toNat
  let layout : Layout := {
    maxReprAlignBytes := none,reprC := false,uninhabited := false,largestNiche := none,
    randomizationSeed := 0,variants := none,backendRepr := none,
    kind := .layout,sizeBytes := some 0,abiAlignBytes := some align,
    unadjustedAbiAlignBytes := some align,fieldOffsetsBytes := .explicit #[],
    fields := some ⟨.arbitrary,0,none,none,#[],#[]⟩,
    variantsLayout := some ⟨.single,some 0,none,none,none,#[]⟩,
    backendRepresentation := some ⟨.memory,some true,none,none,none,none,none,none,none⟩,
    variantsKind := some .single,backendReprKind := some .memory }
  SourceCompilerWorld.internType world
    (.functionDefinition definition canonical ⟨inputs,output,signature.safety,signature.abi,signature.cVariadic⟩ boundVariables)
    layout "source function item"
end Miri.Input.SourceFunctionTypes
