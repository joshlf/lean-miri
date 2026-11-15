import Miri.Frontend.FoundationRuntimeInstances

/-! Explicit FnDef demands: ordinary items and the declaration-backed unit trait
method are resolved. Other trait, shim, pointer or allocation queries reject. Physical, instance and ABI
pools grow monotonically; FnDef ZST types are appended only at finalization. -/
namespace Miri.Frontend.Foundation
open Lean

structure DirectCallPool where
  registry : InstanceRegistry
  abis : Array Input.FunctionAbi := #[]
  instanceAbis : Array Input.Catalog.InstanceAbi := #[]
  functionInstances : Array Nat := #[]
  functionSourceDefinitions : Array Nat := #[]
  functionSourceArguments : Array (Array ItemArgument) := #[]

namespace DirectCallPool

def start (physical : PhysicalTypeRegistry) : Except String DirectCallPool := do
  return { registry := ← InstanceRegistry.start physical }

/-- Retain all previous physical IDs while computing an ordinary item's ABI. -/
def internItem (pool : DirectCallPool) (definition : Nat) (arguments : Array ItemArgument) :
    Except String (DirectCallPool × Input.InstanceNode × Nat) := do
  let (physical, abi) ← rustFunctionAbiInRegistry pool.registry.physical definition arguments
  let (registry, node) ← ({ pool.registry with physical }).intern definition arguments
  let document := registry.physical.registry.document
  let _ ← runtimeInstanceOfItem document (← instantiateItem document definition arguments) node
  let mut pool := { pool with registry }
  if let some existing := pool.instanceAbis.find? (·.instanceId == node.id) then
    unless pool.abis[existing.abiId]? == some abi do throw "conflicting demanded item ABI"
    return (pool, node, existing.abiId)
  let abiId := (pool.abis.findIdx? (· == abi)).getD pool.abis.size
  if abiId == pool.abis.size then pool := { pool with abis := pool.abis.push abi }
  pool := { pool with instanceAbis := pool.instanceAbis.push ⟨node.id, #[], abiId⟩ }
  return (pool, node, abiId)

private def argumentVectors (arguments : Array ItemArgument) :
    Array (Option ConcreteType) × Array (Option Nat) :=
  (arguments.map fun a => match a with | .type ty => some ty | _ => none,
   arguments.map fun a => match a with | .constant n => some n | _ => none)

structure Demand where
  sourceFunctionType : Nat
  sourceDefinition : Nat
  resolvedDefinition : Nat
  functionOrdinal : Nat
  node : Input.InstanceNode
  abiId : Nat

/-- Resolve a zero-sized FnDef operand using its finite definition/argument
structure, substituting the caller's unified arguments. Regions and unknown
constant expressions fail closed. A template's presence is not trait resolution. -/
def demand (pool : DirectCallPool) (callerArguments : Array ItemArgument) (operand : Json) :
    Except String (DirectCallPool × Demand) := do
  unless (← operand.getObjValAs? String "kind") == "constant" do
    throw "direct call requires constant FnDef operand"
  let value ← operand.getObjVal? "value"
  unless (← value.getObjValAs? String "kind") == "zero_sized" do
    throw "direct call requires zero-sized FnDef constant"
  let typeId ← operand.getObjValAs? Nat "type"
  let document := pool.registry.physical.registry.document
  let some row := document.types[typeId]? | throw "direct call source type absent"
  let shape ← row.getObjVal? "shape"
  unless (← shape.getObjValAs? String "kind") == "function_definition" do
    throw "direct call operand is not FnDef"
  let definition ← shape.getObjValAs? Nat "definition"
  let (types, constants) := argumentVectors callerArguments
  let mut arguments := #[]
  for argument in (← shape.getObjValAs? (Array Json) "arguments") do
    match ← argument.getObjValAs? String "kind" with
    | "type" =>
      let ty ← instantiate types constants (← typeExpr document (← argument.getObjValAs? Nat "type"))
      arguments := arguments.push (.type ty)
    | "const" =>
      let c ← argument.getObjVal? "value"
      let bits ← match ← c.getObjValAs? String "kind" with
        | "param" => do
          let index ← c.getObjValAs? Nat "index"
          let some n := constants[index]?.bind id | throw "direct call unbound const argument"
          pure n
        | "value" => do
          let ty ← instantiate types constants (← typeExpr document (← c.getObjValAs? Nat "type"))
          let .primitive "uint" "usize" := ty | throw "direct call non-usize const argument"
          unless (← c.getObjValAs? Nat "size_bytes") * 8 == document.target.pointerSizeBits do
            throw "direct call const width disagrees with target"
          let text ← c.getObjValAs? String "bits"
          let some n := text.toNat? | throw "direct call malformed const bits"
          pure n
        | _ => throw "direct call unsupported const expression"
      arguments := arguments.push (.constant bits)
    | _ => throw "direct call region or unknown generic argument unsupported"
  let resolved ← resolveSourceItem document definition arguments
  let (pool, node, abiId) ← pool.internItem resolved.definition resolved.arguments
  let mut pool := pool
  -- Retain source FnDef generic arguments separately from selected Item args.
  for arg in arguments do
    if let .type ty := arg then
      let (physical, _) ← pool.registry.physical.intern ty
      pool := {pool with registry := {pool.registry with physical}}
  let sameArguments (left right : Array ItemArgument) : Bool :=
    left.size == right.size && (left.zip right).all fun (a,b) => match a,b with
      | .type a, .type b => sameConcrete 1024 a b
      | .constant a, .constant b => a == b
      | _,_ => false
  let existing := (List.range pool.functionInstances.size).find? fun i =>
    pool.functionInstances[i]? == some node.id && pool.functionSourceDefinitions[i]? == some definition &&
      ((pool.functionSourceArguments[i]?).map (sameArguments arguments)).getD false
  let ordinal := existing.getD pool.functionInstances.size
  pool := if existing.isNone then {pool with
      functionInstances := pool.functionInstances.push node.id
      functionSourceDefinitions := pool.functionSourceDefinitions.push definition
      functionSourceArguments := pool.functionSourceArguments.push arguments} else pool
  return (pool, ⟨typeId, definition, resolved.definition, ordinal, node, abiId⟩)

structure FunctionTypes where
  types : Array Input.TypeNode
  layouts : Array Input.Layout
  facts : Array Input.Catalog.FunctionType
  /-- Index by Demand.functionOrdinal. -/
  typeIds : Array Nat

/-- Pinned rustc_ty_utils/src/layout.rs FnDef branch calls
`LayoutData::unit(cx,true)`; rustc_abi/layout/simple.rs uses i8 alignment,
empty arbitrary fields, Memory{sized:true}, size/seed zero and Single variant0.
This is distinct from empty tuple aggregate alignment on some targets. -/
def fnDefinitionLayout (target : ABI.RuntimeTargetDataLayout) : Except String Input.Layout := do
  let alignment ← target.i8Align.bytes.mapError toString
  return {
    maxReprAlignBytes := none
    reprC := false
    uninhabited := false
    largestNiche := none
    randomizationSeed := 0
    kind := .layout
    sizeBytes := some 0
    abiAlignBytes := some alignment.toNat
    unadjustedAbiAlignBytes := some alignment.toNat
    fieldOffsetsBytes := .explicit #[]
    fields := some ⟨.arbitrary, 0, none, none, #[], #[]⟩
    variantsLayout := some ⟨.single, some 0, none, none, none, #[]⟩
    backendRepresentation := some ⟨.memory, some true, none, none, none, none, none, none, none⟩
    variantsKind := some .single
    backendReprKind := some .memory
    variants := none
    backendRepr := none
  }

/-- Freeze the structural pool, then append function-definition ZST types.
The result is separate from PhysicalTypeRegistry: structural interning after
this point would invalidate these appended type IDs and must not be performed. -/
def finishFunctionTypes (pool : DirectCallPool) : Except String FunctionTypes := do
  let physical := pool.registry.physical
  let document := physical.registry.document
  let target ← runtimeTargetOfTarget document.target
  let mut types := physical.types
  let mut facts := #[]
  let mut typeIds := #[]
  let layoutId := physical.layouts.size
  for ordinal in [:pool.functionInstances.size] do
    let some id := pool.functionInstances[ordinal]? | throw "function source ordinal absent"
    let some sourceDefinition := pool.functionSourceDefinitions[ordinal]? | throw "function source definition absent"
    let some sourceArguments := pool.functionSourceArguments[ordinal]? | throw "function source arguments absent"
    let some node := pool.registry.instances[id]? | throw "demanded function instance absent"
    let .Item definition := node.instanceKind | throw "demanded function is not ordinary item"
    let some mapping := pool.instanceAbis.find? (·.instanceId == id) | throw "demanded function ABI mapping absent"
    let some abi := pool.abis[mapping.abiId]? | throw "demanded function ABI absent"
    let some source := document.bodies.find? (fun b =>
        (b.getObjValAs? Nat "definition").toOption == some definition) | throw "demanded function source absent"
    let signature ← source.getObjVal? "signature"
    let boundVariables ← signatureBoundVariables document signature
    let safety ← match ← signature.getObjValAs? String "safety" with
      | "safe" => pure MIR.Safety.Safe
      | "unsafe" => pure MIR.Safety.Unsafe
      | _ => throw "demanded function safety unsupported"
    let inputs := abi.arguments.map (·.typeId)
    let output := abi.returnValue.typeId
    let sourceGenericArgs ← if sourceDefinition == definition then pure node.genericArgs else do
      let mut args : Array MIR.GenericArg := #[]
      for argument in sourceArguments do
        match argument with
        | .type ty =>
          let some index := physical.registry.entries.findIdx? (fun entry => sameConcrete 1024 entry.type ty)
            | throw "function source type argument not interned"
          args := args.push (.Type index)
        | .constant _ => throw "associated const generic FnDef reconstruction unsupported"
      pure args
    let typeId := types.size
    let sig : Input.FunctionSignature := ⟨inputs, output, safety, .Rust, false⟩
    let instanceDisplay := (← runtimeInstanceOfItem document (← instantiateItem document definition
      (← reconstructArguments physical node.genericArgs)) node).display
    let inputDisplays ← inputs.mapM (signatureTypeDisplay physical)
    let outputDisplay ← signatureTypeDisplay physical output
    let display := (if safety == .Unsafe then "unsafe " else "") ++ "fn(" ++
      String.intercalate ", " inputDisplays.toList ++ ")" ++
      (if outputDisplay == "()" then "" else " -> " ++ outputDisplay) ++ " {" ++ instanceDisplay ++ "}"
    types := types.push {
      id := typeId
      layoutId
      shape := .functionDefinition sourceDefinition sourceGenericArgs sig boundVariables
      display }
    facts := facts.push ⟨typeId, some id, ⟨inputs, output, safety, .Rust, false⟩⟩
    typeIds := typeIds.push typeId
  let unitLayout ← fnDefinitionLayout target
  let layouts := if pool.functionInstances.isEmpty then physical.layouts
    else physical.layouts.push unitLayout
  return ⟨types, layouts, facts, typeIds⟩
where
  signatureTypeDisplay (physical : PhysicalTypeRegistry) (id : Nat) : Except String String := do
    let some entry := physical.registry.entries[id]? | throw "function signature type absent"
    concreteRuntimeDisplay entry.type
  reconstructArguments (physical : PhysicalTypeRegistry) (args : Array MIR.GenericArg) :
      Except String (Array ItemArgument) := args.mapM fun arg => do
    match arg with
    | .Type typeId =>
      let some entry := physical.registry.entries[typeId]? | throw "function generic type absent"
      return .type entry.type
    | .Const constantId =>
      let some (.Value _ tree) := physical.typeConstants[constantId]? | throw "function generic const absent"
      let some (.Leaf bits _) := tree.nodes[tree.root]? | throw "function generic const is not scalar"
      return .constant bits
    | _ => throw "function generic lifetime unsupported"

/-- Relocate the function operand type after finalization. -/
def evidence (types : FunctionTypes) (demand : Demand) : Except String Input.CallResolutionEvidence := do
  let some functionType := types.typeIds[demand.functionOrdinal]? | throw "function demand type absent"
  return ⟨.direct, some demand.node.id, some functionType, none, .normal demand.abiId⟩

end DirectCallPool
end Miri.Frontend.Foundation
