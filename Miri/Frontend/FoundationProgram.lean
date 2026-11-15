import Miri.Frontend.FoundationBodyCore
import Miri.Frontend.FoundationInstanceRegistry
import Miri.Frontend.FoundationFnAbiRegistry
import Miri.Frontend.FoundationPrimitiveFacts
import Miri.Frontend.FoundationSpanRegistry

/-! Restricted ordinary-item component assembly for the fixed interpreter.
No compiler query catalog is synthesized here. Completing the ImportDocument
requires explicit remaining compiler facts; this is an assumption boundary,
not validation that those supplied facts came from rustc. -/
namespace Miri.Frontend.Foundation
open Lean

structure SourceProgramComponents where
  physical : PhysicalTypeRegistry
  definitions : Array Input.DefinitionId
  instanceNode : Input.InstanceNode
  abi : Input.FunctionAbi
  source : SpanRegistry
  body : Input.BodyCore

/-- Construct all supported local joins afresh from one finite document and one
explicit ordinary Item request. Supported MIR has only whole-local Copy/Move
and Return; required constants, promoted bodies and allocation operands reject
upstream of the resulting allocation-free component bundle. -/
def buildSourceProgramComponents (document : Document) (definition : Nat)
    (arguments : Array ItemArgument) : Except String SourceProgramComponents := do
  let prepared ← prepareItem document definition arguments
  let (physical, abi) ← rustFunctionAbiOfItem document definition arguments
  let registry ← InstanceRegistry.start physical
  let (registry, instanceNode) ← registry.intern definition arguments
  let mut physical := registry.physical
  for ty in prepared.item.localTypes do
    let (next, _) ← physical.intern ty
    physical := next
  physical ← physical.withPrimitiveFacts
  let source ← buildSpanRegistry prepared.item.source
  let some definitionSource := document.definitions[definition]?
    | throw "foundation program definition absent"
  let defPath ← definitionSource.getObjValAs? String "path"
  let some bodyIndex := document.bodies.findIdx? (· == prepared.item.source)
    | throw "foundation program source body absent"
  let sourcePath := s!"$.bodies[{bodyIndex}]"
  let body ← lowerPreparedBodyCore prepared {
    types := physical.registry.entries.mapIdx (fun id entry => ⟨entry.type, id⟩)
    physicalTypeIds := physical.types.map (·.id)
    spans := source.spans, compilerSpans := source.compilerSpans, files := source.files
    definitionId := definition, instanceNode := instanceNode
    defPath, sourcePath, backtraceSpans := source.backtraces
    requiredConsts := #[] }
  unless instanceNode.bodyId == some 0 && body.instanceId == instanceNode.id do
    throw "foundation program single body identity mismatch"
  return ⟨physical, registry.definitions, instanceNode, abi, source, body⟩

/-- These remaining facts must be supplied from the same source/compiler world.
In particular, root DUMMY_SP, primitive pointer types, startup and entry queries
are not inferred from an ordinary function's MIR. This structure has no defaults.
Supplying it is an explicit trust boundary; component assembly does not prove
catalog correctness or query closure. -/
structure ProgramCompilerFacts where
  producer : Input.Producer
  producerSettings : Input.Catalog.ProducerSettings
  queries : Input.Catalog.Queries
  compilerAbiLayoutSchema : String
  selectedScope : Option Input.SelectedScope
  compilerAllocIdWorld : Option Input.CompilerAllocIdWorld

/-- Relocate constructed components into the existing LoweredProgram API.
The caller-owned catalog is retained exactly; absent facts remain errors in
fixed-interpreter preparation and demand-time lookup. This does not claim that
an arbitrary ordinary function is a runnable process entry. -/
def assembleSourceProgram (document : Document) (definition : Nat)
    (arguments : Array ItemArgument) (facts : ProgramCompilerFacts) :
    Except String Input.LoweredProgram := do
  let components ← buildSourceProgramComponents document definition arguments
  let some definitionId := components.body.definitionId
    | throw "foundation program missing body definition"
  let document : Input.ImportDocument := {
    producer := facts.producer
    producerSettings := facts.producerSettings
    runtimeTargetDataLayout := some (← evidenceOfTarget components.physical.registry.document.target)
    compilerAbiLayoutSchema := some facts.compilerAbiLayoutSchema
    definitions := components.definitions
    typeConstants := components.physical.typeConstants
    layouts := components.physical.layouts
    files := components.source.files, spans := components.source.spans
    types := components.physical.types
    allocations := #[]
    instances := #[components.instanceNode]
    selectedScope := facts.selectedScope
    compilerAllocIdWorld := facts.compilerAllocIdWorld
    functionAbis := #[components.abi]
    bodyRoots := #[{
      bodyId := 0, entryInstance := components.instanceNode.id, definitionId
      defPath := components.body.defPath, isStatic := false
      threadLocalStatic := false, promotedBodies := #[] }]
    bodies := #[{ components.body with promotedBodies := #[] }]
    queries := facts.queries }
  Input.lowerProgram document

end Miri.Frontend.Foundation
