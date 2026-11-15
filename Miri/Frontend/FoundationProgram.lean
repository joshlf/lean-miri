import Miri.Frontend.FoundationBodyCore
import Miri.Frontend.FoundationInstanceRegistry
import Miri.Frontend.FoundationFnAbiRegistry
import Miri.Frontend.FoundationPrimitiveCatalog
import Miri.Frontend.FoundationPrimitiveFacts
import Miri.Frontend.FoundationForeignSymbols
import Miri.Frontend.FoundationEntry
import Miri.Frontend.FoundationProducer
import Miri.Frontend.FoundationRuntimeInstances
import Miri.Frontend.FoundationSession
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
  session : Input.Catalog.Session
  primitives : Input.Catalog.Primitives

/-- Construct all supported local joins afresh from one finite document and one
explicit ordinary Item request. Supported MIR has only whole-local Copy/Move
and Return; required constants, promoted bodies and allocation operands reject
upstream of the resulting allocation-free component bundle. -/
def buildSourceProgramComponents (document : Document) (definition : Nat)
    (arguments : Array ItemArgument) : Except String SourceProgramComponents := do
  let prepared ← prepareItem document definition arguments
  unless (← prepared.item.source.getObjValAs? (Array Json) "required_consts").isEmpty do
    throw "foundation BodyCore required-constant operands are not lowered"
  let (physical, abi) ← rustFunctionAbiOfItem document definition arguments
  let registry ← InstanceRegistry.start physical
  let (registry, instanceNode) ← registry.intern definition arguments
  let mut physical := registry.physical
  for ty in prepared.item.localTypes do
    let (next, _) ← physical.intern ty
    physical := next
  physical ← physical.withPrimitiveFacts
  let (withPrimitives, primitives) ← physicalPrimitiveCatalog physical
  physical := withPrimitives
  let bodySource ← buildSpanRegistry prepared.item.source
  let (source, rootSpan) ← appendSessionRootSpan bodySource document.source
  let session ← sessionOfDocument document rootSpan
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
  return ⟨physical, registry.definitions, instanceNode, abi, source, body, session, primitives⟩

/-- These remaining facts must be supplied from the same source/compiler world.
Session root, structural primitive identities and producer settings are derived
from the finite document. Remaining startup and entry queries are not inferred
from an ordinary function's MIR. This structure has no defaults.
Supplying it is an explicit trust boundary; component assembly does not prove
catalog correctness or query closure. -/
structure ProgramCompilerFacts where
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
  let (producer, producerSettings) ← producerOfDocument document
  let some definitionId := components.body.definitionId
    | throw "foundation program missing body definition"
  let document : Input.ImportDocument := {
    producer
    producerSettings
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
    queries := { facts.queries with session := components.session, primitives := components.primitives } }
  Input.lowerProgram document

/-- Exact effect-domain check for the bounded scalar identity call below. There
are no projections, constants, calls, casts, explicit retags, allocations, drops or
intrinsics in this accepted MIR. Scalar argument/return passing adds no
reference retag demands; Use retag visits only the source-backed u8 leaf. Any broader body is rejected before empty query domains
are constructed. This is a syntax check, not a compiler-correspondence proof. -/
def checkU8IdentityEffects (components : SourceProgramComponents) : Except String Unit := do
  let body := components.body.mir
  unless body.argumentCount == 1 && body.locals == #[components.primitives.u8, components.primitives.u8] &&
      body.basicBlocks.size == 1 do throw "restricted execution requires two-local u8 identity"
  let some block := body.basicBlocks[0]? | throw "restricted identity block absent"
  unless block.statements.size == 1 && block.terminator.kind == .Return do
    throw "restricted identity requires assignment and Return"
  let some statement := block.statements[0]? | throw "restricted identity assignment absent"
  match statement.kind with
  | .Assign destination (.Use (.Copy operand) _)
  | .Assign destination (.Use (.Move operand) _) =>
    unless destination == ⟨0, #[]⟩ && operand == ⟨1, #[]⟩ do
      throw "restricted identity contains projection or different local effects"
  | _ => throw "restricted identity contains unsupported effects"

/-- Catalog construction for one direct scalar identity frame. Foreign metadata
is constructed from captured source/linkage inputs. Optional
catalogs retain absent evidence, so any unexpected demand fails closed. Empty
mandatory operation domains are justified by checkU8IdentityEffects. This API
neither selects process startup nor asserts whole-machine query closure. -/
def restrictedLibraryQueries (document : Document) (definition : Nat)
    (arguments : Array ItemArgument) :
    Except String Input.Catalog.Queries := do
  let components ← buildSourceProgramComponents document definition arguments
  checkU8IdentityEffects components
  let foreign ← foreignSymbols document.source
  let runtime ← buildRuntimeItem document definition arguments
  unless runtime.runtime.instanceId == components.instanceNode.id &&
      runtime.instanceAbi.instanceId == components.instanceNode.id do
    throw "restricted runtime instance join mismatch"
  let selection ← entrySelection document.source
  unless selection.compilerEntry.isNone do
    throw "restricted library runner requires absent compiler process entry"
  let some strType := components.physical.types.findIdx? (·.shapeKind == .str)
    | throw "restricted compiler str type absent"
  return {
    session := components.session
    runtime := {
      startup := none
      types := #[]
      virtualQueries := #[]
      instances := #[runtime.runtime]
      foreignSymbols := foreign }
    frameMetadata := runtime.frames
    instanceAbis := #[runtime.instanceAbi]
    functionFacts := ⟨#[], #[], #[]⟩
    casts := #[]
    typeNames := #[]
    panic := #[]
    nativeSignatures := #[]
    retag := #[]
    covariance := #[]
    globalBytes := ⟨32, strType, #[], #[]⟩
    callerLocations := #[]
    main := ⟨selection.startLangItem, none, none, #[], none⟩
    primitives := components.primitives
    vtables := #[]
    namedTypes := none
    shimAbis := none
    namedShimAbis := none
    libcTypeLayouts := none
    windowsTypeLayouts := none
    namedConstants := none
    namedStatics := none }

/-- Build a genuine fixed-interpreter input for the checked direct-frame domain.
No compiler source allocation identity is requested by this allocation-operand-
free body: allocations are created by the fixed machine while entering the
frame. This does not prepare Rust main/startup or a source allocation graph. -/
def restrictedLibraryProgram (document : Document) (definition : Nat)
    (arguments : Array ItemArgument) : Except String Input.LoweredProgram := do
  let queries ← restrictedLibraryQueries document definition arguments
  assembleSourceProgram document definition arguments {
    queries, compilerAbiLayoutSchema := "physical_ty_and_layout_v1"
    selectedScope := none, compilerAllocIdWorld := none }

end Miri.Frontend.Foundation
