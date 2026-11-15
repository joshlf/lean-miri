import Miri.Frontend.FoundationAllocationOperand
import Miri.Frontend.FoundationProgram

/-! One source allocation-bearing literal assignment and Return, with explicit
unavailable byte-interner evidence. This constructs a direct-frame input; it
does not claim process startup, CTFE or whole-machine safety. -/
namespace Miri.Frontend.Foundation
open Lean

def literalProgram (document : Document) (definition : Nat) : Except String Input.LoweredProgram := do
  let prepared ← prepareItem document definition #[]
  let some resultType := prepared.item.localTypes[0]? | throw "literal return type absent"
  match resultType with
  | .pointer "reference_erased_const" (.array (.primitive "uint" "u8") 4) => pure ()
  | _ => throw "literal direct frame requires shared reference to four u8 values"
  let (physical, abi) ← rustFunctionAbiOfItem document definition #[]
  let registry ← InstanceRegistry.start physical
  let (registry, instanceNode) ← registry.intern definition #[]
  let mut physical := registry.physical
  for type in prepared.item.localTypes do
    let (next, _) ← physical.intern type
    physical := next
  physical ← physical.withPrimitiveFacts
  let (withPrimitives, primitives) ← physicalPrimitiveCatalog physical
  physical := withPrimitives
  let bodySource ← buildSpanRegistry prepared.item.source
  let (source, rootSpan) ← appendSessionRootSpan bodySource document.source
  let session ← sessionOfDocument document rootSpan
  let callback := lowerAllocationConstantOperand physical source
  let required ← (← prepared.item.source.getObjValAs? (Array Json) "required_consts").mapM fun operand =>
    return (← callback operand).1
  let some definitionSource := document.definitions[definition]? | throw "literal definition absent"
  let defPath ← definitionSource.getObjValAs? String "path"
  let body ← lowerPreparedBodyCore prepared {
    types := physical.registry.entries.mapIdx (fun id entry => ⟨entry.type,id⟩)
    physicalTypeIds := physical.types.map (·.id)
    spans := source.spans, compilerSpans := source.compilerSpans, files := source.files
    definitionId := definition, instanceNode, defPath, sourcePath := "$.bodies[0]"
    backtraceSpans := source.backtraces, requiredConsts := required } callback
  unless body.mir.argumentCount == 0 && body.mir.locals.size == 1 && body.mir.basicBlocks.size == 1 do
    throw "literal direct frame requires one return local and one block"
  let some block := body.mir.basicBlocks[0]? | throw "literal block absent"
  unless block.statements.size == 1 && block.terminator.kind == .Return do
    throw "literal direct frame requires constant assignment and Return"
  let some statement := block.statements[0]? | throw "literal assignment absent"
  match statement.kind with
  | .Assign destination (.Use (.Constant constant) _) =>
    unless destination == ⟨0,#[]⟩ do throw "literal destination differs from return place"
    match constant.value with
    | .Val (.Scalar (.Ptr (.Allocation _ 0 _ _))) _ => pure ()
    | _ => throw "literal direct frame requires an source root pointer at offset zero"
  | _ => throw "literal frame has unsupported source effects"
  let allocations ← sourceMemoryGraph document
  let runtime ← buildRuntimeItem document definition #[]
  let selection ← entrySelection document.source
  unless selection.compilerEntry.isNone do throw "literal frame is not process startup"
  let foreign ← foreignSymbols document.source
  let (producer, producerSettings) ← producerOfDocument document
  let strTypes := physical.types.filter (·.shapeKind == .str)
  unless strTypes.size == 1 do throw "literal configuration str type missing"
  let some strType := strTypes[0]? | throw "literal str type absent"
  let queries : Input.Catalog.Queries := {
    session, primitives
    runtime := {startup := none, types := #[], virtualQueries := #[], instances := #[runtime.runtime], foreignSymbols := foreign}
    frameMetadata := runtime.frames, instanceAbis := #[runtime.instanceAbi]
    functionFacts := ⟨#[],#[],#[]⟩, casts := #[], typeNames := #[], panic := #[]
    nativeSignatures := #[], retag := #[], covariance := #[], callerLocations := #[]
    globalBytes := .unavailable strType.id
    main := ⟨selection.startLangItem,none,none,#[],none⟩
    vtables := #[], namedTypes := none, shimAbis := none, namedShimAbis := none
    libcTypeLayouts := none, windowsTypeLayouts := none, namedConstants := none, namedStatics := none }
  Input.lowerProgram {
    producer, producerSettings
    runtimeTargetDataLayout := some (← evidenceOfTarget document.target)
    compilerAbiLayoutSchema := some "physical_ty_and_layout_v1"
    definitions := registry.definitions, typeConstants := physical.typeConstants
    layouts := physical.layouts, files := source.files, spans := source.spans, types := physical.types
    allocations, instances := #[instanceNode], selectedScope := none, compilerAllocIdWorld := none
    functionAbis := #[abi]
    bodyRoots := #[{
      bodyId := 0
      entryInstance := instanceNode.id
      definitionId := definition
      defPath := defPath
      isStatic := false
      threadLocalStatic := false
      promotedBodies := #[] }]
    bodies := #[{body with promotedBodies := #[]}], queries }

end Miri.Frontend.Foundation
