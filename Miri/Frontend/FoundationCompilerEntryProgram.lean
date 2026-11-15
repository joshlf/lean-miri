import Miri.Frontend.FoundationCallProgram
import Miri.Frontend.FoundationMainEntries
import Miri.Frontend.FoundationStartup
import Miri.Frontend.FoundationLinkSections
import Miri.Frontend.FoundationAllocations
import Miri.Frontend.FoundationNamedTypes

/-! Restricted compiler-selected entry composition. The accepted custom
lang-start returns its argc argument; it intentionally does not invoke the main
function pointer. Both source bodies and the actual compiler entry/start joins
are retained. This is not ordinary std startup closure or a safety proof. -/
namespace Miri.Frontend.Foundation
open Lean

/-- Pinned helpers.rs constructs a Safe, nonvariadic Rust signature with no
source definition. Its unwind flag is therefore the captured panic strategy;
no item attributes or MIR attribute deduction participate. Physical identities
are resolved from the same closed registry used by the actual start body. -/
def compilerStartHelperAbi (physical : PhysicalTypeRegistry) (prepared : PreparedItem) :
    Except String Input.FunctionAbi := do
  let document := physical.registry.document
  let compilation ← document.source.getObjVal? "compilation"
  let strategy ← compilation.getObjValAs? String "panic_strategy"
  unless strategy == "abort" || strategy == "unwind" do throw "invalid helper panic strategy"
  let binding (ty : ConcreteType) : Except String AbiTypeBinding := do
    let selected := physical.registry.entries.toList.zipIdx.filter fun (entry, _) =>
      sameConcrete 1024 entry.type ty
    let [(entry, id)] := selected | throw "helper signature physical identity missing/duplicated"
    let (node, _) ← physical.lookup id
    let _ ← physical.runtimeLayout id
    return ⟨entry.type, id, node.layoutId⟩
  let some output := prepared.item.localTypes[0]? | throw "helper output absent"
  let mut inputs := #[]
  for i in [:prepared.item.argumentCount] do
    let some ty := prepared.item.localTypes[i+1]? | throw "helper input absent"
    inputs := inputs.push (← binding ty)
  let unwind : RustUnwindFacts := {
    hasDefinition := false, neverUnwind := false, panicUnwinds := strategy == "unwind"
    foreignItem := false, panicInDropUnwinds := false, dropGlue := false }
  let abi ← rustFunctionAbiComponent document.target document.target.architecture unwind inputs (← binding output)
  for argument in abi.arguments.push abi.returnValue do
    unless argument.mode.kind == .direct || argument.mode.kind == .ignore do
      throw "compiler start helper requires direct scalar ABI"
  return abi

private def lowerEntryUnitConstant (physical : PhysicalTypeRegistry) (spans : SpanRegistry)
    (operand : Json) : Except String (MIR.ConstOperand × ConcreteType) := do
  unless (← operand.getObjValAs? String "kind") == "constant" &&
      (← (← operand.getObjVal? "value").getObjValAs? String "kind") == "zero_sized" &&
      (← operand.getObjVal? "user_type") == Json.null do
    throw "compiler entry constant is not unannotated unit"
  let concrete ← instantiate #[] #[] (← typeExpr physical.registry.document
    (← operand.getObjValAs? Nat "type"))
  unless sameConcrete 1024 concrete (.tuple #[]) do throw "compiler entry zero-sized constant is not unit"
  let (next, typeId) ← physical.intern concrete
  unless next.types.size == physical.types.size do throw "compiler entry unit type pool not closed"
  let (_, layout) ← physical.lookup typeId
  unless layout.sizeBytes == some 0 do throw "compiler entry unit layout not zero-sized"
  let key ← operand.getObjVal? "source_span_key"
  let lo ← key.getObjValAs? Nat "lo"
  let hi ← key.getObjValAs? Nat "hi"
  let context ← key.getObjValAs? String "ctxt"
  let parent ← key.getObjValAs? (Option Nat) "parent_local_definition"
  let candidates := spans.compilerSpans.filter fun span =>
    span.lo == lo && span.hi == hi && span.context == context && span.parentLocalDefinition == parent
  unless candidates.size == 1 do throw "compiler entry unit const source span missing/ambiguous"
  let some source := candidates[0]? | throw "compiler entry unit source span absent"
  return (⟨⟨source.identity⟩, none, .Val .ZeroSized typeId⟩, concrete)

private def checkEntryEffects (main start : Input.BodyCore) (primitives : Input.Catalog.Primitives)
    (mainPointer : Nat) : Except String Unit := do
  unless main.mir.argumentCount == 0 && main.mir.locals == #[primitives.unit] &&
      main.mir.basicBlocks.size == 1 && main.requiredConsts.isEmpty do
    throw "compiler entry requires empty unit main"
  let some mainBlock := main.mir.basicBlocks[0]? | throw "compiler main block absent"
  unless mainBlock.statements.size == 1 && mainBlock.terminator.kind == .Return do
    throw "compiler main requires unit assignment and Return"
  let some unitAssignment := mainBlock.statements[0]? | throw "compiler main unit assignment absent"
  match unitAssignment.kind with
  | .Assign destination (.Use (.Constant value) _) =>
    unless destination == ⟨0, #[]⟩ && value.value == .Val .ZeroSized primitives.unit do
      throw "compiler main unit assignment differs"
  | _ => throw "compiler main effects unsupported"
  unless start.mir.argumentCount == 4 && start.mir.locals == #[primitives.isize,
      mainPointer, primitives.isize, primitives.immU8PointerPointer, primitives.u8] &&
      start.mir.basicBlocks.size == 1 && start.requiredConsts.isEmpty do
    throw "custom start signature/locals unsupported"
  let some startBlock := start.mir.basicBlocks[0]? | throw "custom start block absent"
  unless startBlock.statements.size == 1 && startBlock.terminator.kind == .Return do
    throw "custom start requires argc assignment and Return"
  let some assignment := startBlock.statements[0]? | throw "custom start assignment absent"
  match assignment.kind with
  | .Assign destination (.Use (.Copy argument) _)
  | .Assign destination (.Use (.Move argument) _) =>
    unless destination == ⟨0, #[]⟩ && argument == ⟨2, #[]⟩ do
      throw "custom start must return its exact argc local"
  | _ => throw "custom start effects unsupported"

/-- Build a shared physical/ABI/instance pool and source-backed Main/startup
catalog for the exact checked custom-start domain. Main's FnPtr allocation is
left to the fixed interpreter, not fabricated as a compiler global. Body-local
source namespaces append independently; no cross-body rustc span alias theorem
is claimed. Any retained source memory graph or selected static rejects. -/
def restrictedCompilerEntryDocument (document : Document) : Except String Input.ImportDocument := do
  let sourceGraph ← sourceMemoryGraph document
  unless sourceGraph.isEmpty do throw "compiler entry source memory graph unsupported"
  let initial ← DirectCallPool.start (PhysicalTypeRegistry.start document)
  let (initial, pending) ← prepareMainEntries initial
  let some entry := pending.entries[0]? | throw "compiler entry selection absent"
  unless pending.entries.size == 1 && initial.registry.instances.size == 2 do
    throw "compiler entry requires exactly main and ordinary custom start"
  let some startInstance := entry.startInstance | throw "compiler entry start instance absent"
  let some startDefinition := pending.selection.startLangItem | throw "compiler entry start lang item absent"
  let some mainNode := initial.registry.instances[entry.mainInstance]? | throw "compiler main instance absent"
  let some startNode := initial.registry.instances[startInstance]? | throw "compiler start instance absent"
  let some resultType := initial.registry.physical.registry.entries[entry.returnType]?
    | throw "compiler main return type absent"
  unless sameConcrete 1024 resultType.type (.tuple #[]) do throw "compiler main must return unit"
  let main ← prepareItem document entry.definition #[]
  let start ← prepareItem document startDefinition #[.type resultType.type]
  let mut physical := initial.registry.physical
  for prepared in #[main, start] do
    unless (← prepared.item.source.getObjValAs? (Array Json) "required_consts").isEmpty do
      throw "compiler entry required constants unsupported"
    for ty in prepared.item.localTypes do
      primitiveFactsDomain ty
      let (next, _) ← physical.intern ty
      physical := next
  let (withPrimitives, primitives) ← physicalPrimitiveCatalog physical
  physical := withPrimitives
  let (withNamed, namedTypes) ← startupNamedTypes physical
  physical := withNamed
  let knownFacts := physical.registry.entries.toList.zipIdx.filterMap fun (item, index) =>
    if (primitiveFactsDomain item.type).isOk then some index else none
  physical ← physical.withPrimitiveFactsFor knownFacts.toArray
  let pool := { initial with registry := { initial.registry with physical } }
  let helperAbi ← compilerStartHelperAbi physical start
  let (pool, helperAbiId) := match pool.abis.findIdx? (· == helperAbi) with
    | some id => (pool, id)
    | none => ({ pool with abis := pool.abis.push helperAbi }, pool.abis.size)
  let helper : Input.Catalog.HelperSignature := {
    signature := ⟨helperAbi.arguments.map (·.typeId), helperAbi.returnValue.typeId, .Safe, .Rust, false⟩
    splatted := false, abiId := helperAbiId }
  let frozen ← pool.finishFunctionTypes
  let mut files : Array String := #[]
  let mut spans : Array Input.SourceSpanData := #[]
  let mut bodies : Array Input.Body := #[]
  for (prepared, node) in #[(main, mainNode), (start, startNode)] do
    let source ← buildSpanRegistry prepared.item.source
    let some definition := document.definitions[prepared.item.definition]? | throw "compiler body definition absent"
    let path ← definition.getObjValAs? String "path"
    let some sourceIndex := document.bodies.findIdx? (· == prepared.item.source) | throw "compiler body source index absent"
    let body ← lowerPreparedBodyCore prepared {
      types := physical.registry.entries.mapIdx fun id item => ⟨item.type, id⟩
      physicalTypeIds := frozen.types.map (·.id)
      spans := source.spans, compilerSpans := source.compilerSpans, files := source.files
      definitionId := prepared.item.definition, instanceNode := node
      defPath := path, sourcePath := s!"$.bodies[{sourceIndex}]"
      backtraceSpans := source.backtraces, requiredConsts := #[] }
      (lowerEntryUnitConstant physical source)
    let mut fileIds := #[]
    for name in source.files do
      let id := (files.findIdx? (· == name)).getD files.size
      if id == files.size then files := files.push name
      fileIds := fileIds.push id
    let offset := spans.size
    for span in source.spans do
      let some file := fileIds[span.file]? | throw "compiler body span file relocation absent"
      spans := spans.push { span with file }
    let shifted ← relocateBodySource body offset fileIds
    unless node.bodyId == some bodies.size do throw "compiler body/instance pool order mismatch"
    bodies := bodies.push { shifted with promotedBodies := #[] }
  let some mainBody := bodies[0]? | throw "compiler main body absent"
  let some startBody := bodies[1]? | throw "compiler start body absent"
  checkEntryEffects mainBody.toBodyCore startBody.toBodyCore primitives entry.functionPointerType
  let root ← sessionRootSpan document.source
  let rootFile := (files.findIdx? (· == root.file)).getD files.size
  if rootFile == files.size then files := files.push root.file
  let rootSpan := spans.size
  spans := spans.push {
    isDummy := root.isDummy, lo := root.lo, hi := root.hi
    start := ⟨root.startLine, root.startColumn⟩
    «end» := ⟨root.endLine, root.endColumn⟩, context := root.context, file := rootFile }
  let mainRuntime ← runtimeInstanceOfItem document main.item mainNode
  let startRuntime ← runtimeInstanceOfItem document start.item startNode
  let (_, globalBytes) ← globalBytesWithoutCandidates physical sourceGraph
  let mainCatalog ← finishMainEntries pending frozen
  let queries : Input.Catalog.Queries := {
    session := ← sessionOfDocument document rootSpan
    runtime := {
      startup := some (← startupOfDocument document)
      types := #[], virtualQueries := #[]
      instances := #[mainRuntime, startRuntime]
      foreignSymbols := ← foreignSymbols document.source }
    frameMetadata := ← frameMetadataOfSource document
    instanceAbis := pool.instanceAbis
    functionFacts := ⟨frozen.facts, #[], #[helper]⟩
    casts := #[], typeNames := #[], panic := #[], nativeSignatures := #[], retag := #[], covariance := #[]
    globalBytes, callerLocations := #[]
    main := { mainCatalog with linkSections := some (← checkedEmptyLinkSections document.source) }
    primitives
    vtables := #[], namedTypes := some namedTypes, shimAbis := none, namedShimAbis := none
    libcTypeLayouts := none, windowsTypeLayouts := none, namedConstants := none, namedStatics := none }
  let (producer, producerSettings) ← producerOfDocument document
  let input : Input.ImportDocument := {
    producer, producerSettings
    runtimeTargetDataLayout := some (← evidenceOfTarget document.target)
    compilerAbiLayoutSchema := some "physical_ty_and_layout_v1"
    definitions := pool.registry.definitions, typeConstants := physical.typeConstants
    predicates := physical.predicates
    layouts := frozen.layouts, types := frozen.types, files, spans
    allocations := sourceGraph, instances := pool.registry.instances
    selectedScope := none, compilerAllocIdWorld := none
    functionAbis := pool.abis
    bodyRoots := #[⟨0, mainNode.id, entry.definition, mainBody.defPath, false, false, #[]⟩]
    bodies, queries }
  return input

/-- The same source-derived import enters the ordinary fixed input lowerer. -/
def restrictedCompilerEntryProgram (document : Document) : Except String Input.LoweredProgram := do
  Input.lowerProgram (← restrictedCompilerEntryDocument document)

end Miri.Frontend.Foundation
