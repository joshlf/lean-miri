import Miri.Frontend.FoundationCallGraph

/-! Source-derived acyclic scalar call-graph assembly. Every retained instruction
is lowered through the fixed MIR/BodyCore boundary; empty unrelated query domains
are used only after the same-scalar, no-constant/no-projection effect checks.
Source Span identities remain separate across bodies by explicit relocation. -/
namespace Miri.Frontend.Foundation
open Lean

def scalarCallGraphProgram (document : Document) (definition : Nat) :
    Except String Input.LoweredProgram := do
  let graph ← scalarCallGraph document definition
  unless !graph.sites.isEmpty do throw "scalar graph runner requires a direct call"
  let rootNode := graph.root
  let mut pool := graph.pool
  let physical ← pool.registry.physical.withPrimitiveFacts
  let (physical, primitives) ← physicalPrimitiveCatalog physical
  pool := { pool with registry := { pool.registry with physical } }
  let frozen ← pool.finishFunctionTypes
  let mut globalFiles : Array String := #[]
  let mut globalSpans : Array Input.SourceSpanData := #[]
  let mut bodies : Array Input.Body := #[]
  let mut runtimes : Array Input.Catalog.RuntimeInstance := #[]
  for item in graph.items do
    let prepared := item.prepared
    let node := item.node
    unless node.bodyId == some bodies.size do throw "graph body reservation/order mismatch"
    runtimes := runtimes.push (← runtimeInstanceOfItem document prepared.item node)
    let sourcePool ← buildSpanRegistry prepared.item.source
    let blocks ← prepared.item.source.getObjValAs? (Array Json) "blocks"
    let mut evidence := Array.replicate blocks.size none
    for site in graph.sites do
      if site.caller != node.id then continue
      if h : site.block < evidence.size then
        evidence := evidence.set site.block (some (← DirectCallPool.evidence frozen site.demand)) h
      else throw "graph call evidence block absent"
    let some row := document.definitions[prepared.item.definition]? | throw "body definition absent"
    let defPath ← row.getObjValAs? String "path"
    let some sourceIndex := document.bodies.findIdx? (· == prepared.item.source) | throw "source body index absent"
    let body ← lowerPreparedBodyCore prepared {
      types := pool.registry.physical.registry.entries.mapIdx fun id entry => ⟨entry.type, id⟩
      physicalTypeIds := frozen.types.map (·.id)
      spans := sourcePool.spans
      compilerSpans := sourcePool.compilerSpans
      files := sourcePool.files
      definitionId := prepared.item.definition
      instanceNode := node
      defPath
      sourcePath := s!"$.bodies[{sourceIndex}]"
      backtraceSpans := sourcePool.backtraces
      requiredConsts := #[] }
      (fun _ => .error "call program scalar const unsupported")
      (fun block terminal spans => do
        let some site := graph.sites.find? (fun site => site.caller == node.id && site.block == block)
          | throw "graph call demand site absent"
        lowerScalarDirectCall prepared frozen site.demand terminal spans) evidence
    if !(graph.sites.any (·.caller == node.id)) then
      let some returnType := body.mir.locals[0]? | throw "scalar identity return local absent"
      checkScalarIdentity body returnType
    let mut fileIds := #[]
    for file in sourcePool.files do
      let id := (globalFiles.findIdx? (· == file)).getD globalFiles.size
      if id == globalFiles.size then globalFiles := globalFiles.push file
      fileIds := fileIds.push id
    let offset := globalSpans.size
    for span in sourcePool.spans do
      let some file := fileIds[span.file]? | throw "span file relocation absent"
      globalSpans := globalSpans.push { span with file }
    let relocated ← relocateBodySource body offset fileIds
    bodies := bodies.push { relocated with promotedBodies := #[] }
  let rootSpanSource ← sessionRootSpan document.source
  let rootFile := (globalFiles.findIdx? (· == rootSpanSource.file)).getD globalFiles.size
  if rootFile == globalFiles.size then globalFiles := globalFiles.push rootSpanSource.file
  let rootSpan := globalSpans.size
  globalSpans := globalSpans.push {
    isDummy := rootSpanSource.isDummy
    lo := rootSpanSource.lo
    hi := rootSpanSource.hi
    start := ⟨rootSpanSource.startLine, rootSpanSource.startColumn⟩
    «end» := ⟨rootSpanSource.endLine, rootSpanSource.endColumn⟩
    context := rootSpanSource.context
    file := rootFile }
  let session ← sessionOfDocument document rootSpan
  let foreign ← foreignSymbols document.source
  let selectionSource ← document.source.getObjVal? "entry_selection"
  let _ ← selectionSource.getObj?
  let _ ← selectionSource.getObjVal? "compiler_entry"
  let _ ← selectionSource.getObjVal? "start_lang_item"
  let selection ← entrySelection document.source
  unless selection.compilerEntry.isNone do throw "direct-call library domain excludes process entry"
  let frames ← frameMetadataOfSource document
  let some strType := frozen.types.findIdx? (·.shapeKind == .str) | throw "call program str primitive absent"
  let (_, globalBytes) ← globalBytesWithoutCandidates pool.registry.physical #[]
  unless globalBytes.strType == strType do throw "call byte-interner primitive identity mismatch"
  let queries : Input.Catalog.Queries := {
    session := session
    runtime := {
      startup := none
      types := #[]
      virtualQueries := #[]
      instances := runtimes
      foreignSymbols := foreign }
    frameMetadata := frames
    instanceAbis := pool.instanceAbis
    functionFacts := ⟨frozen.facts, #[], #[]⟩
    casts := #[]
    typeNames := #[]
    panic := #[]
    nativeSignatures := #[]
    retag := #[]
    covariance := #[]
    globalBytes
    callerLocations := #[]
    main := ⟨selection.startLangItem, none, none, #[], none⟩
    primitives := primitives
    vtables := #[]
    namedTypes := none
    shimAbis := none
    namedShimAbis := none
    libcTypeLayouts := none
    windowsTypeLayouts := none
    namedConstants := none
    namedStatics := none }
  let (producer, producerSettings) ← producerOfDocument document
  let some rootDefinition := document.definitions[definition]? | throw "root definition absent"
  let rootPath ← rootDefinition.getObjValAs? String "path"
  let input : Input.ImportDocument := {
    producer
    producerSettings
    runtimeTargetDataLayout := some (← evidenceOfTarget document.target)
    compilerAbiLayoutSchema := some "physical_ty_and_layout_v1"
    definitions := pool.registry.definitions
    typeConstants := pool.registry.physical.typeConstants
    layouts := frozen.layouts
    files := globalFiles
    spans := globalSpans
    types := frozen.types
    allocations := #[]
    instances := pool.registry.instances
    selectedScope := none
    compilerAllocIdWorld := none
    functionAbis := pool.abis
    bodyRoots := #[⟨0, rootNode.id, definition, rootPath, false, false, #[]⟩]
    bodies
    queries }
  Input.lowerProgram input

end Miri.Frontend.Foundation
