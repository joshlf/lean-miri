import Miri.Frontend.FoundationProgram
import Miri.Frontend.FoundationDirectCalls

/-! A deliberately bounded, allocation-operand-free direct-call domain. Two
source bodies share computed physical/instance/ABI pools. Body-local rustc span
identities are relocated explicitly; no compiler allocation identity is invented.
Only a u8 caller with one call to a u8 identity leaf is accepted. -/
namespace Miri.Frontend.Foundation
open Lean

private def place (count : Nat) (j : Json) : Except String MIR.Place := do
  unless (← j.getObjValAs? (Array Json) "projection").isEmpty do throw "call program projection unsupported"
  let localIndex ← j.getObjValAs? Nat "local"
  unless localIndex < count do throw "call program local out of bounds"
  return ⟨localIndex, #[]⟩

private def callSyntax (prepared : PreparedItem) (frozen : DirectCallPool.FunctionTypes)
    (demand : DirectCallPool.Demand) (j spans : Json) : Except String MIR.TerminatorKind := do
  let function ← j.getObjVal? "function"
  unless (← function.getObjValAs? String "kind") == "constant" &&
      (← function.getObjValAs? Nat "type") == demand.sourceFunctionType do
    throw "call program function source identity mismatch"
  unless (← function.getObjVal? "user_type") == Json.null do throw "call user type annotation unsupported"
  let constantSpan ← spans.getObjVal? "function_operand"
  let key ← function.getObjVal? "source_span_key"
  for name in #["lo", "hi", "ctxt", "parent_local_definition"] do
    unless (← key.getObjVal? name) == (← constantSpan.getObjVal? name) do
      throw "call constant source span identity mismatch"
  let some typeId := frozen.typeIds[demand.functionOrdinal]? | throw "call FnDef type absent"
  let constant : MIR.ConstOperand := ⟨⟨← constantSpan.getObjValAs? Nat "span_id"⟩, none, .Val .ZeroSized typeId⟩
  let argumentSources ← j.getObjValAs? (Array Json) "arguments"
  let argumentSpans ← spans.getObjValAs? (Array Json) "arguments"
  unless argumentSources.size == 1 && argumentSpans.size == 1 do throw "call program requires one argument"
  let mut arguments := #[]
  for (source, span) in argumentSources.zip argumentSpans do
    let p ← place prepared.item.localTypes.size (← source.getObjVal? "place")
    let op ← match ← source.getObjValAs? String "kind" with
      | "copy" => pure (MIR.Operand.Copy p)
      | "move" => pure (MIR.Operand.Move p)
      | _ => throw "call program scalar/local argument required"
    arguments := arguments.push ⟨⟨← span.getObjValAs? Nat "span_id"⟩, op⟩
  let destination ← place prepared.item.localTypes.size (← j.getObjVal? "destination")
  let target ← j.getObjValAs? (Option Nat) "target"
  let some targetBlock := target | throw "call program diverging call unsupported"
  unless targetBlock < (← prepared.item.source.getObjValAs? (Array Json) "blocks").size do
    throw "call return target out of bounds"
  unless (← (← j.getObjVal? "unwind").getObjValAs? String "kind") == "Continue" do
    throw "call program unwind action unsupported"
  unless (← j.getObjValAs? String "call_source") == "normal_call" do throw "call source unsupported"
  return .Call (.Constant constant) arguments destination target .Continue .Normal
    ⟨← (← spans.getObjVal? "function").getObjValAs? Nat "span_id"⟩

private def shiftOperand (offset : Nat) : MIR.Operand → MIR.Operand
  | .Constant c => .Constant { c with span := ⟨c.span.id + offset⟩ }
  | op => op

private def shiftBody (body : Input.BodyCore) (offset : Nat) (files : Array Nat) :
    Except String Input.BodyCore := do
  let mut backtraces := #[]
  for b in body.backtraceSpans do
    let some file := files[b.position.filename]? | throw "body backtrace file relocation absent"
    backtraces := backtraces.push { b with spanId := b.spanId + offset, position := { b.position with filename := file } }
  let blocks := body.mir.basicBlocks.map fun block => {
    block with
    statements := block.statements.map fun s => { s with sourceInfo := { s.sourceInfo with span := ⟨s.sourceInfo.span.id + offset⟩ } }
    terminator := {
      sourceInfo := { block.terminator.sourceInfo with span := ⟨block.terminator.sourceInfo.span.id + offset⟩ }
      kind := match block.terminator.kind with
        | .Call fn args dest target unwind source span => .Call (shiftOperand offset fn)
          (args.map fun arg => { arg with span := ⟨arg.span.id + offset⟩, operand := shiftOperand offset arg.operand })
          dest target unwind source ⟨span.id + offset⟩
        | kind => kind } }
  return { body with
    mir := { body.mir with basicBlocks := blocks }
    spanId := body.spanId + offset
    preambleDefSpanId := body.preambleDefSpanId + offset
    localSources := body.localSources.map fun s => { s with spanId := s.spanId + offset }
    sourceScopes := body.sourceScopes.map fun s => { s with spanId := s.spanId + offset }
    backtraceSpans := backtraces }

/-- Build exactly two source-derived bodies and direct call evidence. Every
nonprimitive runtime operation domain remains absent; effect checks restrict
this constructor before those domains are assembled. No process entry is set. -/
def restrictedDirectCallProgram (document : Document) (definition : Nat) :
    Except String Input.LoweredProgram := do
  let root ← prepareItem document definition #[]
  let mut pool ← DirectCallPool.start (PhysicalTypeRegistry.start document)
  let (next, rootNode, _) ← pool.internItem definition #[]
  pool := next
  let sourceBlocks ← root.item.source.getObjValAs? (Array Json) "blocks"
  let mut demands : Array (Nat × DirectCallPool.Demand) := #[]
  for h : i in [:sourceBlocks.size] do
    let terminal ← sourceBlocks[i].getObjVal? "terminator"
    if (← terminal.getObjValAs? String "kind") == "call" then
      let (next, demand) ← pool.demand #[] (← terminal.getObjVal? "function")
      pool := next
      demands := demands.push (i, demand)
  unless demands.size == 1 && pool.registry.instances.size == 2 do
    throw "call program requires one direct call to a distinct leaf"
  let some (_, demand) := demands[0]? | throw "call program demand absent"
  let .Item calleeDefinition := demand.node.instanceKind | throw "call program item callee absent"
  let calleeTypeArgs ← match demand.node.genericArgs.toList with
    | [.Type id] => do
      let some entry := pool.registry.physical.registry.entries[id]? | throw "call generic type absent"
      pure #[ItemArgument.type entry.type]
    | _ => throw "call program requires single type-generic identity leaf"
  let callee ← prepareItem document calleeDefinition calleeTypeArgs
  for item in #[root.item, callee.item] do
    unless item.argumentCount == 1 && item.localTypes.all (sameConcrete 1024 (.primitive "uint" "u8")) do
      throw "call program requires only u8 locals"
    unless (← item.source.getObjValAs? (Array Json) "required_consts").isEmpty do
      throw "call program required const operands unsupported"
    for ty in item.localTypes do
      let (physical, _) ← pool.registry.physical.intern ty
      pool := { pool with registry := { pool.registry with physical } }
  let physical ← pool.registry.physical.withPrimitiveFacts
  let (physical, primitives) ← physicalPrimitiveCatalog physical
  pool := { pool with registry := { pool.registry with physical } }
  let frozen ← pool.finishFunctionTypes
  let mut globalFiles : Array String := #[]
  let mut globalSpans : Array Input.SourceSpanData := #[]
  let mut bodies : Array Input.Body := #[]
  for (prepared, node) in #[(root, rootNode), (callee, demand.node)] do
    let sourcePool ← buildSpanRegistry prepared.item.source
    let blocks ← prepared.item.source.getObjValAs? (Array Json) "blocks"
    let mut evidence := Array.replicate blocks.size none
    if node.id == rootNode.id then
      for (block, d) in demands do
        if h : block < evidence.size then evidence := evidence.set block (some (← DirectCallPool.evidence frozen d)) h
        else throw "call evidence block absent"
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
        unless node.id == rootNode.id do throw "call leaf may not call"
        let some (_, d) := demands.find? (·.1 == block) | throw "call demand site absent"
        callSyntax prepared frozen d terminal spans) evidence
    if node.id == demand.node.id then
      let components ← buildSourceProgramComponents document calleeDefinition calleeTypeArgs
      checkU8IdentityEffects components
    let mut fileIds := #[]
    for file in sourcePool.files do
      let id := (globalFiles.findIdx? (· == file)).getD globalFiles.size
      if id == globalFiles.size then globalFiles := globalFiles.push file
      fileIds := fileIds.push id
    let offset := globalSpans.size
    for span in sourcePool.spans do
      let some file := fileIds[span.file]? | throw "span file relocation absent"
      globalSpans := globalSpans.push { span with file }
    let relocated ← shiftBody body offset fileIds
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
  let mut queries ← restrictedLibraryQueries document calleeDefinition calleeTypeArgs
  let rootRuntime ← runtimeInstanceOfItem document root.item rootNode
  let calleeRuntime ← runtimeInstanceOfItem document callee.item demand.node
  let some strType := frozen.types.findIdx? (·.shapeKind == .str) | throw "call program str primitive absent"
  queries := { queries with
    globalBytes := { queries.globalBytes with strType }
    session
    primitives
    instanceAbis := pool.instanceAbis
    functionFacts := ⟨frozen.facts, #[], #[]⟩
    runtime := { queries.runtime with instances := #[rootRuntime, calleeRuntime] } }
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
