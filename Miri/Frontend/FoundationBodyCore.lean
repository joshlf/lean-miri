import Miri.Frontend.FoundationMIR
import Miri.Frontend.FoundationSpanRegistry
import Miri.Input.LowerMIR

/-! Explicit joins at the fixed-interpreter boundary. This does not create
physical type, instance, backtrace or required-constant evidence. Callers supply
those facts from their document; missing facts are errors, never defaults. -/
namespace Miri.Frontend.Foundation
open Lean

structure PhysicalTypeBinding where
  concrete : ConcreteType
  typeId : Input.TypeId

/-- Remaining compiler-owned facts not present in a syntax candidate.
`backtraceSpans` must come from the compiler's body-dependent hygiene collapse;
ordinary source-span starts cannot substitute for these positions. Physical
bindings must come from the same document's type/layout construction. -/
structure BodyBindings where
  types : Array PhysicalTypeBinding
  physicalTypeIds : Array Input.TypeId
  spans : Array Input.SourceSpanData
  compilerSpans : Array SourceSpan
  files : Array String
  definitionId : Input.DefinitionRef
  instanceNode : Input.InstanceNode
  defPath : String
  sourcePath : String
  backtraceSpans : Array Input.BacktraceSpan
  requiredConsts : Array MIR.ConstOperand

private def joinSpan (bindings : BodyBindings) (j : Json) : Except String Nat := do
  let identity ← j.getObjValAs? Nat "span_id"
  let compiler ← sourceSpan j
  let some source := bindings.compilerSpans[identity]?
    | throw "foundation compiler span identity is not interned"
  unless compiler == source do throw "foundation compiler span identity mismatch"
  let start ← j.getObjVal? "start"
  let finish ← j.getObjVal? "end"
  let filename ← j.getObjValAs? String "file"
  let some file := bindings.files.findIdx? (· == filename)
    | throw "foundation body span filename is not interned"
  let expected : Input.SourceSpanData := {
    isDummy := ← j.getObjValAs? Bool "is_dummy"
    lo := ← j.getObjValAs? Nat "lo", hi := ← j.getObjValAs? Nat "hi"
    start := ⟨← start.getObjValAs? Nat "line", ← start.getObjValAs? Nat "column"⟩
    «end» := ⟨← finish.getObjValAs? Nat "line", ← finish.getObjValAs? Nat "column"⟩
    context := ← j.getObjValAs? String "ctxt", file }
  unless expected.lo ≤ expected.hi do throw "foundation body reversed span"
  let some row := bindings.spans[identity]?
    | throw "foundation body source span is not interned"
  unless row == expected do throw "foundation body source span identity mismatch"
  return identity

private def joinInfo (bindings : BodyBindings) (scopeCount : Nat) (j : Json) :
    Except String Input.SourceInfo := do
  let scope ← j.getObjValAs? Nat "scope"
  unless scope < scopeCount do throw "foundation body source scope out of bounds"
  return ⟨← joinSpan bindings (← j.getObjVal? "span"), scope⟩

private def phase (j : Json) : Except String MIR.MirPhase := do
  unless (← j.getObjValAs? String "kind") == "runtime" do
    throw "foundation body injection phase is unsupported"
  match ← j.getObjValAs? String "phase" with
  | "initial" => return .Runtime .Initial
  | "post_cleanup" => return .Runtime .PostCleanup
  | "optimized" => return .Runtime .Optimized
  | _ => throw "foundation body injection phase is unsupported"

/-- Relocate supported whole-local Copy/Move assignments and Return into a
BodyCore. Metadata and instructions are read afresh from the prepared item,
so a caller cannot smuggle an arbitrary mutated candidate into this boundary.
This is a partial join, not a whole-document compiler-evidence validator. -/
def lowerPreparedBodyCore (prepared : PreparedItem) (bindings : BodyBindings)
    (constantOperand : Json → Except String (MIR.ConstOperand × ConcreteType) :=
      fun _ => .error "foundation scalar constant query is unavailable")
    (callTerminator : Nat → Json → Json → Except String MIR.TerminatorKind :=
      fun _ _ _ => .error "foundation call query is unavailable")
    (callEvidence : Array (Option Input.CallResolutionEvidence) := #[]) :
    Except String Input.BodyCore := do
  let candidate ← lowerPreparedMIR prepared constantOperand callTerminator
  let callEvidence := if callEvidence.isEmpty then Array.replicate candidate.body.basicBlocks.size none
    else callEvidence
  unless callEvidence.size == candidate.body.basicBlocks.size do
    throw "foundation call evidence block count mismatch"
  for h : i in [:candidate.body.basicBlocks.size] do
    let isCall := match candidate.body.basicBlocks[i].terminator.kind with
      | .Call .. => true
      | _ => false
    unless isCall == (callEvidence[i]?.bind id).isSome do
      throw "foundation call terminator/evidence mismatch"
  let mut requiredConsts := #[]
  for source in (← prepared.item.source.getObjValAs? (Array Json) "required_consts") do
    let (constant, concrete) ← constantOperand source
    let .Val _ typeId := constant.value
    unless bindings.physicalTypeIds.contains typeId && constant.span.id < bindings.spans.size do
      throw "foundation required constant physical reference is absent"
    let types := bindings.types.filter (fun entry => sameConcrete 1024 entry.concrete concrete)
    unless types.size == 1 && (types[0]?.map (·.typeId)) == some typeId do
      throw "foundation required constant physical type mismatch"
    requiredConsts := requiredConsts.push constant
  unless requiredConsts == bindings.requiredConsts do
    throw "foundation required constant source-order join mismatch"
  for backtrace in bindings.backtraceSpans do
    unless backtrace.spanId < bindings.spans.size &&
        backtrace.position.filename < bindings.files.size do
      throw "foundation body invalid compiler backtrace reference"
  unless bindings.instanceNode.kind == .instanceMir do
    throw "foundation body requires an item MIR instance"
  match bindings.instanceNode.instanceKind with
  | .Item definition =>
    unless definition == bindings.definitionId do
      throw "foundation body item definition mismatch"
  | _ => throw "foundation body shim or trait dispatch is unsupported"
  unless bindings.instanceNode.definitionId == some bindings.definitionId do
    throw "foundation body instance definition mismatch"
  unless bindings.instanceNode.defPath == some bindings.defPath do
    throw "foundation body instance path mismatch"
  let mut localIds := #[]
  for ty in candidate.localTypes do
    let entries := bindings.types.filter (fun entry => sameConcrete 1024 entry.concrete ty)
    unless entries.size == 1 do throw "foundation body missing or duplicate physical type binding"
    let some entry := entries[0]? | throw "foundation body missing physical type"
    unless bindings.physicalTypeIds.contains entry.typeId do
      throw "foundation body physical type is not in document"
    localIds := localIds.push entry.typeId
  let metadata := candidate.sourceMetadata
  let sourceScopes ← metadata.getObjValAs? (Array Json) "scopes"
  let mut scopes := #[]
  for h : i in [:sourceScopes.size] do
    let source := sourceScopes[i]
    let parent ← source.getObjValAs? (Option Nat) "parent"
    if let some p := parent then
      unless p < i do throw "foundation body invalid source parent"
    scopes := scopes.push {
      id := i, parent := parent
      spanId := ← joinSpan bindings (← source.getObjVal? "span"),
      inlined := none, inlinedParent := none : Input.SourceScope }
  let mut localSources := #[]
  for source in (← metadata.getObjValAs? (Array Json) "locals") do
    localSources := localSources.push (← joinInfo bindings scopes.size
      (← source.getObjVal? "source_info"))
  let mut locations := #[]
  for source in candidate.sourceLocations do
    let info ← joinInfo bindings scopes.size source
    unless bindings.backtraceSpans.any (fun b => b.spanId == info.spanId) do
      throw "foundation body missing compiler backtrace position"
    locations := locations.push info
  let mut blocks := #[]
  for block in candidate.body.basicBlocks do
    let mut statements := #[]
    for statement in block.statements do
      match statement.kind with
      | .Assign destination (.Use (.Constant constant) _) =>
        let .Val _ typeId := constant.value
        unless localIds[destination.localId]? == some typeId do
          throw "foundation constant physical type differs from assignment destination"
        unless constant.span.id < bindings.spans.size do
          throw "foundation constant physical span is absent"
      | _ => pure ()
      let some info := locations[statement.sourceInfo.span.id]?
        | throw "foundation body instruction source is missing"
      statements := statements.push { statement with sourceInfo := ⟨⟨info.spanId⟩, info.scope⟩ }
    let some info := locations[block.terminator.sourceInfo.span.id]?
      | throw "foundation body terminator source is missing"
    blocks := blocks.push { block with
      statements := statements
      terminator := { block.terminator with sourceInfo := ⟨⟨info.spanId⟩, info.scope⟩ } }
  let injection ← metadata.getObjVal? "injection_phase"
  let injectionPhase ← if injection == Json.null then pure none else some <$> phase injection
  return {
    mir := { candidate.body with locals := localIds, basicBlocks := blocks }
    definitionId := some bindings.definitionId, instanceId := bindings.instanceNode.id
    defPath := bindings.defPath, sourcePath := bindings.sourcePath
    spanId := ← joinSpan bindings (← metadata.getObjVal? "span")
    preambleDefSpanId := ← joinSpan bindings (← metadata.getObjVal? "definition_span")
    injectionPhase, localSources, sourceScopes := scopes
    backtraceSpans := bindings.backtraceSpans
    callEvidence
    nodeFacts := blocks.map (fun block => Array.replicate (block.statements.size + 1)
      { places := (localIds.toList.zipIdx.map fun (typeId, index) =>
          { place := ⟨index, #[]⟩, typeId, projectionTypes := #[] } : List Input.PlaceFact).toArray })
    requiredConsts }

end Miri.Frontend.Foundation
