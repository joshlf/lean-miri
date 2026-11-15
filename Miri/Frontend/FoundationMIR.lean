import Miri.Frontend.FoundationRvalueSyntax
import Miri.Frontend.FoundationBridge
import Miri.MIR.Syntax
import Miri.Frontend.FoundationTypeRegistry

/-! Pure syntax lowering into the existing interpreter's MIR datatypes.
This is a candidate, not executable compiler metadata: local type identities
must still be joined to a document-local physical type registry. No layout,
ABI, allocation or query evidence is produced. Source metadata is retained
verbatim and validated; span references index the parallel `sourceLocations`
array, and must be relocated when constructing the interpreter's span table.
Pinned rustc_const_eval/interpret/step.rs evaluates `Use` with its `WithRetag`;
operand.rs distinguishes the Copy and Move constructors. Both are retained. -/
namespace Miri.Frontend.Foundation
open Lean

/-- A syntax candidate awaiting physical type and compiler span interning.
The `body` must not be installed in an executable program before those joins.
Its local type IDs are local ordinals, not compiler type IDs; explicitly
joined type-bearing rvalues must use the same eventual physical pool. -/
structure MIRCandidate where
  body : MIR.Body
  localTypes : Array ConcreteType
  sourceLocations : Array Json
  sourceMetadata : Json
  projectedPlaces : Array SourcePlaceTyping := #[]

private def wholeLocal (count : Nat) (source : Json) : Except String MIR.Place := do
  unless (← source.getObjValAs? (Array Json) "projection").isEmpty do
    throw "foundation MIR projection is unsupported"
  let localId ← source.getObjValAs? Nat "local"
  unless localId < count do throw "foundation MIR local is out of bounds"
  return ⟨localId, #[]⟩

private def runtimePhase (source : Json) : Except String MIR.MirPhase := do
  unless (← source.getObjValAs? String "kind") == "runtime" do
    throw "foundation MIR phase is unsupported"
  match ← source.getObjValAs? String "phase" with
  | "initial" => return .Runtime .Initial
  | "post_cleanup" => return .Runtime .PostCleanup
  | "optimized" => return .Runtime .Optimized
  | _ => throw "foundation MIR runtime phase is unsupported"

private def sourceUnwindReason (source : Json) : Except String MIR.UnwindTerminateReason := do
  match ← source.getObjValAs? String "kind" with
  | "abi" => pure .Abi
  | "in_cleanup" => pure .InCleanup
  | _ => throw "foundation unwind terminate reason unsupported"

/-- Preserve the complete synchronous unwind action; cleanup targets must name
actual cleanup blocks. This performs no drop-glue or exception query. -/
def lowerSourceUnwind (source : Json) (blocks : Array Json) : Except String MIR.UnwindAction := do
  match ← source.getObjValAs? String "kind" with
  | "Continue" => pure .Continue
  | "Unreachable" => pure .Unreachable
  | "Terminate" => return .Terminate (← sourceUnwindReason (← source.getObjVal? "reason"))
  | "Cleanup" =>
    let target ← source.getObjValAs? Nat "target"
    let some block := blocks[target]? | throw "foundation unwind cleanup target absent"
    unless (← block.getObjValAs? Bool "cleanup") do throw "foundation unwind target is not cleanup"
    return .Cleanup target
  | _ => throw "foundation unwind action unsupported"

/-- Synchronous source Drop is retained even for a no-drop type. The fixed
interpreter still needs its genuine drop-glue query. Async drop requires source
expansion and remains Unsupported rather than becoming a goto. -/
def lowerSourceDrop (prepared : PreparedItem) (joins : RvalueSourceJoins) (source : Json) :
    Except String (MIR.TerminatorKind × SourcePlaceTyping) := do
  let _ ← source.getObjVal? "async_drop"
  unless (← source.getObjValAs? (Option Nat) "async_drop").isNone do throw "foundation async drop expansion unsupported"
  let blocks ← prepared.item.source.getObjValAs? (Array Json) "blocks"
  let target ← source.getObjValAs? Nat "target"
  unless target < blocks.size do throw "foundation drop return target out of bounds"
  let place ← lowerSourcePlace prepared.item.localTypes (← source.getObjVal? "place") joins
  let unwind ← lowerSourceUnwind (← source.getObjVal? "unwind") blocks
  let replace ← source.getObjValAs? Bool "replace"
  return (.Drop place.place target unwind replace none,place)

/-- Exact non-call control syntax. A resume is admitted only in a cleanup
block; it does not turn an unwinding frame into a normal return. -/
def lowerSourceControlTerminator (source : Json) (blockCount : Nat) (cleanup : Bool) :
    Except String MIR.TerminatorKind := do
  match ← source.getObjValAs? String "kind" with
  | "return" =>
    unless !cleanup do throw "foundation return in cleanup unsupported"
    pure .Return
  | "goto" =>
    let target ← source.getObjValAs? Nat "target"
    unless target < blockCount do throw "foundation goto target out of bounds"
    pure (.Goto target #[])
  | "unwind_resume" =>
    unless cleanup do throw "foundation unwind resume outside cleanup"
    pure .UnwindResume
  | "unwind_terminate" =>
    let reason ← sourceUnwindReason (← source.getObjVal? "reason")
    if reason == .InCleanup && !cleanup then throw "foundation terminate in cleanup outside cleanup block"
    return .UnwindTerminate reason
  | "unreachable" => pure .Unreachable
  | _ => throw "foundation MIR control terminator is unsupported"

/-- Lower every supported block of one template after substitution.
Span references use candidate-local indices into `sourceLocations`. The locals
array uses local ordinals; type-bearing rvalues use explicit joins. The remaining
unresolved identities mean
this value is not `Input.BodyCore` and cannot enter the fixed interpreter.
No successful no-op replaces an unsupported source instruction. -/
def lowerPreparedMIR (prepared : PreparedItem)
    (constantOperand : Json → Except String (MIR.ConstOperand × ConcreteType) :=
      fun _ => .error "foundation scalar constant query is unavailable")
    (callTerminator : Nat → Json → Json → Except String MIR.TerminatorKind :=
      fun _ _ _ => .error "foundation call query is unavailable")
    (rvalueJoins : RvalueSourceJoins := {}) : Except String MIRCandidate := do
  let item := prepared.item
  validateSourceMetadata item.source
  let metadata ← item.source.getObjVal? "source_metadata"
  let phase ← runtimePhase (← metadata.getObjVal? "phase")
  let blocks ← item.source.getObjValAs? (Array Json) "blocks"
  unless !blocks.isEmpty do throw "missing foundation MIR entry block"
  let locations ← metadata.getObjValAs? (Array Json) "blocks"
  let callSpans ← metadata.getObjValAs? (Array Json) "call_spans"
  unless locations.size == blocks.size && callSpans.size == blocks.size do
    throw "foundation MIR source block count mismatch"
  let mut loweredBlocks := #[]
  let mut sourceLocations := #[]
  let mut projectedPlaces := #[]
  for h : blockIndex in [:blocks.size] do
    let block := blocks[blockIndex]
    let some location := locations[blockIndex]? | throw "foundation MIR source block absent"
    let cleanup ← block.getObjValAs? Bool "cleanup"
    let sources ← location.getObjValAs? (Array Json) "statements"
    let statementsSource ← block.getObjValAs? (Array Json) "statements"
    unless sources.size == statementsSource.size do throw "foundation MIR statement source mismatch"
    let mut statements := #[]
    for (statement, source) in statementsSource.zip sources do
      let sourceInfo : MIR.SourceInfo := ⟨⟨sourceLocations.size⟩, ← source.getObjValAs? Nat "scope"⟩
      let kind ← match ← statement.getObjValAs? String "kind" with
        | "storage_live" => do
          let localId ← statement.getObjValAs? Nat "local"
          unless localId < item.localTypes.size do throw "foundation storage local out of bounds"
          pure (MIR.StatementKind.StorageLive localId)
        | "storage_dead" => do
          let localId ← statement.getObjValAs? Nat "local"
          unless localId < item.localTypes.size do throw "foundation storage local out of bounds"
          pure (MIR.StatementKind.StorageDead localId)
        | "assign" => do
          let destination ← wholeLocal item.localTypes.size (← statement.getObjVal? "place")
          let value ← statement.getObjVal? "value"
          let some destinationType := item.localTypes[destination.localId]? | throw "missing destination type"
          let joined ← lowerJoinedRvalue prepared rvalueJoins constantOperand value
          unless sameConcrete 1024 joined.type destinationType do
            throw "foundation joined rvalue assignment type mismatch"
          projectedPlaces := projectedPlaces ++ joined.places
          pure (MIR.StatementKind.Assign destination joined.value)
        | _ => throw "foundation MIR statement is unsupported"
      statements := statements.push ⟨sourceInfo, kind⟩
      sourceLocations := sourceLocations.push source
    let terminalSource ← location.getObjVal? "terminator"
    let terminal ← block.getObjVal? "terminator"
    let kind ← if (← terminal.getObjValAs? String "kind") == "call" then do
        let some spans := callSpans[blockIndex]? | throw "foundation call spans absent"
        callTerminator blockIndex terminal spans
      else if (← terminal.getObjValAs? String "kind") == "drop" then do
        let (kind,place) ← lowerSourceDrop prepared rvalueJoins terminal
        projectedPlaces := projectedPlaces.push place
        pure kind
      else lowerSourceControlTerminator terminal blocks.size cleanup
    let terminator : MIR.Terminator := {
      sourceInfo := ⟨⟨sourceLocations.size⟩, ← terminalSource.getObjValAs? Nat "scope"⟩
      kind }
    sourceLocations := sourceLocations.push terminalSource
    loweredBlocks := loweredBlocks.push ⟨statements, terminator, cleanup⟩
  return {
    body := { phase, argumentCount := item.argumentCount, spreadArgument := none
              locals := Array.range item.localTypes.size
              basicBlocks := loweredBlocks }
    localTypes := item.localTypes
    sourceLocations
    sourceMetadata := metadata
    projectedPlaces }

end Miri.Frontend.Foundation
