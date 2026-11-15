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

private def operand (count : Nat) (source : Json) : Except String MIR.Operand := do
  let kind ← source.getObjValAs? String "kind"
  unless kind == "copy" || kind == "move" do
    throw "foundation MIR operand is unsupported"
  let place ← wholeLocal count (← source.getObjVal? "place")
  return if kind == "copy" then .Copy place else .Move place

private def runtimePhase (source : Json) : Except String MIR.MirPhase := do
  unless (← source.getObjValAs? String "kind") == "runtime" do
    throw "foundation MIR phase is unsupported"
  match ← source.getObjValAs? String "phase" with
  | "initial" => return .Runtime .Initial
  | "post_cleanup" => return .Runtime .PostCleanup
  | "optimized" => return .Runtime .Optimized
  | _ => throw "foundation MIR runtime phase is unsupported"

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
          if (← value.getObjValAs? String "kind") != "use" then
            let joined ← lowerJoinedRvalue prepared rvalueJoins constantOperand value
            unless sameConcrete 1024 joined.type destinationType do
              throw "foundation joined rvalue assignment type mismatch"
            projectedPlaces := projectedPlaces ++ joined.places
            pure (MIR.StatementKind.Assign destination joined.value)
          else do
            let sourceOperand ← value.getObjVal? "operand"
            let (op, sourceType) ← if (← sourceOperand.getObjValAs? String "kind") == "constant" then do
              let (constant, type) ← constantOperand sourceOperand
              pure (MIR.Operand.Constant constant, type)
            else do
              let op ← operand item.localTypes.size sourceOperand
              let sourceLocal ← match op with
                | .Copy p | .Move p => pure p.localId
                | _ => throw "foundation MIR operand invariant"
              let some sourceType := item.localTypes[sourceLocal]? | throw "missing source local type"
              pure (op, sourceType)
            unless sameConcrete 1024 sourceType destinationType do
              throw "foundation MIR assignment type mismatch"
            let retag ← value.getObjValAs? Bool "retag"
            pure (MIR.StatementKind.Assign destination (.Use op (if retag then .Yes else .No)))
        | _ => throw "foundation MIR statement is unsupported"
      statements := statements.push ⟨sourceInfo, kind⟩
      sourceLocations := sourceLocations.push source
    let terminalSource ← location.getObjVal? "terminator"
    let terminal ← block.getObjVal? "terminator"
    let kind ← if (← terminal.getObjValAs? String "kind") == "call" then do
        let some spans := callSpans[blockIndex]? | throw "foundation call spans absent"
        callTerminator blockIndex terminal spans
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
