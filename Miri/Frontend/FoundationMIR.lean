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
Its local IDs are local ordinals, not compiler type IDs. -/
structure MIRCandidate where
  body : MIR.Body
  localTypes : Array ConcreteType
  sourceLocations : Array Json
  sourceMetadata : Json

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

/-- Lower every instruction of one straight-line template after substitution.
Span references use candidate-local indices into `sourceLocations`. Type IDs
use candidate-local local ordinals. These are explicitly unresolved identities,
so this value is not `Input.BodyCore` and cannot enter the fixed interpreter.
No successful no-op replaces an unsupported source instruction. -/
def lowerPreparedMIR (prepared : PreparedItem) : Except String MIRCandidate := do
  let item := prepared.item
  validateSourceMetadata item.source
  let metadata ← item.source.getObjVal? "source_metadata"
  let phase ← runtimePhase (← metadata.getObjVal? "phase")
  let blocks ← item.source.getObjValAs? (Array Json) "blocks"
  unless blocks.size == 1 do throw "foundation MIR control flow is unsupported"
  let some block := blocks[0]? | throw "missing foundation MIR entry block"
  unless !(← block.getObjValAs? Bool "cleanup") do
    throw "foundation MIR cleanup is unsupported"
  let locations ← metadata.getObjValAs? (Array Json) "blocks"
  let some location := locations[0]? | throw "missing foundation MIR source block"
  let sources ← location.getObjValAs? (Array Json) "statements"
  let mut statements := #[]
  for (statement, source) in (← block.getObjValAs? (Array Json) "statements").zip sources do
    unless (← statement.getObjValAs? String "kind") == "assign" do
      throw "foundation MIR statement is unsupported"
    let destination ← wholeLocal item.localTypes.size (← statement.getObjVal? "place")
    let value ← statement.getObjVal? "value"
    unless (← value.getObjValAs? String "kind") == "use" do
      throw "foundation MIR rvalue is unsupported"
    let op ← operand item.localTypes.size (← value.getObjVal? "operand")
    let sourceLocal ← match op with
      | .Copy p | .Move p => pure p.localId
      | _ => throw "foundation MIR operand invariant"
    let some sourceType := item.localTypes[sourceLocal]? | throw "missing source local type"
    let some destinationType := item.localTypes[destination.localId]? | throw "missing destination type"
    unless sameConcrete 1024 sourceType destinationType do
      throw "foundation MIR assignment type mismatch"
    let retag ← value.getObjValAs? Bool "retag"
    statements := statements.push {
      sourceInfo := ⟨⟨statements.size⟩, ← source.getObjValAs? Nat "scope"⟩
      kind := .Assign destination (.Use op (if retag then .Yes else .No)) }
  unless (← (← block.getObjVal? "terminator").getObjValAs? String "kind") == "return" do
    throw "foundation MIR terminator is unsupported"
  let terminalSource ← location.getObjVal? "terminator"
  let terminator : MIR.Terminator := {
    sourceInfo := ⟨⟨statements.size⟩, ← terminalSource.getObjValAs? Nat "scope"⟩
    kind := .Return }
  return {
    body := { phase, argumentCount := item.argumentCount, spreadArgument := none
              locals := Array.range item.localTypes.size
              basicBlocks := #[⟨statements, terminator, false⟩] }
    localTypes := item.localTypes
    sourceLocations := sources.push terminalSource
    sourceMetadata := metadata }

end Miri.Frontend.Foundation
