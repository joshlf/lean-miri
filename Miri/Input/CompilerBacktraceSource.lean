import Miri.Input.CompilerInstance
import Miri.Interpreter.Backtrace
import Miri.Interpreter.BacktraceMachine
import Miri.Input.SourceHygiene

/-! Expansion declarations compute body-dependent collapse without a body/span
answer table. BytePos values outside exported span starts remain unresolved;
no nearby-position approximation is valid. -/
namespace Miri.Input.CompilerBacktraceSource
open Lean Miri.Interpreter
structure Position where
  bytePosition : UInt32
  line : Nat
  column : Nat
  filename : Nat
  deriving DecidableEq
structure Prepared where
  program : LoweredProgram
  positions : Std.HashMap UInt32 Position
  names : Array (CallInstance × String)

def prepare (program : LoweredProgram) : Except String Prepared := do
  let mut positions : Std.HashMap UInt32 Position := {}
  for span in program.input.spans do
    let offset := UInt32.ofNat span.lo
    positions := positions.insert offset ⟨offset,span.start.line,span.start.column,span.runtimeFile⟩
  let ctx := LowerContext.ofDocument program.input
  let records := program.input.queries.runtime.instances
  let mut names := #[]
  let mut namesByDefinition : Std.HashMap Nat (Array Nat) := {}
  for record in records do
    let callee := record.instanceId
    let _ ← CompilerInstance.source ctx.instances callee
    let name := record.display
    let candidates := namesByDefinition.getD callee #[]
    if let some index := candidates.find? fun index =>
        match names[index]? with
        | some (oldCallee,_) => oldCallee == callee
        | none => false then
      let some (_,old) := names[index]? | throw "compiler full-instance bucket index invariant"
      unless old == name do throw "conflicting compiler full-instance rendering"
    else
      let index := names.size
      names := names.push (callee,name)
      namesByDefinition := namesByDefinition.insert callee (candidates.push index)
  return ⟨program,positions,names⟩

def collapsedSpanLo (p : Prepared) (identity : BodyIdentity) (span : MIR.SpanRef) :
    Except String UInt32 := do
  let some body := p.program.bundle.bodies[identity.index]? | throw "canonical backtrace body identity absent"
  let id ← SourceHygiene.collapse p.program.input.spans p.program.input.syntaxContexts
    p.program.input.expansions span.id body.input.spanId
  let some collapsed := p.program.input.spans[id]? | throw "collapsed source span is absent"
  pure (UInt32.ofNat collapsed.lo)

private def lift (result : Except String A) : EStateM StepError S A :=
  match result with
  | .ok value => pure value
  | .error error => throw (.unsupported s!"compiler backtrace source: {error}")

/-- Compiler-source construction with only runtime global/pointer queries.
Hygiene walks use finite declarations; source positions and names retain exact identities. -/
def source (p : Prepared) (hostUsizeMax : Nat)
    (unitPointerLayout : EStateM StepError S LocalLayout)
    (misaligned : Memory.Pointer (Option Memory.Provenance) → ABI.Align → EStateM StepError S (Option Memory.Misalignment))
    (functionPointer : CallInstance → EStateM StepError S (Memory.Pointer (Option Memory.Provenance)))
    (allocation : Memory.Pointer (Option Memory.Provenance) → EStateM StepError S (Memory.AllocId × ABI.Size))
    (globalFunction : Memory.AllocId → EStateM StepError S (Option CallInstance)) :
    BacktraceMachine.Sources S Position := {
  hostUsizeMax,unitPointerLayout,misaligned,functionPointer,allocation,globalFunction
  collapsedSpanLo := fun identity span => lift do
    collapsedSpanLo p identity span
  lookupCharPos := fun offset => lift do
    let some location := p.positions[offset]?
      | throw "unseen BytePos needs actual compiler source-map query"
    return location
  line := Position.line
  column := Position.column
  renderInstance := fun callee => lift do
    let some (_,name) := p.names.find? (·.1 == callee) | throw "exact full-instance rendering absent"
    return name
  remappedFilename := fun location => lift do
    let some filename := p.program.input.files[location.filename]?
      | throw "backtrace filename ID out of bounds"
    return filename }

def hooks (p : Prepared) (base : Backtrace.Hooks P S D MD B I E Position) :
    Backtrace.Hooks P S D MD B I E Position :=
  {base with
    collapsedSpanLo := fun identity span => lift do
      collapsedSpanLo p identity span
    lookupCharPos := fun offset => lift do
      let some location := p.positions[offset]?
        | throw "unseen BytePos needs actual compiler source-map query"
      return location
    line := Position.line
    column := Position.column
    renderInstance := fun callee => lift do
      let some (_,name) := p.names.find? (·.1 == callee) | throw "exact full-instance rendering absent"
      return name
    remappedFilename := fun location => lift do
      let some filename := p.program.input.files[location.filename]?
        | throw "backtrace filename ID out of bounds"
      return filename }
end Miri.Input.CompilerBacktraceSource
