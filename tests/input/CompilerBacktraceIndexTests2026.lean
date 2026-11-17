import Miri.Input.CompilerBacktraceSource

open Miri Miri.Input Miri.Interpreter
private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def check (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)
private def blocked {α : Type} : EStateM StepError Unit α := throw (.unsupported "unused test leaf")

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected a fresh exported input")
  let decoded ← must (decodeJson (← IO.FS.readFile path))
  let document := decoded.document
  let program ← must (lowerProgram document)
  let prepared ← must (CompilerBacktraceSource.prepare program)
  let some first := document.spans[0]? | throw (IO.userError "fixture has no source spans")
  let root := {first with lo := 1, hi := 1, context := 0}
  let middle := {first with lo := 2, hi := 2, context := 1}
  let inner := {first with lo := 3, hi := 3, context := 2}
  let spans := #[root,middle,inner]
  let contexts : Array SyntaxContext := #[⟨none⟩,⟨some 0⟩,⟨some 1⟩]
  let expansions : Array SourceExpansion := #[⟨0,true⟩,⟨1,false⟩]
  must (SourceHygiene.validate spans contexts expansions)
  check ((← must (SourceHygiene.collapse spans contexts expansions 2 0)) == 0)
    "nested collapsed/noncollapsed source walk differs"
  check ((← must (SourceHygiene.collapse spans contexts expansions 2 1)) == 2)
    "the same source span ignored the body syntax context"
  check ((← must (SourceHygiene.collapse spans contexts expansions 2 2)) == 2)
    "body-context equality did not stop immediately"
  check ((← must (SourceHygiene.collapse spans contexts expansions 0 2)) == 0)
    "root context did not terminate"
  for invalid in #[SourceHygiene.validate spans #[] expansions,
      SourceHygiene.validate spans (contexts.push ⟨none⟩) expansions,
      SourceHygiene.validate spans contexts (expansions.push ⟨spans.size,true⟩),
      SourceHygiene.validate spans contexts #[⟨1,true⟩,⟨1,false⟩],
      SourceHygiene.validate (spans.push {root with lo := 2^32}) contexts expansions,
      SourceHygiene.validate (spans.push {root with start := {root.start with line := root.start.line + 1}}) contexts expansions] do
    check (!invalid.isOk) "malformed hygiene declaration was accepted"
  check (!(SourceHygiene.collapse spans contexts expansions spans.size 0).isOk) "missing source span accepted"
  check (!(SourceHygiene.collapse spans contexts expansions 0 spans.size).isOk) "missing body span accepted"
  let source : BacktraceMachine.Sources Unit CompilerBacktraceSource.Position :=
    CompilerBacktraceSource.source prepared (2^64-1) blocked (fun _ _ => blocked)
      (fun _ => blocked) (fun _ => blocked) (fun _ => blocked)
  let some forged := (List.range (document.spans.size+1)).find? fun value =>
      !(prepared.positions.contains (UInt32.ofNat value)) |
    throw (IO.userError "failed to select an unseen BytePos")
  match (source.lookupCharPos (UInt32.ofNat forged)).run () with
  | .error (.unsupported _) _ => pure ()
  | _ => throw (IO.userError "forged unseen BytePos did not remain Unsupported")
  let runtime := program.input.queries.runtime
  let some row := runtime.instances[0]? | throw (IO.userError "fixture has no instance rendering")
  let changed := {row with display := row.display ++ "-conflict"}
  let queries := {program.input.queries with runtime := {runtime with instances := runtime.instances.push changed}}
  check (!(CompilerBacktraceSource.prepare {program with input := {program.input with queries}}).isOk)
    "conflicting full-instance rendering accepted"
  IO.println "source hygiene: body contexts, collapsed/noncollapsed steps, malformed graphs and unseen BytePos controls passed"
