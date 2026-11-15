import Miri.Frontend.FoundationExecute

open Lean Miri Miri.Frontend.Foundation

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

/-- Fresh foundation source -> physical/ABI/instance/source/canonical input ->
fixed compiler providers -> actual call frame, assignment and Return. Finite
u8 observation only; no process-exit or Rust safety assertion is made. -/
def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected fresh full foundation identity export")
  let document ← checked (Json.parse (← IO.FS.readFile path) >>= decode)
  let some body := document.bodies[0]? | throw (IO.userError "source body absent")
  let definition ← checked (body.getObjValAs? Nat "definition")
  let arguments := #[ItemArgument.type (.primitive "uint" "u8")]
  let program ← checked (restrictedLibraryProgram document definition arguments)
  let prepared ← checked (Input.CompilerProviders.prepare program)
  IO.println (← checked (FixedIdentityRun.runPrepared prepared))
  match restrictedLibraryProgram document definition #[.type (.primitive "uint" "u16")] with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "unsupported u16 direct frame accepted")
  let broken := { document with source := document.source.setObjVal! "producer" Json.null }
  match restrictedLibraryProgram broken definition arguments with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "missing producer material accepted")
  let components ← checked (buildSourceProgramComponents document definition arguments)
  let badBody := { components.body with mir := { components.body.mir with basicBlocks := #[] } }
  match checkU8IdentityEffects { components with body := badBody } with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "unsupported effect domain accepted")
  let absentAbi := { program with input := { program.input with queries := {
    program.input.queries with instanceAbis := #[] } } }
  let preparedAbsentAbi ← checked (Input.CompilerProviders.prepare absentAbi)
  match FixedIdentityRun.runPrepared preparedAbsentAbi with
  | .error "missing exact full-instance/extra-argument FnAbi query" => pure ()
  | .error error => throw (IO.userError s!"unexpected missing ABI error: {error}")
  | .ok _ => throw (IO.userError "fixed call ignored missing instance ABI")
  let absentCaller := { program with input := { program.input with queries := {
    program.input.queries with runtime := { program.input.queries.runtime with instances := #[] } } } }
  let preparedAbsentCaller ← checked (Input.CompilerProviders.prepare absentCaller)
  match FixedIdentityRun.runPrepared preparedAbsentCaller with
  | .error error =>
    unless (error.splitOn "missing exact full-instance caller-location query").length > 1 do
      throw (IO.userError s!"unexpected missing caller-location error: {error}")
  | .ok _ => throw (IO.userError "fixed frame ignored missing caller-location fact")
  IO.println "foundation fixed identity: source-domain controls and missing demanded ABI/caller facts reject"
