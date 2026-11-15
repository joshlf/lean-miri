import Miri.Frontend.FoundationCallExecute
import Miri.Input.Decoder

open Lean Miri Miri.Frontend.Foundation

private def checked {α : Type} : Except String α → IO α
  | .ok value => pure value
  | .error e => throw (IO.userError e)

def main (paths : List String) : IO Unit := do
  let path :: rest := paths | throw (IO.userError "expected fresh calls+identity foundation export")
  let document ← checked (Json.parse (← IO.FS.readFile path) >>= decode)
  let some definition := document.definitions.findIdx? (fun row =>
      (row.getObjValAs? String "path").toOption == some "calls") | throw (IO.userError "missing calls definition")
  let program ← checked (restrictedDirectCallProgram document definition)
  unless program.input.bodies.size == 2 && program.input.instances.size == 2 do
    throw (IO.userError "missing two-body instance closure")
  let prepared ← checked (Input.CompilerProviders.prepare program)
  IO.println (← checked (FixedDirectCallRun.runPrepared prepared))

  let calleeId := (program.input.instances.find? (·.id != 0)).map (·.id)
  let some calleeId := calleeId | throw (IO.userError "callee instance absent")
  let absentCalleeAbi := { program.input with queries := { program.input.queries with
    instanceAbis := program.input.queries.instanceAbis.filter (·.instanceId != calleeId) } }
  let lowered ← checked (Input.lowerProgram absentCalleeAbi)
  let missing ← checked (Input.CompilerProviders.prepare lowered)
  match FixedDirectCallRun.runPrepared missing with
  | .error error =>
    unless (error.splitOn "missing exact full-instance/extra-argument FnAbi query").length > 1 do
      throw (IO.userError s!"unexpected missing callee ABI error: {error}")
  | .ok _ => throw (IO.userError "fixed direct call ignored absent callee ABI")
  let absentCalleeRuntime := { program.input with queries := { program.input.queries with
    runtime := { program.input.queries.runtime with
      instances := program.input.queries.runtime.instances.filter (·.instanceId != calleeId) } } }
  let lowered ← checked (Input.lowerProgram absentCalleeRuntime)
  let missing ← checked (Input.CompilerProviders.prepare lowered)
  match FixedDirectCallRun.runPrepared missing with
  | .error error =>
    unless (error.splitOn "missing exact full-instance caller-location query").length > 1 do
      throw (IO.userError s!"unexpected missing callee runtime error: {error}")
  | .ok _ => throw (IO.userError "fixed direct call ignored absent callee runtime facts")
  let absentCallEvidence := { program.input with bodies := program.input.bodies.map fun body =>
    { body with callEvidence := body.callEvidence.map fun _ => none } }
  match Input.lowerProgram absentCallEvidence >>= Input.CompilerProviders.prepare with
  | .error _ => pure ()
  | .ok missing =>
    match FixedDirectCallRun.runPrepared missing with
    | .error error =>
      unless (error.splitOn "missing compiler call resolution").length > 1 do
        throw (IO.userError s!"unexpected missing call evidence error: {error}")
    | .ok _ => throw (IO.userError "fixed direct call ignored absent site resolution")
  IO.println "foundation fixed direct call: missing callee ABI/runtime/site evidence reject"
  match rest with
  | [] => pure ()
  | [ordinaryPath] =>
    let ordinary ← checked (Input.decodeJson (← IO.FS.readFile ordinaryPath))
    let ordinaryProgram ← checked (Input.lowerProgram ordinary.document)
    let ordinaryPrepared ← checked (Input.CompilerProviders.prepare ordinaryProgram)
    IO.println (← checked (FixedDirectCallRun.runPrepared ordinaryPrepared))
    IO.println "foundation and genuine schema12 direct calls both returned 42"
  | _ => throw (IO.userError "expected foundation and optional ordinary export paths")
