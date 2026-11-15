import Miri.Input.SourceCompilerBodies
import Miri.Input.CallResolution
import Miri.Input.CompilerCallPipeline
import Miri.Frontend.FoundationCallGraphProgram

set_option maxHeartbeats 2000000
open Lean Miri Miri.Input Miri.Frontend.Foundation
private def checked (r : Except String α) : IO α :=
  match r with | .ok a => pure a | .error e => throw (IO.userError e)
private def require (b : Bool) (e : String) : IO Unit := unless b do throw (IO.userError e)
private def reject (r : Except String α) : IO Unit :=
  match r with | .error _ => pure () | .ok _ => throw (IO.userError "invalid/unavailable World body accepted")

def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected genuine source chain fixture")
  let document ← checked (Json.parse (← IO.FS.readFile path) >>= decode)
  let some root := document.definitions.findIdx? (fun d =>
    (d.getObjValAs? String "path").toOption == some "chain") | throw (IO.userError "source chain absent")
  let program ← checked (scalarCallGraphProgram document root)
  let world ← checked (SourceCompilerWorld.create program.input)
  let prepared ← checked (CallResolution.prepare program)
  for node in world.canonical.instances do
    let current ← checked (SourceCompilerBodies.loadedBodyOfInstance world node.id)
    let existing ← checked (CallResolution.loadedBodyOfInstance prepared node.id)
    require (current == existing) "World loader differs from existing fixed compiler loader"
    let lowered ← checked (SourceCompilerBodies.frameBody world node.id current.identity)
    require (lowered.input.instanceId == node.id && lowered.body == current.body)
      "current World frame body differs"
  let some rootNode := world.canonical.instances[0]? | throw (IO.userError "source root instance absent")
  let rootBody ← checked (SourceCompilerBodies.loadedBodyOfInstance world rootNode.id)
  let access : SourceCompilerWorld.Access SourceCompilerWorld.World := ⟨some,fun _ next => next⟩
  match CompilerCallPipeline.loadMir access rootNode.id world with
  | .ok loaded _ => require (loaded == rootBody) "normal compiler pipeline did not use current World body"
  | .error error _ => throw (IO.userError (reprStr error))
  let missing : SourceCompilerWorld.Access Unit := ⟨fun _ => none,fun _ _ => ()⟩
  match CompilerCallPipeline.loadMir missing rootNode.id () with
  | .error (.unsupported _) _ => pure ()
  | _ => throw (IO.userError "normal compiler pipeline accepted missing World or used Prepared fallback")
  let some genericNode := world.canonical.instances.find? (fun n => n.genericArgs.size == 1)
    | throw (IO.userError "genuine generic callee absent")
  let key ← checked (SourceCompilerWorld.keyOf world genericNode.id)
  let some sourceDef := document.definitions.find? (fun d =>
    (d.getObjValAs? Nat "crate_index").toOption == some key.definition.crateIndex &&
    (d.getObjValAs? Nat "index").toOption == some key.definition.index)
    | throw (IO.userError "generic source declaration absent")
  let definition ← checked (sourceDef.getObjValAs? Nat "definition_id")
  let some sourceBody := document.bodies.find? (fun b =>
    (b.getObjValAs? Nat "definition").toOption == some definition) | throw (IO.userError "source body absent")
  let flat ← checked (flattenEnvironment document (← checked (sourceBody.getObjVal? "environment")))
  let parameters ← checked (flat.getObjValAs? (Array Json) "parameters")
  let mut kinds : Array SourceCompilerWorld.ParameterKind := #[]
  for parameter in parameters do
    require ((← checked (parameter.getObjValAs? String "kind")) == "type") "control parameter domain changed"
    kinds := kinds.push .typeParameter
  let declaration : SourceCompilerWorld.ItemDeclaration := {
    definition := key.definition, path := ← checked (sourceDef.getObjValAs? String "path"),
    kind := .function, parameters := kinds }
  let some u8 := world.canonical.types.find? (fun t => match t.shape with | .uint (.known .u8) => true | _ => false)
    | throw (IO.userError "canonical scalar type absent")
  let newKey : SourceCompilerWorld.InstanceKey := ⟨key.definition,#[.Type u8.id]⟩
  require (SourceCompilerWorld.findItem world newKey |>.isNone) "control demand already materialized"
  let (grown,newHandle) ← checked (SourceCompilerWorld.internItem #[declaration] world newKey)
  require (newHandle == world.canonical.instances.size && grown.canonical.instances.size == newHandle+1)
    "World new demand identity differs"
  reject (SourceCompilerBodies.loadedBodyOfInstance grown newHandle)
  match CompilerCallPipeline.loadMir access newHandle grown with
  | .error (.unsupported _) _ => pure ()
  | _ => throw (IO.userError "identity-only source demand acquired a body through normal pipeline")
  let after ← checked (SourceCompilerBodies.loadedBodyOfInstance grown rootNode.id)
  require (after == rootBody) "World growth changed existing body identity/MIR"
  let (same,again) ← checked (SourceCompilerWorld.internItem #[declaration] grown newKey)
  require (again == newHandle && same.canonical.instances.size == grown.canonical.instances.size)
    "same source key allocated another instance"
  let some otherBody := genericNode.bodyId | throw (IO.userError "generic actual body absent")
  require (otherBody != rootBody.identity.index) "control body keys unexpectedly alias"
  reject (SourceCompilerBodies.frameBody grown rootNode.id (.ofCanonicalIndex otherBody))
  reject (SourceCompilerBodies.frameBody grown rootNode.id (.ofCanonicalIndex grown.canonical.bodies.size))
  let some old := grown.canonical.bodies[rootBody.identity.index]? | throw (IO.userError "current root body absent")
  let wrong := { old with instanceId := newHandle }
  let brokenCanonical := { grown.canonical with bodies := grown.canonical.bodies.set! rootBody.identity.index wrong }
  let broken := { grown with canonical := brokenCanonical }
  reject (SourceCompilerBodies.loadedBodyOfInstance broken rootNode.id)
  IO.println "current World body loader: genuine fixed loader equivalence, persistent handle/frame identities, identity-only and malformed ownership rejection passed"
