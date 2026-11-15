import Miri.Input.SourceCompilerInstances
import Miri.Input.SourceCompilerBodies
import Miri.Frontend.FoundationSourceMaterial
import Miri.Frontend.FoundationCallGraphProgram

set_option maxHeartbeats 2000000
open Lean Miri Miri.Input Miri.Frontend.Foundation
private def checked (r : Except String α) : IO α :=
  match r with | .ok a => pure a | .error e => throw (IO.userError e)
private def require (b : Bool) (e : String) : IO Unit := unless b do throw (IO.userError e)
private def result (r : EStateM.Result Interpreter.StepError SourceCompilerWorld.World α) : IO (α × SourceCompilerWorld.World) :=
  match r with | .ok a w => pure (a,w) | .error e _ => throw (IO.userError (reprStr e))
private def unsupported (r : EStateM.Result Interpreter.StepError SourceCompilerWorld.World α) : IO Unit :=
  match r with | .error (.unsupported _) _ => pure () | _ => throw (IO.userError "unsupported Item source demand accepted")

def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected genuine generic chain source")
  let document ← checked (Json.parse (← IO.FS.readFile path) >>= decode)
  let some root := document.definitions.findIdx? (fun d =>
    (d.getObjValAs? String "path").toOption == some "chain") | throw (IO.userError "chain source absent")
  let program ← checked (scalarCallGraphProgram document root)
  let material ← checked (typedSourceMaterial document)
  let input := {program.input with sourceMaterial := some material}
  let world ← checked (SourceCompilerWorld.create input)
  let access : SourceCompilerWorld.Access SourceCompilerWorld.World := ⟨some,fun _ next => next⟩
  let some generic := world.canonical.instances.find? (fun n => n.genericArgs.size == 1)
    | throw (IO.userError "source generic Item absent")
  let .Item definition := generic.instanceKind | throw (IO.userError "generic source kind differs")
  let (existing,same) ← result (SourceCompilerInstances.itemInstance access definition generic.genericArgs world)
  require (existing == generic.id && same.canonical.instances.size == world.canonical.instances.size)
    "existing source key did not deduplicate"
  let some u8 := world.canonical.types.find? (fun t => match t.shape with | .uint (.known .u8) => true | _ => false)
    | throw (IO.userError "canonical u8 absent")
  let arguments := #[MIR.GenericArg.Type u8.id]
  let key ← checked (SourceCompilerWorld.keyOf world generic.id)
  require ((SourceCompilerWorld.findItem world ⟨key.definition,arguments⟩).isNone) "control key was pre-enumerated"
  let (callee,grown) ← result (SourceCompilerInstances.itemInstance access definition arguments world)
  require (callee == world.canonical.instances.size) "new source demand did not append canonical handle"
  let (kind,_) ← result (SourceCompilerInstances.instanceKind access callee grown)
  let (actualArgs,_) ← result (SourceCompilerInstances.instanceArgs access callee grown)
  require (kind == .Item definition && actualArgs == arguments) "live World kind/arguments differ"
  let (again,repeated) ← result (SourceCompilerInstances.itemInstance access definition arguments grown)
  require (again == callee && repeated.canonical.instances.size == grown.canonical.instances.size)
    "repeated source demand allocated another handle"
  match SourceCompilerBodies.loadedBodyOfInstance grown callee with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "identity construction fabricated executable MIR")
  let withoutKinds := { grown.canonical.queries.functionFacts with types := #[] }
  let queries := { grown.canonical.queries with functionFacts := withoutKinds }
  let live := {grown with canonical := {grown.canonical with queries}}
  for type in live.canonical.types do
    match type.shape with
    | .functionDefinition expected expectedArgs _ _ =>
      let (actual,_) ← result (SourceCompilerInstances.functionKind access type.id live)
      match actual with
      | .FnDef definition arguments =>
        require (definition == expected && arguments == expectedArgs) "function kind used a resolved/cached instance instead of original shape"
      | _ => throw (IO.userError "FnDef shape became a function pointer")
    | _ => pure ()
  unsupported (SourceCompilerInstances.functionKind access u8.id live)
  unsupported (SourceCompilerInstances.itemInstance access definition #[] grown)
  unsupported (SourceCompilerInstances.itemInstance access definition #[.Lifetime .Erased] grown)
  let associated := {material with declarations := material.declarations.map fun d =>
    if d.definition == key.definition then {d with kind := .associatedFunction} else d}
  let associatedWorld ← checked (SourceCompilerWorld.create {input with sourceMaterial := some associated})
  unsupported (SourceCompilerInstances.itemInstance access definition generic.genericArgs associatedWorld)
  for role in #[SourceDeclarations.ItemRole.intrinsic,.dropGlue,.foreign,.unavailable] do
    let declarations := material.declarations.map fun d => if d.definition == key.definition then {d with role} else d
    let special := {material with declarations}
    let specialWorld ← checked (SourceCompilerWorld.create {input with sourceMaterial := some special})
    unsupported (SourceCompilerInstances.itemInstance access definition generic.genericArgs specialWorld)
  let missing := {material with declarations := material.declarations.filter (·.definition != key.definition)}
  let missingWorld ← checked (SourceCompilerWorld.create {input with sourceMaterial := some missing})
  unsupported (SourceCompilerInstances.itemInstance access definition generic.genericArgs missingWorld)
  let legacy ← checked (SourceCompilerWorld.create program.input)
  let (old,_) ← result (SourceCompilerInstances.itemInstance access definition generic.genericArgs legacy)
  require (old == generic.id) "legacy exact raw identity was lost"
  unsupported (SourceCompilerInstances.itemInstance access definition arguments legacy)
  IO.println "typed World Items: live kind/args/original FnDef shapes, runtime key growth/dedup, source class/fullslot guards and no-body capability passed"
