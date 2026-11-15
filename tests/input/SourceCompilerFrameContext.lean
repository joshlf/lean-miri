import Miri.Frontend.FoundationEntrySeed
import Miri.Input.SourceCompilerBodies
import Miri.Input.CompilerFrameContext
open Lean Miri Miri.Input Miri.Interpreter Miri.Frontend.Foundation
private def checked (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def rejects (value : Except String α) : IO Unit :=
  match value with | .error _ => pure () | .ok _ => throw (IO.userError "invalid frame identity accepted")

def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected genuine custom source")
  let document ← checked (decode (← checked (Json.parse (← IO.FS.readFile path))))
  let initial ← checked (compilerEntrySeed document)
  let some node := initial.canonical.instances.find? (·.defPath == some "main")
    | throw (IO.userError "main identity absent")
  let (world,loaded) ← checked (SourceCompilerBodies.demandLoadedBody initial node.id)
  let some returnType := loaded.body.locals[0]? | throw (IO.userError "return local absent")
  let runtime ← checked (RuntimeMetadata.ofDocument world.canonical |>.mapError toString)
  let layout ← checked (runtime.lookup returnType |>.mapError toString)
  let identity := (LocalsIdentitySupply.allocate ⟨0⟩).2
  let destination := RuntimeStackPlace.frameLocal 0 0 none layout identity
  let extra : MachineHooks.FrameExtra := ⟨none,none,0,none⟩
  let frame := Frame.create loaded node.id extra (.stop true) destination
    ⟨world.canonical.queries.session.rootSpan⟩ identity
  let actual ← checked (CompilerFrameContext.worldBodyOfFrame world frame)
  unless actual.mir == loaded.body do throw (IO.userError "current body content changed")
  unless (← checked (CompilerFrameContext.localType world frame 0)) == returnType do
    throw (IO.userError "current local type changed")
  rejects (CompilerFrameContext.worldBodyOfFrame initial frame)
  rejects (CompilerFrameContext.worldBodyOfFrame world
    {frame with bodyIdentity := .ofCanonicalIndex world.canonical.bodies.size})
  rejects (CompilerFrameContext.worldBodyOfFrame world
    {frame with functionInstance := world.canonical.instances.size})
  rejects (CompilerFrameContext.worldBodyOfFrame world
    {frame with body := {frame.body with argumentCount := frame.body.argumentCount+1}})
  IO.println "live frame context: actual demanded body/local type; stale World/wrong identity/instance/MIR reject"
