import Miri.Input.Decoder
import Miri.Input.CallResolution
import Miri.Input.CompilerInstanceAbi

/-! Concrete FnPtr conversion shims carry rustc MIR and FnAbi rows. -/
open Miri.Input

private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected fresh FnPtr export")
  let document := (← must (decodeJson (← IO.FS.readFile path))).document
  let metadata ← must ((RuntimeMetadata.ofDocument document).mapError toString)
  let initial ← must ((RuntimeArrayTypes.create metadata).mapError reprStr)
  let program ← must (lowerProgram document)
  let prepared ← must (CallResolution.prepareWithRuntime metadata program)
  let abi ← must (CompilerInstanceAbi.prepare metadata program)
  let mut count := 0
  for (source,id) in document.instances.zipIdx do
    let isShim := match source.instanceKind with
      | .Shim (.FnPtrAsPtr _ _) | .Shim (.FnPtrFromPtr _ _) => true
      | _ => false
    unless isShim do continue
    let some bodyIndex := document.bodies.findIdx? (·.instanceId == id)
      | throw (IO.userError "concrete shim has no rustc body")
    let some seed := document.bodies[bodyIndex]?
      | throw (IO.userError "concrete shim body index disappeared")
    let .material body := seed
      | throw (IO.userError "concrete shim body is not rustc material")
    let (loaded,world) ← must ((CallResolution.loadedBodyOfInstance prepared id).run initial)
    unless loaded.identity.index == bodyIndex && loaded.body == body.mir do
      throw (IO.userError "loaded shim differs from rustc material body")
    let _ ← must ((CompilerInstanceAbi.abiOfInstanceInWorld abi id #[]).run world)
    count := count + 1
  unless count == 8 do
    throw (IO.userError s!"expected 8 concrete FnPtr shims, found {count}")
  IO.println s!"PASS {count} rustc material FnPtr shim MIR and ABI rows"
