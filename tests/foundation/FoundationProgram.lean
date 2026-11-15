import Miri.Frontend.FoundationProgram

open Lean Miri.Frontend.Foundation

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

/-- Fresh finite-source component assembly. No catalog is invented to turn this
check into a process execution; those remaining facts are explicit API inputs. -/
def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected fresh foundation identity export")
  let document ← checked (Json.parse (← IO.FS.readFile path) >>= decode)
  let some body := document.bodies[0]? | throw (IO.userError "missing source body")
  let definition ← checked (body.getObjValAs? Nat "definition")
  let components ← checked (buildSourceProgramComponents document definition
    #[.type (.primitive "uint" "u8")])
  unless components.instanceNode.id == 0 && components.instanceNode.bodyId == some 0 &&
      components.body.instanceId == 0 && components.body.definitionId == some definition do
    throw (IO.userError "component instance/body join changed")
  unless components.body.mir.locals.size == 2 &&
      components.body.mir.locals[0]? == components.body.mir.locals[1]? do
    throw (IO.userError "identity local physical types changed")
  unless components.abi.arguments.size == 1 && components.body.backtraceSpans.size > 0 do
    throw (IO.userError "ABI/source component lost")
  for typeId in components.body.mir.locals do
    let (node, _) ← checked (components.physical.lookup typeId)
    unless node.compilerFacts.isSome do throw (IO.userError "missing demanded primitive compiler leaves")
  let broken := { document with definitions := #[] }
  match buildSourceProgramComponents broken definition #[.type (.primitive "uint" "u8")] with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "missing source definition accepted")
  IO.println "foundation source program: physical/ABI/instance/body/source joins passed; executable compiler catalogs still required"
