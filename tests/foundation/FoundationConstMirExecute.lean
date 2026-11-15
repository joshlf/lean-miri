import Miri.Frontend.FoundationExecute
open Lean Miri Miri.Frontend.Foundation

private def checked (value : Except String α) : IO α := do
  match value with | .ok value => pure value | .error error => throw (IO.userError error)

def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected fresh expression-const frame JSON")
  let document ← checked (Json.parse (← IO.FS.readFile path) >>= decode)
  let some source := document.bodies[0]? | throw (IO.userError "const frame source absent")
  let definition ← checked (source.getObjValAs? Nat "definition")
  let required ← checked (source.getObjValAs? (Array Json) "required_consts")
  unless !required.isEmpty do throw (IO.userError "expression const required list absent")
  let program ← checked (restrictedLibraryProgram document definition #[])
  let prepared ← checked (Input.CompilerProviders.prepare program)
  IO.println (← checked (FixedIdentityRun.runPrepared prepared 36))
  IO.println "expression const source -> pure CTFE -> required/operand lowering -> actual fixed frame returned 36"
