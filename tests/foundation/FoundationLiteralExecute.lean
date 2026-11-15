import Miri.Frontend.FoundationLiteralExecute
open Lean Miri Miri.Frontend.Foundation
private def checked (value : Except String α) : IO α :=
  match value with | .ok result => pure result | .error e => throw (IO.userError e)

def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected fresh literal-byte source")
  let document ← checked (Json.parse (← IO.FS.readFile path) >>= decode)
  let some source := document.bodies[0]? | throw (IO.userError "literal source body absent")
  let definition ← checked (source.getObjValAs? Nat "definition")
  let program ← checked (literalProgram document definition)
  unless !program.input.queries.globalBytes.evidenceAvailable do
    throw (IO.userError "literal interner availability invented")
  let missing := {document with source := document.source.setObjVal! "source_allocations" (toJson (#[] : Array Json))}
  match literalProgram missing definition with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "literal without source allocation image accepted")
  let prepared ← checked (Input.CompilerProviders.prepare program)
  IO.println (← checked (FixedLiteralRun.runPrepared prepared "Miri".toUTF8.data))
