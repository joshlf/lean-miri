import Miri.Frontend.FoundationStrLiteralExecute
open Lean Miri Miri.Frontend.Foundation
private def checked (value : Except String α) : IO α :=
  match value with | .ok result => pure result | .error e => throw (IO.userError e)

def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected fresh Unicode str source")
  let document ← checked (Json.parse (← IO.FS.readFile path) >>= decode)
  let some source := document.bodies[0]? | throw (IO.userError "str body absent")
  let definition ← checked (source.getObjValAs? Nat "definition")
  let program ← checked (strLiteralProgram document definition)
  let prepared ← checked (Input.CompilerProviders.prepare program)
  IO.println (← checked (runStrLiteral prepared "Lean🦀".toUTF8.data))
  -- A character-count length must not replace actual runtime UTF-8 metadata.
  match runStrLiteral prepared (Array.replicate 5 (0 : UInt8)) with
  | .error "fixed str metadata length differs from expected source bytes" => pure ()
  | .error e => throw (IO.userError s!"unexpected metadata mismatch: {e}")
  | .ok _ => throw (IO.userError "str metadata length inferred from expected text")
  let blocks ← checked (source.getObjValAs? (Array Json) "blocks")
  let some block := blocks[0]? | throw (IO.userError "str block absent")
  let statements ← checked (block.getObjValAs? (Array Json) "statements")
  let some statement := statements[0]? | throw (IO.userError "str assignment absent")
  let use ← checked (statement.getObjVal? "value")
  let operand ← checked (use.getObjVal? "operand")
  let slice ← checked (operand.getObjVal? "value")
  let changed := statement.setObjVal! "value" (use.setObjVal! "operand"
    (operand.setObjVal! "value" (slice.setObjVal! "metadata" (toJson (9 : Nat)))))
  let altered ← if h : 0 < statements.size then
    pure (block.setObjVal! "statements" (toJson (statements.set 0 changed h)))
    else throw (IO.userError "str assignment index absent")
  let altered ← if h : 0 < blocks.size then
    pure (source.setObjVal! "blocks" (toJson (blocks.set 0 altered h)))
    else throw (IO.userError "str block index absent")
  let alteredDocument ← if h : 0 < document.bodies.size then
    pure {document with bodies := document.bodies.set 0 altered h}
    else throw (IO.userError "str source body index absent")
  let alteredProgram ← checked (strLiteralProgram alteredDocument definition)
  let alteredPrepared ← checked (Input.CompilerProviders.prepare alteredProgram)
  match runStrLiteral alteredPrepared "Lean🦀".toUTF8.data with
  | .error e =>
    unless e == "source prefix failed: Miri.Interpreter.StepError.undefinedBehavior\n  \"validation: encountered a dangling reference (going beyond the bounds of its allocation)\"" do
      throw (IO.userError s!"unexpected altered metadata outcome: {e}")
    IO.println "altered str metadata rejected by fixed reference-bounds validation"
  | .ok _ => throw (IO.userError "out-of-bounds str metadata accepted")
  let missing := {document with source := document.source.setObjVal! "source_allocations" (toJson (#[] : Array Json))}
  match strLiteralProgram missing definition with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "str without allocation image accepted")
  IO.println "str runtime metadata retained; character-count length and missing image reject"
