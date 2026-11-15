import Miri.Frontend.FoundationCompilerEntryExecute

open Lean Miri Miri.Frontend.Foundation

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

/-- Fresh finite source to the canonical compiler-selected entry/startup factory
and natural process exit. The custom source start returns argc and does not call
main; this test does not claim ordinary std main execution or Rust safety. -/
def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected fresh two-root compiler-entry foundation export")
  let document ← checked (Json.parse (← IO.FS.readFile path) >>= decode)
  let program ← checked (restrictedCompilerEntryProgram document)
  unless program.bundle.bodies.size == 2 && program.input.queries.main.compilerEntry.isSome &&
      program.input.queries.runtime.startup.isSome do
    throw (IO.userError "compiler entry/startup joins absent")
  let attempt := Input.EvalPreparation.prepare program
  let prepared ← checked attempt.outcome
  IO.println (← checked (CompilerEntryRun.runPrepared prepared attempt.memory))
  let missingSource := { document with source := document.source.setObjVal! "startup_material" Json.null }
  match restrictedCompilerEntryProgram missingSource with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "missing source startup material accepted")
  let selection ← checked (entrySelection document.source)
  let some start := selection.startLangItem | throw (IO.userError "source start selection absent")
  let missingStart := { document with bodies := document.bodies.filter fun body =>
    (body.getObjValAs? Nat "definition").toOption != some start }
  match restrictedCompilerEntryProgram missingStart with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "missing actual start body accepted")
  let some startBody := document.bodies.find? (fun body =>
      (body.getObjValAs? Nat "definition").toOption == some start)
    | throw (IO.userError "source start body absent")
  let blocks ← checked (startBody.getObjValAs? (Array Json) "blocks")
  let some block := blocks[0]? | throw (IO.userError "source start block absent")
  let statements ← checked (block.getObjValAs? (Array Json) "statements")
  let some statement := statements[0]? | throw (IO.userError "source start assignment absent")
  let value ← checked (statement.getObjVal? "value")
  let operand ← checked (value.getObjVal? "operand")
  let place ← checked (operand.getObjVal? "place")
  let badOperand := operand.setObjVal! "place" (place.setObjVal! "local" (toJson (0 : Nat)))
  let badStatement := statement.setObjVal! "value" (value.setObjVal! "operand" badOperand)
  let badBlock := block.setObjVal! "statements" (toJson (statements.mapIdx fun i original =>
    if i == 0 then badStatement else original))
  let badBody := startBody.setObjVal! "blocks" (toJson (blocks.mapIdx fun i original =>
    if i == 0 then badBlock else original))
  let badEffects := { document with bodies := document.bodies.map fun original =>
    if (original.getObjValAs? Nat "definition").toOption == some start then badBody else original }
  match restrictedCompilerEntryProgram badEffects with
  | .error "custom start must return its exact argc local" => pure ()
  | .error error => throw (IO.userError s!"unexpected effect-domain error: {error}")
  | .ok _ => throw (IO.userError "unsupported custom-start effects accepted")
  let missingHelper := { program with input := { program.input with queries := {
    program.input.queries with functionFacts := { program.input.queries.functionFacts with helperSignatures := #[] } } } }
  let missingAttempt := Input.EvalPreparation.prepare missingHelper
  let missingPrepared ← checked missingAttempt.outcome
  match CompilerEntryRun.runPrepared missingPrepared missingAttempt.memory with
  | .error error =>
    unless (error.splitOn "missing exact compiler dummy-signature ABI query").length > 1 do
      throw (IO.userError s!"unexpected missing helper error: {error}")
  | .ok _ => throw (IO.userError "fixed startup ignored missing demanded helper ABI")
  IO.println "foundation compiler entry: source absence/effect domain and missing demanded helper ABI reject"
