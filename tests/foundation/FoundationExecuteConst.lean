import Miri.Frontend.FoundationExecute

open Lean Miri Miri.Frontend.Foundation

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

/-- Fresh source const-item demand is lowered, retained in required_consts and
executed by the fixed machine. This is one finite observation, not safety. -/
def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected fresh scalar foundation export")
  let document ← checked (Json.parse (← IO.FS.readFile path) >>= decode)
  let some body := document.bodies[0]? | throw (IO.userError "source body absent")
  let definition ← checked (body.getObjValAs? Nat "definition")
  let program ← checked (restrictedLibraryProgram document definition #[])
  let some lowered := program.bundle.bodies[0]? | throw (IO.userError "lowered body absent")
  unless lowered.input.requiredConsts.size == 1 do
    throw (IO.userError "required const operand was omitted")
  let prepared ← checked (Input.CompilerProviders.prepare program)
  IO.println (← checked (FixedIdentityRun.runPrepared prepared 37))
  -- A source const cycle fails during pure demand checking/lowering.
  let some constDefinition := document.definitions.findIdx? (fun row =>
      (row.getObjValAs? String "kind").toOption == some "const")
    | throw (IO.userError "source const definition absent")
  let some row := document.definitions[constDefinition]?
    | throw (IO.userError "source const row absent")
  let expression ← checked (row.getObjVal? "const_expression")
  let operand ← checked (expression.getObjVal? "operand")
  let cycleValue := Json.mkObj [("kind", toJson "unevaluated"),
    ("definition", toJson constDefinition), ("arguments", toJson (#[] : Array Json))]
  let cycleOperand := operand.setObjVal! "value" cycleValue
  let cycleRow := row.setObjVal! "const_expression" (expression.setObjVal! "operand" cycleOperand)
  let definitions := document.definitions.mapIdx (fun index original =>
    if index == constDefinition then cycleRow else original)
  let malformed := { document with definitions }
  match restrictedLibraryProgram malformed definition #[] with
  | .error "cyclic const source expression" => pure ()
  | .error error => throw (IO.userError s!"unexpected cyclic source error: {error}")
  | .ok _ => throw (IO.userError "cyclic source constant accepted")
  IO.println "foundation fixed scalar const: required operand retained; cyclic source rejects"
