import Miri.Frontend.FoundationInstance

open Lean Miri.Frontend.Foundation

private def fixture (parameters : String := "[{\"kind\":\"type\",\"index\":0}]")
    (required : String := "[]") : Except String Document := do
  let body ← Json.parse ("{\"definition\":0,\"argument_count\":1,\"environment\":{\"parameters\":" ++ parameters ++
    ",\"clauses\":[]},\"required_consts\":" ++ required ++ ",\"locals\":[0,0],\"blocks\":[{}]}")
  let flat ← body.getObjVal? "environment"
  let parameters ← flat.getObjValAs? (Array Json) "parameters"
  let parameters := parameters.mapIdx fun index parameter => parameter.setObjVal! "definition" (toJson (index + 1))
  let declaration := Json.mkObj [("parent",Json.null),("parent_count",toJson (0 : Nat)),
    ("own_parameter_count",toJson parameters.size),("self_type",Json.null)]
  let owner := Json.mkObj [("definition_id",toJson (0 : Nat)),("kind",toJson "fn"),("generic_declaration",declaration)]
  let definitions := #[owner] ++ parameters.mapIdx fun index parameter => Json.mkObj [
    ("definition_id",toJson (index + 1)),("kind",toJson (if (parameter.getObjValAs? String "kind").toOption == some "const" then "ConstParam" else "TyParam")),
    ("generic_parameter",Json.mkObj [("owner",toJson (0 : Nat)),("index",toJson index)])]
  let layer := Json.mkObj [("owner",toJson (0 : Nat)),("parent",Json.null),("parent_count",toJson (0 : Nat)),
    ("self_type",Json.null),("parameters",toJson parameters),("clauses",toJson (#[] : Array Json))]
  let body := body.setObjVal! "environment" (Json.mkObj [("owner",toJson (0 : Nat)),("layers",toJson #[layer])])
  let ty ← Json.parse "{\"type_id\":0,\"shape\":{\"kind\":\"param\",\"index\":0}}"
  let target : Target := {
    triple := "x86_64-unknown-linux-gnu"
    dataLayout := ""
    pointerSizeBits := 64
    endian := "little"
    runtimeDataLayout := Json.null
  }
  return {
    source := Json.null
    target := target
    definitions := definitions
    types := #[ty]
    bodies := #[body]
  }

private def run (d : Except String Document)
    (args := #[ItemArgument.type (.primitive "uint" "u8")]) : Except String ItemTemplate := do
  instantiateItem (← d) 0 args

private def expectError (r : Except String ItemTemplate) : IO Unit := do
  match r with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "unexpected item construction success")

def main : IO Unit := do
  match run (fixture) with
  | .ok item =>
    unless item.localTypes.size == 2 && item.argumentCount == 1 do
      throw (IO.userError "incorrect item substitution")
    match item.localTypes[0]? with
    | some (.primitive "uint" "u8") => pure ()
    | _ => throw (IO.userError "unsubstituted return local")
  | .error e => throw (IO.userError e)
  expectError (run (fixture) #[])
  expectError (run (fixture) #[.constant 8])
  expectError (run (fixture "[{\"kind\":\"type\",\"index\":1}]"))
  expectError (run (fixture "[{\"kind\":\"type\",\"index\":0}]" "[{}]"))
  let duplicate := do
    let d ← fixture
    pure { d with bodies := d.bodies ++ d.bodies }
  expectError (run duplicate)
  IO.println "foundation item construction: 6 checks passed"
