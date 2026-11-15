import Miri.Frontend.FoundationConstBindings

open Lean Miri.Frontend.Foundation

private def documentAndBody : Except String (Document × Json) := do
  let usize ← Json.parse "{\"type_id\":0,\"shape\":{\"kind\":\"uint\",\"name\":\"usize\"}}"
  let body ← Json.parse "{\"environment\":{\"parameters\":[{\"kind\":\"const\",\"index\":0,\"type\":0}]},\"required_consts\":[{\"kind\":\"constant\",\"type\":0,\"value\":{\"kind\":\"param\",\"index\":0}}]}"
  let declaration := Json.mkObj [("parent",Json.null),("parent_count",toJson (0 : Nat)),
    ("own_parameter_count",toJson (1 : Nat)),("self_type",Json.null)]
  let owner := Json.mkObj [("definition_id",toJson (0 : Nat)),("kind",toJson "fn"),("generic_declaration",declaration)]
  let parameterDefinition := Json.mkObj [("definition_id",toJson (1 : Nat)),("kind",toJson "ConstParam"),
    ("generic_parameter",Json.mkObj [("owner",toJson (0 : Nat)),("index",toJson (0 : Nat))])]
  let parameter := Json.mkObj [("definition",toJson (1 : Nat)),("kind",toJson "const"),("index",toJson (0 : Nat)),("type",toJson (0 : Nat))]
  let layer := Json.mkObj [("owner",toJson (0 : Nat)),("parent",Json.null),("parent_count",toJson (0 : Nat)),
    ("self_type",Json.null),("parameters",toJson #[parameter]),("clauses",toJson (#[] : Array Json))]
  let body := body.setObjVal! "environment" (Json.mkObj [("owner",toJson (0 : Nat)),("layers",toJson #[layer])])
  let target : Target := {
    triple := "test", dataLayout := "", pointerSizeBits := 64, endian := "little"
  }
  return ({source := Json.null, target, definitions := #[owner,parameterDefinition], types := #[usize], bodies := #[body]}, body)

def main : IO Unit := do
  let (d, body) ← match documentAndBody with
    | .ok result => pure result
    | .error e => throw (IO.userError e)
  match checkRequiredConstants d body #[some 7] with
  | .ok () => pure ()
  | .error e => throw (IO.userError e)
  for arguments in [#[], #[none], #[some (2 ^ 64)]] do
    if (checkRequiredConstants d body arguments).isOk then
      throw (IO.userError "missing or oversized required const parameter accepted")
  IO.println "foundation required-const argument binding passed"
