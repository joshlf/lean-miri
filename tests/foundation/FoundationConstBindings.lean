import Miri.Frontend.FoundationConstBindings

open Lean Miri.Frontend.Foundation

private def documentAndBody : Except String (Document × Json) := do
  let usize ← Json.parse "{\"type_id\":0,\"shape\":{\"kind\":\"uint\",\"name\":\"usize\"}}"
  let body ← Json.parse "{\"environment\":{\"parameters\":[{\"kind\":\"const\",\"index\":0,\"type\":0}]},\"required_consts\":[{\"kind\":\"constant\",\"type\":0,\"value\":{\"kind\":\"param\",\"index\":0}}]}"
  let target : Target := {
    triple := "test", dataLayout := "", pointerSizeBits := 64, endian := "little"
  }
  return ({source := Json.null, target, definitions := #[], types := #[usize], bodies := #[body]}, body)

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
