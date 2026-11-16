import Miri.Input.Decoder

open Lean Miri.Input

private def set (value : Json) (key : String) (child : Json) : Except String Json := do
  let fields ← value.getObj?
  pure (Json.mkObj ((key, child) :: fields.toList.filter (fun item => item.1 != key)))

private def malformedCast : Json := Json.mkObj [
  ("kind", toJson ("Cast" : String)),
  ("vtable_allocation", Json.mkObj [
    ("kind", toJson ("dynamic_vtable_upcast" : String))])]

private def must {α : Type} (value : Except String α) : IO α :=
  match value with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected current exporter MIR JSON")
  let base ← must (Json.parse (← IO.FS.readFile path))
  let _ ← must (decodeJson base.compress)
  IO.println "PASS direct-format input accepted before malformed-cast injection"
  -- Unknown extension fields are skipped, even when their names or contents
  -- resemble MIR. Validation applies to the schema's actual typed nodes.
  let withFirst ← must (set base "synthetic_first" malformedCast)
  let extensions ← must (set withFirst "synthetic_second" malformedCast)
  let _ ← must (decodeJson extensions.compress)
  IO.println "PASS unknown Cast-shaped extension payloads skipped"
  let material ← must (base.getObjVal? "source_vtables")
  let bindings ← must ((← must (material.getObjVal? "bindings")).getArr?)
  let malformed := Json.mkObj [("type_id", toJson (0 : Nat)), ("principal", Json.null),
    ("methods", Json.arr #[])]
  let material ← must (set material "bindings" (.arr (bindings.push malformed)))
  let input ← must (set base "source_vtables" material)
  match decodeJson input.compress with
  | .error message =>
    check (message.contains "drop_instance")
      s!"malformed typed vtable must fail its missing metadata; got {message}"
    IO.println s!"PASS malformed typed vtable declaration rejected: {message}"
  | .ok _ => throw (IO.userError "malformed typed vtable declaration was accepted")
