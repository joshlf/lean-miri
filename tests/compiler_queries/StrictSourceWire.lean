import Miri.Input.Decoder

/-! Obsolete source and layout recipes cannot enter the rustc-result document. -/
open Lean Miri.Input
private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)
private def rejects (value : Json) (message : String) : IO Unit := do
  match decodeJson value.compress with
  | .ok _ => throw (IO.userError s!"accepted obsolete wire: {message}")
  | .error _ => pure ()

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected fresh rustc export")
  let input ← must (Json.parse (← IO.FS.readFile path))
  let _ ← must (decodeJson input.compress)
  for (key,message) in [
      ("mir_templates","mir_templates"),
      ("ctfe_scalar_sources","ctfe_scalar_sources")] do
    rejects (input.setObjVal! key (toJson #[Json.mkObj []])) message
  let bodies ← must ((← must (input.getObjVal? "bodies")).getArr?)
  let some first := bodies[0]? | throw (IO.userError "fixture has no body")
  let legacy := first.setObjVal! "body_kind" (toJson "material")
  rejects (input.setObjVal! "bodies" (toJson (bodies.set! 0 legacy))) "body_kind"
  let layouts ← must ((← must (input.getObjVal? "layout_values")).getArr?)
  let some firstLayout := layouts[0]? | throw (IO.userError "fixture has no layout")
  let recipe := firstLayout.setObjVal! "primitive_recipe" (toJson "u128")
  rejects (input.setObjVal! "layout_values" (toJson (layouts.set! 0 recipe))) "primitive_recipe"
  IO.println "PASS obsolete source and layout wires reject"
