import Miri.Frontend.FoundationBridge

open Lean Miri.Frontend.Foundation

/-- Uses a fresh finite-material export; success prepares data only and does not
execute the fixed interpreter or establish safety. -/
def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected fresh identity foundation JSON path")
  let source ← IO.FS.readFile path
  let document ← match Json.parse source >>= decode with
    | .ok d => pure d
    | .error e => throw (IO.userError e)
  let some body := document.bodies[0]? | throw (IO.userError "missing identity body")
  let definition ← match body.getObjValAs? Nat "definition" with
    | .ok n => pure n
    | .error e => throw (IO.userError e)
  let args := #[ItemArgument.type (.primitive "uint" "u8")]
  match prepareItem document definition args with
  | .ok prepared =>
    unless prepared.item.argumentCount == 1 do throw (IO.userError "unexpected identity argument count")
  | .error e => throw (IO.userError e)
  let broken := { document with bodies := #[body.setObjVal! "signature" Json.null] }
  match prepareItem broken definition args with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "missing signature accepted")
  IO.println "foundation bridge preparation: 2 checks passed"
