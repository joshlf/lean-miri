import Miri.Frontend.FoundationBodyCore

open Lean Miri Miri.Frontend.Foundation

/-- These negative controls intentionally supply no compiler facts. A syntax
candidate alone must never become an executable body. -/
def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected foundation identity JSON")
  let text ← IO.FS.readFile path
  let result : Except String Unit := do
    let d ← Json.parse text >>= decode
    let some source := d.bodies[0]? | throw "missing body"
    let definition ← source.getObjValAs? Nat "definition"
    let prepared ← prepareItem d definition #[.type (.primitive "uint" "u8")]
    let bindings : BodyBindings := {
      types := #[], physicalTypeIds := #[], spans := #[], files := #[]
      definitionId := 0
      instanceNode := {
        instanceKind := .Item 0, genericArgs := #[], id := 0
        kind := .instanceMir, defPath := some "identity", definitionId := some 0
        bodyId := none, promotedBodies := #[] }
      defPath := "identity", sourcePath := "", backtraceSpans := #[], requiredConsts := #[] }
    match lowerPreparedBodyCore prepared bindings with
    | .error "foundation body missing or duplicate physical type binding" => pure ()
    | .error e => throw s!"unexpected missing-type diagnostic: {e}"
    | .ok _ => throw "body without physical types accepted"
    let bound := { bindings with types := #[⟨.primitive "uint" "u8", 7⟩] }
    match lowerPreparedBodyCore prepared bound with
    | .error "foundation body physical type is not in document" => pure ()
    | .error e => throw s!"unexpected foreign-type diagnostic: {e}"
    | .ok _ => throw "foreign physical type accepted"
    match lowerPreparedBodyCore prepared { bound with physicalTypeIds := #[7] } with
    | .error "foundation body span filename is not interned" => pure ()
    | .error e => throw s!"unexpected source diagnostic: {e}"
    | .ok _ => throw "body without source facts accepted"
  match result with
  | .ok _ => IO.println "foundation BodyCore: missing physical/source joins reject"
  | .error e => throw (IO.userError e)
