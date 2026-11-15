import Miri.Frontend.FoundationExistentialRegistry
import Miri.Frontend.FoundationExistentialBounds
import Miri.Frontend.FoundationObligations
open Lean Miri.Frontend.Foundation

private def checked (value : Except String α) : IO α := do
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def rejected (value : Except String α) : IO Unit := do
  match value with | .error _ => pure () | .ok _ => throw (IO.userError "unsupported existential query accepted")

def main (paths : List String) : IO Unit := do
  let [path, genericPath] := paths | throw (IO.userError "expected fresh mono/generic dynamic source JSON")
  let document ← checked (Json.parse (← IO.FS.readFile path) >>= decode)
  let some id := document.types.findIdx? (fun row =>
      ((row.getObjVal? "shape").bind (fun shape => shape.getObjValAs? String "kind")).toOption == some "dynamic" &&
      ((row.getObjVal? "shape").bind (fun shape => shape.getObjValAs? String "region")).toOption == some "erased")
    | throw (IO.userError "erased dynamic source absent")
  let (registry, identity) ← checked ((ExistentialRegistry.start document).intern id)
  let (same, sameId) ← checked (registry.intern id)
  unless sameId == identity && same.entries.size == 1 do throw (IO.userError "dynamic source interning unstable")
  let some source := registry.entries[identity]? | throw (IO.userError "dynamic structural identity absent")
  let some principal := source.principal | throw (IO.userError "Fn principal absent")
  unless source.arguments.size == 1 && source.projections.size == 1 && source.autoTraits.size == 2 do
    throw (IO.userError "Fn existential source components lost")
  let some projection := source.projections[0]? | throw (IO.userError "Fn Output equality absent")
  unless sameConcrete 1024 projection.term (.primitive "int" "i32") do throw (IO.userError "Fn Output type lost")
  let _ ← checked (checkExplicitExistentialTrait source principal source.arguments)
  for traitId in source.autoTraits do
    let _ ← checked (checkExplicitExistentialTrait source traitId #[])
  let _ ← checked (checkExplicitExistentialProjection source projection.definition projection.arguments projection.term)
  rejected (checkExplicitExistentialTrait source projection.parentTrait source.arguments)
  rejected (checkExplicitExistentialProjection source projection.definition projection.arguments (.primitive "int" "i64"))
  let some typeRow := document.types[id]? | throw (IO.userError "dynamic type source absent")
  let shape ← checked (typeRow.getObjVal? "shape")
  let predicates ← checked (shape.getObjValAs? (Array Json) "predicates")
  let some first := predicates[0]? | throw (IO.userError "principal source absent")
  let selfArgument := Json.mkObj [("kind",toJson "type"),("type",toJson id)]
  let arguments ← checked (first.getObjValAs? (Array Json) "arguments")
  let clause := first.setObjVal! "arguments" (toJson (#[selfArgument] ++ arguments))
  let environment := Json.mkObj [("parameters",toJson (#[] : Array Json)),("clauses",toJson #[clause])]
  let _ ← checked (checkEnvironment document #[] #[] environment)
  let badTerm := Json.mkObj [("kind",toJson "const"),("bits",toJson "0")]
  for changed in #[
      shape.setObjVal! "predicates" (toJson (predicates.push first)),
      shape.setObjVal! "predicates" (toJson (predicates.map fun p =>
        if (p.getObjValAs? String "kind").toOption == some "projection" then p.setObjVal! "term" badTerm else p)),
      shape.setObjVal! "predicates" (toJson (predicates.map fun p => p.setObjVal! "bound_variables" (toJson #[Json.null])))] do
    rejected (parseExistential document.definitions (typeExpr document) changed)
  let generic ← checked (Json.parse (← IO.FS.readFile genericPath) >>= decode)
  let some genericId := generic.types.findIdx? (fun row =>
      ((row.getObjVal? "shape").bind (fun shape => shape.getObjValAs? String "kind")).toOption == some "dynamic")
    | throw (IO.userError "generic dynamic source absent")
  let expression ← checked (typeExpr generic genericId)
  let .dynamicObject substituted ← checked (instantiate #[some (.primitive "uint" "u16")] #[] expression)
    | throw (IO.userError "dynamic substitution lost constructor")
  let some output := substituted.projections[0]? | throw (IO.userError "generic Output absent")
  unless sameConcrete 1024 output.term (.primitive "uint" "u16") do
    throw (IO.userError "generic existential Output placeholder was not substituted")
  IO.println "existential source: interning, explicit Fn/auto/projection joins, generic substitution and unsupported controls passed"
