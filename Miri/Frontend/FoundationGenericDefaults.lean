import Miri.Frontend.Foundation

/-! Retained declaration defaults do not supply instance arguments. The caller
must still pass the full generic argument vector to the existing environment
checker and substituter. -/
namespace Miri.Frontend.Foundation
open Lean

/-- Read a type parameter's optional source template, validating its declaration
identity. No substitution, default application, or obligation discharge occurs. -/
def typeParameterDefaultSource (document : Document) (parameter : Json) : Except String (Option TypeExpr) := do
  unless (← parameter.getObjValAs? String "kind") == "type" do
    throw "source default query requires a type parameter"
  let definition ← parameter.getObjValAs? Nat "definition"
  let some row := document.definitions[definition]? | throw "type parameter source definition absent"
  unless (← row.getObjValAs? Nat "definition_id") == definition &&
      (← row.getObjValAs? String "kind") == "TyParam" do
    throw "type parameter source definition mismatch"
  let hasDefault ← parameter.getObjValAs? Bool "has_default"
  let source ← parameter.getObjVal? "default"
  if !hasDefault then
    unless source == Json.null do throw "unexpected default on type parameter"
    return none
  let type ← source.getNat?
  return some (← typeExpr document type)

end Miri.Frontend.Foundation
