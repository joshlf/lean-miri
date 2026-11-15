import Miri.Frontend.FoundationGenericEnvironment
import Miri.Input.Model.SourceMaterial

/-! Project finite source declaration headers once, during frontend decoding.
These typed rows retain original kind and complete generic slots; they contain
no substitutions, callee winner, canonical instance, body or ABI answer. -/
namespace Miri.Frontend.Foundation
open Lean

private def headerRows (document : Document) : Except String (Array Json) :=
  match document.source.getObjVal? "source_function_signatures" with
  | .ok value => fromJson? value
  | .error _ => pure #[]

/-- A body and a signature-only declaration can both witness the same source
header, but their original environments must agree. Associated classification
is retained and does not select a trait implementation. -/
def sourceItemDeclaration (document : Document) (definition : Nat) :
    Except String Input.SourceMaterial.ItemDeclaration := do
  let some row := document.definitions[definition]? | throw "Item source declaration absent"
  unless (← row.getObjValAs? Nat "definition_id") == definition do throw "Item source declaration identity mismatch"
  let kind : Input.SourceMaterial.ItemKind ← match ← row.getObjValAs? String "kind" with
    | "fn" => pure .function
    | "assoc_fn" => pure .associatedFunction
    | _ => throw "Item source declaration is not an ordinary function or associated method"
  let bodies ← document.bodies.filterM fun body =>
    return (← body.getObjValAs? Nat "definition") == definition
  let headers ← (← headerRows document).filterM fun header =>
    return (← header.getObjValAs? Nat "definition") == definition
  unless bodies.size ≤ 1 && headers.size ≤ 1 do throw "duplicate Item declaration source"
  let environment ← match bodies[0]?,headers[0]? with
    | none,none => throw "Item generic declaration source unavailable"
    | some body,none => body.getObjVal? "environment"
    | none,some header => header.getObjVal? "environment"
    | some body,some header => do
      let original ← body.getObjVal? "environment"
      unless original == (← header.getObjVal? "environment") do throw "conflicting Item generic declaration"
      pure original
  unless (← environment.getObjValAs? Nat "owner") == definition do throw "Item generic source owner mismatch"
  let flat ← flattenEnvironment document environment
  let mut parameters := #[]
  for parameter in (← flat.getObjValAs? (Array Json) "parameters") do
    let kind ← match ← parameter.getObjValAs? String "kind" with
      | "type" => pure Input.SourceSymbols.ParameterKind.typeParameter
      | "const" => pure .constParameter
      | _ => throw "Item source generic slot unsupported"
    parameters := parameters.push kind
  let raw : Input.DefinitionId := ⟨← row.getObjValAs? Nat "crate_index",← row.getObjValAs? Nat "index"⟩
  unless raw.crateIndex < 2^32 && raw.index < 2^32 do throw "Item source DefId exceeds rustc index width"
  return ⟨raw,← row.getObjValAs? String "path",kind,parameters⟩

/-- Only finite declaration owners are traversed, never argument combinations.
A missing function header is not replaced by guessed parameter slots. -/
def sourceItemDeclarations (document : Document) : Except String (Array Input.SourceMaterial.ItemDeclaration) := do
  let mut definitions := #[]
  for row in document.bodies ++ (← headerRows document) do
    let definition ← row.getObjValAs? Nat "definition"
    let some owner := document.definitions[definition]? | throw "Item declaration source owner absent"
    unless (← owner.getObjValAs? Nat "definition_id") == definition do throw "Item declaration source owner identity mismatch"
    let kind ← owner.getObjValAs? String "kind"
    if (kind == "fn" || kind == "assoc_fn") && !definitions.contains definition then
      definitions := definitions.push definition
  definitions.mapM (sourceItemDeclaration document)

end Miri.Frontend.Foundation
