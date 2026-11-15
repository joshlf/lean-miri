import Miri.Frontend.FoundationEntry
import Miri.Frontend.FoundationClosure

/-! Checked source-demand composition for one explicit std startup spine. This
is not a LoweredProgram: executable closure/shim/vtable/static demands remain. -/
namespace Miri.Frontend.Foundation
open Lean
structure StdStartupSource where
  main : Nat
  start : Nat
  internal : Nat
  mainBody : Json
  startBody : Json
  internalBody : Json
  closure : SelectedClosureTemplate

private def uniqueBody (document : Document) (definition : Nat) : Except String Json := do
  let bodies ← document.bodies.filterM fun body => return (← body.getObjValAs? Nat "definition") == definition
  let [body] := bodies.toList | throw "std source body missing or duplicated"
  validateSourceMetadata body
  return body

/-- Join compiler-selected main/start, the actual start Call FnDef and Closure
aggregate, and the selected closure's parent identity in the same document. -/
def stdStartupSource (document : Document) : Except String StdStartupSource := do
  let selection ← entrySelection document.source
  let some entry := selection.compilerEntry | throw "std source compiler main absent"
  let some start := selection.startLangItem | throw "std source start lang item absent"
  let mainBody ← uniqueBody document entry.definition
  let signature ← mainBody.getObjVal? "signature"
  unless (← signature.getObjValAs? (Array Nat) "inputs").isEmpty do throw "std source main arguments unsupported"
  let returnType ← instantiate #[] #[] (← typeExpr document (← signature.getObjValAs? Nat "output"))
  let startBody ← uniqueBody document start
  let blocks ← startBody.getObjValAs? (Array Json) "blocks"
  let mut internalDefinitions := #[]
  let mut closureDefinitions := #[]
  for block in blocks do
    for statement in (← block.getObjValAs? (Array Json) "statements") do
      if (← statement.getObjValAs? String "kind") == "assign" then
        let value ← statement.getObjVal? "value"
        if (← value.getObjValAs? String "kind") == "aggregate_closure" then
          closureDefinitions := closureDefinitions.push (← value.getObjValAs? Nat "definition")
    let terminal ← block.getObjVal? "terminator"
    if (← terminal.getObjValAs? String "kind") == "call" then
      let operand ← terminal.getObjVal? "function"
      unless (← operand.getObjValAs? String "kind") == "constant" do throw "std start indirect call unsupported"
      let value ← operand.getObjVal? "value"
      unless (← value.getObjValAs? String "kind") == "zero_sized" do throw "std start callee not FnDef ZST"
      let type ← operand.getObjValAs? Nat "type"
      let some row := document.types[type]? | throw "std start callee type absent"
      let shape ← row.getObjVal? "shape"
      unless (← shape.getObjValAs? String "kind") == "function_definition" do throw "std start callee not function definition"
      unless (← shape.getObjValAs? (Array Json) "arguments").isEmpty do throw "std internal generic call unsupported"
      internalDefinitions := internalDefinitions.push (← shape.getObjValAs? Nat "definition")
  let [internal] := internalDefinitions.toList | throw "std start internal Call demand missing or duplicated"
  let some definition := document.definitions[internal]? | throw "std internal definition absent"
  unless (← definition.getObjValAs? String "path") == "std::rt::lang_start_internal" &&
      (← definition.getObjValAs? String "kind") == "fn" do throw "std internal source edge mismatch"
  let internalBody ← uniqueBody document internal
  let [closureDefinition] := closureDefinitions.toList | throw "std start Closure demand missing or duplicated"
  let closure ← selectClosureTemplate document closureDefinition #[.type returnType]
  unless closure.parentDefinition == start do throw "std start closure parent mismatch"
  return { main := entry.definition, start, internal, mainBody, startBody, internalBody, closure }
end Miri.Frontend.Foundation
