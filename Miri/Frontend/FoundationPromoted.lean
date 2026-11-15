import Miri.Frontend.Foundation

/-! Complete promoted source-table decoding. These are generic MIR templates,
not evaluated allocations, executable BodyIds or monomorphic compiler answers.
An explicit zero-length table is distinct from missing source material. -/
namespace Miri.Frontend.Foundation
open Lean

structure PromotedTemplate where
  owner : Nat
  index : Nat
  localTypes : Array Nat
  requiredConstants : Array Json
  source : Json

structure PromotedSourceTable where
  owner : Nat
  environment : Json
  templates : Array PromotedTemplate

private def validatePlace (document : Document) (locals : Nat) (place : Json) : Except String Unit := do
  unless (← place.getObjValAs? Nat "local") < locals do throw "promoted place local out of bounds"
  for projection in (← place.getObjValAs? (Array Json) "projection") do
    match ← projection.getObjValAs? String "kind" with
    | "deref" => pure ()
    | "field" =>
      unless (← projection.getObjValAs? Nat "type") < document.types.size do throw "promoted field type absent"
      let _ ← projection.getObjValAs? Nat "index"
      pure ()
    | "index" => unless (← projection.getObjValAs? Nat "local") < locals do throw "promoted index local absent"
    | _ => throw "promoted projection unsupported"

private def validateOperand (document : Document) (locals : Nat) (operand : Json) : Except String Unit := do
  match ← operand.getObjValAs? String "kind" with
  | "copy" | "move" => validatePlace document locals (← operand.getObjVal? "place")
  | "constant" =>
    unless (← operand.getObjValAs? Nat "type") < document.types.size do throw "promoted constant type absent"
    let value ← operand.getObjVal? "value"
    unless (← value.getObjValAs? String "kind") == "zero_sized" do
      throw "promoted non-ZST constant source selection unsupported"
    let _ ← operand.getObjVal? "source_span_key"
    let _ ← operand.getObjVal? "user_type"
    pure ()
  | _ => throw "promoted operand unsupported"

/-- Validate the complete requested source table, including unused entries.
Source owner/index joins, the full required-constant list, runtime phase and
source scopes survive unchanged. This reader does not discharge environment
predicates, evaluate required constants or reify function-pointer allocations. -/
def promotedSourceTable (document : Document) (owner : Nat) : Except String PromotedSourceTable := do
  let some definition := document.definitions[owner]? | throw "promoted source owner absent"
  unless (← definition.getObjValAs? String "kind") == "fn" do throw "promoted source owner kind unsupported"
  let tables ← document.source.getObjValAs? (Array Json) "promoted_tables"
  let candidates ← tables.filterM fun row => return (← row.getObjValAs? Nat "definition") == owner
  unless candidates.size == 1 do throw "missing or duplicate complete promoted source table"
  let some table := candidates[0]? | throw "promoted source table absent"
  let environment ← table.getObjVal? "environment"
  let _ ← environment.getObjValAs? (Array Json) "parameters"
  let _ ← environment.getObjValAs? (Array Json) "clauses"
  let count ← table.getObjValAs? Nat "promoted_count"
  let bodies ← table.getObjValAs? (Array Json) "templates"
  unless count == bodies.size do throw "promoted source table count mismatch"
  let mut templates := #[]
  for h : i in [:bodies.size] do
    let body := bodies[i]
    unless (← body.getObjValAs? Nat "definition") == owner &&
        (← body.getObjValAs? Nat "promoted_index") == i &&
        (← body.getObjValAs? Nat "source_promoted") == i do
      throw "promoted source owner/index identity mismatch"
    let instanceSource ← body.getObjVal? "source_instance"
    unless (← instanceSource.getObjValAs? String "kind") == "item" &&
        (← instanceSource.getObjValAs? Nat "definition") == owner do
      throw "promoted source instance identity mismatch"
    validateSourceMetadata body
    let metadata ← body.getObjVal? "source_metadata"
    let phase ← metadata.getObjVal? "phase"
    unless (← phase.getObjValAs? String "phase") ∈ ["initial", "post_cleanup", "optimized"] do
      throw "promoted runtime phase unsupported"
    let locals ← body.getObjValAs? (Array Nat) "locals"
    unless !locals.isEmpty do throw "promoted return local absent"
    for type in locals do
      unless type < document.types.size do throw "promoted local type absent"
    unless (← body.getObjValAs? Nat "argument_count") == 0 do throw "promoted value argument locals unsupported"
    let _ ← body.getObjVal? "spread_argument"
    unless (← body.getObjVal? "spread_argument") == Json.null do throw "promoted spread argument unsupported"
    let required ← body.getObjValAs? (Array Json) "required_consts"
    for constant in required do validateOperand document locals.size constant
    let blocks ← body.getObjValAs? (Array Json) "blocks"
    unless !blocks.isEmpty do throw "promoted entry block absent"
    for block in blocks do
      for statement in (← block.getObjValAs? (Array Json) "statements") do
        match ← statement.getObjValAs? String "kind" with
        | "assign" =>
          validatePlace document locals.size (← statement.getObjVal? "place")
          let value ← statement.getObjVal? "value"
          match ← value.getObjValAs? String "kind" with
          | "use" =>
            let _ ← value.getObjValAs? Bool "retag"
            validateOperand document locals.size (← value.getObjVal? "operand")
          | "ref" =>
            unless (← value.getObjValAs? String "borrow_kind") == "shared" do throw "promoted borrow kind unsupported"
            unless (← value.getObjValAs? String "region") ∈ ["erased", "static"] do throw "promoted borrow region unsupported"
            validatePlace document locals.size (← value.getObjVal? "place")
          | "cast_reify_function_pointer" =>
            unless (← value.getObjValAs? String "safety") ∈ ["safe", "unsafe"] &&
                (← value.getObjValAs? String "source") ∈ ["as_cast", "implicit"] do
              throw "promoted function reification source unsupported"
            let target ← value.getObjValAs? Nat "target"
            let some targetRow := document.types[target]? | throw "promoted reification target type absent"
            unless (← (← targetRow.getObjVal? "shape").getObjValAs? String "kind") == "function_pointer" do
              throw "promoted reification target is not FnPtr"
            let operand ← value.getObjVal? "operand"
            validateOperand document locals.size operand
            unless (← operand.getObjValAs? String "kind") == "constant" do
              throw "promoted nonconstant reification source unsupported"
            let sourceType ← operand.getObjValAs? Nat "type"
            let some sourceRow := document.types[sourceType]? | throw "promoted reification source type absent"
            let sourceShape ← sourceRow.getObjVal? "shape"
            unless (← sourceShape.getObjValAs? Nat "definition") < document.definitions.size do
              throw "promoted reification function definition absent"
            let _ ← sourceShape.getObjValAs? (Array Json) "arguments"
            unless (← sourceShape.getObjValAs? String "kind") == "function_definition" &&
                (← (← operand.getObjVal? "value").getObjValAs? String "kind") == "zero_sized" do
              throw "promoted reification source is not zero-sized FnDef"
          | _ => throw "promoted rvalue source unsupported"
        | "storage_live" | "storage_dead" =>
          unless (← statement.getObjValAs? Nat "local") < locals.size do throw "promoted storage local absent"
        | "nop" => pure ()
        | _ => throw "promoted statement source unsupported"
      let terminal ← block.getObjVal? "terminator"
      match ← terminal.getObjValAs? String "kind" with
      | "return" | "unreachable" => pure ()
      | "goto" => unless (← terminal.getObjValAs? Nat "target") < blocks.size do throw "promoted goto target absent"
      | _ => throw "promoted terminator source unsupported"
    templates := templates.push ⟨owner, i, locals, required, body⟩
  return ⟨owner, environment, templates⟩

def selectPromotedTemplate (document : Document) (owner index : Nat) : Except String PromotedTemplate := do
  let table ← promotedSourceTable document owner
  let some body := table.templates[index]? | throw "promoted source index absent"
  return body

end Miri.Frontend.Foundation
