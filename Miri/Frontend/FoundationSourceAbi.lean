import Miri.Frontend.Foundation
import Miri.Frontend.FoundationSourceTypes
import Miri.Input.Model.SourceAbi

/-! One-time ingestion of ABI declaration syntax. JSON is discarded after this
conversion; runtime ABI demands consume only the typed SourceAbi records. -/
namespace Miri.Frontend.Foundation.SourceAbiParser
open Lean Miri
open Input.SourceAbi
private def raw (document : Document) (definition : Nat) : Except String Input.DefinitionId := do
  let some row := document.definitions[definition]? | throw "ABI source definition absent"
  unless (← row.getObjValAs? Nat "definition_id") == definition do throw "ABI source definition index mismatch"
  return ⟨← row.getObjValAs? Nat "crate_index",← row.getObjValAs? Nat "index"⟩
private def role (name : String) : Except String BuiltinTrait := do
  match name with
  | "sized" => pure .sized | "copy" => pure .copy | "meta_sized" => pure .metaSized
  | _ => throw "unknown ABI builtin language-item role"
private def declaration (document : Document) (clause : Json) : Except String (Clause × Option BuiltinDeclaration) := do
  match ← clause.getObjValAs? String "kind" with
  | "trait" =>
    let definition ← raw document (← clause.getObjValAs? Nat "definition")
    let mut arguments : Array Input.SourceTypes.TypeRef := #[]
    for argument in (← clause.getObjValAs? (Array Json) "arguments") do
      unless (← argument.getObjValAs? String "kind") == "type" do
        return (.unsupported "non-type trait argument",none)
      arguments := arguments.push (← argument.getObjValAs? Nat "type")
    let sourceRole ← match clause.getObjVal? "lang_item" with
      | .error _ | .ok .null => pure none
      | .ok source => do
        let name ← source.getStr?
        pure (some (← role name))
    let builtin ← match sourceRole with
      | none => pure none
      | some kind =>
        let pinned ← clause.getObjValAs? Bool "pinned_core_builtin"
        pure (some (BuiltinDeclaration.mk definition kind pinned))
    return (.trait definition sourceRole arguments,builtin)
  | "type_outlives" =>
    return (.typeOutlives (← clause.getObjValAs? Nat "type") (← SourceTypesParser.region (← clause.getObjVal? "region")),none)
  | "const_has_type" =>
    let value ← clause.getObjVal? "value"
    if (← value.getObjValAs? String "kind") != "param" then return (.unsupported "non-parameter const typing clause",none)
    return (.constHasType (← value.getObjValAs? Nat "index") (← clause.getObjValAs? Nat "type"),none)
  | other => pure (.unsupported other,none)

private def ordinaryTraits (document : Document) : Except String (Array TraitDeclaration × Array BuiltinDeclaration) := do
  let source ← document.source.getObjVal? "termination_source"
  if source == Json.null then return (#[],#[])
  let definition ← raw document (← source.getObjValAs? Nat "definition")
  let parent ← (← source.getObjValAs? (Option Nat) "generic_parent").mapM (raw document)
  let mut supers := #[]
  for clause in (← source.getObjValAs? (Array Json) "super_clauses") do
    unless (← clause.getObjValAs? String "kind") == "trait" do throw "ordinary trait super-clause encoding unsupported"
    supers := supers.push (SuperTrait.mk (← raw document (← clause.getObjValAs? Nat "definition"))
      (← clause.getObjValAs? Nat "argument_count") (← clause.getObjValAs? (Option Nat) "self_parameter")
      ((← clause.getObjValAs? String "polarity") == "Positive") (← clause.getObjValAs? Nat "bound_variable_count"))
  let mut implementations := #[]
  for header in (← source.getObjValAs? (Array Json) "implementations") do
    let head ← header.getObjVal? "self_constructor"
    let head : SelfHead ← match ← head.getObjValAs? String "kind" with
      | "tuple" => SelfHead.tuple <$> head.getObjValAs? Nat "arity"
      | "never" => pure SelfHead.never
      | "adt" => do
        let crate ← head.getObjValAs? Nat "crate_index"
        let index ← head.getObjValAs? Nat "index"
        pure (SelfHead.adt ⟨crate,index⟩)
      | tag => pure (SelfHead.unsupported tag)
    implementations := implementations.push (ImplHeader.mk (← raw document (← header.getObjValAs? Nat "definition"))
      (← raw document (← header.getObjValAs? Nat "trait_definition")) (← header.getObjValAs? Nat "argument_count") head
      (← header.getObjValAs? Nat "parameter_count") (← (← header.getObjValAs? (Option Nat) "generic_parent").mapM (raw document))
      (← header.getObjValAs? Nat "clause_count") (← (← header.getObjValAs? (Option Nat) "clause_parent").mapM (raw document))
      ((← header.getObjValAs? String "polarity") == "Positive") ((← header.getObjValAs? String "constness") == "NotConst")
      (← header.getObjValAs? Bool "final"))
  let declaration := TraitDeclaration.mk definition (← source.getObjValAs? Bool "auto")
    (← source.getObjValAs? Bool "marker") (← source.getObjValAs? Bool "coinductive")
    ((← source.getObjValAs? String "safety") == "Safe") ((← source.getObjValAs? String "constness") == "NotConst")
    (← source.getObjValAs? Nat "parameter_count") (← source.getObjValAs? Bool "has_self") parent
    (← source.getObjValAs? Bool "complete_impl_headers") supers implementations
  let metadataDefinition ← source.getObjValAs? (Option Nat) "meta_sized_definition"
  let builtins ← metadataDefinition.toArray.mapM fun id => do
    let pinned ← match source.getObjValAs? Bool "meta_sized_core_source" with | .ok value => pure value | .error _ => pure false
    return BuiltinDeclaration.mk (← raw document id) .metaSized pinned
  return (#[declaration],builtins)

/-- Preserve every captured source header and lexical clause owner exactly once.
No concrete substitutions, ABI results or selected implementations are produced. -/
def material (document : Document) : Except String Material := do
  let compilation ← document.source.getObjVal? "compilation"
  let panic ← compilation.getObjValAs? String "panic_strategy"
  let drop ← compilation.getObjValAs? String "panic_in_drop"
  unless (panic == "abort" || panic == "unwind") && (drop == "abort" || drop == "unwind") do
    throw "ABI source panic strategy invalid"
  let headers ← document.source.getObjValAs? (Array Json) "source_function_signatures"
  let mut rows := document.bodies
  for header in headers do
    let definition ← header.getObjValAs? Nat "definition"
    let matching := rows.filter fun row => (row.getObjValAs? Nat "definition").toOption == some definition
    if let some body := matching[0]? then
      unless matching.size == 1 do throw "duplicate ABI source body owner"
      for field in #["environment","signature","function_attributes"] do
        unless (← body.getObjVal? field) == (← header.getObjVal? field) do throw "conflicting ABI source signature/header"
    else rows := rows.push header
  let mut functions : Array Function := #[]
  let mut owners : Array OwnerClauses := #[]
  let mut builtins : Array BuiltinDeclaration := #[]
  for row in rows do
    let definition ← raw document (← row.getObjValAs? Nat "definition")
    unless !(functions.any fun f => f.definition == definition) do throw "duplicate ABI function declaration"
    let signature ← SourceTypesParser.signature (← row.getObjVal? "signature")
    unless signature.output < document.types.size && signature.inputs.all (· < document.types.size) do throw "ABI signature source type reference absent"
    let attrs ← row.getObjVal? "function_attributes"
    let attributes : Attributes := ⟨← attrs.getObjValAs? Bool "never_unwind",← attrs.getObjValAs? Bool "track_caller",
      ← attrs.getObjValAs? Bool "is_foreign",← attrs.getObjValAs? Bool "is_drop_glue"⟩
    let environment ← row.getObjVal? "environment"
    unless (← raw document (← environment.getObjValAs? Nat "owner")) == definition do throw "ABI source environment owner mismatch"
    let mut parameters : Array ConstParameterType := #[]
    for layer in (← environment.getObjValAs? (Array Json) "layers") do
      let owner ← raw document (← layer.getObjValAs? Nat "owner")
      let parent ← (← layer.getObjValAs? (Option Nat) "parent").mapM (raw document)
      let mut clauses := #[]
      for clause in (← layer.getObjValAs? (Array Json) "clauses") do
        let (clause,builtin) ← declaration document clause
        clauses := clauses.push clause
        if let some builtin := builtin then
          if let some existing := builtins.find? (·.definition == builtin.definition) then
            unless existing == builtin do throw "conflicting builtin source declaration role"
          else builtins := builtins.push builtin
      let source := OwnerClauses.mk owner parent clauses
      if let some existing := owners.find? (·.owner == owner) then
        unless existing == source do throw "conflicting ABI lexical clauses"
      else owners := owners.push source
      for parameter in (← layer.getObjValAs? (Array Json) "parameters") do
        if (← parameter.getObjValAs? String "kind") == "const" then
          parameters := parameters.push (ConstParameterType.mk (← raw document (← parameter.getObjValAs? Nat "definition"))
            (← parameter.getObjValAs? Nat "type"))
    functions := functions.push (Function.mk definition signature attributes parameters)
  let (traits,extraBuiltins) ← ordinaryTraits document
  for declaration in extraBuiltins do
    if let some existing := builtins.find? (·.definition == declaration.definition) then
      unless existing == declaration do throw "conflicting ordinary trait builtin declaration"
    else builtins := builtins.push declaration
  return ⟨functions,owners,builtins,panic == "unwind",drop == "unwind",traits⟩
end Miri.Frontend.Foundation.SourceAbiParser
