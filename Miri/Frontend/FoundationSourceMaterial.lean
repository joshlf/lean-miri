import Miri.Frontend.FoundationWorldDeclarations
import Miri.Frontend.FoundationTarget
import Miri.Frontend.FoundationLinkSections
import Miri.Input.Model.SourceMaterial

/-! One-way decoder projection into the typed evaluation-local carrier. JSON is
used only while parsing, never stored in SourceMaterial or reconstructed by a
runtime query. This slice keeps source declarations and lexical slots; generic
MIR/type/constraint demand remains explicitly unavailable until its typed
component is supplied. -/
namespace Miri.Frontend.Foundation
open Lean

private def rawDefinition (document : Document) (id : Nat) : Except String Input.DefinitionId := do
  let some row := document.definitions[id]? | throw "typed source declaration reference absent"
  unless (← row.getObjValAs? Nat "definition_id") == id do throw "typed source declaration reference/index mismatch"
  let crate ← row.getObjValAs? Nat "crate_index"
  let index ← row.getObjValAs? Nat "index"
  unless crate < 2^32 && index < 2^32 do throw "typed source declaration raw DefId exceeds rustc width"
  return ⟨crate,index⟩

private def parseLayer (document : Document) (source : Json) : Except String Input.SourceMaterial.GenericLayer := do
  let owner ← rawDefinition document (← source.getObjValAs? Nat "owner")
  let parent ← (← source.getObjValAs? (Option Nat) "parent").mapM (rawDefinition document)
  let parameters : Array Input.SourceMaterial.GenericParameter ← (← source.getObjValAs? (Array Json) "parameters").mapM fun parameter => do
    let kind ← match ← parameter.getObjValAs? String "kind" with
      | "type" => pure Input.SourceSymbols.ParameterKind.typeParameter
      | "const" => pure .constParameter
      | "region" => pure .region
      | _ => throw "typed source generic parameter kind unsupported"
    return {
      definition := ← rawDefinition document (← parameter.getObjValAs? Nat "definition")
      index := ← parameter.getObjValAs? Nat "index"
      kind }
  return ⟨owner,parent,← source.getObjValAs? Nat "parent_count",parameters⟩

private def sectionDeclaration (entry : SourceLinkSection) : Except String Input.SourceMaterial.LinkSectionDeclaration := do
  let key ← entry.source.getObjVal? "source_span_key"
  let position ← entry.source.getObjVal? "source_span"
  let start ← position.getObjVal? "start"
  let finish ← position.getObjVal? "end"
  let parentSource ← key.getObjVal? "parent_local_definition"
  let parent : Option Nat ← fromJson? parentSource
  return {
    name := entry.name, definition := ⟨entry.crateIndex,entry.definitionIndex⟩
    span := {
      isDummy := ← position.getObjValAs? Bool "is_dummy"
      lo := ← key.getObjValAs? Nat "lo", hi := ← key.getObjValAs? Nat "hi"
      context := ← key.getObjValAs? String "ctxt", parentLocalDefinition := parent
      file := ← position.getObjValAs? String "file"
      startLine := ← start.getObjValAs? Nat "line", startColumn := ← start.getObjValAs? Nat "column"
      endLine := ← finish.getObjValAs? Nat "line", endColumn := ← finish.getObjValAs? Nat "column" } }

/-- Project only callable declaration capabilities, without letting an unrelated
const/closure body masquerade as a free Item or invalidate known main/start rows.
Every zero-slot Item still retains its original zero-slot source layer. -/
def typedSourceMaterial (document : Document) : Except String Input.SourceMaterial := do
  let declarations ← sourceItemDeclarations document
  let headers ← match document.source.getObjVal? "source_function_signatures" with
    | .ok value => fromJson? value
    | .error _ => pure (#[] : Array Json)
  let mut layers : Array Input.SourceMaterial.GenericLayer := #[]
  for row in document.bodies ++ headers do
    let id ← row.getObjValAs? Nat "definition"
    let some definition := document.definitions[id]? | throw "typed source callable owner absent"
    let kind ← definition.getObjValAs? String "kind"
    unless kind == "fn" || kind == "assoc_fn" do continue
    let environment ← row.getObjVal? "environment"
    let _ ← flattenEnvironment document environment
    for original in (← environment.getObjValAs? (Array Json) "layers") do
      let layer ← parseLayer document original
      if let some old := layers.find? (·.owner == layer.owner) then
        unless old == layer do throw "typed source lexical layer conflict"
      else layers := layers.push layer
  let target : Input.SourceMaterial.Target := {
    triple := document.target.triple
    architecture := document.target.architecture
    dataLayout := document.target.dataLayout
    pointerSizeBits := document.target.pointerSizeBits
    endian := document.target.endian
    runtimeDataLayout := some (← evidenceOfTarget document.target) }
  let linkSections ← (← sourceLinkSections document.source).mapM sectionDeclaration
  let material : Input.SourceMaterial := {target,declarations,genericLayers := layers,
    linkSections := some linkSections}
  material.validate
  return material

/-- Decoder-only entry for the original finite source text/tree. Its result
contains typed data exclusively; no source JSON survives this boundary. -/
def decodeTypedSourceMaterial (source : Json) : Except String Input.SourceMaterial := do
  typedSourceMaterial (← decode source)

end Miri.Frontend.Foundation
