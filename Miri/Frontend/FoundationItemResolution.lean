import Miri.Frontend.FoundationInstance
import Miri.Frontend.FoundationTermination

/-! Resolve only declaration-backed unit trait-method calls. Ordinary function
items retain their identity. A concrete impl method is accepted only after its
exact declaration link has been checked against the complete source headers.
Other associated items and shim/virtual dispatch remain Unsupported. -/
namespace Miri.Frontend.Foundation
open Lean

structure SourceItemResolution where
  sourceDefinition : Nat
  sourceArguments : Array ItemArgument
  definition : Nat
  arguments : Array ItemArgument

private def unitSelection (document : Document) : Except String SourceUnitTraitSelection := do
  let source ← document.source.getObjVal? "termination_source"
  sourceTerminationUnitSelection document (← source.getObjValAs? Nat "definition") (.tuple #[])

/-- Inherent associated functions are explicit Items, not trait selection.
The retained owner link must agree with the checked lexical impl layer. -/
def sourceInherentItem (document : Document) (definition : Nat) : Except String Bool := do
  let headers ← document.source.getObjValAs? (Array Json) "source_function_signatures"
  let candidates := headers.filter fun h => (h.getObjValAs? Nat "definition").toOption == some definition
  if candidates.isEmpty then return false
  unless candidates.size == 1 do throw "duplicate inherent source header"
  let some header := candidates[0]? | throw "inherent source header absent"
  let owner ← header.getObjVal? "owner_declaration"
  unless (← owner.getObjValAs? String "kind") == "inherent_method" do return false
  let implementation ← owner.getObjValAs? Nat "impl_definition"
  let selfType ← owner.getObjValAs? Nat "self_type"
  let some row := document.definitions[implementation]? | throw "inherent impl source absent"
  unless (← row.getObjValAs? String "kind").startsWith "Impl" do throw "inherent owner is not impl"
  let environment ← header.getObjVal? "environment"
  let _ ← flattenEnvironment document environment
  let layers ← environment.getObjValAs? (Array Json) "layers"
  let some layer := layers.find? (fun layer => (layer.getObjValAs? Nat "owner").toOption == some implementation)
    | throw "inherent impl lexical layer absent"
  unless (← layer.getObjValAs? Nat "self_type") == selfType do throw "inherent impl Self source mismatch"
  return true

/-- Resolve the original FnDef identity separately from the selected Item.
Keeping both is necessary: a trait-method FnDef type has Self arguments even
when its concrete implementation method has no own/inherited arguments. -/
def resolveSourceItem (document : Document) (definition : Nat) (arguments : Array ItemArgument) :
    Except String SourceItemResolution := do
  let some row := document.definitions[definition]? | throw "item resolution definition absent"
  match ← row.getObjValAs? String "kind" with
  | "fn" => return ⟨definition,arguments,definition,arguments⟩
  | "assoc_fn" =>
    if ← sourceInherentItem document definition then return ⟨definition,arguments,definition,arguments⟩
    let selected ← unitSelection document
    if definition == selected.traitMethodDefinition then
      let [.type self] := arguments.toList | throw "unit trait method requires exact Self argument"
      let source ← document.source.getObjVal? "termination_source"
      let checked ← sourceTerminationUnitSelection document (← source.getObjValAs? Nat "definition") self
      return ⟨definition,arguments,checked.implementationMethodDefinition,#[]⟩
    if definition == selected.implementationMethodDefinition && arguments.isEmpty then
      return ⟨definition,arguments,definition,#[]⟩
    throw "associated function source selection unsupported"
  | _ => throw "source item kind unsupported"

/-- Derive pinned unit impl method spelling from declaration structure, not an
impl's diagnostic `{impl#N}` path or a cached Instance::print answer. -/
def sourceUnitMethodDisplay (document : Document) (definition : Nat) : Except String String := do
  let selected ← unitSelection document
  unless selected.implementationMethodDefinition == definition do throw "unit method display definition mismatch"
  let some traitRow := document.definitions[selected.traitDefinition]? | throw "unit method trait source absent"
  let source ← document.source.getObjVal? "termination_source"
  let methods ← source.getObjValAs? (Array Json) "associated_items"
  let some method := methods[0]? | throw "unit method name source absent"
  let name ← method.getObjValAs? String "name"
  unless !name.isEmpty && !name.contains ':' do throw "unit method source name unsupported"
  return "<() as " ++ (← traitRow.getObjValAs? String "path") ++ ">::" ++ name

end Miri.Frontend.Foundation
