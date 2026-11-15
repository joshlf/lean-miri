import Miri.Frontend.FoundationItemResolution
import Miri.Frontend.FoundationInstanceRegistry

namespace Miri.Frontend.Foundation
open Lean

/-- Runtime facts for a declaration-selected concrete unit impl method. All
attributes and names come from original source; no symbol address is invented. -/
def runtimeUnitMethodOfItem (document : Document) (item : ItemTemplate)
    (node : Input.InstanceNode) : Except String Input.Catalog.RuntimeInstance := do
  let resolved ← resolveSourceItem document item.definition item.arguments
  unless resolved.definition == item.definition && resolved.arguments.isEmpty && item.arguments.isEmpty &&
      node.instanceKind == .Item item.definition && node.definitionId == some item.definition && node.genericArgs.isEmpty do
    throw "unit method runtime Item identity mismatch"
  let display ← sourceUnitMethodDisplay document item.definition
  let facts ← item.source.getObjVal? "runtime_source"
  let some name ← facts.getObjValAs? (Option String) "item_name" | throw "unit method source name absent"
  let source ← document.source.getObjVal? "termination_source"
  let methods ← source.getObjValAs? (Array Json) "associated_items"
  let some method := methods[0]? | throw "unit method declaration absent"
  unless (← method.getObjValAs? String "name") == name do throw "unit method name/source mismatch"
  let attrs ← item.source.getObjVal? "function_attributes"
  let track ← attrs.getObjValAs? Bool "track_caller"
  let foreign ← attrs.getObjValAs? Bool "is_foreign"
  unless !track && !foreign && !(← attrs.getObjValAs? Bool "is_drop_glue") &&
      !(← facts.getObjValAs? Bool "rustc_intrinsic") do throw "unit method runtime attributes unsupported"
  let inlineAttribute ← facts.getObjValAs? String "inline"
  unless inlineAttribute ∈ ["none","hint","always","never"] &&
      (← facts.getObjValAs? (Array Json) "target_features").isEmpty do throw "unit method runtime codegen attributes unsupported"
  return {
    instanceId := node.id, requiresCallerLocation := track, display,
    inlineNever := inlineAttribute == "never", targetFeatures := #[], isForeignItem := foreign,
    isClosureLike := false, intrinsicMetadata := some none, itemName := some name,
    codegenSymbolName := some (← facts.getObjValAs? (Option String) "codegen_symbol_name"), symbolName := none }

end Miri.Frontend.Foundation
