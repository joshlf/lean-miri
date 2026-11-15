import Miri.Frontend.FoundationInstanceRegistry
import Miri.Frontend.FoundationFnAbiRegistry

/-! Source attributes to fixed-interpreter runtime metadata for ordinary root
items. `Instance::print` and `FmtPrinter::print_path_with_generic_args` supply the
restricted diagnostic formatting below; no mangled symbol is invented. Frame
crate IDs/names and definition attributes are finite material, while physical
and ABI identities are computed by the demand-local registries. -/
namespace Miri.Frontend.Foundation
open Lean

/-- Preserve compiler crate identity/name material, rejecting missing joins. -/
def frameMetadataOfSource (document : Document) : Except String Input.Catalog.FrameMetadata := do
  let source ← document.source.getObjVal? "frame_metadata"
  let localCrate ← source.getObjValAs? Nat "local_crate"
  let mut crates : Array (Nat × String) := #[]
  for row in (← source.getObjValAs? (Array Json) "crates") do
    let id ← row.getObjValAs? Nat "crate"
    unless id < 2^32 && !(crates.any (·.1 == id)) do throw "invalid or duplicate frame crate identity"
    crates := crates.push (id, ← row.getObjValAs? String "name")
  unless crates.any (·.1 == localCrate) do throw "local frame crate identity absent"
  for definition in document.definitions do
    let crateId ← definition.getObjValAs? Nat "crate_index"
    unless crates.any (·.1 == crateId) do throw "definition frame crate identity absent"
  return ⟨localCrate, crates⟩

private def scalarArgumentDisplay : ConcreteType → Except String String
  | .primitive "bool" "" => pure "bool"
  | .primitive "char" "" => pure "char"
  | .primitive "uint" name =>
    if name ∈ ["u8", "u16", "u32", "u64", "u128", "usize"] then pure name
    else throw "unsupported runtime instance unsigned argument display"
  | .primitive "int" name =>
    if name ∈ ["i8", "i16", "i32", "i64", "i128", "isize"] then pure name
    else throw "unsupported runtime instance signed argument display"
  | _ => throw "unsupported runtime instance argument display"

/-- Runtime facts for a generated ordinary Item identity. Generic display is
restricted to one primitive type argument, and definition paths to local root
functions with unambiguous ordinary names. Symbol mangling is not implemented:
`symbolName = none` retains the genuine absent-query boundary for later demands. -/
private def runtimeInstanceOfItem (document : Document) (item : ItemTemplate)
    (node : Input.InstanceNode) : Except String Input.Catalog.RuntimeInstance := do
  let some definition := document.definitions[item.definition]? | throw "runtime source definition absent"
  unless node.instanceKind == .Item item.definition &&
      node.definitionId == some item.definition do throw "runtime source instance identity mismatch"
  unless (← definition.getObjValAs? String "kind") == "fn" do
    throw "runtime instance requires ordinary function source kind"
  let facts ← item.source.getObjVal? "runtime_source"
  unless (← facts.getObjValAs? Bool "is_local_root") do
    throw "runtime instance requires local root function source"
  let frame ← frameMetadataOfSource document
  unless (← definition.getObjValAs? Nat "crate_index") == frame.localCrate do
    throw "runtime instance local crate mismatch"
  let some name ← facts.getObjValAs? (Option String) "item_name"
    | throw "runtime instance item name absent"
  unless (← definition.getObjValAs? String "path") == name do
    throw "runtime instance nontrivial definition path display unsupported"
  let display ← match item.arguments.toList with
    | [] => pure name
    | [.type ty] => do pure (name ++ "::<" ++ (← scalarArgumentDisplay ty) ++ ">")
    | _ => throw "runtime instance generic display unsupported"
  let attrs ← item.source.getObjVal? "function_attributes"
  let track ← attrs.getObjValAs? Bool "track_caller"
  let foreign ← attrs.getObjValAs? Bool "is_foreign"
  unless !track && !foreign do throw "runtime instance requires ordinary nonforeign item"
  unless !(← facts.getObjValAs? Bool "rustc_intrinsic") do
    throw "runtime instance intrinsic definition unsupported"
  let inlineAttribute ← facts.getObjValAs? String "inline"
  unless inlineAttribute ∈ ["none", "hint", "always", "never"] do
    throw "runtime instance inline attribute unsupported"
  -- Foundation export rejects nonempty source target_features before capture.
  let targetFeatures ← facts.getObjValAs? (Array Json) "target_features"
  unless targetFeatures.isEmpty do throw "runtime instance target features unsupported"
  let symbol ← facts.getObjValAs? (Option String) "codegen_symbol_name"
  return {
    instanceId := node.id
    requiresCallerLocation := track
    display
    inlineNever := inlineAttribute == "never"
    targetFeatures := #[]
    isForeignItem := foreign
    isClosureLike := false -- source kind is exactly an ordinary free function
    intrinsicMetadata := some none
    itemName := some name
    codegenSymbolName := some symbol
    symbolName := none
  }

structure RuntimeItemComponents where
  registry : InstanceRegistry
  abi : Input.FunctionAbi
  runtime : Input.Catalog.RuntimeInstance
  frames : Input.Catalog.FrameMetadata
  instanceAbi : Input.Catalog.InstanceAbi

/-- Fresh single-item ABI/instance/runtime component construction. ABI index zero
is the index of this returned single ABI pool, with no extra variadic arguments.
This introduces no allocation IDs and does not construct a process entry. -/
def buildRuntimeItem (document : Document) (definition : Nat)
    (arguments : Array ItemArgument) : Except String RuntimeItemComponents := do
  let item ← instantiateItem document definition arguments
  let (physical, abi) ← rustFunctionAbiOfItem document definition arguments
  let registry ← InstanceRegistry.start physical
  let (registry, node) ← registry.intern definition arguments
  let runtime ← runtimeInstanceOfItem document item node
  let frames ← frameMetadataOfSource document
  let instanceAbi : Input.Catalog.InstanceAbi := ⟨node.id, #[], 0⟩
  return ⟨registry, abi, runtime, frames, instanceAbi⟩

end Miri.Frontend.Foundation
