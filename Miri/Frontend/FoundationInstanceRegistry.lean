import Miri.Frontend.FoundationInstance
import Miri.Frontend.FoundationPhysicalRegistry

/-! Demand-local instance identities for explicitly selected ordinary functions.
Pinned `Instance::new_raw` pairs Item with its complete generic arguments; it
performs no trait resolution. Definition references preserve the finite source
DefId table. Instance/body numbers below are fresh Lean-local dense pool indices,
not rustc global IDs. Pending body slots must be filled before execution. -/
namespace Miri.Frontend.Foundation
open Lean

structure InstanceRegistry where
  physical : PhysicalTypeRegistry
  definitions : Array Input.DefinitionId
  instances : Array Input.InstanceNode := #[]
  /-- Exact source definition associated with each reserved body slot. -/
  bodyDefinitions : Array Nat := #[]

namespace InstanceRegistry

def start (physical : PhysicalTypeRegistry) : Except String InstanceRegistry := do
  let mut definitions : Array Input.DefinitionId := #[]
  for h : i in [:physical.registry.document.definitions.size] do
    let row := physical.registry.document.definitions[i]
    unless (← row.getObjValAs? Nat "definition_id") == i do
      throw "instance registry requires dense source definition references"
    let definition : Input.DefinitionId := {
      crateIndex := ← row.getObjValAs? Nat "crate_index"
      index := ← row.getObjValAs? Nat "index" }
    unless definition.crateIndex < 2^32 && definition.index < 2^32 do
      throw "source DefId exceeds rustc index width"
    unless !definitions.contains definition do throw "duplicate source DefId"
    definitions := definitions.push definition
  return { physical, definitions }

/-- Intern one explicit ordinary Item request. Full arguments, required constants
and predicates are checked by instantiateItem. Only source `fn` definitions with
no promoted bodies are supported; associated methods require additional dispatch
classification. No caller-supplied InstanceNode or DefinitionRef is accepted. -/
def intern (registry : InstanceRegistry) (definition : Nat)
    (arguments : Array ItemArgument) : Except String (InstanceRegistry × Input.InstanceNode) := do
  let document := registry.physical.registry.document
  let item ← instantiateItem document definition arguments
  let some sourceDefinition := document.definitions[definition]?
    | throw "missing instance source definition"
  unless (← sourceDefinition.getObjValAs? String "kind") == "fn" do
    throw "instance registry requires ordinary function source kind"
  unless (← item.source.getObjValAs? Nat "promoted_count") == 0 do
    throw "instance registry promoted body construction is unsupported"
  let some _ := registry.definitions[definition]? | throw "missing preserved source DefId"
  let mut physical := registry.physical
  let mut genericArgs : Array MIR.GenericArg := #[]
  for argument in arguments do
    match argument with
    | .type ty =>
      let (next, typeId) ← physical.intern ty
      physical := next
      genericArgs := genericArgs.push (.Type typeId)
    | .constant bits =>
      -- instantiateItem accepts only typed usize const parameters and checks
      -- their target-width bound. Reuse the exact physical usize type identity.
      let (next, typeId) ← physical.intern (.primitive "uint" "usize")
      physical := next
      let target ← runtimeTargetOfTarget document.target
      let width := target.base.pointerWidth.bits.toNat / 8
      let constant := MIR.TypeConst.Value typeId ⟨#[.Leaf bits width], 0⟩
      let constantId ← match physical.typeConstants.findIdx? (· == constant) with
        | some id => pure id
        | none => do
          let id := physical.typeConstants.size
          physical := { physical with typeConstants := physical.typeConstants.push constant }
          pure id
      genericArgs := genericArgs.push (.Const constantId)
  for node in registry.instances do
    if node.instanceKind == .Item definition && node.genericArgs == genericArgs then
      return ({ registry with physical }, node)
  let bodyId := registry.bodyDefinitions.size
  let node : Input.InstanceNode := {
    instanceKind := .Item definition
    genericArgs
    id := registry.instances.size
    kind := .instanceMir
    defPath := some (← sourceDefinition.getObjValAs? String "path")
    definitionId := some definition
    bodyId := some bodyId
    promotedBodies := #[] }
  let registry := { registry with
    physical := physical
    instances := registry.instances.push node
    bodyDefinitions := registry.bodyDefinitions.push definition
  }
  return (registry, node)

end InstanceRegistry
end Miri.Frontend.Foundation
