import Miri.Input.Model.SourceVTables
import Miri.Input.JsonReader

namespace Miri.Input.SourceVTablesDecoder
open JsonReader

private structure Fields where
  principal : Option (Option Nat) := none
  ownMethods : Option (Array Nat) := none
  superTraits : Option (Array Nat) := none
  owner : Option Nat := none
  definition : Option Nat := none
  instanceId : Option (Option Nat) := none
  typeId : Option Nat := none
  dropInstance : Option Nat := none
  methods : Option (Array SourceVTableMethod) := none

private def objectTrait : Parser SourceObjectTrait := do
  let p ← object ({} : Fields) fun p key => do
    match key with
    | "principal" => return {p with principal := some (some (← natural))}
    | "own_methods" => return {p with ownMethods := some (← array natural)}
    | "super_traits" => return {p with superTraits := some (← array natural)}
    | _ => skipValue; return p
  let some principal ← required p.principal "principal" | fail "object trait principal is null"
  return ⟨principal,← required p.ownMethods "own_methods",← required p.superTraits "super_traits"⟩

private def method : Parser SourceVTableMethod := do
  let p ← object ({} : Fields) fun p key => do
    match key with
    | "owner" => return {p with owner := some (← natural)}
    | "definition" => return {p with definition := some (← natural)}
    | "instance_id" => return {p with instanceId := some (← nullable natural)}
    | _ => skipValue; return p
  return ⟨← required p.owner "owner",← required p.definition "definition",← required p.instanceId "instance_id"⟩

private def binding : Parser SourceVTableBinding := do
  let p ← object ({} : Fields) fun p key => do
    match key with
    | "type_id" => return {p with typeId := some (← natural)}
    | "principal" => return {p with principal := some (← nullable natural)}
    | "drop_instance" => return {p with dropInstance := some (← natural)}
    | "methods" => return {p with methods := some (← array method)}
    | _ => skipValue; return p
  return ⟨← required p.typeId "type_id",← required p.principal "principal",
    ← required p.dropInstance "drop_instance",← required p.methods "methods"⟩

private structure MaterialFields where
  noTraitVptr : Option Bool := none
  objectTraits : Option (Array SourceObjectTrait) := none
  bindings : Option (Array SourceVTableBinding) := none

def parse : Parser SourceVTableMaterial := do
  let p ← object ({} : MaterialFields) fun p key => do
    match key with
    | "no_trait_vptr" => return {p with noTraitVptr := some (← boolean)}
    | "object_traits" => return {p with objectTraits := some (← array objectTrait)}
    | "bindings" => return {p with bindings := some (← array binding)}
    | _ => skipValue; return p
  return ⟨← required p.noTraitVptr "no_trait_vptr",← required p.objectTraits "object_traits",
    ← required p.bindings "bindings"⟩

def validate (types : Array TypeNode) (definitions : Array DefinitionId)
    (predicates : Array VtablePredicate) (instances : Array InstanceNode)
    (material : SourceVTableMaterial) : Except String Unit := do
  let mut seen : Std.HashSet Nat := {}
  for object in material.objectTraits do
    if seen.contains object.principal then throw "duplicate instantiated object trait declaration"
    seen := seen.insert object.principal
    let some predicate := predicates[object.principal]? | throw "object trait principal is absent"
    unless predicate.kind == .trait do throw "object trait principal is not a trait"
    for method in object.ownMethods do
      unless method < definitions.size do throw "object method definition is absent"
    for parent in object.superTraits do
      unless material.objectTraits.any (·.principal == parent) do throw "object supertrait declaration is absent"
  let mut bindings : Std.HashSet (Nat × Option Nat) := {}
  for binding in material.bindings do
    let key := (binding.typeId,binding.principal)
    if bindings.contains key then throw "duplicate concrete vtable executable binding"
    bindings := bindings.insert key
    unless binding.typeId < types.size do throw "vtable concrete type is absent"
    unless binding.dropInstance < instances.size do throw "vtable drop executable identity is absent"
    if let some principal := binding.principal then
      unless seen.contains principal do throw "vtable principal object declaration is absent"
    let mut methods : Std.HashSet (Nat × Nat) := {}
    for method in binding.methods do
      let key := (method.owner,method.definition)
      if methods.contains key then throw "duplicate vtable method executable binding"
      methods := methods.insert key
      let some owner := material.objectTraits.find? (·.principal == method.owner)
        | throw "vtable method owner is absent"
      unless owner.ownMethods.contains method.definition do throw "vtable method is absent from its owner declaration"
      if let some id := method.instanceId then
        unless id < instances.size do throw "vtable method executable identity is absent"

end Miri.Input.SourceVTablesDecoder
