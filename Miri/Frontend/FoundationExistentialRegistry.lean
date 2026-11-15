import Miri.Frontend.FoundationTypeRegistry

/-! Document-local existential structural identities. These IDs deliberately
carry no physical layout, vtable, trait-selection or associated-type query
answer. Predicate equalities remain source syntax until such queries exist. -/
namespace Miri.Frontend.Foundation

structure ExistentialRegistry where
  document : Document
  entries : Array (ExistentialType ConcreteType) := #[]

def ExistentialRegistry.start (document : Document) : ExistentialRegistry := ⟨document, #[]⟩

def ExistentialRegistry.intern (registry : ExistentialRegistry) (sourceId : Nat)
    (types : Array (Option ConcreteType) := #[]) (constants : Array (Option Nat) := #[]) :
    Except String (ExistentialRegistry × Nat) := do
  let .dynamicObject source ← instantiate types constants (← typeExpr registry.document sourceId)
    | throw "existential registry demand is not dynamic source"
  for i in [:registry.entries.size] do
    let some entry := registry.entries[i]? | throw "existential registry identity absent"
    if sameExistential (sameConcrete 1024) entry source then return (registry, i)
  return ({registry with entries := registry.entries.push source}, registry.entries.size)

end Miri.Frontend.Foundation
