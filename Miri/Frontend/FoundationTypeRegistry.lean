import Miri.Frontend.FoundationLayout

/-! Document-local type interning from pure foundation queries.  The returned
IDs are Lean identities for explicitly requested monomorphic types, not rustc
type or layout IDs.  The registry is an immutable value owned by one document. -/

namespace Miri.Frontend.Foundation

def sameConcrete : Nat → ConcreteType → ConcreteType → Bool
  | 0, _, _ => false
  | _+1, .primitive k n, .primitive k' n' => k == k' && n == n'
  | f+1, .array element length, .array element' length' =>
    length == length' && sameConcrete f element element'
  | f+1, .tuple elements, .tuple elements' =>
    elements.size == elements'.size &&
      (elements.zip elements').all (fun (left, right) => sameConcrete f left right)
  | f+1, .pointer kind pointee, .pointer kind' pointee' =>
    kind == kind' && sameConcrete f pointee pointee'
  | f+1, .functionPointer inputs output safety abi variadic,
      .functionPointer inputs' output' safety' abi' variadic' =>
    safety == safety' && abi == abi' && variadic == variadic' &&
      inputs.size == inputs'.size && sameConcrete f output output' &&
      (inputs.zip inputs').all (fun (a,b) => sameConcrete f a b)
  | _, _, _ => false

structure MaterializedType where
  type : ConcreteType
  layout : FoundationLayout

structure TypeRegistry where
  document : Document
  entries : Array MaterializedType := #[]

def TypeRegistry.start (document : Document) : TypeRegistry := { document }

/-- Add an explicitly demanded structural type.  Only types with a complete
supported layout can acquire an ID.  The input and answer are immutable values. -/
def TypeRegistry.intern (registry : TypeRegistry) (ty : ConcreteType) :
    Except String (TypeRegistry × Nat) := do
  let layout ← layoutOf registry.document.target ty
  for i in [:registry.entries.size] do
    let some entry := registry.entries[i]? | throw "type registry index invariant"
    if sameConcrete 1024 entry.type ty then
      unless entry.layout == layout do
        throw "type registry layout contradiction"
      return (registry, i)
  let id := registry.entries.size
  return ({registry with entries := registry.entries.push ⟨ty, layout⟩}, id)

def TypeRegistry.internSource (registry : TypeRegistry) (sourceId : Nat)
    (types : Array (Option ConcreteType)) (constants : Array (Option Nat)) :
    Except String (TypeRegistry × Nat) := do
  let source ← typeExpr registry.document sourceId
  registry.intern (← instantiate types constants source)

end Miri.Frontend.Foundation
