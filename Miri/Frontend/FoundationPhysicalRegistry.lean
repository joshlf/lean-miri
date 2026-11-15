import Miri.Frontend.FoundationPhysicalTypes
import Miri.Frontend.FoundationTypeRegistry

/-! Demand-local physical pools. Every array child and usize length is interned
before its parent. No input document, compiler-fact catalog or executable entry
point is synthesized by these component tables. -/
namespace Miri.Frontend.Foundation

structure PhysicalTypeRegistry where
  registry : TypeRegistry
  types : Array Input.TypeNode := #[]
  layouts : Array Input.Layout := #[]
  typeConstants : Array MIR.TypeConst := #[]

namespace PhysicalTypeRegistry

def start (document : Document) : PhysicalTypeRegistry :=
  { registry := TypeRegistry.start document }

/-- Read the exact document-local type/layout pair, rejecting broken identities. -/
def lookup (r : PhysicalTypeRegistry) (id : Nat) : Except String (Input.TypeNode × Input.Layout) := do
  let some node := r.types[id]? | throw "physical type ID absent"
  unless node.id == id do throw "physical type ID/index mismatch"
  let some layout := r.layouts[node.layoutId]? | throw "physical layout ID absent"
  return (node, layout)

/-- Materialize only supported demanded types, retaining canonical structural
identity through TypeRegistry. Constants are canonical typed usize valtree leaves. -/
def intern (r : PhysicalTypeRegistry) (ty : ConcreteType) :
    Except String (PhysicalTypeRegistry × Nat) := go 1024 r ty
where
  go (fuel : Nat) (r : PhysicalTypeRegistry) (ty : ConcreteType) :
      Except String (PhysicalTypeRegistry × Nat) := do
    let .succ fuel := fuel | throw "physical registry recursion exhausted"
    -- Validate the full parent before adding any recursively demanded material.
    let layout ← physicalLayoutOf r.registry.document.target ty
    for i in [:r.registry.entries.size] do
      let some entry := r.registry.entries[i]? | throw "physical registry entry absent"
      if sameConcrete 1024 entry.type ty then
        let _ ← r.lookup i
        return (r, i)
    let (r, references) ← match ty with
      | .array element count => do
        let (r, elementId) ← go fuel r element
        let (r, usizeId) ← go fuel r (.primitive "uint" "usize")
        let target ← runtimeTargetOfTarget r.registry.document.target
        let width := target.base.pointerWidth.bits.toNat / 8
        let constant := MIR.TypeConst.Value usizeId ⟨#[.Leaf count width], 0⟩
        let mut found := none
        for i in [:r.typeConstants.size] do
          if r.typeConstants[i]? == some constant then found := some i
        let (r, constantId) := match found with
          | some id => (r, id)
          | none => ({ r with typeConstants := r.typeConstants.push constant }, r.typeConstants.size)
        pure (r, some (elementId, constantId))
      | _ => pure (r, none)
    let (registry, id) ← r.registry.intern ty
    unless id == r.types.size && id == r.layouts.size do
      throw "physical registry pool identity mismatch"
    let node ← physicalTypeNode ty id id references
    return ({ r with registry, types := r.types.push node, layouts := r.layouts.push layout }, id)

/-- Resolve source types without changing the identity scheme. -/
def internSource (r : PhysicalTypeRegistry) (sourceId : Nat)
    (types : Array (Option ConcreteType)) (constants : Array (Option Nat)) :
    Except String (PhysicalTypeRegistry × Nat) := do
  let source ← typeExpr r.registry.document sourceId
  r.intern (← instantiate types constants source)

/-- Convert the exact generated row with the existing fixed-interpreter bridge. -/
def runtimeLayout (r : PhysicalTypeRegistry) (id : Nat) : Except String (ABI.TyAndLayout Nat) := do
  let (node, row) ← r.lookup id
  let target ← runtimeTargetOfTarget r.registry.document.target
  return ⟨node.id, ← (Input.RuntimeMetadata.layout target row).mapError toString⟩

end PhysicalTypeRegistry
end Miri.Frontend.Foundation
