import Miri.Frontend.FoundationClosure
import Miri.Frontend.FoundationPhysicalRegistry

/-! Source-selected closure representations. IDs belong only to the immutable
physical registry returned here. No closure trait obligation, executable Item,
shim body, vtable or allocation is produced. The initial layout domain is empty
or a single nonzero scalar upvar (the genuine lang_start function pointer).
Pinned rustc_ty_utils/layout.rs maps Closure to default-repr univariant upvars;
rustc_abi/layout.rs preserves the sole filling scalar's backend and niche,
uses offset zero and identity order, and sums the field seed with default zero. -/
namespace Miri.Frontend.Foundation

structure ClosurePhysicalBinding where
  selected : SelectedClosureTemplate
  closureTy : ConcreteType
  typeId : Nat
  fullArguments : Array MIR.GenericArg

/-- Select the exact source template, substitute inherited arguments and intern
all synthetic arguments before the closure. Retain RustCall on its signature
FnPtr. Parent predicates remain obligations for the caller's checked entry.
Successful physical construction alone does not discharge those predicates. -/
def internSourceClosure (physical : PhysicalTypeRegistry) (definition : Nat)
    (parentArguments : Array ItemArgument) :
    Except String (PhysicalTypeRegistry × ClosurePhysicalBinding) := do
  let selected ← selectClosureTemplate physical.registry.document definition parentArguments
  let mut arguments := #[]
  for argument in selected.fullArguments do
    let .type ty := argument | throw "physical closure const/region arguments unsupported"
    arguments := arguments.push ty
  let closureTy := ConcreteType.closure definition arguments
  let (physical, typeId) ← physical.intern closureTy
  let (node, _) ← physical.lookup typeId
  let .closure actualDefinition fullArguments upvarCount := node.shape
    | throw "physical closure shape mismatch"
  let .tuple upvars := selected.tupledUpvars | throw "closure upvars tuple absent"
  unless actualDefinition == definition && upvarCount == upvars.size &&
      fullArguments.size == selected.fullArguments.size do throw "physical closure identity mismatch"
  return (physical, ⟨selected, closureTy, typeId, fullArguments⟩)

end Miri.Frontend.Foundation
