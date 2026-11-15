import Miri.Input.Model.Types

/-! Existing finite compiler memory images. Source graph indices, raw rustc
AllocIds, canonical graph indices and runtime AllocIds are separate namespaces.
No allocator frontier, static initializer or byte-interner answer is inferred. -/
namespace Miri.Input.SourceAllocations
structure Image where
  id : Nat
  rawId : UInt64
  memory : AllocationMemory
  deriving Repr, DecidableEq
structure Material where
  images : Array Image
  deriving Repr, DecidableEq

def validate (material : Material) : Except String Unit := do
  let mut rawIds : Array UInt64 := #[]
  for index in [:material.images.size] do
    let some image := material.images[index]? | throw "source memory image absent"
    unless image.id == index && image.rawId.toNat > 0 && image.rawId.toNat < 2^62 &&
        !rawIds.contains image.rawId do throw "source memory graph identity invalid/duplicated"
    rawIds := rawIds.push image.rawId
    for relocation in image.memory.relocations do
      let some target := material.images[relocation.target]? | throw "source memory relocation target absent"
      unless relocation.ctfeProvenance.allocId.value == target.rawId &&
          relocation.ctfeProvenance.immutable == relocation.immutable &&
          relocation.ctfeProvenance.sharedRef == relocation.sharedRef do
        throw "source memory relocation raw identity disagrees with graph target"
  return ()
end Miri.Input.SourceAllocations
