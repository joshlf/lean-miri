import Miri.Frontend.FoundationAllocations
import Miri.Input.Model.SourceAllocations

/-! Decoder-only projection of genuine compiler memory images into typed source
material. JSON is discarded; source/raw identities and provenance remain exact. -/
namespace Miri.Frontend.Foundation

def sourceAllocationMaterial (document : Document) : Except String Input.SourceAllocations.Material := do
  let nodes ← sourceMemoryGraph document
  let images ← nodes.mapM fun node => do
    let some rawId := node.sourceAllocId | throw "source memory raw allocation identity absent"
    let some memory := node.memory | throw "source allocation is not a memory image"
    unless node.kind == .memory do throw "source allocation memory kind mismatch"
    return ({id := node.id,rawId,memory} : Input.SourceAllocations.Image)
  let material : Input.SourceAllocations.Material := ⟨images⟩
  Input.SourceAllocations.validate material
  return material
end Miri.Frontend.Foundation
