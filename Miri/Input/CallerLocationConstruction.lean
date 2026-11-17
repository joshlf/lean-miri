import Miri.Input.RuntimeMetadata
import Miri.Memory.Allocation

namespace Miri.Input.CallerLocationConstruction
open Miri.ABI Miri.Memory

def initializeFields (runtime : RuntimeMetadata) (location : TyAndLayout TypeId)
    (allocation : Allocation CtfeProvenance Unit) (filename : AllocId) (length : Nat) (line column : UInt32) :
    Except String (Allocation CtfeProvenance Unit) := do
  let pointerSize := Size.fromBits runtime.target.base.pointerWidth.bits
  let mut allocation := allocation
  let file ← RuntimeMetadata.field runtime location 0 |>.mapError toString
  let lineLayout ← RuntimeMetadata.field runtime location 1 |>.mapError toString
  let columnLayout ← RuntimeMetadata.field runtime location 2 |>.mapError toString
  unless file.layout.size.bytes == pointerSize.bytes * 2 && lineLayout.layout.size.bytes == 4 &&
      columnLayout.layout.size.bytes == 4 do throw "caller-location field layouts differ from Location declaration"
  let fileOffset ← location.layout.fields.offset 0 |>.mapError reprStr
  let lineOffset ← location.layout.fields.offset 1 |>.mapError reprStr
  let columnOffset ← location.layout.fields.offset 2 |>.mapError reprStr
  let provenance ← CtfeProvenance.fromAllocId filename |>.mapError reprStr
  let pointer : Pointer CtfeProvenance := ⟨.ZERO,provenance⟩
  let values := #[(fileOffset, Scalar.fromPointer runtime.target.base pointer),
    ((← fileOffset.add pointerSize |>.mapError reprStr), ← Scalar.fromUInt (BitVec.ofNat 128 length) pointerSize |>.mapError toString),
    (lineOffset, ← Scalar.fromUInt (BitVec.ofNat 128 line.toNat) lineLayout.layout.size |>.mapError toString),
    (columnOffset, ← Scalar.fromUInt (BitVec.ofNat 128 column.toNat) columnLayout.layout.size |>.mapError toString)]
  for (offset,value) in values do
    match allocation.writeScalar runtime.target.base (allocRange offset value.size) value with
    | .ok _ updated => allocation := updated
    | .error error _ => throw (toString error)
  pure (allocation.withMutability .Not)

end Miri.Input.CallerLocationConstruction
