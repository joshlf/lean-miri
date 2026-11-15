import Miri.Frontend.FoundationTypeRegistry
import Miri.Frontend.FoundationConstAggregate
import Miri.Frontend.FoundationPhysicalTypes
import Miri.Frontend.FoundationNominalRules

/-! Scalar storage projection of an already evaluated source aggregate. Every
nominal layer needs its source-derived physical one-field/offset-zero/scalar
representation and validity range. No type name selects representation. -/
namespace Miri.Frontend.Foundation
open Lean

private def initializedInteger (layout : Input.Layout) (value : RequiredScalar) : Except String Unit := do
  unless layout.sizeBytes == some value.sizeBytes && !layout.uninhabited do throw "const nominal scalar storage size/uninhabited mismatch"
  let some backend := layout.backendRepresentation | throw "const nominal backend source absent"
  unless backend.kind == .scalar do throw "const nominal storage is not scalar"
  let some scalar := backend.scalar | throw "const nominal scalar source absent"
  unless scalar.kind == .initialized && scalar.primitive.kind == .integer do throw "const nominal scalar must be initialized integer"
  let some (first,last) := scalar.validRange | throw "const nominal scalar validity source absent"
  unless (if first ≤ last then first ≤ value.bits && value.bits ≤ last else first ≤ value.bits || value.bits ≤ last) do
    throw "const nominal scalar violates source-derived validity range"

/-- Obtain scalar storage only for validated single-field nominal chains. The
result retains the original outer source type identity for later interning. -/
def sourceConstantScalar (document : Document) (value : SourceConstantValue) : Except String RequiredScalar :=
  go (document.types.size + 1) value
where
  go (fuel : Nat) (value : SourceConstantValue) : Except String RequiredScalar := do
    let .succ fuel := fuel | throw "const aggregate physical traversal exhausted"
    match value with
    | .scalar value =>
      evaluateRequiredConstant document.types document.target.pointerSizeBits #[] (Json.mkObj [
        ("kind",toJson "constant"),("type",toJson value.typeId),("value",Json.mkObj [
          ("kind",toJson "scalar"),("bits",toJson (toString value.bits)),("size_bytes",toJson value.sizeBytes)])])
      return value
    | .structureValue typeId definition children =>
      let [child] := children.toList | throw "const scalar aggregate requires one field"
      let source ← typeExpr document typeId
      let concrete ← instantiate #[] #[] source
      let .nominal actual arguments := concrete | throw "const scalar aggregate nominal type absent"
      unless actual == definition && arguments.isEmpty do throw "const scalar aggregate definition/generic mismatch"
      let fields ← nominalFields document definition arguments
      let [variant] := fields.toList | throw "const scalar aggregate requires single variant"
      let [field] := variant.toList | throw "const scalar aggregate requires single field"
      let fieldType ← instantiate #[] #[] (← typeExpr document child.typeId)
      unless sameConcrete 1024 field fieldType do throw "const scalar aggregate field source mismatch"
      let result ← go fuel child
      let layout ← physicalLayoutOfDocument document concrete
      unless layout.fieldOffsetsBytes == .explicit #[0] && layout.variantsKind == some .single do
        throw "const scalar aggregate requires offset-zero single variant layout"
      let result := {result with typeId}
      initializedInteger layout result
      return result

end Miri.Frontend.Foundation
