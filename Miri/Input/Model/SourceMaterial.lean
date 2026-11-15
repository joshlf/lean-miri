import Miri.Input.Model.SourceDeclarations
import Miri.Input.Model.SourceAbi

/-! Evaluation-local typed source carrier. This first slice retains declaration
identity, target and lexical generic slots. No JSON value is retained. Generic
MIR, type expressions and semantic constraints are not represented by this
slice and their demand APIs must return Unsupported; these rows certify neither
an executable body nor an ABI. -/
namespace Miri.Input
namespace SourceMaterial
abbrev ItemKind := SourceDeclarations.ItemKind
abbrev ItemDeclaration := SourceDeclarations.ItemDeclaration
abbrev Target := SourceDeclarations.Target
abbrev GenericParameter := SourceDeclarations.GenericParameter
abbrev GenericLayer := SourceDeclarations.GenericLayer

/-- Explicit absence, with no constructor pretending unsupported material is
an empty known source body/type/constraint table. -/
inductive Unavailable where
  | unsupported
  deriving Repr, DecidableEq
end SourceMaterial

structure SourceMaterial where
  target : SourceMaterial.Target
  declarations : Array SourceMaterial.ItemDeclaration
  genericLayers : Array SourceMaterial.GenericLayer
  abi : Option SourceAbi.Material := none
  genericMir : SourceMaterial.Unavailable := .unsupported
  typeExpressions : SourceMaterial.Unavailable := .unsupported
  constraints : SourceMaterial.Unavailable := .unsupported
  deriving Repr, DecidableEq

namespace SourceMaterial

def validate (material : Input.SourceMaterial) : Except String Unit := do
  let target := material.target
  unless !target.triple.isEmpty && !target.architecture.isEmpty &&
      !target.dataLayout.isEmpty && target.pointerSizeBits > 0 && target.pointerSizeBits % 8 == 0 &&
      (target.endian == "little" || target.endian == "big") do
    throw "typed source target declaration invalid"
  if let some evidence := target.runtimeDataLayout then
    unless evidence.llvmDataLayout == target.dataLayout && evidence.pointerWidthBits == target.pointerSizeBits &&
        evidence.endian == target.endian do throw "typed source target evidence disagrees with declaration"
  let mut seen : Array DefinitionId := #[]
  for declaration in material.declarations do
    unless declaration.definition.crateIndex < 2^32 && declaration.definition.index < 2^32 &&
        !declaration.path.isEmpty && !seen.contains declaration.definition do
      throw "typed source Item declaration identity/path invalid or duplicated"
    let parameters ← SourceDeclarations.fullParameters material.genericLayers declaration.definition
    unless parameters == declaration.parameters do throw "typed source Item full generic slots disagree"
    seen := seen.push declaration.definition
  for layer in material.genericLayers do
    let _ ← SourceDeclarations.fullParameters material.genericLayers layer.owner
  return ()

end SourceMaterial
end Miri.Input
