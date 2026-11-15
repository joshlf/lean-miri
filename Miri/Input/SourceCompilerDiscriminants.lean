import Miri.Input.SourceCompilerRuntime
import Miri.Input.CompilerPrimitiveFacts

/-! Pinned rustc_middle/ty/sty.rs::Ty::{discriminant_ty,
discriminant_for_variant} (1697–1767). Concrete non-enum/non-coroutine types
have u8 discriminant type and no declared discriminant value. This is a type
constructor rule, not a successful default for absent enum/CTFE evidence. -/
namespace Miri.Input.SourceCompilerDiscriminants
open Miri.ABI
private def node (runtime : RuntimeMetadata) (id : Nat) : Except String TypeNode :=
  runtime.node id |>.mapError toString

def layout (runtime : RuntimeMetadata) (id : Nat) : Except String (TyAndLayout TypeId) :=
  go (runtime.source.types.size + 1) id
where
  go (fuel id : Nat) : Except String (TyAndLayout TypeId) := do
    let .succ fuel := fuel | throw "Invalid cyclic source discriminant type graph"
    match (← node runtime id).shape with
    | .patternType inner _ | .unsafeBinder inner _ => go fuel inner
    | .adt data =>
      if data.kind == .enumKind then throw "Unsupported source enum discriminant representation"
      CompilerPrimitiveFacts.primitiveLayout runtime "u8"
    | .coroutine .. => throw "Unsupported source coroutine discriminant representation"
    | .alias .. => throw "Unsupported source discriminant alias normalization"
    | _ => CompilerPrimitiveFacts.primitiveLayout runtime "u8"

def value (runtime : RuntimeMetadata) (id : Nat) (_variant : Nat) :
    Except String (Option (TypeId × U128)) := go (runtime.source.types.size + 1) id
where
  go (fuel id : Nat) : Except String (Option (TypeId × U128)) := do
    let .succ fuel := fuel | throw "Invalid cyclic source discriminant value graph"
    match (← node runtime id).shape with
    | .unsafeBinder inner _ => go fuel inner
    | .adt data =>
      if data.kind == .enumKind then throw "Unsupported source enum discriminant value"
      pure none
    | .coroutine .. => throw "Unsupported source coroutine discriminant value"
    | .alias .. => throw "Unsupported source discriminant alias normalization"
    -- Unlike discriminant_ty, discriminant_for_variant does not unwrap Pat.
    | _ => pure none

def variantCount (runtime : RuntimeMetadata) (id : Nat) : Except String Nat := do
  let .adt data := (← node runtime id).shape
    | throw "Invalid source ADT variant count requested for non-ADT"
  return data.variants.size
end Miri.Input.SourceCompilerDiscriminants
