import Miri.Frontend.FoundationPointer

/-! Pure region erasure for the closed structural source domain. Pinned rustc
uses erase_regions/normalize_erasing_regions before executable MIR and FnAbi.
Only Static/Erased references occur in this source format; mutability and every
non-region type component remain exact. Original source JSON is retained. -/
namespace Miri.Frontend.Foundation

def eraseRegions (ty : ConcreteType) : Except String ConcreteType := go 1024 ty
where
  go (fuel : Nat) (ty : ConcreteType) : Except String ConcreteType := do
    let .succ fuel := fuel | throw "region erasure recursion exhausted"
    match ty with
    | .primitive k n => return .primitive k n
    | .array element count => return .array (← go fuel element) count
    | .tuple fields => return .tuple (← fields.mapM (go fuel))
    | .pointer kind pointee =>
      let info ← pointerKindInfo kind
      let kind := if info.region.isSome then
          if info.mutability == .Mut then "reference_erased_mut" else "reference_erased_const"
        else kind
      return .pointer kind (← go fuel pointee)
    | .functionPointer inputs output safety abi variadic =>
      return .functionPointer (← inputs.mapM (go fuel)) (← go fuel output) safety abi variadic

/-- HAS_FREE_REGIONS includes ReStatic and excludes ReErased in pinned
rustc_type_ir/sty/mod.rs; composite type flags include their children. -/
def hasErasableRegions (ty : ConcreteType) : Except String Bool := go 1024 ty
where
  go (fuel : Nat) (ty : ConcreteType) : Except String Bool := do
    let .succ fuel := fuel | throw "region flag recursion exhausted"
    match ty with
    | .primitive .. => return false
    | .array element _ => go fuel element
    | .tuple fields => return (← fields.mapM (go fuel)).any id
    | .pointer kind pointee =>
      let info ← pointerKindInfo kind
      return info.region == some .Static || (← go fuel pointee)
    | .functionPointer inputs output .. =>
      return (← go fuel output) || (← inputs.mapM (go fuel)).any id

end Miri.Frontend.Foundation
