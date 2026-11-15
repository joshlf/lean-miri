import Miri.Frontend.Foundation

/-! Pure size/ABI alignment queries over structural foundation material.
The integer defaults and overrides follow pinned rustc_abi/src/lib.rs,
TargetDataLayout::{default,parse_from_llvm_datalayout_string,obj_size_bound};
array sizing follows rustc_abi/src/layout.rs::layout_of_array_like.
This is deliberately not a Rust aggregate field-layout implementation. -/
namespace Miri.Frontend.Foundation

structure FoundationLayout where
  size : Nat
  align : Nat
  deriving Repr, DecidableEq

private def objectBound (target : Target) : Except String Nat :=
  match target.pointerSizeBits with
  | 16 => pure (2 ^ 15)
  | 32 => pure (2 ^ 31)
  | 64 => pure (2 ^ 61)
  | _ => throw "unsupported target pointer width for object size bound"

/-- ABI integer alignment, in bytes. Defaults here are rustc's documented
parser defaults, not host ABI guesses. Preferred alignments do not affect ABI. -/
private def integerAlign (target : Target) (width : Nat) : Except String Nat := do
  let mut result := match width with
    | 8 => 1 | 16 => 2 | 32 => 4 | 64 => 4 | 128 => 4 | _ => 0
  if result == 0 then throw "unsupported integer alignment width"
  let mut largest := 64
  for spec in target.dataLayout.splitOn "-" do
    let parts := spec.splitOn ":"
    let head := parts.head!
    if head.startsWith "i" then
      let some bits := (head.drop 1).toString.toNat? |
        throw "invalid target integer data layout"
      let some text := parts[1]? | throw "missing target integer ABI alignment"
      let some alignmentBits := text.toNat? | throw "invalid target ABI alignment"
      -- Align::from_bits rounds up to bytes and requires a power of two.
      let bytes := (alignmentBits + 7) / 8
      let bytes := max 1 bytes
      unless bytes &&& (bytes - 1) == 0 && bytes < 2 ^ 30 do
        throw "invalid target integer ABI alignment"
      if width == bits then result := bytes
      if bits >= largest && bits <= 128 then
        largest := bits
        if width == 128 then result := bytes
  return result

private def integerWidth (target : Target) (kind name : String) : Except String Nat := do
  if (kind == "int" && name == "isize") || (kind == "uint" && name == "usize") then
    return target.pointerSizeBits
  let names := if kind == "int" then #["i8", "i16", "i32", "i64", "i128"]
    else if kind == "uint" then #["u8", "u16", "u32", "u64", "u128"] else #[]
  let widths := #[8, 16, 32, 64, 128]
  for i in [:names.size] do
    if names[i]! == name then return widths[i]!
  throw s!"unsupported foundation integer {kind} {name}"

/-- Compute only requested layouts. Nonempty Rust tuples can reorder fields;
without the complete pinned aggregate algorithm they remain explicit errors.
Pointers, floats, unsized types and nominal types likewise remain unsupported. -/
def layoutOf (target : Target) (ty : ConcreteType) : Except String FoundationLayout := do
  let bound ← objectBound target
  go bound 1024 ty
where
  go (bound fuel : Nat) (ty : ConcreteType) : Except String FoundationLayout := do
    let .succ remaining := fuel | throw "foundation layout recursion exhausted"
    match ty with
    | .primitive kind name =>
      let width ← if kind == "bool" && name == "" then pure 8
        else if kind == "char" && name == "" then pure 32
        else integerWidth target kind name
      let align ← integerAlign target width
      return ⟨width / 8, align⟩
    | .array element length =>
      unless length < 2 ^ target.pointerSizeBits do throw "array length exceeds target usize"
      let elem ← go bound remaining element
      let size := elem.size * length
      unless size < bound do throw "foundation array layout size overflow"
      return ⟨size, elem.align⟩
    | .tuple elements =>
      if elements.isEmpty then return ⟨0, 1⟩
      throw "nonempty Rust tuple layout is unsupported"
    | .pointer _ _ => throw "foundation pointer layout is unsupported"

/-- Resolve and instantiate a finite source type before its demand-time query. -/
def layoutOfType (d : Document) (id : Nat) (types : Array (Option ConcreteType))
    (constants : Array (Option Nat)) : Except String FoundationLayout := do
  layoutOf d.target (← instantiate types constants (← typeExpr d id))

end Miri.Frontend.Foundation
