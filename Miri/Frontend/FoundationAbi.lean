import Miri.Frontend.FoundationLayout

/-! Demand-time components of the pinned Rust ABI algorithm.

Sources: rustc_target/src/callconv/mod.rs::{ArgAbi::new,adjust_for_rust_abi}
and rustc_middle/src/ty/layout.rs::fn_can_unwind, revision
8144389c895da997dbdecaa635e41d6a50be6ffd. These components do not construct
`Input.FunctionAbi`: mode shapes omit attributes and physical layout identities.
The architecture and unwind facts below must come from finite compiler source
material; they must not be inferred from the host or the target triple. -/
namespace Miri.Frontend.Foundation

/-- Source/session facts consumed by `fn_can_unwind` for an ordinary Rust-ABI
instance. Foreign-item and drop-glue facts are retained even though ordinary
Rust definitions normally make these branches trivial. -/
structure RustUnwindFacts where
  hasDefinition : Bool
  neverUnwind : Bool
  panicUnwinds : Bool
  foreignItem : Bool
  panicInDropUnwinds : Bool
  dropGlue : Bool
  deriving Repr, DecidableEq

/-- The Rust-family branch of the pinned `fn_can_unwind` algorithm. This does
not compute definition attributes or establish that supplied facts are genuine. -/
def rustCanUnwind (facts : RustUnwindFacts) : Bool :=
  if facts.hasDefinition && (facts.neverUnwind ||
      (!facts.panicUnwinds && !facts.foreignItem) ||
      (!facts.panicInDropUnwinds && facts.dropGlue)) then false
  else facts.panicUnwinds

theorem rustCanUnwind_panicAbort (facts : RustUnwindFacts)
    (h : facts.panicUnwinds = false) : rustCanUnwind facts = false := by
  simp [rustCanUnwind, h]

theorem rustCanUnwind_noDefinition (facts : RustUnwindFacts)
    (h : facts.hasDefinition = false) : rustCanUnwind facts = facts.panicUnwinds := by
  simp [rustCanUnwind, h]

/-- Read only finite source/session facts, never a precomputed unwind answer.
The caller supplies the requested body's source row from the same document. -/
def rustUnwindFactsOfSource (source body : Lean.Json) : Except String RustUnwindFacts := do
  let compilation ← source.getObjVal? "compilation"
  let strategy ← compilation.getObjValAs? String "panic_strategy"
  let dropStrategy ← compilation.getObjValAs? String "panic_in_drop"
  unless (strategy == "unwind" || strategy == "abort") &&
      (dropStrategy == "unwind" || dropStrategy == "abort") do
    throw "invalid foundation panic strategy"
  let attrs ← body.getObjVal? "function_attributes"
  return {
    hasDefinition := true
    neverUnwind := ← attrs.getObjValAs? Bool "never_unwind"
    panicUnwinds := strategy == "unwind"
    foreignItem := ← attrs.getObjValAs? Bool "is_foreign"
    panicInDropUnwinds := dropStrategy == "unwind"
    dropGlue := ← attrs.getObjValAs? Bool "is_drop_glue"
  }

/-- A projection of pass modes, deliberately excluding optimization attributes,
cast noundef, address spaces and physical layout IDs. It cannot be used as a
replacement for genuine interpreter `FnAbi` evidence. -/
inductive RustModeShape where
  | ignore
  | direct (zeroExtendBool : Bool)
  | pair
  | integerCast (sizeBytes : Nat)
  | indirect
  deriving Repr, DecidableEq

/-- Supported scalar, array and pointer Rust ABI mode shapes on x86_64.
The architecture-specific pre-adjustment is empty on this architecture. Shared
str references have scalar-pair shape; their attributes remain separately guarded
by source optimization/position facts. Floats, mutable references, nonempty
tuples, foreign ABIs and other architectures fail closed.
`layoutOf` supplies the supported scalar/array size checks before classification.
No complete FnAbi or attribute equivalence is claimed. -/
private def rustModeCore (target : Target) (architecture : String)
    (isReturn : Bool) (ty : ConcreteType)
    (query : ConcreteType → Except String FoundationLayout) : Except String RustModeShape := do
  unless architecture == "x86_64" do
    throw "foundation Rust ABI mode shape requires explicit x86_64 architecture"
  unless target.pointerSizeBits == 64 do
    throw "foundation x86_64 Rust ABI requires 64-bit pointers"
  if let .primitive "str" "" := ty then
    throw "unsized str Rust ABI mode shape is unsupported"
  if let .dynamicObject _ := ty then
    throw "unsized dynamic object Rust ABI mode shape is unsupported"
  let layout ← query ty
  if layout.size == 0 then return .ignore
  match ty with
  | .patternNotNull _ => throw "general constrained-pattern Rust ABI unsupported"
  | .primitive kind _ => return .direct (kind == "bool")
  | .array _ _ =>
    if isReturn && layout.size > 2 * (target.pointerSizeBits / 8) then return .indirect
    if layout.size <= target.pointerSizeBits / 8 then return .integerCast layout.size
    return .indirect
  | .tuple _ => throw "nonzero tuple Rust ABI mode shape is unsupported"
  | .pointer kind pointee =>
    let info ← pointerKindInfo kind
    if info.region.isSome && info.mutability != .Not then
      throw "mutable-reference Rust ABI attributes are unsupported"
    match pointee with
    | .primitive "str" "" | .dynamicObject _ =>
      unless info.region.isSome do throw "wide raw-pointer Rust ABI mode shape is unsupported"
      return .pair
    | _ => pure ()
    return .direct false
  | .dynamicObject _ => throw "dynamic object ABI mode unsupported"
  | .functionPointer .. => return .direct false

/-- Target-only mode queries cannot assert unavailable dyn declaration evidence. -/
def rustModeShape (target : Target) (architecture : String) (isReturn : Bool)
    (ty : ConcreteType) : Except String RustModeShape :=
  rustModeCore target architecture isReturn ty (layoutOf target)

/-- Use finite declaration material when a dyn pointer needs its metadata layout. -/
def rustModeShapeOfDocument (d : Document) (isReturn : Bool) (ty : ConcreteType) : Except String RustModeShape :=
  rustModeCore d.target d.target.architecture isReturn ty (layoutOfDocument d)

/-- Instantiate the requested finite type before computing its mode projection. -/
def rustModeShapeOfType (d : Document) (architecture : String) (isReturn : Bool)
    (id : Nat) (types : Array (Option ConcreteType)) (constants : Array (Option Nat)) :
    Except String RustModeShape := do
  rustModeShape d.target architecture isReturn
    (← instantiate types constants (← typeExpr d id))

end Miri.Frontend.Foundation
