import Miri.Frontend.FoundationBridge
import Miri.Frontend.FoundationPointer

/-! Checked syntax construction for reference/closure/unsize rvalues. Physical
identities and closure field material are explicit joins; unavailable joins
reject. Constructing Cast.Unsize does not provide a vtable or a successful cast
answer: the unchanged interpreter must still demand its compiler evidence. -/
namespace Miri.Frontend.Foundation
open Lean

structure SourcePlaceTyping where
  place : MIR.Place
  type : ConcreteType
  projectionTypes : Array ConcreteType

structure RvalueSourceJoins where
  sourceType : Nat → Except String ConcreteType := fun _ => .error "rvalue source type join unavailable"
  physicalType : ConcreteType → Except String Nat := fun _ => .error "rvalue physical type join unavailable"
  /-- Exact closure type and ordered upvar types, instantiated from source. -/
  closureType : Nat → Array Json → Except String (ConcreteType × Array ConcreteType) :=
    fun _ _ => .error "closure type/upvar source join unavailable"

structure JoinedRvalue where
  value : MIR.Rvalue
  type : ConcreteType
  places : Array SourcePlaceTyping

/-- Dereference-only source places. Every intermediate type is retained for
BodyCore's checked projected-place compiler fact join. -/
def lowerSourcePlace (localTypes : Array ConcreteType) (source : Json) :
    Except String SourcePlaceTyping := do
  let localId ← source.getObjValAs? Nat "local"
  let some initial := localTypes[localId]? | throw "rvalue source local absent"
  let mut type := initial
  let mut projection := #[]
  let mut projectionTypes := #[]
  for step in (← source.getObjValAs? (Array Json) "projection") do
    unless (← step.getObjValAs? String "kind") == "deref" do
      throw "rvalue source projection unsupported"
    let .pointer kind pointee := type | throw "rvalue dereference source is not a pointer"
    let _ ← pointerKindInfo kind
    type := pointee
    projection := projection.push .Deref
    projectionTypes := projectionTypes.push type
  return ⟨⟨localId, projection⟩, type, projectionTypes⟩

private def lowerOperand (prepared : PreparedItem)
    (constant : Json → Except String (MIR.ConstOperand × ConcreteType)) (source : Json) :
    Except String (MIR.Operand × ConcreteType × Array SourcePlaceTyping) := do
  match ← source.getObjValAs? String "kind" with
  | "copy" | "move" =>
    let place ← lowerSourcePlace prepared.item.localTypes (← source.getObjVal? "place")
    let op := if (← source.getObjValAs? String "kind") == "copy" then
        MIR.Operand.Copy place.place else .Move place.place
    return (op, place.type, #[place])
  | "constant" =>
    let (operand, type) ← constant source
    return (.Constant operand, type, #[])
  | _ => throw "joined rvalue operand unsupported"

/-- Preserve exact source constructors; no allocation, borrow permission,
unsize/vtable query or aggregate layout is evaluated by this syntax function. -/
def lowerJoinedRvalue (prepared : PreparedItem) (joins : RvalueSourceJoins)
    (constant : Json → Except String (MIR.ConstOperand × ConcreteType)) (source : Json) :
    Except String JoinedRvalue := do
  match ← source.getObjValAs? String "kind" with
  | "ref" =>
    unless (← source.getObjValAs? String "borrow_kind") == "shared" do
      throw "joined rvalue borrow kind unsupported"
    let region ← source.getObjValAs? String "region"
    unless region == "static" || region == "erased" do throw "joined rvalue borrow region unsupported"
    let place ← lowerSourcePlace prepared.item.localTypes (← source.getObjVal? "place")
    -- prepareItem erases regions before executable MIR construction.
    return ⟨.Ref .Erased .Shared place.place,
      .pointer "reference_erased_const" place.type, #[place]⟩
  | "cast_unsize" =>
    let (operand, sourceType, places) ← lowerOperand prepared constant (← source.getObjVal? "operand")
    let target ← joins.sourceType (← source.getObjValAs? Nat "target")
    let .pointer kind _ := sourceType | throw "unsize source is not a pointer"
    let .pointer targetKind _ := target | throw "unsize target is not a pointer"
    unless kind == targetKind do throw "unsize pointer identity adjustment unsupported"
    let coercionSource ← match ← source.getObjValAs? String "source" with
      | "implicit" => pure MIR.CoercionSource.Implicit
      | "as_cast" => pure .AsCast
      | _ => throw "unsize coercion source unsupported"
    return ⟨.Cast (.PointerCoercion .Unsize coercionSource) operand (← joins.physicalType target), target, places⟩
  | "aggregate_closure" =>
    let definition ← source.getObjValAs? Nat "definition"
    let argumentsSource ← source.getObjValAs? (Array Json) "arguments"
    let (type, captures) ← joins.closureType definition argumentsSource
    let mut arguments := #[]
    for argument in argumentsSource do
      unless (← argument.getObjValAs? String "kind") == "type" do
        throw "closure generic argument kind unsupported"
      arguments := arguments.push (.Type (← joins.physicalType
        (← joins.sourceType (← argument.getObjValAs? Nat "type"))) : MIR.GenericArg)
    let operandsSource ← source.getObjValAs? (Array Json) "operands"
    unless operandsSource.size == captures.size do throw "closure capture source count mismatch"
    let mut operands := #[]
    let mut places := #[]
    for (operandSource, capture) in operandsSource.zip captures do
      let (operand, actual, facts) ← lowerOperand prepared constant operandSource
      unless sameConcrete 1024 actual capture do throw "closure capture source type mismatch"
      operands := operands.push operand
      places := places ++ facts
    return ⟨.Aggregate (.Closure definition arguments) operands, type, places⟩
  | _ => throw "joined foundation rvalue unsupported"

end Miri.Frontend.Foundation
