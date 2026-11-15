import Miri.Input.SourceCompilerWorld
import Miri.Input.Model.SourceMir

/-! Typed MIR place projection from the current canonical type graph. Supplied
source field types are checked against the structural projection; they never
replace an unavailable type path. No source JSON or compiler answer is used. -/
namespace Miri.Input.SourceMirPlaces
private def shape (world : SourceCompilerWorld.World) (id : Nat) : Except String TypeShape := do
  let some row := world.canonical.types[id]? | throw "Invalid source place type handle"
  unless row.id == id do throw "Invalid source place type/index identity"
  return row.shape
private def fieldType (world : SourceCompilerWorld.World) (base index : Nat) : Except String Nat := do
  match ← shape world base with
  | .tuple fields =>
    let some ty := fields[index]? | throw "Invalid source tuple field index"
    pure ty
  | .closure _ args count =>
    unless index < count do throw "Invalid source closure field index"
    let some (.Type upvars) := args.back? | throw "Invalid source closure upvars argument"
    let .tuple fields ← shape world upvars | throw "Invalid source closure upvars type"
    unless fields.size == count do throw "Invalid source closure capture count"
    let some ty := fields[index]? | throw "Invalid source closure capture index"
    pure ty
  | .adt adt =>
    unless adt.kind == .structKind || adt.kind == .unionKind do
      throw "Unsupported source enum place requires checked downcast"
    let [variant] := adt.variants.toList | throw "Invalid source struct/union variant count"
    let some field := variant.fields[index]? | throw "Invalid source nominal field index"
    unless field.index == index do throw "Invalid source nominal field identity"
    pure field.typeId
  | _ => throw "Unsupported source field projection base"

/-- All projection result types are derived from the actual local base. The
compiler source field annotation must name the same canonical type. -/
def lower (world : SourceCompilerWorld.World) (locals : Array Nat)
    (sourceTypes : Array (Option Nat)) (source : SourceMir.Place) : Except String (MIR.Place × PlaceFact) := do
  let some base := locals[source.localId]? | throw "Invalid source place local index"
  let mut current := base
  let mut projection := #[]
  let mut projectionTypes := #[]
  for step in source.projection do
    match step with
    | .deref =>
      let pointee ← match ← shape world current with
        | .rawPointer ty _ | .reference ty _ _ => pure ty
        | _ => throw "Unsupported source dereference base type"
      current := pointee
      projection := projection.push .Deref
    | .field index sourceType =>
      let some supplied := sourceTypes[sourceType]?.join | throw "Unsupported source field type not instantiated"
      let actual ← fieldType world current index
      unless supplied == actual do throw "Invalid source field annotation/structural type mismatch"
      current := actual
      projection := projection.push (.Field index actual)
    | .index indexLocal =>
      let some indexType := locals[indexLocal]? | throw "Invalid source array index local"
      let .uint (.known .usize) ← shape world indexType | throw "Invalid source array index type"
      let element ← match ← shape world current with
        | .array element _ _ | .slice element => pure element
        | _ => throw "Unsupported source index projection base"
      current := element
      projection := projection.push (.Index indexLocal)
    | .unsupported tag => throw s!"Unsupported source place projection {tag}"
    let _ ← shape world current
    projectionTypes := projectionTypes.push current
  let place : MIR.Place := ⟨source.localId,projection⟩
  return (place,⟨place,current,projectionTypes⟩)
end Miri.Input.SourceMirPlaces
