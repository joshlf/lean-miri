import Miri.Input.SourceCompilerWorld
import Miri.Input.Model.SourceTypes

/-! Inversion of requested canonical arguments into typed source syntax. No
normalization, layout-equivalence identity or all-pool reconstruction occurs.
Callers must round-trip through source physical interning before using a type. -/
namespace Miri.Input.SourceConcreteTypes
open Miri.Interpreter
abbrev World := SourceCompilerWorld.World
private def integerName (kind : MIR.IntegerKind) (signed : Bool) : Except String String := do
  match signed,kind with
  | true,.i8 => pure "i8" | true,.i16 => pure "i16" | true,.i32 => pure "i32"
  | true,.i64 => pure "i64" | true,.i128 => pure "i128" | true,.isize => pure "isize"
  | false,.u8 => pure "u8" | false,.u16 => pure "u16" | false,.u32 => pure "u32"
  | false,.u64 => pure "u64" | false,.u128 => pure "u128" | false,.usize => pure "usize"
  | _,_ => throw "typed ABI integer kind/tag mismatch"

def scalarConstant (world : World) (width : Nat) (constant : Nat) : Except String (Nat × Nat × Nat) := do
  let some (.Value type tree) := world.canonical.typeConstants[constant]? | throw "typed ABI constant argument is not a value"
  let some row := world.canonical.types[type]? | throw "typed ABI constant type absent"
  unless row.id == type do throw "typed ABI constant type identity mismatch"
  match row.shape with
  | .uint (.known .usize) => pure ()
  | _ => throw "typed ABI constant argument requires usize"
  let [.Leaf bits bytes] := tree.nodes.toList | throw "typed ABI constant argument tree unsupported"
  unless tree.root == 0 && bytes*8 == width && bits < 2^width do throw "typed ABI constant argument width/range invalid"
  return (type,bits,bytes)

def concreteType (world : World) (width : Nat) (typeId : Nat) : Except String SourceTypes.Concrete :=
  go (world.canonical.types.size + 1) #[] typeId
where
  go (fuel : Nat) (active : Array Nat) (typeId : Nat) : Except String SourceTypes.Concrete := do
    let .succ fuel := fuel | throw "typed ABI argument type traversal exhausted"
    unless !active.contains typeId do throw "recursive typed ABI argument unsupported"
    let some row := world.canonical.types[typeId]? | throw "typed ABI argument type absent"
    unless row.id == typeId do throw "typed ABI argument type identity mismatch"
    let child := go fuel (active.push typeId)
    match row.shape with
    | .bool => pure (.primitive "bool" "")
    | .char => pure (.primitive "char" "")
    | .int (.known kind) => return .primitive "int" (← integerName kind true)
    | .uint (.known kind) => return .primitive "uint" (← integerName kind false)
    | .tuple fields => return .tuple (← fields.mapM child)
    | .rawPointer pointee mutable => return .pointer (if mutable == .Mut then "raw_pointer_mut" else "raw_pointer_const") (← child pointee)
    | .array element length constructor =>
      let (_,bits,_) ← scalarConstant world width length
      unless constructor.canonicalValueConstructor && constructor.count == bits do throw "typed ABI array count identity mismatch"
      return .array (← child element) bits
    | .functionPointer signature binders =>
      unless binders.isEmpty && !signature.cVariadic do throw "typed ABI argument function binder/variadic unsupported"
      return .functionPointer (← signature.inputs.mapM child) (← child signature.output) signature.safety signature.abi false
    | _ => throw "typed ABI argument type constructor unsupported"

end Miri.Input.SourceConcreteTypes
