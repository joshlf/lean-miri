import Miri.Frontend.Foundation
import Miri.Frontend.FoundationConst

/-! Pure demand evaluation for an acyclic unsigned scalar CTFE MIR subset.
Checked arithmetic, scalar comparisons, overflow assertions and switches retain
source control flow. Pinned interpret/operator.rs supplies unsigned operations,
and interpret/step.rs supplies switch/assert order. This subset conservatively
rejects overflow rather than returning a wrapped checked pair. Overflow, uninitialized reads, cycles and unsupported forms
are errors; there is no successful fuel-exhaustion or compiler-answer fallback. -/
namespace Miri.Frontend.Foundation
open Lean

private inductive ConstMirValue where
  | scalar (value : RequiredScalar)
  | pair (first second : Option RequiredScalar)

private def validateConstMirScalar (document : Document) (scalar : RequiredScalar) : Except String Unit :=
  evaluateRequiredConstant document.types document.target.pointerSizeBits #[] (Json.mkObj [
    ("kind",toJson "constant"),("type",toJson scalar.typeId),("value",Json.mkObj [
      ("kind",toJson "scalar"),("bits",toJson (toString scalar.bits)),("size_bytes",toJson scalar.sizeBytes)])])

private def unsignedWidth (document : Document) (scalar : RequiredScalar) : Except String Nat := do
  validateConstMirScalar document scalar
  let some row := document.types[scalar.typeId]? | throw "const MIR type absent"
  let shape ← row.getObjVal? "shape"
  unless (← shape.getObjValAs? String "kind") == "uint" do throw "const MIR arithmetic requires unsigned integer"
  let name ← shape.getObjValAs? String "name"
  unless #["u8","u16","u32","u64","u128","usize"].contains name do throw "unsupported const MIR integer width"
  return scalar.sizeBytes * 8

private def store (locals : Array Nat) (state : Array (Option ConstMirValue))
    (localId : Nat) (value : Option ConstMirValue) : Except String (Array (Option ConstMirValue)) := do
  let some typeId := locals[localId]? | throw "const MIR destination out of bounds"
  if let some (.scalar scalar) := value then
    unless scalar.typeId == typeId do throw "const MIR assignment type mismatch"
  if h : localId < state.size then return state.set localId value h
  else throw "const MIR state out of bounds"

private def readOperand (document : Document) (evaluateConstant : Json → Except String RequiredScalar)
    (locals : Array Nat) (state : Array (Option ConstMirValue)) (operand : Json) :
    Except String (Array (Option ConstMirValue) × RequiredScalar) := do
  let kind ← operand.getObjValAs? String "kind"
  if kind == "constant" then
    let scalar ← evaluateConstant operand
    unless scalar.typeId == (← operand.getObjValAs? Nat "type") do throw "const MIR constant operand type mismatch"
    validateConstMirScalar document scalar
    return (state, scalar)
  unless kind == "copy" || kind == "move" do throw "unsupported const MIR operand"
  let place ← operand.getObjVal? "place"
  let localId ← place.getObjValAs? Nat "local"
  let some _ := locals[localId]? | throw "const MIR operand local out of bounds"
  let some value := state[localId]?.bind id | throw "uninitialized const MIR local"
  let projections ← place.getObjValAs? (Array Json) "projection"
  if projections.isEmpty then
    let .scalar scalar := value | throw "const MIR pair read requires field projection"
    let state ← if kind == "move" then store locals state localId none else pure state
    return (state,scalar)
  unless projections.size == 1 do throw "unsupported const MIR projection chain"
  let some projection := projections[0]? | throw "const MIR projection absent"
  unless (← projection.getObjValAs? String "kind") == "field" do throw "unsupported const MIR projection"
  let field ← projection.getObjValAs? Nat "index"
  let .pair first second := value | throw "const MIR field read from scalar"
  let scalar ← match field with
    | 0 => match first with | some scalar => pure scalar | none => throw "uninitialized const MIR first field"
    | 1 => match second with | some scalar => pure scalar | none => throw "uninitialized const MIR second field"
    | _ => throw "const MIR field out of bounds"
  unless (← projection.getObjValAs? Nat "type") == scalar.typeId do throw "const MIR projected field type mismatch"
  let state ← if kind == "move" then
      store locals state localId (some (if field == 0 then .pair none second else .pair first none))
    else pure state
  validateConstMirScalar document scalar
  return (state,scalar)

private def booleanScalar (document : Document) (typeId : Nat) (value : Bool) : Except String RequiredScalar := do
  let some row := document.types[typeId]? | throw "const MIR boolean type absent"
  unless (← (← row.getObjVal? "shape").getObjValAs? String "kind") == "bool" do
    throw "const MIR expected boolean type"
  return ⟨typeId, if value then 1 else 0, 1⟩

private def rvalue (document : Document) (evaluateConstant : Json → Except String RequiredScalar)
    (locals : Array Nat) (state : Array (Option ConstMirValue)) (destination : Nat) (value : Json) :
    Except String (Array (Option ConstMirValue) × ConstMirValue) := do
  if (← value.getObjValAs? String "kind") == "use" then
    let _ ← value.getObjValAs? Bool "retag"
    let (state,scalar) ← readOperand document evaluateConstant locals state (← value.getObjVal? "operand")
    return (state,.scalar scalar)
  unless (← value.getObjValAs? String "kind") == "binary" do throw "unsupported const MIR rvalue"
  let (state,left) ← readOperand document evaluateConstant locals state (← value.getObjVal? "left")
  let (state,right) ← readOperand document evaluateConstant locals state (← value.getObjVal? "right")
  let width ← unsignedWidth document left
  let _ ← unsignedWidth document right
  unless left.typeId == right.typeId && left.sizeBytes == right.sizeBytes do throw "const MIR binary input type mismatch"
  let some outputType := locals[destination]? | throw "const MIR output local absent"
  let operator ← value.getObjValAs? String "operator"
  let comparison : Option Bool := match operator with
    | "equal" => some (left.bits == right.bits) | "not_equal" => some (left.bits != right.bits)
    | "less_than" => some (left.bits < right.bits) | "less_equal" => some (left.bits ≤ right.bits)
    | "greater_than" => some (left.bits > right.bits) | "greater_equal" => some (left.bits ≥ right.bits)
    | _ => none
  if let some comparison := comparison then
    return (state,.scalar (← booleanScalar document outputType comparison))
  let bits ← match operator with
    | "add" | "add_with_overflow" => pure (left.bits + right.bits)
    | "sub" | "sub_with_overflow" =>
      unless right.bits ≤ left.bits do throw "const MIR integer arithmetic overflow"
      pure (left.bits - right.bits)
    | "mul" | "mul_with_overflow" => pure (left.bits * right.bits)
    | _ => throw "unsupported const MIR binary operator"
  unless bits < 2^width do throw "const MIR integer arithmetic overflow"
  let scalar := {left with bits}
  if #["add_with_overflow","sub_with_overflow","mul_with_overflow"].contains operator then
    let some row := document.types[outputType]? | throw "const MIR checked pair type absent"
    let shape ← row.getObjVal? "shape"
    unless (← shape.getObjValAs? String "kind") == "tuple" do throw "const MIR checked result not pair"
    let elements ← shape.getObjValAs? (Array Nat) "elements"
    unless elements.size == 2 && elements[0]? == some scalar.typeId do throw "const MIR checked pair type mismatch"
    let some boolType := elements[1]? | throw "const MIR overflow flag type absent"
    let flag ← booleanScalar document boolType false
    return (state,.pair (some scalar) (some flag))
  unless outputType == scalar.typeId do throw "const MIR binary output type mismatch"
  return (state,.scalar scalar)

/-- Interpret a demanded const body. Definition recursion/cycle detection belongs
inside evaluateConstant; this evaluator independently rejects cyclic control flow.
The full required list is evaluated before any block, preserving source order. -/
def evaluateConstMir (document : Document) (material : Json)
    (evaluateConstant : Json → Except String RequiredScalar) : Except String RequiredScalar := do
  let locals ← material.getObjValAs? (Array Nat) "locals"
  unless !locals.isEmpty do throw "const MIR return local absent"
  for operand in (← material.getObjValAs? (Array Json) "required_consts") do
    unless (← operand.getObjValAs? String "kind") == "constant" do throw "const MIR required operand is not constant"
    let _ ← readOperand document evaluateConstant locals (Array.replicate locals.size none) operand
  let blocks ← material.getObjValAs? (Array Json) "blocks"
  go blocks (blocks.size + 1) #[] locals (Array.replicate locals.size none) 0
where
  go (blocks : Array Json) (fuel : Nat) (seen : Array Nat) (locals : Array Nat)
      (state : Array (Option ConstMirValue)) (blockId : Nat) : Except String RequiredScalar := do
    if seen.contains blockId then throw "cyclic const MIR control flow unsupported"
    let .succ fuel := fuel | throw "const MIR control flow traversal exhausted"
    let some block := blocks[blockId]? | throw "const MIR branch target out of bounds"
    let mut state := state
    for statement in (← block.getObjValAs? (Array Json) "statements") do
      match ← statement.getObjValAs? String "kind" with
      | "assign" =>
        let place ← statement.getObjVal? "place"
        unless (← place.getObjValAs? (Array Json) "projection").isEmpty do throw "const MIR projected assignment unsupported"
        let localId ← place.getObjValAs? Nat "local"
        let (next,value) ← rvalue document evaluateConstant locals state localId (← statement.getObjVal? "value")
        state ← store locals next localId (some value)
      | "storage_live" | "storage_dead" =>
        state ← store locals state (← statement.getObjValAs? Nat "local") none
      | "nop" => pure ()
      | _ => throw "unsupported const MIR statement"
    let terminator ← block.getObjVal? "terminator"
    let kind ← terminator.getObjValAs? String "kind"
    if kind == "return" then
      let some value := state[0]?.bind id | throw "const MIR return scalar uninitialized"
      let ConstMirValue.scalar scalar := value | throw "const MIR return is not scalar"
      validateConstMirScalar document scalar
      return scalar
    let target ← match kind with
      | "goto" => terminator.getObjValAs? Nat "target"
      | "assert" =>
        unless (← terminator.getObjValAs? String "unwind") == "continue" &&
            (← (← terminator.getObjVal? "message").getObjValAs? String "kind") == "overflow" do
          throw "unsupported const MIR assertion"
        let (next,scalar) ← readOperand document evaluateConstant locals state (← terminator.getObjVal? "condition")
        state := next
        let expected ← booleanScalar document scalar.typeId (← terminator.getObjValAs? Bool "expected")
        unless scalar.bits == expected.bits do throw "const MIR assertion failed"
        terminator.getObjValAs? Nat "target"
      | "switch_int" =>
        let (next,scalar) ← readOperand document evaluateConstant locals state (← terminator.getObjVal? "operand")
        state := next
        validateConstMirScalar document scalar
        let some typeRow := document.types[scalar.typeId]? | throw "const MIR switch type absent"
        let switchKind ← (← typeRow.getObjVal? "shape").getObjValAs? String "kind"
        let limit ← match switchKind with
          | "bool" => pure 2
          | "uint" => pure (2^(← unsignedWidth document scalar))
          | _ => throw "unsupported const MIR switch type"
        let mut target ← terminator.getObjValAs? Nat "otherwise"
        let mut values : Array Nat := #[]
        for entry in (← terminator.getObjValAs? (Array Json) "targets") do
          let some bits := (← entry.getObjValAs? String "value").toNat? | throw "invalid const MIR switch value"
          unless bits < limit && !(values.contains bits) do throw "invalid/duplicate const MIR switch target"
          values := values.push bits
          if scalar.bits == bits then target ← entry.getObjValAs? Nat "target"
        pure target
      | _ => throw "unsupported const MIR terminator"
    go blocks fuel (seen.push blockId) locals state target

end Miri.Frontend.Foundation
