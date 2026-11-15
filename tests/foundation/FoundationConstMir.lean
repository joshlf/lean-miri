import Miri.Frontend.FoundationConstOperand
import Miri.Frontend.FoundationConstBindings
open Lean Miri.Frontend.Foundation

private def checked (value : Except String α) : IO α := do
  match value with | .ok value => pure value | .error error => throw (IO.userError error)

private def rejected (document : Document) (operand : Json) (expected : String) : IO Unit := do
  match evaluateScalarConstant document operand with
  | .ok _ => throw (IO.userError "invalid const MIR accepted")
  | .error error => unless error == expected do throw (IO.userError s!"unexpected const rejection: {error}")

private def withMir (document : Document) (definition : Nat) (material : Json) : Except String Document := do
  let some row := document.definitions[definition]? | throw "const definition absent"
  let expression ← row.getObjVal? "const_expression"
  if h : definition < document.definitions.size then
    let definitions := document.definitions.set definition (row.setObjVal! "const_expression" (expression.setObjVal! "mir" material)) h
    return {document with definitions}
  else throw "const definition out of bounds"

private def replaceFirst (values : Array Json) (value : Json) : Array Json :=
  values.mapIdx fun index original => if index == 0 then value else original

def main (paths : List String) : IO Unit := do
  let [path, referencePath] := paths | throw (IO.userError "expected fresh source and compiler reference JSON")
  let document ← checked (Json.parse (← IO.FS.readFile path) >>= decode)
  let reference ← checked (Json.parse (← IO.FS.readFile referencePath))
  let some body := document.bodies[0]? | throw (IO.userError "runtime source body absent")
  let blocks ← checked (body.getObjValAs? (Array Json) "blocks")
  let some block := blocks[0]? | throw (IO.userError "runtime block absent")
  let statements ← checked (block.getObjValAs? (Array Json) "statements")
  let some statement := statements[0]? | throw (IO.userError "runtime const statement absent")
  let operand ← checked do (← statement.getObjVal? "value").getObjVal? "operand"
  let result ← checked (evaluateScalarConstant document operand)
  let bits ← checked (reference.getObjValAs? String "bits")
  let size ← checked (reference.getObjValAs? Nat "size_bytes")
  unless toString result.bits == bits && result.sizeBytes == size do
    throw (IO.userError "pure const MIR disagrees with genuine compiler CTFE")
  let _ ← checked (checkRequiredConstants document body #[])
  let spans ← checked (buildSpanRegistry body)
  let (_, lowered) ← checked (lowerScalarConstantOperand (PhysicalTypeRegistry.start document) spans operand)
  match lowered.value with
  | .Val (.Scalar (.Int actual width)) _ =>
    unless actual == result.bits && width == result.sizeBytes do throw (IO.userError "const MIR fixed operand join mismatch")
  | _ => throw (IO.userError "const MIR did not lower to scalar")
  if (← checked (reference.getObjValAs? String "root")) == "sum" then
    let definition ← checked do (← operand.getObjVal? "value").getObjValAs? Nat "definition"
    let some row := document.definitions[definition]? | throw (IO.userError "const source absent")
    let material ← checked do (← row.getObjVal? "const_expression").getObjVal? "mir"
    let blocks ← checked (material.getObjValAs? (Array Json) "blocks")
    let some first := blocks[0]? | throw (IO.userError "CTFE first block absent")
    let statements ← checked (first.getObjValAs? (Array Json) "statements")
    let some assignment := statements[0]? | throw (IO.userError "CTFE checked arithmetic absent")
    let binary ← checked (assignment.getObjVal? "value")
    let right ← checked (binary.getObjVal? "right")
    let raw ← checked (right.getObjVal? "value")
    for (changed, expected) in #[
        (binary.setObjVal! "right" (right.setObjVal! "value" (raw.setObjVal! "bits" (toJson "255"))), "const MIR integer arithmetic overflow"),
        (binary.setObjVal! "right" (right.setObjVal! "value" (raw.setObjVal! "size_bytes" (toJson (2 : Nat)))), "required const scalar width mismatch"),
        (binary.setObjVal! "left" operand, "cyclic const source expression"),
        (binary.setObjVal! "operator" (toJson "div"), "unsupported const MIR binary operator")] do
      let changedBlock := first.setObjVal! "statements" (toJson (replaceFirst statements (assignment.setObjVal! "value" changed)))
      let changedMir := material.setObjVal! "blocks" (toJson (replaceFirst blocks changedBlock))
      rejected (← checked (withMir document definition changedMir)) operand expected
    let terminator ← checked (first.getObjVal? "terminator")
    for (changed, expected) in #[
        (terminator.setObjVal! "target" (toJson (0 : Nat)), "cyclic const MIR control flow unsupported"),
        (terminator.setObjVal! "expected" (toJson true), "const MIR assertion failed")] do
      let changedMir := material.setObjVal! "blocks" (toJson (replaceFirst blocks (first.setObjVal! "terminator" changed)))
      rejected (← checked (withMir document definition changedMir)) operand expected
    let invalid := right.setObjVal! "value" (raw.setObjVal! "size_bytes" (toJson (2 : Nat)))
    rejected (← checked (withMir document definition (material.setObjVal! "required_consts" (toJson #[invalid]))))
      operand "required const scalar width mismatch"
  IO.println s!"const MIR compiler CTFE/required-list/fixed-operand comparison passed: {bits}/{size}"
