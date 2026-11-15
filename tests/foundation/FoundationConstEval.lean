import Miri.Frontend.FoundationConstOperand
import Miri.Frontend.FoundationConstBindings
open Lean Miri.Frontend.Foundation

private def checked (value : Except String α) : IO α :=
  match value with | .ok result => pure result | .error e => throw (IO.userError e)

def main (args : List String) : IO Unit := do
  let some path := args.head? | throw (IO.userError "expected freshly exported const JSON")
  let input ← checked (Json.parse (← IO.FS.readFile path))
  let document ← checked (decode input)
  let bodies ← checked (input.getObjValAs? (Array Json) "bodies")
  let some body := bodies[0]? | throw (IO.userError "no body")
  let blocks ← checked (body.getObjValAs? (Array Json) "blocks")
  let some block := blocks[0]? | throw (IO.userError "no block")
  let statements ← checked (block.getObjValAs? (Array Json) "statements")
  let some statement := statements[0]? | throw (IO.userError "no assignment")
  let operand ← checked do (← statement.getObjVal? "value").getObjVal? "operand"
  let result ← checked (evaluateScalarConstant document operand)
  let spans ← checked (buildSpanRegistry body)
  let (_, lowered) ← checked (lowerScalarConstantOperand (PhysicalTypeRegistry.start document) spans operand)
  match lowered.value with
  | .Val (.Scalar (.Int bits width)) _ =>
    unless bits == 37 && width == 1 do throw (IO.userError "fixed MIR scalar mismatch")
  | _ => throw (IO.userError "unexpected fixed MIR constant constructor")
  unless result.bits == 37 && result.sizeBytes == 1 do throw (IO.userError "const evaluation mismatch")
  let badValue := Json.mkObj [("kind",toJson "scalar"),("bits",toJson "256"),("size_bytes",toJson (1 : Nat))]
  let required := body.setObjVal! "required_consts" (toJson (#[operand] : Array Json))
  let _ ← checked (checkRequiredConstants document required #[])
  let bad := operand.setObjVal! "value" badValue
  match checkRequiredConstants document (body.setObjVal! "required_consts" (toJson (#[bad] : Array Json))) #[] with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "invalid required constant accepted")
  match evaluateScalarConstant document bad with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "overflowing scalar constant accepted")
  let value ← checked (operand.getObjVal? "value")
  let id ← checked (value.getObjValAs? Nat "definition")
  let some row := document.definitions[id]? | throw (IO.userError "missing const definition")
  let expression := Json.mkObj [("type",toJson result.typeId),("operand",operand),("retag",toJson true)]
  let definitions ← if h : id < document.definitions.size then
    pure (document.definitions.set id (row.setObjVal! "const_expression" expression) h)
    else throw (IO.userError "const definition index out of bounds")
  match evaluateScalarConstant {document with definitions} operand with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "cyclic const definition accepted")
  IO.println "fresh scalar const-item demand and rejection controls passed"
