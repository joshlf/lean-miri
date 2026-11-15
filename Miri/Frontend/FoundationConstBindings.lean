import Miri.Frontend.Foundation
import Miri.Frontend.FoundationGenericEnvironment
import Miri.Frontend.FoundationConst
import Miri.Frontend.FoundationConstEval

/-! Join a requested const-generic argument tuple with the source parameter
types before checking all frame-entry required constants. -/

namespace Miri.Frontend.Foundation
open Lean

def requiredScalarArguments (d : Document) (body : Json)
    (constants : Array (Option Nat)) : Except String (Array (Option RequiredScalar)) := do
  let environment ← flattenEnvironment d (← body.getObjVal? "environment")
  let parameters ← environment.getObjValAs? (Array Json) "parameters"
  let mut values := Array.replicate constants.size (none : Option RequiredScalar)
  for param in parameters do
    if (← param.getObjValAs? String "kind") == "const" then
      let index ← param.getObjValAs? Nat "index"
      let typeId ← param.getObjValAs? Nat "type"
      let some shape := (d.types[typeId]?).bind (fun row =>
          (row.getObjVal? "shape").toOption) | throw "const parameter type is missing"
      unless (← shape.getObjValAs? String "kind") == "uint" &&
          (← shape.getObjValAs? String "name") == "usize" do
        throw "unsupported required const parameter type"
      let some bits := constants[index]?.bind id | throw "unbound required const parameter"
      if h : index < values.size then
        values := values.set index (some ⟨typeId, bits, d.target.pointerSizeBits / 8⟩) h
      else throw "required const argument index is out of bounds"
  return values

/-- Pure frame-entry check over the complete retained required-constant list.
Already-material scalar/unit/function values, typed scalar parameters and the
supported free scalar const-item source expressions are evaluated in order. -/
def checkRequiredConstants (d : Document) (body : Json)
    (constants : Array (Option Nat)) : Except String Unit := do
  let arguments ← requiredScalarArguments d body constants
  for operand in (← body.getObjValAs? (Array Json) "required_consts") do
    let value ← operand.getObjVal? "value"
    if (← value.getObjValAs? String "kind") == "unevaluated" then
      let _ ← evaluateScalarConstant d operand arguments
    else
      evaluateRequiredConstant d.types d.target.pointerSizeBits arguments operand

end Miri.Frontend.Foundation
