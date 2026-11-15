import Miri.Frontend.Foundation
import Miri.Frontend.FoundationConst

/-! Join a requested const-generic argument tuple with the source parameter
types before checking all frame-entry required constants. -/

namespace Miri.Frontend.Foundation
open Lean

def requiredScalarArguments (d : Document) (body : Json)
    (constants : Array (Option Nat)) : Except String (Array (Option RequiredScalar)) := do
  let environment ← body.getObjVal? "environment"
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
Only already-material scalar/unit/function values and typed scalar parameters
are supported; unevaluated const MIR never produces a successful answer. -/
def checkRequiredConstants (d : Document) (body : Json)
    (constants : Array (Option Nat)) : Except String Unit := do
  evaluateRequiredConstants d.types d.target.pointerSizeBits body
    (← requiredScalarArguments d body constants)

end Miri.Frontend.Foundation
