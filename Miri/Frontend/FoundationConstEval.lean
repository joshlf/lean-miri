import Miri.Frontend.Foundation
import Miri.Frontend.FoundationConst

/-! Demand evaluation of finite scalar const-item expressions. No rustc query,
allocation, process, mutable state or answer cache participates. The source
subset is a scalar literal or a reference to another free scalar const item;
cycles, generic/promoted constants and other expressions fail closed. -/
namespace Miri.Frontend.Foundation
open Lean

/-- Evaluate a requested source scalar. A bound on definition traversal rejects
cycles; it is not guest execution fuel or a successful evaluation outcome. -/
def evaluateScalarConstant (document : Document) (operand : Json)
    (arguments : Array (Option RequiredScalar) := #[]) : Except String RequiredScalar :=
  go (document.definitions.size + 1) #[] operand
where
  go (fuel : Nat) (seen : Array Nat) (operand : Json) : Except String RequiredScalar := do
    unless (← operand.getObjValAs? String "kind") == "constant" do
      throw "const expression is not a constant operand"
    let typeId ← operand.getObjValAs? Nat "type"
    let value ← operand.getObjVal? "value"
    match ← value.getObjValAs? String "kind" with
    | "unevaluated" =>
      let definition ← value.getObjValAs? Nat "definition"
      unless (← value.getObjValAs? (Array Json) "arguments").isEmpty do
        throw "generic unevaluated const expression unsupported"
      if seen.contains definition then throw "cyclic const source expression"
      let .succ fuel := fuel | throw "const source traversal exhausted"
      let some row := document.definitions[definition]? | throw "const definition out of bounds"
      unless (← row.getObjValAs? String "kind") == "const" do throw "source definition is not a free const"
      let expression ← row.getObjVal? "const_expression"
      -- WithRetag has no pointer provenance to transform for validated scalar integers.
      let _ ← expression.getObjValAs? Bool "retag"
      unless (← expression.getObjValAs? Nat "type") == typeId do
        throw "const definition output type mismatch"
      let result ← go fuel (seen.push definition) (← expression.getObjVal? "operand")
      unless result.typeId == typeId do throw "const expression operand type mismatch"
      return result
    | "scalar" | "value" =>
      evaluateRequiredConstant document.types document.target.pointerSizeBits arguments operand
      let bits ← value.getObjValAs? String "bits"
      let some bits := bits.toNat? | throw "invalid const scalar digits"
      return ⟨typeId, bits, ← value.getObjValAs? Nat "size_bytes"⟩
    | "param" =>
      evaluateRequiredConstant document.types document.target.pointerSizeBits arguments operand
      let index ← value.getObjValAs? Nat "index"
      let some result := arguments[index]?.bind id | throw "unbound const scalar argument"
      return result
    | _ => throw "unsupported const source scalar expression"

end Miri.Frontend.Foundation
