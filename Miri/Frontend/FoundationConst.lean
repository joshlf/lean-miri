import Lean

/-! Required-constant checking for the already-material scalar subset. Pinned
rustc `interpret/stack.rs` evaluates the entire required list before running a
frame, including obligations in unreachable MIR. This module does not evaluate
const MIR, allocations or unevaluated definitions. Unsupported forms fail.
There is no persistent state or cross-run cache. -/
namespace Miri.Frontend.Foundation
open Lean

set_option autoImplicit false in
structure RequiredScalar where
  typeId : Nat
  bits : Nat
  sizeBytes : Nat
  deriving Repr, DecidableEq

private def scalarWidth (pointerBits : Nat) (shape : Json) : Except String Nat := do
  match ← shape.getObjValAs? String "kind" with
  | "bool" => return 8
  | "char" => return 32
  | "uint" | "int" | "float" =>
    match ← shape.getObjValAs? String "name" with
    | "usize" | "isize" =>
      unless pointerBits > 0 && pointerBits ≤ 128 && pointerBits % 8 == 0 do throw "invalid const pointer width"
      return pointerBits
    | "u8" | "i8" => return 8
    | "u16" | "i16" | "f16" => return 16
    | "u32" | "i32" | "f32" => return 32
    | "u64" | "i64" | "f64" => return 64
    | "u128" | "i128" | "f128" => return 128
    | _ => throw "unsupported required scalar type"
  | _ => throw "unsupported required scalar type"

private def checkScalar (types : Array Json) (pointerBits : Nat)
    (scalar : RequiredScalar) : Except String Unit := do
  let some type := types[scalar.typeId]? | throw "required const type is out of bounds"
  let shape ← type.getObjVal? "shape"
  let width ← scalarWidth pointerBits shape
  unless scalar.sizeBytes * 8 == width do throw "required const scalar width mismatch"
  unless scalar.bits < 2 ^ width do throw "required const scalar bits overflow"
  match ← shape.getObjValAs? String "kind" with
  | "bool" => unless scalar.bits ≤ 1 do throw "invalid required bool constant"
  | "char" =>
    unless scalar.bits ≤ 0x10ffff && !(0xd800 ≤ scalar.bits && scalar.bits ≤ 0xdfff) do
      throw "invalid required char constant"
  | _ => pure ()

/-- Evaluate one retained scalar or generic scalar parameter. Bindings carry
both type and width; missing or mismatched bindings cannot establish success. -/
def evaluateRequiredConstant (types : Array Json) (pointerBits : Nat)
    (arguments : Array (Option RequiredScalar)) (operand : Json) : Except String Unit := do
  unless (← operand.getObjValAs? String "kind") == "constant" do
    throw "required const is not a constant operand"
  let typeId ← operand.getObjValAs? Nat "type"
  let some type := types[typeId]? | throw "required const type is out of bounds"
  let value ← operand.getObjVal? "value"
  match ← value.getObjValAs? String "kind" with
  | "scalar" | "value" =>
    if (← value.getObjValAs? String "kind") == "value" then
      unless (← value.getObjValAs? Nat "type") == typeId do
        throw "required const value type mismatch"
    let bits ← value.getObjValAs? String "bits"
    let some bits := bits.toNat? | throw "invalid required scalar digits"
    checkScalar types pointerBits ⟨typeId, bits, ← value.getObjValAs? Nat "size_bytes"⟩
  | "param" =>
    let index ← value.getObjValAs? Nat "index"
    let some scalar := arguments[index]?.bind id | throw "unbound required const parameter"
    unless scalar.typeId == typeId do throw "required const parameter type mismatch"
    checkScalar types pointerBits scalar
  | "zero_sized" =>
    let shape ← type.getObjVal? "shape"
    match ← shape.getObjValAs? String "kind" with
    | "function_definition" => pure ()
    | "tuple" =>
      unless (← shape.getObjValAs? (Array Nat) "elements").isEmpty do
        throw "unsupported non-unit zero-sized required const"
    | _ => throw "unsupported zero-sized required const"
  | _ => throw "unsupported required const source expression"

/-- Check every obligation in source order, independently of control flow.
Call this before entry on each instantiated frame; passing this check alone
establishes neither frame validity nor execution safety. -/
def evaluateRequiredConstants (types : Array Json) (pointerBits : Nat)
    (body : Json) (arguments : Array (Option RequiredScalar) := #[]) : Except String Unit := do
  for operand in (← body.getObjValAs? (Array Json) "required_consts") do
    evaluateRequiredConstant types pointerBits arguments operand

end Miri.Frontend.Foundation
