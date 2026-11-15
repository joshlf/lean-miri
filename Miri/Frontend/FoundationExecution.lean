import Miri.Frontend.FoundationConstBindings

/-! A restricted, pure execution path for foundation MIR. This is separate from
schema-12 machine execution and is only a structural fixture evaluator: only pointer-free, whole-local values are accepted.
No allocation/provenance/borrow metadata is fabricated. In particular references,
raw pointers, ADTs, projections, calls and control flow fail closed.

Pinned rustc_const_eval/interpret/operand.rs `eval_operand` treats Copy and Move
identically (including its explicit FIXME about invalidation). We preserve that
rule rather than imposing source-language move checking on MIR. `Use` retagging
(step.rs) has no pointer to visit in the accepted value domain. This restriction
is essential; it does not establish general retag or whole-machine equivalence. -/
namespace Miri.Frontend.Foundation
open Lean

inductive ExecutionValue where
  | scalar (bits : Nat)
  | aggregate (elements : Array ExecutionValue)
  deriving Repr, BEq

private def get (j : Json) (k : String) : Except String Json := j.getObjVal? k
private def str (j : Json) (k : String) : Except String String := j.getObjValAs? String k
private def num (j : Json) (k : String) : Except String Nat := j.getObjValAs? Nat k
private def arr (j : Json) (k : String) : Except String (Array Json) := j.getObjValAs? (Array Json) k

private def integerWidth (d : Document) (name : String) : Except String Nat :=
  match name with
  | "u8" | "i8" => pure 8
  | "u16" | "i16" => pure 16
  | "u32" | "i32" => pure 32
  | "u64" | "i64" => pure 64
  | "u128" | "i128" => pure 128
  | "usize" | "isize" =>
    if d.target.pointerSizeBits ∈ [16, 32, 64, 128] then pure d.target.pointerSizeBits
    else throw "unsupported target pointer width"
  | _ => throw "unsupported integer type"

private def supportedType (d : Document) : Nat → ConcreteType → Except String Unit
  | 0, _ => throw "type validation exhausted"
  | _+1, .primitive "bool" "" | _+1, .primitive "char" "" => pure ()
  | _+1, .primitive "uint" n => do
      unless n.startsWith "u" do throw "invalid unsigned integer name"
      let _ ← integerWidth d n
      pure ()
  | _+1, .primitive "int" n => do
      unless n.startsWith "i" do throw "invalid signed integer name"
      let _ ← integerWidth d n
      pure ()
  | f+1, .array t _ => supportedType d f t
  | f+1, .tuple ts => ts.forM (supportedType d f)
  | _, _ => throw "unsupported restricted execution type"

private def validate (d : Document) (ty : ConcreteType) (v : ExecutionValue) : Except String Unit :=
  go 1024 ty v
where
  go (fuel : Nat) (ty : ConcreteType) (v : ExecutionValue) : Except String Unit := do
    let .succ fuel := fuel | throw "value validation exhausted"
    match ty, v with
    | .primitive "bool" "", .scalar n => unless n < 2 do throw "invalid bool"
    | .primitive "char" "", .scalar n =>
      unless n < 0x110000 && !(0xD800 ≤ n && n < 0xE000) do throw "invalid char"
    | .primitive "uint" name, .scalar n
    | .primitive "int" name, .scalar n =>
      unless n < 2 ^ (← integerWidth d name) do throw "integer out of range"
    | .array t n, .aggregate vs =>
      unless vs.size == n do throw "array length mismatch"
      for v in vs do go fuel t v
    | .tuple ts, .aggregate vs =>
      unless ts.size == vs.size do throw "tuple length mismatch"
      for h : i in [:ts.size] do
        let some v := vs[i]? | throw "tuple length mismatch"
        go fuel ts[i] v
    | _, _ => throw "unsupported foundation execution type or value"

private def sameType : Nat → ConcreteType → ConcreteType → Bool
  | 0, _, _ => false
  | _+1, .primitive k n, .primitive k' n' => k == k' && n == n'
  | f+1, .array t n, .array t' n' => n == n' && sameType f t t'
  | f+1, .tuple ts, .tuple us => ts.size == us.size &&
      (ts.zip us).all (fun (t,u) => sameType f t u)
  | _, _, _ => false

private def localIndex (p : Json) : Except String Nat := do
  unless (← arr p "projection").isEmpty do throw "unsupported foundation projection"
  num p "local"

/-- Execute the requested body's single straight-line block, after substituting
its local types on demand. Inputs/outputs are fully initialized scalar bits or
aggregates. Success means return was reached with a validated return value;
unsupported material and invalid/uninitialized reads are errors, never success.
The caller must check every environment obligation through `checkEnvironment`;
this explicit parameter is an assumption boundary, not evidence that obligations
are satisfied. This fixture evaluator is not the fixed Miri interpreter and
does not support Rust safety claims. -/
def evaluateRestrictedBody (d : Document) (definition : Nat)
    (typeArguments : Array (Option ConcreteType)) (constArguments : Array (Option Nat))
    (checkEnvironment : Json → Except String Unit)
    (arguments : Array ExecutionValue) : Except String ExecutionValue := do
  let candidates ← d.bodies.filterM fun b => return (← num b "definition") == definition
  unless candidates.size == 1 do throw "missing or duplicate foundation body"
  let some body := candidates[0]? | throw "missing foundation body"
  checkEnvironment (← get body "environment")
  checkRequiredConstants d body constArguments
  unless (← num body "argument_count") == arguments.size do throw "argument count mismatch"
  let mut types := #[]
  for id in (← arr body "locals") do
    types := types.push (← instantiate typeArguments constArguments (← typeExpr d (← id.getNat?)))
  for ty in types do supportedType d 1024 ty
  unless types.size > arguments.size do throw "missing return or argument local"
  let mut locals : Array (Option ExecutionValue) := Array.replicate types.size none
  for h : i in [:arguments.size] do
    let some ty := types[i+1]? | throw "missing argument type"
    validate d ty arguments[i]
    if hLocal : i+1 < locals.size then
      locals := locals.set (i+1) (some arguments[i]) hLocal
    else throw "argument local out of bounds"
  let blocks ← arr body "blocks"
  unless blocks.size == 1 do throw "unsupported foundation control flow"
  let some block := blocks[0]? | throw "missing entry block"
  unless !(← block.getObjValAs? Bool "cleanup") do throw "unsupported cleanup block"
  for stmt in (← arr block "statements") do
    unless (← str stmt "kind") == "assign" do throw "unsupported foundation statement"
    let dest ← localIndex (← get stmt "place")
    let rv ← get stmt "value"
    unless (← str rv "kind") == "use" do throw "unsupported foundation rvalue"
    let _retag ← rv.getObjValAs? Bool "retag"
    let op ← get rv "operand"
    let kind ← str op "kind"
    unless kind == "copy" || kind == "move" do throw "unsupported foundation operand"
    let source ← localIndex (← get op "place")
    let some sourceTy := types[source]? | throw "source local out of bounds"
    let some destTy := types[dest]? | throw "destination local out of bounds"
    unless sameType 1024 sourceTy destTy do throw "assignment type mismatch"
    let some value := (locals[source]?.bind id) | throw "uninitialized local read"
    validate d sourceTy value
    if hLocal : dest < locals.size then
      locals := locals.set dest (some value) hLocal
    else throw "destination local out of bounds"
  unless (← str (← get block "terminator") "kind") == "return" do
    throw "unsupported foundation terminator"
  let some result := (locals[0]?.bind id) | throw "uninitialized return local"
  let some returnTy := types[0]? | throw "missing return type"
  validate d returnTy result
  return result

end Miri.Frontend.Foundation
