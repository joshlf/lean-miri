import Miri.Frontend.FoundationGenericEnvironment
import Miri.Frontend.FoundationConstMir

/-! Pure finite CTFE source values. Nominal aggregates retain their field tree;
this module introduces no layout, raw bytes, allocation IDs or function address.
Only straight-line, nongeneric struct initialization is supported. The pinned
metadata trivial-literal encoding is trusted declaration material: its original
reference chain is unavailable and is not reconstructed or claimed here. -/
namespace Miri.Frontend.Foundation
open Lean

inductive SourceConstantValue where
  | scalar (value : RequiredScalar)
  | structureValue (typeId definition : Nat) (fields : Array SourceConstantValue)
  deriving Repr

def SourceConstantValue.typeId : SourceConstantValue → Nat
  | .scalar value => value.typeId
  | .structureValue typeId .. => typeId

private def validateLeaf (document : Document) (value : RequiredScalar) : Except String Unit :=
  evaluateRequiredConstant document.types document.target.pointerSizeBits #[] (Json.mkObj [
    ("kind",toJson "constant"),("type",toJson value.typeId),("value",Json.mkObj [
      ("kind",toJson "scalar"),("bits",toJson (toString value.bits)),("size_bytes",toJson value.sizeBytes)])])

private def structureFields (document : Document) (typeId definition : Nat) : Except String (Array Nat) := do
  let some type := document.types[typeId]? | throw "const aggregate type absent"
  let shape ← type.getObjVal? "shape"
  unless (← shape.getObjValAs? String "kind") == "adt" &&
      (← shape.getObjValAs? Nat "definition") == definition &&
      (← shape.getObjValAs? (Array Json) "arguments").isEmpty do throw "const aggregate nominal type mismatch/generics"
  let some row := document.definitions[definition]? | throw "const aggregate declaration absent"
  let declaration ← row.getObjVal? "adt"
  unless (← declaration.getObjValAs? String "kind") == "struct" do throw "const aggregate requires struct source"
  let environment ← flattenEnvironment document (← declaration.getObjVal? "environment")
  unless (← environment.getObjValAs? (Array Json) "parameters").isEmpty &&
      (← environment.getObjValAs? (Array Json) "clauses").isEmpty do throw "const aggregate generic/conditional declaration"
  let variants ← declaration.getObjValAs? (Array Json) "variants"
  let [variant] := variants.toList | throw "const aggregate variant source mismatch"
  (← variant.getObjValAs? (Array Json) "fields").mapM fun field => field.getObjValAs? Nat "type"

private def integerShape (document : Document) (typeId : Nat) : Except String (Nat × Bool) := do
  let some row := document.types[typeId]? | throw "integer cast type absent"
  let shape ← row.getObjVal? "shape"
  let kind ← shape.getObjValAs? String "kind"
  unless kind == "int" || kind == "uint" do throw "const integer cast type unsupported"
  let size ← match ← shape.getObjValAs? String "name" with
    | "u8" | "i8" => pure 1
    | "u16" | "i16" => pure 2
    | "u32" | "i32" => pure 4
    | "u64" | "i64" => pure 8
    | "u128" | "i128" => pure 16
    | "usize" | "isize" => pure (document.target.pointerSizeBits / 8)
    | _ => throw "const integer cast width unsupported"
  unless size > 0 && size ≤ 16 do throw "const integer cast width invalid"
  return (size,kind == "int")

private def evaluateAggregateMir (document : Document) (source : Json)
    (constant : Json → Except String SourceConstantValue) : Except String SourceConstantValue := do
  let locals ← source.getObjValAs? (Array Nat) "locals"
  let blocks ← source.getObjValAs? (Array Json) "blocks"
  let [block] := blocks.toList | throw "aggregate const MIR control flow unsupported"
  for operand in (← source.getObjValAs? (Array Json) "required_consts") do let _ ← constant operand
  let mut values : Array (Option SourceConstantValue) := Array.replicate locals.size none
  let read (state : Array (Option SourceConstantValue)) (operand : Json) :
      Except String (Array (Option SourceConstantValue) × SourceConstantValue) := do
    let kind ← operand.getObjValAs? String "kind"
    if kind == "constant" then return (state, ← constant operand)
    unless kind == "copy" || kind == "move" do throw "aggregate const operand unsupported"
    let place ← operand.getObjVal? "place"
    unless (← place.getObjValAs? (Array Json) "projection").isEmpty do throw "aggregate const projection unsupported"
    let sourceIndex ← place.getObjValAs? Nat "local"
    let some value := state[sourceIndex]?.bind id | throw "aggregate const uninitialized local"
    if kind == "move" then
      if h : sourceIndex < state.size then return (state.set sourceIndex none h, value)
      else throw "aggregate const move local absent"
    return (state,value)
  for statement in (← block.getObjValAs? (Array Json) "statements") do
    match ← statement.getObjValAs? String "kind" with
    | "nop" => pure ()
    | "storage_live" | "storage_dead" =>
      let localIndex ← statement.getObjValAs? Nat "local"
      if h : localIndex < values.size then values := values.set localIndex none h
      else throw "aggregate const storage localIndex absent"
    | "assign" =>
      let place ← statement.getObjVal? "place"
      unless (← place.getObjValAs? (Array Json) "projection").isEmpty do throw "aggregate const destination projection unsupported"
      let localIndex ← place.getObjValAs? Nat "local"
      let some typeId := locals[localIndex]? | throw "aggregate const destination absent"
      let rvalue ← statement.getObjVal? "value"
      let value ← match ← rvalue.getObjValAs? String "kind" with
        | "use" => do
          let _ ← rvalue.getObjValAs? Bool "retag"
          let (next,value) ← read values (← rvalue.getObjVal? "operand")
          values := next
          pure value
        | "integer_cast" => do
          let (next,input) ← read values (← rvalue.getObjVal? "operand")
          values := next
          let .scalar input := input | throw "const integer cast requires scalar"
          let (inputSize,inputSigned) ← integerShape document input.typeId
          unless input.sizeBytes == inputSize do throw "const integer cast input width mismatch"
          if inputSigned && input.bits ≥ 2^(inputSize*8-1) then throw "negative const integer casts unsupported"
          let target ← rvalue.getObjValAs? Nat "target_type"
          unless target == typeId do throw "const integer cast target mismatch"
          let (size,signed) ← integerShape document target
          unless input.bits < 2^(size*8 - (if signed then 1 else 0)) do throw "const integer cast narrowing unsupported"
          let result := RequiredScalar.mk target input.bits size
          validateLeaf document result
          pure (.scalar result)
        | "aggregate_adt" => do
          unless (← rvalue.getObjValAs? Nat "variant") == 0 &&
              (← rvalue.getObjValAs? (Array Json) "arguments").isEmpty do throw "aggregate const variant/generics unsupported"
          let definition ← rvalue.getObjValAs? Nat "definition"
          let fields ← structureFields document typeId definition
          let operands ← rvalue.getObjValAs? (Array Json) "operands"
          unless fields.size == operands.size do throw "aggregate const field count mismatch"
          let mut children := #[]
          for operand in operands do
            let (next,child) ← read values operand
            values := next
            children := children.push child
          unless (fields.zip children).all (fun (type,value) => type == value.typeId) do throw "aggregate const field type mismatch"
          pure (.structureValue typeId definition children)
        | _ => throw "aggregate const rvalue unsupported"
      unless value.typeId == typeId do throw "aggregate const assignment type mismatch"
      if h : localIndex < values.size then values := values.set localIndex (some value) h
      else throw "aggregate const state localIndex absent"
    | _ => throw "aggregate const statement unsupported"
  unless (← (← block.getObjVal? "terminator").getObjValAs? String "kind") == "return" do throw "aggregate const terminator unsupported"
  let some value := values[0]?.bind id | throw "aggregate const return uninitialized"
  return value

/-- Evaluate a source definition on demand; cycles and missing source fail.
Explicit inherent-owner layers justify associated constants, never trait lookup. -/
def evaluateSourceConstant (document : Document) (operand : Json)
    (arguments : Array (Option RequiredScalar) := #[]) : Except String SourceConstantValue :=
  go (document.definitions.size + 1) #[] operand
where
  go (fuel : Nat) (seen : Array Nat) (operand : Json) : Except String SourceConstantValue := do
    unless (← operand.getObjValAs? String "kind") == "constant" do throw "source const operand kind unsupported"
    let typeId ← operand.getObjValAs? Nat "type"
    let value ← operand.getObjVal? "value"
    match ← value.getObjValAs? String "kind" with
    | "unevaluated" =>
      let definition ← value.getObjValAs? Nat "definition"
      unless (← value.getObjValAs? (Array Json) "arguments").isEmpty do throw "generic source const unsupported"
      unless !seen.contains definition do throw "cyclic source const"
      let .succ fuel := fuel | throw "source const traversal exhausted"
      let some row := document.definitions[definition]? | throw "source const definition absent"
      let kind ← row.getObjValAs? String "kind"
      unless kind == "const" || kind == "AssocConst" do throw "source const owner kind unsupported"
      if kind == "AssocConst" then
        let owner ← row.getObjVal? "const_owner"
        unless (← owner.getObjValAs? String "kind") == "inherent_impl" do throw "trait-associated const unsupported"
        let implementation ← owner.getObjValAs? Nat "definition"
        let some impl := document.definitions[implementation]? | throw "associated const impl absent"
        unless (← impl.getObjValAs? String "kind") == "Impl { of_trait: false }" do throw "associated const owner is not inherent impl"
        let declaration ← row.getObjVal? "generic_declaration"
        unless (← declaration.getObjValAs? Nat "parent") == implementation do throw "associated const impl parent mismatch"
        let sourceEnvironment ← owner.getObjVal? "environment"
        unless (← sourceEnvironment.getObjValAs? Nat "owner") == definition do throw "associated const environment owner mismatch"
        let environment ← flattenEnvironment document sourceEnvironment
        unless (← environment.getObjValAs? (Array Json) "parameters").isEmpty &&
            (← environment.getObjValAs? (Array Json) "clauses").isEmpty do throw "associated const environment unsupported"
      let expression ← row.getObjVal? "const_expression"
      unless (← expression.getObjValAs? Nat "type") == typeId do throw "source const return type mismatch"
      let evaluate := go fuel (seen.push definition)
      let result ← match (expression.getObjValAs? String "kind").toOption with
        | some "metadata_trivial_literal" => do
          unless (← expression.getObjValAs? String "original_reference_chain") == "unavailable_in_pinned_metadata" do
            throw "metadata literal source encoding mismatch"
          let literal ← expression.getObjVal? "literal"
          unless (← (← literal.getObjVal? "value").getObjValAs? String "kind") == "scalar" do
            throw "metadata literal must be scalar source"
          evaluate literal
        | some "aggregate_mir" => evaluateAggregateMir document (← expression.getObjVal? "mir") evaluate
        | some "mir" => do
          let scalar ← evaluateConstMir document (← expression.getObjVal? "mir") fun operand => do
            let .scalar value ← evaluate operand | throw "scalar const MIR consumed aggregate"
            return value
          pure (.scalar scalar)
        | none => do
          let _ ← expression.getObjValAs? Bool "retag"
          evaluate (← expression.getObjVal? "operand")
        | _ => throw "source const expression unsupported"
      unless result.typeId == typeId do throw "source const expression type mismatch"
      return result
    | "scalar" | "value" =>
      evaluateRequiredConstant document.types document.target.pointerSizeBits arguments operand
      let some bits := (← value.getObjValAs? String "bits").toNat? | throw "source scalar bits malformed"
      let scalar := RequiredScalar.mk typeId bits (← value.getObjValAs? Nat "size_bytes")
      validateLeaf document scalar
      return .scalar scalar
    | "param" =>
      evaluateRequiredConstant document.types document.target.pointerSizeBits arguments operand
      let index ← value.getObjValAs? Nat "index"
      let some scalar := arguments[index]?.bind id | throw "source scalar parameter absent"
      return .scalar scalar
    | _ => throw "source const value unsupported"

end Miri.Frontend.Foundation
