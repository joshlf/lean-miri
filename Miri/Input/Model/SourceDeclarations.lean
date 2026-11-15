import Miri.Input.Model.SourceSymbols

/-! Typed finite declaration facts. No JSON syntax, executable MIR, compiler
query result or evaluation-local handle is stored in these records. -/
namespace Miri.Input.SourceDeclarations

inductive ItemKind where
  | function | associatedFunction
  deriving Repr, DecidableEq

/-- Declaration attributes/lang-item role, not an instance-resolution answer.
Unknown source evidence never defaults to an ordinary Item selection. -/
inductive ItemRole where
  | ordinary | intrinsic | dropGlue | foreign | unavailable
  deriving Repr, DecidableEq

structure ItemDeclaration where
  definition : DefinitionId
  path : String
  kind : ItemKind
  parameters : Array SourceSymbols.ParameterKind
  role : ItemRole := .unavailable
  deriving Repr, DecidableEq

structure Target where
  triple : String
  architecture : String
  dataLayout : String
  pointerSizeBits : Nat
  endian : String
  runtimeDataLayout : Option TargetDataLayoutEvidence := none
  deriving Repr, DecidableEq

structure GenericParameter where
  definition : DefinitionId
  index : Nat
  kind : SourceSymbols.ParameterKind
  deriving Repr, DecidableEq

/-- Lexical ownership, not a trait-implementation or selection answer. -/
structure GenericLayer where
  owner : DefinitionId
  parent : Option DefinitionId
  parentCount : Nat
  parameters : Array GenericParameter
  deriving Repr, DecidableEq

private def checkDefinition (definition : DefinitionId) : Except String Unit := do
  unless definition.crateIndex < 2^32 && definition.index < 2^32 do
    throw "typed source declaration DefId exceeds rustc index width"

/-- Reconstruct full slots from original lexical layers; missing parents,
cycles, duplicate owners/slots and inconsistent parent counts are errors. -/
def fullParameters (layers : Array GenericLayer) (owner : DefinitionId) :
    Except String (Array SourceSymbols.ParameterKind) := go (layers.size + 1) #[] owner
where
  go (fuel : Nat) (active : Array DefinitionId) (owner : DefinitionId) :
      Except String (Array SourceSymbols.ParameterKind) := do
    let .succ fuel := fuel | throw "typed source generic parent traversal exhausted"
    checkDefinition owner
    unless !active.contains owner do throw "typed source generic owner cycle"
    let rows := layers.filter (·.owner == owner)
    let some layer := rows[0]? | throw "typed source generic declaration unavailable"
    unless rows.size == 1 do throw "typed source generic owner duplicated"
    let inherited ← match layer.parent with
      | none => pure #[]
      | some parent => go fuel (active.push owner) parent
    unless layer.parentCount == inherited.size do throw "typed source generic parent count mismatch"
    let mut result := inherited
    let mut seen : Array DefinitionId := #[]
    for parameter in layer.parameters do
      checkDefinition parameter.definition
      unless parameter.definition.crateIndex == owner.crateIndex && parameter.definition != owner &&
          parameter.index == result.size && !seen.contains parameter.definition do
        throw "typed source generic slot identity/index mismatch"
      seen := seen.push parameter.definition
      result := result.push parameter.kind
    return result

end Miri.Input.SourceDeclarations
