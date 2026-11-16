import Miri.Input.Model.SourceTraits

namespace Miri.Input.SourceDeclarationQueries

private def requiresSized (material : SourceTraitMaterial) (definition : DefinitionRef) : Except String Bool :=
  go (material.declarations.size + 1) #[] definition
where
  go (fuel : Nat) (seen : Array DefinitionRef) (definition : DefinitionRef) : Except String Bool := do
    if seen.contains definition then return false
    let .succ fuel := fuel | throw "trait Sized supertrait traversal limit"
    let some declaration := material.declarations.find? (·.definition == definition)
      | throw "trait declaration needed for its Sized bound is absent"
    if declaration.role == .sized then return true
    for parent in declaration.superTraits do
      if ← go fuel (seen.push definition) parent then return true
    return false

private def sizedBounds (material : SourceTraitMaterial) (clauses : Array SourceTraitClause) :
    Except String (Array Nat) := do
  let mut expressions := #[]
  for clause in clauses do
    if let .trait definition arguments := clause then
      if ← requiresSized material definition then
        if let some (SourceTraitArgument.type expression) := arguments[0]? then expressions := expressions.push expression
  return expressions

def maybeUnsized (material : SourceTraitMaterial) (definition : DefinitionRef) : Except String Bool := do
  let some declaration := material.adtDeclarations.find? (·.definition == definition)
    | throw "source ADT declaration is absent"
  if !declaration.isStruct then return false
  let some tail := declaration.tailType | return false
  let bounds ← sizedBounds material declaration.clauses
  let arguments := Array.replicate declaration.parameters.size false
  return !(← sized (material.types.size + material.adtDeclarations.size + 1) bounds arguments tail)
where
  sized (fuel : Nat) (bounds : Array Nat) (arguments : Array Bool) (expression : Nat) : Except String Bool := do
    if bounds.contains expression then return true
    let .succ fuel := fuel | throw "generic ADT tail Sized traversal limit"
    let some value := material.types[expression]? | throw "generic ADT tail expression is absent"
    match value with
    | .parameter index =>
      let some answer := arguments[index]? | throw "generic ADT tail parameter is out of bounds"
      return answer
    | .primitive kind .. => return kind != .str
    | .slice _ => return false
    | .adt definition inputs =>
      let some declaration := material.adtDeclarations.find? (·.definition == definition)
        | throw "nested ADT declaration is absent"
      if !declaration.isStruct then return true
      let some tail := declaration.tailType | return true
      let mut substituted := #[]
      for input in inputs do
        let answer ← match input with
          | .type expression => sized fuel bounds arguments expression
          | .lifetime | .constant _ | .constantParameter _ => pure false
          | .unsupported reason => throw s!"unsupported generic ADT argument: {reason}"
        substituted := substituted.push answer
      let ownBounds ← sizedBounds material declaration.clauses
      sized fuel ownBounds substituted tail
    | .tuple fields =>
      for field in fields do unless (← sized fuel bounds arguments field) do return false
      return true
    | .projectionAlias definition _ =>
      let some declaration := material.associatedTypes.find? (·.definition == definition)
        | throw "associated type bound declaration is absent"
      for bound in declaration.bounds do
        if let .trait trait arguments := bound then
          if let some (SourceTraitArgument.type self) := arguments[0]? then
            if let some (.projectionAlias own _) := material.types[self]? then
              if own == definition && (← requiresSized material trait) then return true
      return false
    | .unsupported reason kind =>
      match kind with
      | some .dynamicTraitObject | some .foreign => return false
      | some .functionPointer | some .closure | some .coroutine | some .coroutineClosure
      | some .patternType | some .unsafeBinder => return true
      | _ => throw s!"unsupported generic ADT tail type: {reason}"
    | .array .. | .reference .. | .rawPointer .. | .functionDefinition .. | .closure .. | .patternType .. => return true

end Miri.Input.SourceDeclarationQueries
