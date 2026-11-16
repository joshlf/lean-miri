import Miri.Input.CompilerFacts

namespace Miri.Input.ConcreteCastQueries
open Miri.MIR Miri.ABI

def lockstepTails (runtime : RuntimeMetadata) (source target : TypeId) :
    Except String (TypeId × TypeId) :=
  go (runtime.source.types.size + 1) source target
where
  go (fuel source target : Nat) : Except String (TypeId × TypeId) := do
    let .succ fuel := fuel | throw "recursive lockstep struct tails"
    let a ← runtime.node source |>.mapError toString
    let b ← runtime.node target |>.mapError toString
    match a.shape,b.shape with
    | .adt a, .adt b =>
      if a.definition == b.definition && a.kind == .structKind then
        let some av := a.variants[0]? | throw "struct has no variant"
        let some bv := b.variants[0]? | throw "struct has no variant"
        if let some af := av.fields.back? then
          let some bf := bv.fields.back? | throw "same struct has different field arities"
          return ← go fuel af.typeId bf.typeId
      return (source,target)
    | .tuple a, .tuple b =>
      if a.size == b.size then
        if let some sourceTail := a.back? then
          let some bt := b.back? | throw "same tuple arity has no target tail"
          return ← go fuel sourceTail bt
      return (source,target)
    | _,_ => return (source,target)

def boxType (context : CompilerFacts.Context) (pointee : TypeId) : Except String TypeId := do
  let mut result := none
  for node in context.runtime.source.types do
    if node.sourceLayout.isBox then
      let .adt data := node.shape | throw "Box attribute attached to non-ADT"
      if data.args[0]? == some (.Type pointee) &&
          (← CompilerFacts.boolean context node.id "is_global_box") then
        if result.isSome then throw "ambiguous canonical Box type"
        result := some node.id
  let some selected := result | throw "required concrete Box type is absent"
  return selected

private def regionHasNoBoundVars (depth : Nat) : Region → Bool
  | .Bound (.Bound index) _ _ => index < depth
  | .Bound .Canonical _ _ => false
  | _ => true

mutual
  private def argumentsHaveNoBoundVars (runtime : RuntimeMetadata) (fuel depth : Nat)
      (arguments : Array GenericArg) : Except String Bool := do
    let .succ fuel := fuel | throw "bound-variable walk exhausted finite source graph"
    for argument in arguments do
      match argument with
      | .Lifetime region => unless regionHasNoBoundVars depth region do return false
      | .Type ty => unless ← typeHasNoBoundVars runtime fuel depth ty do return false
      | .Const value => unless ← constantHasNoBoundVars runtime fuel depth value do return false
    return true

  private def typeHasNoBoundVars (runtime : RuntimeMetadata) (fuel depth : Nat)
      (ty : TypeId) : Except String Bool := do
    let .succ fuel := fuel | throw "bound-variable walk exhausted finite source graph"
    let node ← runtime.node ty |>.mapError toString
    match node.shape with
    | .adt data => argumentsHaveNoBoundVars runtime fuel depth data.args
    | .closure _ args _ | .coroutineClosure _ args | .coroutine _ args | .alias _ _ args =>
      argumentsHaveNoBoundVars runtime fuel depth args
    | .functionDefinition _ args _ _ => argumentsHaveNoBoundVars runtime fuel (depth + 1) args
    | .functionPointer signature _ =>
      for ty in signature.inputs.push signature.output do
        unless ← typeHasNoBoundVars runtime fuel (depth + 1) ty do return false
      return true
    | .reference pointee _ region =>
      if !regionHasNoBoundVars depth region then return false
      typeHasNoBoundVars runtime fuel depth pointee
    | .rawPointer pointee _ | .slice pointee => typeHasNoBoundVars runtime fuel depth pointee
    | .unsafeBinder inner _ => typeHasNoBoundVars runtime fuel (depth + 1) inner
    | .array element length _ =>
      return (← typeHasNoBoundVars runtime fuel depth element) &&
        (← constantHasNoBoundVars runtime fuel depth length)
    | .tuple fields =>
      for ty in fields do
        unless ← typeHasNoBoundVars runtime fuel depth ty do return false
      return true
    | .dynamicTraitObject predicates _ region =>
      if !regionHasNoBoundVars depth region then return false
      for predicate in predicates do
        let some value := runtime.source.predicates[predicate]? | throw "missing existential predicate"
        unless ← argumentsHaveNoBoundVars runtime fuel (depth + 1) value.genericArgs do return false
        if let some ty := value.projectionTerm then
          unless ← typeHasNoBoundVars runtime fuel (depth + 1) ty do return false
      return true
    | .patternType base pattern =>
      return (← typeHasNoBoundVars runtime fuel depth base) &&
        (← patternHasNoBoundVars runtime fuel depth pattern)
    | _ => return true

  private def constantHasNoBoundVars (runtime : RuntimeMetadata) (fuel depth : Nat)
      (id : TypeConstantId) : Except String Bool := do
    let .succ fuel := fuel | throw "bound-variable walk exhausted finite source graph"
    let some value := runtime.source.typeConstants[id]? | throw "missing type constant"
    match value with
    | .Bound (.Bound index) _ => return index < depth
    | .Bound .Canonical _ => return false
    | .Alias _ _ _ args | .Expr _ args => argumentsHaveNoBoundVars runtime fuel depth args
    | .Value ty tree =>
      unless ← typeHasNoBoundVars runtime fuel depth ty do return false
      for node in tree.nodes do
        if let .Branch fields := node then
          for id in fields do
            unless ← constantHasNoBoundVars runtime fuel depth id do return false
      return true
    | .Param _ _ declared =>
      if let some ty := declared then typeHasNoBoundVars runtime fuel depth ty else pure true
    | _ => return true

  private def patternHasNoBoundVars (runtime : RuntimeMetadata) (fuel depth : Nat)
      (pattern : CompilerPattern) : Except String Bool := do
    let .succ fuel := fuel | throw "bound-variable walk exhausted finite source graph"
    match pattern with
    | .notNull => return true
    | .range start finish => return (← constantHasNoBoundVars runtime fuel depth start) &&
        (← constantHasNoBoundVars runtime fuel depth finish)
    | .or patterns =>
      for pattern in patterns do
        unless ← patternHasNoBoundVars runtime fuel depth pattern do return false
      return true
end

def noBoundVars (runtime : RuntimeMetadata) (arguments : Array GenericArg) : Except String Bool :=
  argumentsHaveNoBoundVars runtime (4 * (runtime.source.types.size +
    runtime.source.typeConstants.size + runtime.source.predicates.size + 1)) 0 arguments

end Miri.Input.ConcreteCastQueries
