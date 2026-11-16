import Miri.Input.RuntimeMetadata

namespace Miri.Input.ConcreteCovariance
open Miri.MIR

def compose : Variance → Variance → Variance
  | .Bivariant, _ | _, .Bivariant => .Bivariant
  | .Invariant, _ | _, .Invariant => .Invariant
  | .Covariant, other => other
  | .Contravariant, .Covariant => .Contravariant
  | .Contravariant, .Contravariant => .Covariant

mutual
  private def relate (runtime : RuntimeMetadata) (fuel : Nat) (variance : Variance)
      (source target : TypeId) : Except String Bool := do
    if variance == .Bivariant || source == target then return true
    let .succ fuel := fuel | throw "concrete type relation exhausted its finite type graph"
    let sourceNode ← runtime.node source |>.mapError toString
    let targetNode ← runtime.node target |>.mapError toString
    let source := sourceNode.sourceLayout.normalizedType
    let target := targetNode.sourceLayout.normalizedType
    if source != sourceNode.id || target != targetNode.id then
      return ← relate runtime fuel variance source target
    let nested := relate runtime fuel variance
    let invariant := relate runtime fuel .Invariant
    match sourceNode.shape, targetNode.shape with
    | .bool, .bool | .char, .char | .str, .str | .never, .never => return true
    | .int a, .int b | .uint a, .uint b => return a == b
    | .float a, .float b => return a == b
    | .foreign a, .foreign b => return a == b
    | .adt a, .adt b =>
      if a.definition != b.definition then return false
      relateArguments runtime fuel variance sourceNode.sourceLayout.variances a.args b.args
    | .functionDefinition a aa _ _, .functionDefinition b ba _ _ =>
      if a != b then return false
      relateArguments runtime fuel variance sourceNode.sourceLayout.variances aa ba
    | .closure a aa _, .closure b ba _
    | .coroutine a aa, .coroutine b ba
    | .coroutineClosure a aa, .coroutineClosure b ba =>
      if a != b then return false
      relateArguments runtime fuel .Invariant (Array.replicate aa.size .Invariant) aa ba
    | .rawPointer a am, .rawPointer b bm
    | .reference a am _, .reference b bm _ =>
      if am != bm then return false
      if am == .Mut then invariant a b else nested a b
    | .array a ac _, .array b bc _ =>
      if !(← nested a b) then return false
      relateConstant runtime fuel ac bc
    | .slice a, .slice b => nested a b
    | .tuple a, .tuple b =>
      if a.size != b.size then return false
      for (a,b) in a.zip b do
        unless ← nested a b do return false
      return true
    | .functionPointer a ab, .functionPointer b bb =>
      unless ab.all (fun value => match value with | .Region _ => true | _ => false) &&
          bb.all (fun value => match value with | .Region _ => true | _ => false) do
        throw "type relation for non-region higher-ranked function binders is unsupported"
      if a.abi != b.abi || a.safety != b.safety || a.cVariadic != b.cVariadic || a.splatted != b.splatted ||
          a.inputs.size != b.inputs.size then return false
      for (a,b) in a.inputs.zip b.inputs do
        unless ← relate runtime fuel (compose variance .Contravariant) a b do return false
      nested a.output b.output
    | .dynamicTraitObject a _ _, .dynamicTraitObject b _ _ =>
      if a.size != b.size then return false
      for (a,b) in a.zip b do
        unless ← relatePredicate runtime fuel a b do return false
      return true
    | .unsafeBinder a ab, .unsafeBinder b bb =>
      if ab != bb then return false
      nested a b
    | .patternType a ap, .patternType b bp =>
      if !(← nested a b) then return false
      relatePattern runtime fuel ap bp
    | .alias .., _ | _, .alias .. => throw "unnormalized alias in concrete type relation"
    | _, _ => return false

  private def relateArguments (runtime : RuntimeMetadata) (fuel : Nat) (outer : Variance)
      (variances : Array Variance) (source target : Array GenericArg) : Except String Bool := do
    let .succ fuel := fuel | throw "concrete generic relation exhausted its finite type graph"
    if source.size != target.size then return false
    unless variances.size == source.size do throw "declaration variance arity mismatch"
    for ((a,b), variance) in (source.zip target).zip variances do
      match a,b with
      | .Lifetime _, .Lifetime _ => pure ()
      | .Type a, .Type b =>
        unless ← relate runtime fuel (compose outer variance) a b do return false
      | .Const a, .Const b =>
        unless ← relateConstant runtime fuel a b do return false
      | _, _ => return false
    return true

  private def relateConstant (runtime : RuntimeMetadata) (fuel : Nat)
      (source target : TypeConstantId) : Except String Bool := do
    if source == target then return true
    let .succ fuel := fuel | throw "concrete constant relation exhausted its finite graph"
    let some a := runtime.source.typeConstants[source]? | throw "missing source constant"
    let some b := runtime.source.typeConstants[target]? | throw "missing target constant"
    match a,b with
    | .Value aType av, .Value bType bv =>
      unless ← relate runtime fuel .Invariant aType bType do return false
      let some a := av.nodes[av.root]? | throw "missing source value tree node"
      let some b := bv.nodes[bv.root]? | throw "missing target value tree node"
      match a,b with
      | .Leaf a asize, .Leaf b bsize => return a == b && asize == bsize
      | .Branch a, .Branch b =>
        if a.size != b.size then return false
        for (a,b) in a.zip b do
          unless ← relateConstant runtime fuel a b do return false
        return true
      | _, _ => return false
    | _, _ => throw "unevaluated constant in concrete type relation"

  private def relatePredicate (runtime : RuntimeMetadata) (fuel : Nat)
      (source target : PredicateId) : Except String Bool := do
    if source == target then return true
    let .succ fuel := fuel | throw "concrete predicate relation exhausted its finite graph"
    let some a := runtime.source.predicates[source]? | throw "missing source existential predicate"
    let some b := runtime.source.predicates[target]? | throw "missing target existential predicate"
    if a.kind != b.kind || a.definitionId != b.definitionId then return false
    unless ← relateArguments runtime fuel .Invariant
      (Array.replicate a.genericArgs.size .Invariant) a.genericArgs b.genericArgs do return false
    match a.projectionTerm,b.projectionTerm with
    | none, none => return true
    | some a, some b => relate runtime fuel .Invariant a b
    | _, _ => return false

  private def relatePattern (runtime : RuntimeMetadata) (fuel : Nat)
      (source target : CompilerPattern) : Except String Bool := do
    let .succ fuel := fuel | throw "concrete pattern relation exhausted its finite graph"
    match source,target with
    | .notNull, .notNull => return true
    | .range a b, .range c d =>
      return (← relateConstant runtime fuel a c) && (← relateConstant runtime fuel b d)
    | .or a, .or b =>
      if a.size != b.size then return false
      for (a,b) in a.zip b do
        unless ← relatePattern runtime fuel a b do return false
      return true
    | _, _ => return false
end

def relation (runtime : RuntimeMetadata) (source target : TypeId) : Except String Bool :=
  relate runtime (4 * (runtime.source.types.size + runtime.source.typeConstants.size +
    runtime.source.predicates.size + 1)) .Covariant source target

@[simp] theorem relation_self (runtime : RuntimeMetadata) (ty : TypeId) :
    relation runtime ty ty = .ok true := by
  unfold relation
  rw [relate.eq_def]
  simp [pure, Except.pure]

end Miri.Input.ConcreteCovariance
