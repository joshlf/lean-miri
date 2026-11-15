import Miri.Input.SourceCompilerCasts

/-! Demand-time vtable input checks. The identity erasure rule applies only to
complete graphs without regions to erase or binders to anonymize, following
pinned rustc_middle/ty/erase_regions.rs:23–29 (the flags-free identity fast path).
interpret/traits.rs:26–30 erases the pair before monomorphism checks. Other graphs
need a structural transformation, not a table of precomputed pair answers. -/
namespace Miri.Input.SourceCompilerVTables
open Miri.Interpreter
abbrev World := SourceCompilerWorld.World
private def node (world : World) (id : Nat) : Except String TypeNode := do
  let some value := world.canonical.types[id]? | throw "Invalid source vtable type handle"
  unless value.id == id do throw "Invalid source vtable type/index identity"
  return value
private def predicate (world : World) (id : Nat) : Except String VtablePredicate := do
  let some value := world.canonical.predicates[id]? | throw "Invalid source vtable predicate handle"
  return value

/-- A checked fixed point of region erasure and binder anonymization. This is
not layout equality: every child, generic argument and predicate is inspected. -/
def erasedPair (world : World) (type : Nat) (predicates : PredicateList) :
    Except String (Nat × PredicateList) := do
  let fuel := world.canonical.types.size + world.canonical.predicates.size + 1
  checkType world fuel #[] type
  for id in predicates do checkPredicate world fuel #[] id
  return (type,predicates)
where
  checkArgs (world : World) (fuel : Nat) (seen : Array Nat) (args : Array MIR.GenericArg) : Except String Unit := do
    for arg in args do
      match arg with
      | .Type id => checkType world fuel seen id
      | .Lifetime .Erased => pure ()
      | .Lifetime _ => throw "Unsupported source vtable region-erasure transformation"
      | .Const id =>
        let some (.Value type tree) := world.canonical.typeConstants[id]?
          | throw "Unsupported source vtable non-value constant erasure"
        checkType world fuel seen type
        unless tree.nodes.all (fun value => match value with | .Leaf .. => true | _ => false) do
          throw "Unsupported source vtable aggregate constant erasure"
  checkPredicate (world : World) (fuel : Nat) (seen : Array Nat) (id : Nat) : Except String Unit := do
    let .succ fuel := fuel | throw "Invalid cyclic source vtable predicate graph"
    let value ← predicate world id
    unless value.boundVariables.isEmpty do throw "Unsupported source vtable predicate anonymization"
    checkArgs world fuel seen value.genericArgs
    if let some id := value.projectionTerm then checkType world fuel seen id
  checkType (world : World) (fuel : Nat) (seen : Array Nat) (id : Nat) : Except String Unit := do
    if seen.contains id then return
    let .succ fuel := fuel | throw "Invalid cyclic source vtable type graph"
    let seen := seen.push id
    match (← node world id).shape with
    | .bool | .char | .int _ | .uint _ | .float _ | .str | .never | .foreign _ => pure ()
    | .rawPointer child _ | .slice child | .patternType child .notNull => checkType world fuel seen child
    | .reference child _ region =>
      unless region == .Erased do throw "Unsupported source vtable reference region-erasure transformation"
      checkType world fuel seen child
    | .tuple fields => for child in fields do checkType world fuel seen child
    | .array child length _ =>
      checkArgs world fuel seen #[.Const length]
      checkType world fuel seen child
    | .closure _ args _ => checkArgs world fuel seen args
    | .adt data => checkArgs world fuel seen data.args
    | .functionDefinition _ args signature bound =>
      checkArgs world fuel seen args
      unless bound.isEmpty do throw "Unsupported source vtable signature anonymization"
      for child in signature.inputs.push signature.output do checkType world fuel seen child
    | .functionPointer signature bound =>
      unless bound.isEmpty do throw "Unsupported source vtable signature anonymization"
      for child in signature.inputs.push signature.output do checkType world fuel seen child
    | .dynamicTraitObject predicates _ region =>
      unless region == .Erased do throw "Unsupported source vtable object region-erasure transformation"
      for id in predicates do checkPredicate world fuel seen id
    | _ => throw "Unsupported source vtable type erasure constructor"

def ensureMonomorphicPredicates (world : World) (predicates : PredicateList) : Except String Unit := do
  for id in predicates do
    let value ← predicate world id
    unless value.boundVariables.isEmpty do throw "Unsupported source vtable predicate binder"
    for arg in value.genericArgs do
      match arg with
      | .Type id => SourceCompilerCasts.ensureMonomorphic world id
      | .Lifetime .Erased => pure ()
      | _ => throw "Unsupported source vtable predicate generic argument"
    if let some id := value.projectionTerm then SourceCompilerCasts.ensureMonomorphic world id
end Miri.Input.SourceCompilerVTables
