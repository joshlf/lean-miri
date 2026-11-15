import Miri.Input.SourcePhysical

/-! Original signature identities and their region-erased layout queries are
separate. Bound regions below a checked signature binder are never replaced by
an erased region in the resulting TypeShape. -/
namespace Miri.Input.SourceSignatureTypes
open SourceTypes

private def region (material : Material) (binder : Array BoundVariable)
    (world : SourceCompilerWorld.World) (value : Region) :
    Except String (SourceCompilerWorld.World × MIR.Region) := do
  match value with
  | .static => return (world,.Static)
  | .erased => return (world,.Erased)
  | .bound depth slot kind =>
    unless depth == 0 && binder[slot]? == some (.region kind) do
      throw "Unsupported original signature region binder depth/slot"
    let (world,kind) ← match kind with
      | .anonymous => pure (world,MIR.BoundRegionKind.Anon)
      | .namedForPrinting name => pure (world,.NamedForPrinting name)
      | .closureEnvironment => pure (world,.ClosureEnv)
      | .named definition => do
        let some row := material.definitions[definition]? | throw "Invalid signature named region definition"
        unless row.kind == "LifetimeParam" do throw "Invalid signature named region category"
        let (world,id) ← SourceCompilerWorld.internDefinition world row.raw
        pure (world,.Named id)
    return (world,.Bound (.Bound depth) slot kind)
  | .unsupported tag => throw s!"Unsupported original signature region {tag}"

/-- Translate binder declarations through the same checked raw-definition map
used by signature references. -/
def boundVariables (initial : SourceCompilerWorld.World) (binder : Array BoundVariable) :
    Except String (SourceCompilerWorld.World × Array MIR.BoundVariableKind) := do
  let some source := initial.canonical.sourceMaterial | throw "Unsupported signature source unavailable"
  let some material := source.physical | throw "Unsupported signature types unavailable"
  let mut world := initial
  let mut result := #[]
  for (entry,slot) in binder.zipIdx do
    let .region kind := entry | throw "Unsupported original signature non-region binder"
    let (updated,value) ← region material binder world (.bound 0 slot kind)
    world := updated
    let .Bound _ _ kind := value | throw "Invalid translated signature region binder"
    result := result.push (MIR.BoundVariableKind.Region kind)
  return (world,result)

/-- Construct source signature identity using the erased physical query only
for geometry. This domain supports primitive, tuple, array, pointer and
existential predicate trees, plus instantiated nominal types under an empty
signature binder; other constructors remain Unsupported rather than silently erase identity. -/
def intern (initial : SourceCompilerWorld.World) (bindings : Array (Option Concrete))
    (constants : Array (Option Nat)) (binder : Array BoundVariable) (reference : TypeRef) :
    Except String (SourceCompilerWorld.World × TypeId) := go 1024 initial reference
where
  go (fuel : Nat) (world : SourceCompilerWorld.World) (reference : TypeRef) :
      Except String (SourceCompilerWorld.World × TypeId) := do
    let .succ fuel := fuel | throw "Unsupported original signature recursion exhausted"
    let some source := world.canonical.sourceMaterial | throw "Unsupported signature source unavailable"
    let some material := source.physical | throw "Unsupported signature types unavailable"
    let some expr := material.types[reference]? | throw "Invalid signature type reference"
    let erased ← instantiate material bindings constants reference binder
    let (world,erasedId) ← SourcePhysical.intern world erased
    let some erasedNode := world.canonical.types[erasedId]? | throw "Invalid erased signature type"
    let some layout := world.canonical.layouts[erasedNode.layoutId]? | throw "Invalid erased signature layout"
    let (world,shape) ← match expr with
      | .primitive .. | .parameter .. => pure (world,erasedNode.shape)
      | .nominal .. =>
        -- Successful instantiation with an empty signature binder cannot
        -- erase any bound reference: bound-region lookup would have failed.
        -- Static and already-erased regions remain unchanged in Concrete.
        unless binder.isEmpty do throw "Unsupported original nominal signature under a binder"
        pure (world,erasedNode.shape)
      | .reference pointee mutable value => do
        let (world,pointee) ← go fuel world pointee
        let (updated,value) ← region material binder world value
        pure (updated,TypeShape.reference pointee mutable value)
      | .rawPointer pointee mutable => do
        let (world,pointee) ← go fuel world pointee
        pure (world,TypeShape.rawPointer pointee mutable)
      | .tuple references => do
        let mut world := world
        let mut ids := #[]
        for reference in references do
          let (updated,id) ← go fuel world reference
          world := updated; ids := ids.push id
        pure (world,TypeShape.tuple ids)
      | .array element _ => do
        let .array _ length constructor := erasedNode.shape | throw "Invalid erased signature array shape"
        let (world,element) ← go fuel world element
        pure (world,TypeShape.array element length constructor)
      | .dynamicObject value predicates => do
        let .dynamicTraitObject erasedPredicates _ _ := erasedNode.shape
          | throw "Invalid erased signature dynamic shape"
        unless predicates.size == erasedPredicates.size do throw "Invalid erased signature predicate count"
        let mut world := world
        let mut ids := #[]
        let mut principal := none
        for (predicate,erasedPredicate) in predicates.zip erasedPredicates do
          let some row := world.canonical.predicates[erasedPredicate]?
            | throw "Invalid erased signature predicate"
          let (arguments,term) ← match predicate with
            | .trait _ arguments bound =>
              unless bound.isEmpty do throw "Unsupported nested existential binder"
              pure (arguments,none)
            | .projection _ _ arguments term bound =>
              unless bound.isEmpty do throw "Unsupported nested existential binder"
              pure (arguments,some term)
            | .autoTrait _ bound =>
              unless bound.isEmpty do throw "Unsupported nested existential binder"
              pure (#[],none)
            | .unsupported tag => throw s!"Unsupported signature predicate {tag}"
          let mut args : Array MIR.GenericArg := #[]
          for argument in arguments do
            let .type reference := argument | throw "Unsupported signature predicate non-type argument"
            let (updated,id) ← go fuel world reference
            world := updated; args := args.push (.Type id)
          let mut termId := none
          if let some term := term then
            let (updated,id) ← go fuel world term
            world := updated; termId := some id
          let (updated,id) ← SourceCompilerWorld.internPredicate world {row with genericArgs := args, projectionTerm := termId}
          world := updated; ids := ids.push id
          if row.kind == .trait then principal := some id
        let (updated,value) ← region material binder world value
        world := updated
        pure (world,TypeShape.dynamicTraitObject ids principal value)
      | _ => throw "Unsupported original signature constructor identity"
    SourceCompilerWorld.internType world shape layout "source signature type"
end Miri.Input.SourceSignatureTypes
