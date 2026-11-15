import Miri.Input.TypeArenaWorld

namespace Miri.Input.WorldTypeMetadata
open TypeArena
private def lift [Monad m] [MonadExceptOf String m] (value : Except String A) : m A :=
  match value with | .ok result => pure result | .error error => throw error

def adtDeclaration (id : TypeId) : WorldM AdtDeclaration.Material := do
  let world ← get
  let definition ← match ← lift (world.lookupType id) with
    | .material source => match source.shape with
      | .adt data => pure data.definition
      | _ => throw "metadata ADT declaration requested for another type"
    | .constructed (.adt identity _) => lift (world.definitionRef identity)
    | _ => throw "metadata ADT declaration requested for another constructor"
  let some source := world.definitions[definition]? | throw "metadata ADT definition absent"
  let some declaration := source.adtDeclaration | throw "metadata canonical ADT declaration absent"
  let some template := source.genericTemplate | throw "metadata ADT field template absent"
  lift (declaration.validate template)
  pure declaration

end Miri.Input.WorldTypeMetadata
