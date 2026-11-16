import Miri.Input.Model.Types

namespace Miri.Input

structure SourceObjectTrait where
  principal : PredicateId
  ownMethods : Array DefinitionRef
  superTraits : Array PredicateId
  deriving Repr, DecidableEq

structure SourceVTableMethod where
  owner : PredicateId
  definition : DefinitionRef
  instanceId : Option InstanceId
  deriving Repr, DecidableEq

structure SourceVTableBinding where
  typeId : TypeId
  principal : Option PredicateId
  dropInstance : InstanceId
  methods : Array SourceVTableMethod
  deriving Repr, DecidableEq

structure SourceVTableMaterial where
  noTraitVptr : Bool := false
  objectTraits : Array SourceObjectTrait := #[]
  bindings : Array SourceVTableBinding := #[]
  deriving Repr, DecidableEq

end Miri.Input
