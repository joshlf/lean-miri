import Miri.Input.Model.Types

namespace Miri.Input

structure SourceAbiPolicy where
  architecture : String
  windows : Bool
  darwin : Bool
  simdTypesIndirect : Bool
  softFloat : Bool
  maxReliableAlignment : Nat
  boxNoAlias : Bool
  llvmWritable : Bool
  optimize : Bool
  panicUnwinds : Bool
  panicInDropUnwinds : Bool

structure SourceAbiDefinition where
  instanceId : InstanceId
  signature : FunctionSignature
  callerLocation : Option TypeId
  virtualCall : Bool
  hasDefinition : Bool
  foreign : Bool
  neverUnwind : Bool
  dropGlue : Bool
  noWritable : Bool


structure SourceAbiMaterial where
  policy : SourceAbiPolicy
  definitions : Array (Option SourceAbiDefinition)

end Miri.Input
