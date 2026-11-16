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
  incremental : Bool
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
  /-- Optimized defining-body use summaries; concrete instance MIR can have
  different uses after substitution, so it is not a substitute for this input. -/
  parameterUses : Array UInt8

structure SourceAbiMaterial where
  policy : SourceAbiPolicy
  definitions : Array (Option SourceAbiDefinition)

end Miri.Input
