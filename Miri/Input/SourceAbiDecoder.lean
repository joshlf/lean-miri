import Miri.Input.Model.SourceAbi
import Miri.Input.TableCore

namespace Miri.Input.SourceAbiDecoder
open JsonReader DecoderValues

private structure PolicyFields where
  architecture : Option String := none
  windows : Option Bool := none
  darwin : Option Bool := none
  simdTypesIndirect : Option Bool := none
  softFloat : Option Bool := none
  maxReliableAlignment : Option Nat := none
  boxNoAlias : Option Bool := none
  llvmWritable : Option Bool := none
  optimize : Option Bool := none
  incremental : Option Bool := none
  panicUnwinds : Option Bool := none
  panicInDropUnwinds : Option Bool := none

private def policy : Parser SourceAbiPolicy := do
  let p ← object ({} : PolicyFields) fun p key => do
    match key with
    | "architecture" => return {p with architecture := some (← string)}
    | "windows" => return {p with windows := some (← boolean)}
    | "darwin" => return {p with darwin := some (← boolean)}
    | "simd_types_indirect" => return {p with simdTypesIndirect := some (← boolean)}
    | "soft_float" => return {p with softFloat := some (← boolean)}
    | "max_reliable_alignment" => return {p with maxReliableAlignment := some (← natural)}
    | "box_noalias" => return {p with boxNoAlias := some (← boolean)}
    | "llvm_writable" => return {p with llvmWritable := some (← boolean)}
    | "optimize" => return {p with optimize := some (← boolean)}
    | "incremental" => return {p with incremental := some (← boolean)}
    | "panic_unwinds" => return {p with panicUnwinds := some (← boolean)}
    | "panic_in_drop_unwinds" => return {p with panicInDropUnwinds := some (← boolean)}
    | _ => skipValue; return p
  let alignment ← required p.maxReliableAlignment "max_reliable_alignment"
  unless alignment > 0 && alignment &&& (alignment - 1) == 0 do
    fail "source_abi.policy.max_reliable_alignment must be a power of two"
  return {
    architecture := ← required p.architecture "architecture"
    windows := ← required p.windows "windows", darwin := ← required p.darwin "darwin"
    simdTypesIndirect := ← required p.simdTypesIndirect "simd_types_indirect"
    softFloat := ← required p.softFloat "soft_float"
    maxReliableAlignment := alignment, boxNoAlias := ← required p.boxNoAlias "box_noalias"
    llvmWritable := ← required p.llvmWritable "llvm_writable", optimize := ← required p.optimize "optimize"
    incremental := ← required p.incremental "incremental"
    panicUnwinds := ← required p.panicUnwinds "panic_unwinds"
    panicInDropUnwinds := ← required p.panicInDropUnwinds "panic_in_drop_unwinds" }

private structure DefinitionFields where
  instanceId : Option Nat := none
  signature : Option FunctionSignature := none
  callerLocation : Option (Option Nat) := none
  virtualCall : Option Bool := none
  hasDefinition : Option Bool := none
  foreign : Option Bool := none
  neverUnwind : Option Bool := none
  dropGlue : Option Bool := none
  noWritable : Option Bool := none
  parameterUses : Option (Array UInt8) := none

private def definition : Parser SourceAbiDefinition := do
  let d ← object ({} : DefinitionFields) fun d key => do
    match key with
    | "instance_id" => return {d with instanceId := some (← natural)}
    | "signature" => return {d with signature := some (← parseFunctionSignature)}
    | "caller_location" => return {d with callerLocation := some (← nullable natural)}
    | "virtual_call" => return {d with virtualCall := some (← boolean)}
    | "has_definition" => return {d with hasDefinition := some (← boolean)}
    | "foreign" => return {d with foreign := some (← boolean)}
    | "never_unwind" => return {d with neverUnwind := some (← boolean)}
    | "drop_glue" => return {d with dropGlue := some (← boolean)}
    | "no_writable" => return {d with noWritable := some (← boolean)}
    | "parameter_uses" =>
      let uses ← array do
        let bits ← natural
        unless bits < 16 do fail "source_abi.parameter_uses: unknown usage bits"
        return UInt8.ofNat bits
      return {d with parameterUses := some uses}
    | _ => skipValue; return d
  return {
    instanceId := ← required d.instanceId "instance_id"
    signature := ← required d.signature "signature"
    callerLocation := ← required d.callerLocation "caller_location"
    virtualCall := ← required d.virtualCall "virtual_call"
    hasDefinition := ← required d.hasDefinition "has_definition"
    foreign := ← required d.foreign "foreign"
    neverUnwind := ← required d.neverUnwind "never_unwind"
    dropGlue := ← required d.dropGlue "drop_glue"
    noWritable := ← required d.noWritable "no_writable"
    parameterUses := ← required d.parameterUses "parameter_uses" }

def parse : Parser SourceAbiMaterial := do
  let (policy, definitions) ← object (none, none) fun (p, d) key => do
    match key with
    | "policy" => return (some (← policy), d)
    | "definitions" => return (p, some (← array (nullable definition)))
    | _ => skipValue; return (p, d)
  return ⟨← required policy "source_abi.policy", ← required definitions "source_abi.definitions"⟩

def validate (types : Array TypeNode) (instances : Array InstanceNode)
    (material : SourceAbiMaterial) : Except String Unit := do
  for (row, index) in material.definitions.toList.zipIdx do
    let some definition := row | continue
    unless definition.instanceId < instances.size do throw "source_abi: missing instance"
    unless definition.instanceId == index do throw "source_abi: instance/index mismatch"
    if let some (Miri.Interpreter.CallInstanceKind.LlvmIntrinsic _) := (instances[definition.instanceId]?).map (·.instanceKind) then
      throw "source_abi: LLVM intrinsic must not have an ordinary ABI definition"
    for id in definition.signature.inputs.push definition.signature.output ++ definition.callerLocation.toArray do
      unless id < types.size do throw "source_abi: missing signature type"

end Miri.Input.SourceAbiDecoder
