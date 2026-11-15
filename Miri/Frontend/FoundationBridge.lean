import Miri.Frontend.FoundationInstance
import Miri.Frontend.FoundationTarget
import Miri.Frontend.FoundationSource
import Miri.Frontend.FoundationRegionErasure
import Miri.Frontend.FoundationTypeRegistry

/-! Preparation at the finite-material/fixed-interpreter boundary. This module
constructs genuine target data and substituted item templates, checking retained
source metadata and signature/local joins. It does not construct `Input.Program`
or invoke a second evaluator. Executable lowering, physical type interning and
full FnAbi construction remain necessary before fixed-interpreter execution. -/
namespace Miri.Frontend.Foundation
open Lean

structure PreparedItem where
  target : ABI.RuntimeTargetDataLayout
  item : ItemTemplate
  /-- Original compiler signature, including ABI, safety and variadic status. -/
  signature : Json

/-- Prepare one explicitly selected template. Signature/local joins currently
compare structural types after exact supported region erasure. Original source
signature/local IDs remain retained; no other normalization is inferred.
The template's supported environment and every local type are instantiated by
`instantiateItem`; this function is not trait-method or shim resolution. -/
def prepareItem (d : Document) (definition : Nat)
    (arguments : Array ItemArgument) : Except String PreparedItem := do
  let target ← runtimeTargetOfTarget d.target
  let sourceItem ← instantiateItem d definition arguments
  let item := {sourceItem with localTypes := ← sourceItem.localTypes.mapM eraseRegions}
  validateSourceMetadata item.source
  let signature ← item.source.getObjVal? "signature"
  let inputs ← signature.getObjValAs? (Array Nat) "inputs"
  let output ← signature.getObjValAs? Nat "output"
  let locals ← item.source.getObjValAs? (Array Nat) "locals"
  unless inputs.size == item.argumentCount do throw "signature argument count disagrees with MIR"
  let types := arguments.map fun arg => match arg with | .type ty => some ty | _ => none
  let constants := arguments.map fun arg => match arg with | .constant n => some n | _ => none
  let resolved (id : Nat) : Except String ConcreteType := do
    eraseRegions (← instantiate types constants (← typeExpr d id))
  let some returnSource := locals[0]? | throw "MIR return local source type absent"
  unless sameConcrete 1024 (← resolved output) (← resolved returnSource) do
    throw "signature output disagrees with MIR return local after region erasure"
  for h : i in [:inputs.size] do
    let some localSource := locals[i+1]? | throw "MIR argument source type absent"
    unless sameConcrete 1024 (← resolved inputs[i]) (← resolved localSource) do
      throw "signature input disagrees with MIR argument local after region erasure"
  let safety ← signature.getObjValAs? String "safety"
  unless safety == "safe" || safety == "unsafe" do throw "unsupported function safety"
  let _abi ← signature.getObjVal? "abi"
  let _variadic ← signature.getObjValAs? Bool "c_variadic"
  return { target, item, signature }

end Miri.Frontend.Foundation
