import Miri.Frontend.FoundationInstance
import Miri.Frontend.FoundationTarget
import Miri.Frontend.FoundationSource

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
require identical source type IDs. This conservative check rejects any distinct
but equivalent source representation instead of inventing normalization results.
The template's supported environment and every local type are instantiated by
`instantiateItem`; this function is not trait-method or shim resolution. -/
def prepareItem (d : Document) (definition : Nat)
    (arguments : Array ItemArgument) : Except String PreparedItem := do
  let target ← runtimeTargetOfTarget d.target
  let item ← instantiateItem d definition arguments
  validateSourceMetadata item.source
  let signature ← item.source.getObjVal? "signature"
  let inputs ← signature.getObjValAs? (Array Nat) "inputs"
  let output ← signature.getObjValAs? Nat "output"
  let locals ← item.source.getObjValAs? (Array Nat) "locals"
  unless inputs.size == item.argumentCount do throw "signature argument count disagrees with MIR"
  unless locals[0]? == some output do throw "signature output disagrees with MIR return local"
  for h : i in [:inputs.size] do
    unless locals[i+1]? == some inputs[i] do
      throw "signature input disagrees with MIR argument local"
  let safety ← signature.getObjValAs? String "safety"
  unless safety == "safe" || safety == "unsafe" do throw "unsupported function safety"
  let _abi ← signature.getObjVal? "abi"
  let _variadic ← signature.getObjValAs? Bool "c_variadic"
  return { target, item, signature }

end Miri.Frontend.Foundation
