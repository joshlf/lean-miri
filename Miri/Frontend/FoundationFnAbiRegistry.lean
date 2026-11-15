import Miri.Frontend.FoundationFnAbi
import Miri.Frontend.FoundationPhysicalRegistry
import Miri.Frontend.FoundationBridge

/-! Document-to-ABI construction for explicit ordinary item requests. IDs are
created by the physical registry, never supplied by the requester. Indirect modes
fail: pinned rustc_ty_utils/src/abi.rs::fn_abi_of_instance_raw can add attributes
from MIR deduction after fn_abi_new_uncached, and that analysis is not ported.
Direct/ignore/cast modes are unaffected by apply_deduced_attributes. -/
namespace Miri.Frontend.Foundation

private def internAbiType (registry : PhysicalTypeRegistry) (ty : ConcreteType) :
    Except String (PhysicalTypeRegistry × AbiTypeBinding) := do
  let (registry, id) ← registry.intern ty
  let (node, layout) ← registry.lookup id
  let expected ← layoutOf registry.registry.document.target ty
  unless layout.sizeBytes == some expected.size && layout.abiAlignBytes == some expected.align do
    throw "foundation ABI physical layout size/alignment mismatch"
  let _ ← registry.runtimeLayout id
  return (registry, ⟨ty, node.id, node.layoutId⟩)

/-- Build physical tables and exact supported FunctionAbi from a finite document
and an explicit item request. A fresh registry guarantees every identity was
constructed here. This returns component tables, not an executable Program.
Foreign, variadic, track_caller and non-Rust signatures fail closed. -/
def rustFunctionAbiOfItem (document : Document) (definition : Nat)
    (arguments : Array ItemArgument) : Except String (PhysicalTypeRegistry × Input.FunctionAbi) := do
  let prepared ← prepareItem document definition arguments
  let signature := prepared.signature
  let abi ← signature.getObjVal? "abi"
  unless (← abi.getObjValAs? String "kind") == "rust" do
    throw "foundation FnAbi requires ordinary Rust ABI"
  unless (← abi.getObjVal? "unwind") == Lean.Json.null do
    throw "foundation Rust ABI has unexpected unwind spelling"
  unless !(← signature.getObjValAs? Bool "c_variadic") do
    throw "foundation variadic FnAbi is unsupported"
  let attrs ← prepared.item.source.getObjVal? "function_attributes"
  unless !(← attrs.getObjValAs? Bool "track_caller") &&
      !(← attrs.getObjValAs? Bool "is_foreign") &&
      !(← attrs.getObjValAs? Bool "is_drop_glue") do
    throw "foundation FnAbi requires ordinary item without caller-location adjustment"
  let unwind ← rustUnwindFactsOfSource document.source prepared.item.source
  let some resultType := prepared.item.localTypes[0]? | throw "missing ABI return type"
  let mut registry := PhysicalTypeRegistry.start document
  let (next, result) ← internAbiType registry resultType
  registry := next
  let mut bindings := #[]
  for i in [:prepared.item.argumentCount] do
    let some ty := prepared.item.localTypes[i+1]? | throw "missing ABI argument type"
    let (next, binding) ← internAbiType registry ty
    registry := next
    bindings := bindings.push binding
  let result ← rustFunctionAbiComponent document.target document.target.architecture unwind bindings result
  for arg in result.arguments.push result.returnValue do
    if arg.mode.kind == .indirect || arg.mode.kind == .indirectUnsized then
      throw "foundation indirect FnAbi requires unported MIR attribute deduction"
  return (registry, result)

end Miri.Frontend.Foundation
