import Miri.Frontend.FoundationAllocations
import Miri.Frontend.FoundationConstOperand
import Miri.Frontend.FoundationRegionErasure

/-! Exact source allocation operands. Existing compiler allocation images are
retained as graph references; no byte key, pointer address or new allocation
identity is manufactured here. -/
namespace Miri.Frontend.Foundation
open Lean

def lowerAllocationConstantOperand (physical : PhysicalTypeRegistry) (spans : SpanRegistry)
    (operand : Json) : Except String (MIR.ConstOperand × ConcreteType) := do
  unless (← operand.getObjValAs? String "kind") == "constant" do throw "expected source constant"
  unless (← operand.getObjValAs? (Option Nat) "user_type").isNone do
    throw "allocation constant user-type annotation unsupported"
  let document := physical.registry.document
  let sourceType ← operand.getObjValAs? Nat "type"
  let concrete ← eraseRegions (← instantiate #[] #[] (← typeExpr document sourceType))
  let (next, typeId) ← physical.intern concrete
  unless next.types.size == physical.types.size && next.layouts.size == physical.layouts.size &&
      next.typeConstants.size == physical.typeConstants.size do
    throw "allocation operand physical type pool is not closed"
  let value ← sourceAllocationConstant document (← operand.getObjVal? "value")
  let key ← operand.getObjVal? "source_span_key"
  let lo ← key.getObjValAs? Nat "lo"
  let hi ← key.getObjValAs? Nat "hi"
  let context ← key.getObjValAs? String "ctxt"
  let parent ← key.getObjValAs? (Option Nat) "parent_local_definition"
  let entries := spans.compilerSpans.filter fun span =>
    span.lo == lo && span.hi == hi && span.context == context && span.parentLocalDefinition == parent
  unless entries.size == 1 do throw "missing exact allocation operand source span"
  let some entry := entries[0]? | throw "missing allocation operand span"
  unless entry.identity < spans.spans.size do throw "allocation operand physical span absent"
  return (⟨⟨entry.identity⟩,none,.Val value typeId⟩,concrete)

end Miri.Frontend.Foundation
