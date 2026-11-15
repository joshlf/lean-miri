import Miri.Frontend.FoundationConstEval
import Miri.Frontend.FoundationConstAggregatePhysical
import Miri.Frontend.FoundationPhysicalRegistry
import Miri.Frontend.FoundationSpanRegistry

/-! Demand evaluation and exact source/type relocation for scalar operands in
fixed MIR. Allocation/provenance constants and annotation joins are unsupported. -/
namespace Miri.Frontend.Foundation
open Lean

/-- Materialize a scalar literal into the existing fixed interpreter's constant
constructor, after pure source evaluation and document-local physical joins. -/
def lowerScalarConstantOperand (physical : PhysicalTypeRegistry) (spans : SpanRegistry)
    (operand : Json) : Except String (PhysicalTypeRegistry × MIR.ConstOperand) := do
  let document := physical.registry.document
  let result ← sourceConstantScalar document (← evaluateSourceConstant document operand)
  unless (← operand.getObjValAs? (Option Nat) "user_type").isNone do
    throw "const user-type annotation join unsupported"
  let key ← operand.getObjVal? "source_span_key"
  let lo ← key.getObjValAs? Nat "lo"
  let hi ← key.getObjValAs? Nat "hi"
  let context ← key.getObjValAs? String "ctxt"
  let parent ← key.getObjValAs? (Option Nat) "parent_local_definition"
  let entries := spans.compilerSpans.filter fun span =>
    span.lo == lo && span.hi == hi && span.context == context && span.parentLocalDefinition == parent
  unless entries.size == 1 do throw "missing or ambiguous exact const source span"
  let some source := entries[0]? | throw "missing const source span"
  let some _ := spans.spans[source.identity]? | throw "const physical source span absent"
  let sourceType ← typeExpr document result.typeId
  let concrete ← instantiate #[] #[] sourceType
  let (physical, typeId) ← physical.intern concrete
  let (_, layout) ← physical.lookup typeId
  unless layout.sizeBytes == some result.sizeBytes do throw "const scalar physical size mismatch"
  return (physical, {
    span := ⟨source.identity⟩, userType := none
    value := .Val (.Scalar (.Int result.bits result.sizeBytes)) typeId })

end Miri.Frontend.Foundation
