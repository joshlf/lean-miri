import Miri.Frontend.FoundationClosurePhysical
import Miri.Frontend.FoundationBodyCore
import Miri.Frontend.FoundationInstanceRegistry

/-! Ordinary closure Item MIR, sharing the existing syntax/importer path.
Preparation gathers structural types before a caller freezes shim/FnDef pools.
It preserves source calls; call resolution/ABI evidence is a separate demand.
No closure Item instance, body slot, executable query or allocation is invented. -/
namespace Miri.Frontend.Foundation
open Lean

private def closureSourceType (document : Document) (selected : SelectedClosureTemplate)
    (id : Nat) : Except String ConcreteType := do
  let types := selected.fullArguments.map fun arg => match arg with | .type ty => some ty | _ => none
  let constants := selected.fullArguments.map fun arg => match arg with | .constant n => some n | _ => none
  eraseRegions (← instantiate types constants (← typeExpr document id))

/-- Nonexecuting type preparation: parent predicates remain obligations. Validate
source closure signature against the explicit environment receiver and unpacked
argument tuple of its ordinary MIR. RustCall here is the retained closure call
signature, not an invented ordinary Item FnAbi. -/
def prepareClosureMIRTypes (physical : PhysicalTypeRegistry) (definition : Nat)
    (parentArguments : Array ItemArgument) :
    Except String (PhysicalTypeRegistry × PreparedItem) := do
  let document := physical.registry.document
  let (physical,binding) ← internSourceClosure physical definition parentArguments
  let selected := binding.selected
  unless selected.spreadArgument.isNone do throw "closure Item spread argument lowering unsupported"
  let mut locals := #[]
  for id in (← selected.body.getObjValAs? (Array Nat) "locals") do
    locals := locals.push (← closureSourceType document selected id)
  let some output := locals[0]? | throw "closure MIR output local absent"
  unless sameConcrete 1024 output (← eraseRegions selected.signature.output) do
    throw "closure MIR output differs from retained closure signature"
  unless selected.signature.inputs.size == 1 do throw "closure call signature tuple input absent"
  let some (ConcreteType.tuple arguments) := selected.signature.inputs[0]? | throw "closure call input is not tuple"
  let argumentCount ← selected.body.getObjValAs? Nat "argument_count"
  unless argumentCount == arguments.size + 1 && argumentCount < locals.size do
    throw "closure MIR environment/argument count differs from source signature"
  let closureTy ← eraseRegions binding.closureTy
  let receiver := match selected.kind with
    | .fn => ConcreteType.pointer "reference_erased_const" closureTy
    | .fnMut => .pointer "reference_erased_mut" closureTy
    | .fnOnce => closureTy
  let some actualReceiver := locals[1]? | throw "closure MIR environment local absent"
  unless sameConcrete 1024 receiver actualReceiver do throw "closure MIR receiver differs from closure kind"
  for (expected,i) in arguments.zipIdx do
    let some actual := locals[i+2]? | throw "closure MIR explicit argument local absent"
    unless sameConcrete 1024 actual (← eraseRegions expected) do throw "closure MIR argument type mismatch"
  -- Closure templates carry a validated parent environment plus synthetic
  -- parameters rather than an ordinary body's flat environment field.
  -- Admit only the genuinely empty full required list at this boundary.
  unless (← selected.body.getObjValAs? (Array Json) "required_consts").isEmpty do
    throw "closure required-constant evaluation unsupported"
  let some signatureRow := document.types[← selected.body.getObjValAs? Nat "signature_type"]?
    | throw "closure call signature source absent"
  let signature ← (← signatureRow.getObjVal? "shape").getObjVal? "signature"
  let item : ItemTemplate := ⟨definition, selected.fullArguments, locals, argumentCount, selected.body⟩
  let prepared : PreparedItem := ⟨← runtimeTargetOfTarget document.target, item, signature⟩
  let mut physical := physical
  for localType in locals do
    let (next,_) ← physical.intern localType
    physical := next
  return (physical,prepared)

/-- Resolve source projection annotations against the same substituted closure
arguments and physical pool used by the ordinary MIR locals. -/
def closureMIRJoins (physical : PhysicalTypeRegistry) (selected : SelectedClosureTemplate) :
    RvalueSourceJoins := {
  sourceType := closureSourceType physical.registry.document selected
  physicalType := fun concrete => do
    let some id := physical.registry.entries.findIdx? (fun entry => sameConcrete 1024 entry.type concrete)
      | throw "closure source projected type not interned"
    return id }

/-- Check the syntax returned by a call-query join against every supported
source call field. In particular a missing query cannot substitute Return or
another successful no-op for a real call. Function-instance/ABI resolution is
still supplied by the caller's checked demand pool. -/
def checkClosureCallSyntax (prepared : PreparedItem) (joins : RvalueSourceJoins)
    (constantOperand : Json → Except String (MIR.ConstOperand × ConcreteType))
    (evidence : Input.CallResolutionEvidence) (source spans : Json)
    (result : MIR.TerminatorKind) : Except String Unit := do
  let .Call function arguments destination target unwind callSource functionSpan := result
    | throw "closure call join replaced source Call constructor"
  unless evidence.kind == .direct && evidence.instanceId.isSome && evidence.dispatchSlot.isNone do
    throw "closure FnDef call requires checked direct-instance evidence"
  let fnSource ← source.getObjVal? "function"
  unless (← fnSource.getObjValAs? String "kind") == "constant" &&
      (← (← fnSource.getObjVal? "value").getObjValAs? String "kind") == "zero_sized" &&
      (← fnSource.getObjVal? "user_type") == Json.null do throw "closure source FnDef call unsupported"
  let .Constant constant := function | throw "closure source FnDef call changed operand kind"
  let .Val .ZeroSized functionType := constant.value
    | throw "closure source FnDef call changed constant"
  let span ← spans.getObjVal? "function_operand"
  unless constant.userType.isNone && constant.span.id == (← span.getObjValAs? Nat "span_id") &&
      evidence.functionType == some functionType do throw "closure FnDef type/span join mismatch"
  let sourceKey ← fnSource.getObjVal? "source_span_key"
  for field in #["lo", "hi", "ctxt", "parent_local_definition"] do
    unless (← sourceKey.getObjVal? field) == (← span.getObjVal? field) do throw "closure FnDef source span mismatch"
  let argumentSources ← source.getObjValAs? (Array Json) "arguments"
  let argumentSpans ← spans.getObjValAs? (Array Json) "arguments"
  unless arguments.size == argumentSources.size && arguments.size == argumentSpans.size do
    throw "closure Call argument count mismatch"
  for i in [:arguments.size] do
    let some argument := arguments[i]? | throw "closure call argument absent"
    let some argumentSource := argumentSources[i]? | throw "closure source argument absent"
    let some argumentSpan := argumentSpans[i]? | throw "closure argument source span absent"
    let (expected,_,_) ← lowerSourceOperand prepared joins constantOperand argumentSource
    unless argument.operand == expected && argument.span.id == (← argumentSpan.getObjValAs? Nat "span_id") do
      throw "closure Call argument syntax/span changed"
  let expectedDestination ← lowerSourcePlace prepared.item.localTypes (← source.getObjVal? "destination") joins
  unless destination == expectedDestination.place do throw "closure Call destination changed"
  let _ ← source.getObjVal? "target"
  let expectedTarget ← source.getObjValAs? (Option Nat) "target"
  unless target == expectedTarget do throw "closure Call target changed"
  let blocks ← prepared.item.source.getObjValAs? (Array Json) "blocks"
  if let some target := target then
    unless target < blocks.size do throw "closure Call target out of bounds"
  let sourceUnwind ← source.getObjVal? "unwind"
  let expectedUnwind ← match ← sourceUnwind.getObjValAs? String "kind" with
    | "Continue" => pure MIR.UnwindAction.Continue
    | "Cleanup" => do
      let target ← sourceUnwind.getObjValAs? Nat "target"
      let some block := blocks[target]? | throw "closure unwind cleanup target absent"
      unless (← block.getObjValAs? Bool "cleanup") do throw "closure unwind target not cleanup"
      pure (.Cleanup target)
    | _ => throw "closure Call unwind action unsupported"
  unless unwind == expectedUnwind && callSource == .Normal &&
      (← source.getObjValAs? String "call_source") == "normal_call" &&
      functionSpan.id == (← (← spans.getObjVal? "function").getObjValAs? Nat "span_id") do
    throw "closure Call unwind/source/function span changed"

structure ClosureItemBody where
  bodyId : Nat
  body : Input.Body
  /-- Body-local namespace; assembly must relocate it once alongside this body. -/
  spans : SpanRegistry

/-- Join the selected ordinary closure body to an already reserved canonical
Item slot. Structural preparation must precede shim/FnDef finalization: this
function rejects if a local type would grow the existing registry. The caller
provides source-derived call query answers through the existing BodyCore join;
missing calls, required constants or parent obligations reject. -/
def lowerClosureItemBody (registry : InstanceRegistry) (definition : Nat)
    (parentArguments : Array ItemArgument) (physicalTypeIds : Array Nat)
    (constantOperand : Json → Except String (MIR.ConstOperand × ConcreteType) :=
      fun _ => .error "closure constant query unavailable")
    (callTerminator : Nat → Json → Json → Except String MIR.TerminatorKind :=
      fun _ _ _ => .error "closure call resolution unavailable")
    (callEvidence : Array (Option Input.CallResolutionEvidence) := #[])
    (requiredConsts : Array MIR.ConstOperand := #[]) : Except String ClosureItemBody := do
  let document := registry.physical.registry.document
  let (physical,prepared) ← prepareClosureMIRTypes registry.physical definition parentArguments
  unless physical.types.size == registry.physical.types.size do
    throw "closure local types must be interned before function-type finalization"
  let selected ← selectClosureTemplate document definition parentArguments
  let parentTypes := parentArguments.map fun arg => match arg with | .type ty => some ty | _ => none
  let parentConsts := parentArguments.map fun arg => match arg with | .constant n => some n | _ => none
  checkEnvironment document parentTypes parentConsts selected.parentEnvironment
  let mut arguments := #[]
  for argument in selected.fullArguments do
    let .type concrete := argument | throw "closure Item non-type generic argument unsupported"
    let some id := physical.registry.entries.findIdx? (fun entry => sameConcrete 1024 entry.type concrete)
      | throw "closure Item generic physical type absent"
    arguments := arguments.push (MIR.GenericArg.Type id)
  let candidates := registry.instances.filter fun node =>
    node.instanceKind == .Item definition && node.genericArgs == arguments
  unless candidates.size == 1 do throw "missing or duplicate canonical closure Item instance"
  let some node := candidates[0]? | throw "canonical closure Item absent"
  let some nodeIndex := registry.instances.findIdx? (fun existing =>
    existing.instanceKind == .Item definition && existing.genericArgs == arguments)
    | throw "canonical closure Item index absent"
  unless node.id == nodeIndex do throw "canonical closure Item dense identity mismatch"
  let some bodyId := node.bodyId | throw "canonical closure Item body absent"
  unless registry.bodyDefinitions[bodyId]? == some definition && node.promotedBodies.isEmpty do
    throw "closure Item body source association mismatch"
  let some row := document.definitions[definition]? | throw "closure source definition absent"
  let templates ← document.source.getObjValAs? (Array Json) "closure_templates"
  let some sourceIndex := templates.findIdx? (· == selected.body) | throw "closure source template location absent"
  let spans ← buildSpanRegistry selected.body
  let joins := closureMIRJoins physical selected
  let body ← lowerPreparedBodyCore prepared {
    types := physical.registry.entries.mapIdx fun id entry => ⟨entry.type,id⟩
    physicalTypeIds, spans := spans.spans, compilerSpans := spans.compilerSpans,
    files := spans.files, definitionId := definition, instanceNode := node,
    defPath := ← row.getObjValAs? String "path", sourcePath := s!"$.closure_templates[{sourceIndex}]",
    backtraceSpans := spans.backtraces, requiredConsts }
    constantOperand (fun block source sourceSpans => do
      let result ← callTerminator block source sourceSpans
      let some evidence := callEvidence[block]?.bind id | throw "closure call query evidence unavailable"
      let some functionType := evidence.functionType | throw "closure FnDef evidence type absent"
      unless physicalTypeIds.contains functionType do throw "closure FnDef evidence type not in frozen pool"
      checkClosureCallSyntax prepared joins constantOperand evidence source sourceSpans result
      return result) callEvidence joins
  return ⟨bodyId,{ body with promotedBodies := #[] },spans⟩

end Miri.Frontend.Foundation
