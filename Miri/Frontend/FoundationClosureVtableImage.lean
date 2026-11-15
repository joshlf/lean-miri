import Miri.Frontend.FoundationCallable
import Miri.Frontend.FoundationLayout
import Miri.Interpreter.VTableMachine

/-! Symbolic *candidate* image, not an allocation image. Pinned rustc
rustc_middle/ty/vtable.rs::vtable_allocation_provider initializes pointer-sized
cells and reserves function identities only after concrete method selection.
This module deliberately does not turn constructor recipes into AllocIds.
Closure layout follows rustc_ty_utils/layout.rs's univariant upvar layout;
only a sole function-pointer capture is admitted here. -/
namespace Miri.Frontend.Foundation

inductive ClosureVtableCell where
  | nullDrop
  | unsigned (value : Nat)
  /-- The method-or-vacant decision and executable shim remain obligations. -/
  | methodOrVacant (candidate : BuiltinClosureCandidate)

structure ClosureVtableImageCandidate where
  pointerBytes : Nat
  allocationAlign : Nat
  byteLength : Nat
  selfLayout : FoundationLayout
  cells : Array ClosureVtableCell
  /-- Preserved premises, never interpreted as discharged by layout. -/
  parentEnvironment : Lean.Json

/-- A one-field Rust closure cannot reorder fields. Its sole fn-pointer field
has no drop components (ty/util.rs::needs_drop_components); closure drop recurses
into upvars. The aggregate ABI minimum still contributes to alignment/rounding.
No general tuple/closure layout or DropGlue resolver is implied. -/
def closureVtableImageCandidate (document : Document) (definition : Nat)
    (parentArguments : Array ItemArgument) (principal : SourceClosureKind)
    (tupledInputs output : ConcreteType) : Except String ClosureVtableImageCandidate := do
  let plan ← builtinClosureVtableCandidates document definition parentArguments principal tupledInputs output
  let some first := plan.methods[0]? | throw "closure vtable has no method candidates"
  let .tuple captures := first.closure.tupledUpvars
    | throw "closure vtable upvars are not a source tuple"
  unless captures.size == 1 do throw "closure vtable layout requires one function-pointer capture"
  let some capture := captures[0]? | throw "closure vtable capture absent"
  let .functionPointer .. := capture
    | throw "closure vtable layout/drop requires a function-pointer capture"
  let field ← layoutOfDocument document capture
  let target ← runtimeTargetOfTarget document.target
  let aggregate ← target.aggregateAlign.bytes.mapError toString
  let alignment := max field.align aggregate.toNat
  unless alignment > 0 do throw "closure vtable alignment is zero"
  let size := (field.size + alignment - 1) / alignment * alignment
  unless size < target.base.objSizeBound.toNat do throw "closure vtable self size overflows"
  let pointerBytes := target.defaultAddressSpacePointerSpec.pointerSize.bytes.toNat
  let allocationAlign ← target.defaultAddressSpacePointerSpec.pointerAlign.bytes.mapError toString
  unless size < 2 ^ (8 * pointerBytes) && alignment < 2 ^ (8 * pointerBytes) do
    throw "closure vtable metadata does not fit target usize"
  let mut cells := #[]
  let mut methodIndex := 0
  for slot in plan.shape.slots do
    match slot with
    | .dropInPlace => cells := cells.push .nullDrop
    | .size => cells := cells.push (.unsigned size)
    | .alignment => cells := cells.push (.unsigned alignment)
    | .methodOrVacant .. =>
      let some candidate := plan.methods[methodIndex]? | throw "closure vtable method source missing"
      cells := cells.push (.methodOrVacant candidate)
      methodIndex := methodIndex + 1
  unless methodIndex == plan.methods.size do throw "closure vtable method source surplus"
  return ⟨pointerBytes,allocationAlign.toNat,pointerBytes * cells.size,
    ⟨size,alignment⟩,cells,first.parentEnvironment⟩

/-- A relocation candidate is conditional on selecting Method rather than
Vacant. Its byte offset is exact; its target is a constructor recipe, not an
allocation identifier or a pointer with invented provenance. -/
structure ClosureVtableRelocationCandidate where
  offset : Nat
  width : Nat
  target : BuiltinClosureCandidate

def ClosureVtableImageCandidate.relocations (image : ClosureVtableImageCandidate) :
    Array ClosureVtableRelocationCandidate := Id.run do
  let mut result := #[]
  for (cell,index) in image.cells.toList.zipIdx do
    if let .methodOrVacant candidate := cell then
      result := result.push ⟨index * image.pointerBytes,image.pointerBytes,candidate⟩
  return result

/-- Actual identity demand uses the unchanged fixed reservation machine. A
source-world miss remains Unsupported before any mutation. This is symbolic
identity reservation only: it neither writes the candidate image nor certifies
method dispatchability, executable shim bodies, or their function allocations.
The type/predicate IDs must come from the caller's checked physical registry. -/
def demandSourceClosureVtableIdentity
    (hooks : Miri.Interpreter.VTableMachine.Hooks K User Other)
    (typeId : Miri.MIR.TyId) (predicates : Miri.Interpreter.PredicateList)
    (salt : Fin 32) : Miri.Interpreter.MachineHooks.M K User Miri.Memory.AllocId := do
  unless (← get).machine.memory.sourceAllocIdWorldActive do
    throw (.unsupported "foundation closure vtable requires a source allocation identity world")
  Miri.Interpreter.VTableMachine.reserve hooks typeId predicates salt

end Miri.Frontend.Foundation
