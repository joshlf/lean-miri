import Miri.Input.CompilerVirtualFacts
import Miri.Input.CompilerInstance
import Miri.Input.ConcreteVTable

/-! Actual imported GlobalAlloc::Function/VTable identity leaves. Runtime
allocation IDs are resolved through AllocationImage's mapping, never equated
with exported IDs. Complete instances share the program's compiler tables. -/
namespace Miri.Input.CompilerVTableRuntime
open Lean Miri.Memory Miri.Interpreter
abbrev Result := Except String

structure Prepared where
  facts : CompilerFactAdapters.Prepared
  obligations : Array Obligation

/-- Canonical instances remain in the input table. Preparation creates no
second identity table or semantic instance graph. -/
def prepare (facts : CompilerFactAdapters.Prepared) : Prepared := ⟨facts,#[]⟩

def functionInstance (prepared : Prepared) (id : InstanceId) : Result CallInstance := do
  let _ ← CompilerInstance.source prepared.facts.context.loweringContext.instances id
  pure id

/-- None means a known non-symbolic-function/vtable allocation. Missing image
metadata for an allocation declared symbolic is unresolved evidence, not None. -/
private def sourceNode (image : AllocationImage.Imported) (memory : MemoryState P E K)
    (id : AllocId) : Result (Option AllocationNode) := do
  if memory.hasImportedRuntimeId id then
    return some (← image.sourceNode memory id)
  let info ← (memory.getAllocInfo id).mapError fun error => reprStr error
  if info.kind == .function || info.kind == .vtable then
    throw "symbolic allocation has no imported compiler identity"
  return none

def globalFunction (prepared : Prepared)
    (image : AllocationImage.Imported)
    (memory : MemoryState P E K) (id : AllocId) : Result (Option CallInstance) := do
  let some node ← sourceNode image memory id | return none
  let some (.function source) := node.data | return none
  let fnInstance ← functionInstance prepared source.instanceId
  return some fnInstance

def globalVTable (prepared : Prepared) (image : AllocationImage.Imported)
    (memory : MemoryState P E K) (id : AllocId) : Result (Option (MIR.TyId × PredicateList)) := do
  let some node ← sourceNode image memory id | return none
  let some (.vtable source) := node.data | return none
  let _ ← prepared.facts.context.runtime.node source.typeId |>.mapError toString
  pure (some (source.typeId,source.predicates))

def entries (prepared : Prepared) (principal : Option Nat) (ty : MIR.TyId) :
    Result (Array (Interpreter.VTableEntry CallInstance)) :=
  ConcreteVTable.entries prepared.facts.context.program.input principal ty

private def lift (value : Result A) : EStateM StepError S A :=
  match value with
  | .ok value => pure value
  | .error error => throw (.unsupported s!"compiler symbolic allocation query: {error}")

/-- Install imported symbolic allocation queries with canonical machine memory.
Address resolution and vtable-entry/principal queries remain required leaves;
this does not manufacture them from the selected pointer's bytes. -/
def hooks (prepared : Prepared) (image : AllocationImage.Imported)
    (memory : S → MemoryState P E K) (base : VTableHooks P S C CallInstance Abi) :
    VTableHooks P S C CallInstance Abi :=
  { base with
    entries := fun _ principal ty => lift (entries prepared principal ty)
    globalFunction := fun _ id => do lift (globalFunction prepared image (memory (← get)) id)
    globalVTable := fun _ id => do lift (globalVTable prepared image (memory (← get)) id) }

end Miri.Input.CompilerVTableRuntime
