import Miri.Frontend.FoundationDirectCalls
import Miri.Frontend.FoundationEntry

/-! Pure selected-main and custom ordinary lang-start queries. The exporter
retains entry selection and generic signatures, never a monomorphic start answer.
The supported resolver checks an ordinary free-function template and substitutes
exactly the main return type, as pinned Miri eval.rs::call_main requests. -/
namespace Miri.Frontend.Foundation
open Lean

structure PendingMainEntry where
  definition : Nat
  mainInstance : Nat
  returnType : Nat
  functionPointerType : Nat
  startInstance : Option Nat
  startFunctionOrdinal : Option Nat

structure PendingMainEntries where
  selection : EntrySelection
  entries : Array PendingMainEntry

/-- Extend shared pools using source-selected entry and start definitions.
All supported signature constructors are binder-free; the exporter rejects
bound signatures and the structural type resolver rejects bound type variables.
Generic main, foreign/non-Rust/variadic signatures and missing start templates
fail closed. No source or runtime allocation identity is selected here. -/
def prepareMainEntries (initial : DirectCallPool) :
    Except String (DirectCallPool × PendingMainEntries) := do
  let document := initial.registry.physical.registry.document
  let sourceSelection ← document.source.getObjVal? "entry_selection"
  let _ ← sourceSelection.getObj?
  let _ ← sourceSelection.getObjVal? "compiler_entry"
  let _ ← sourceSelection.getObjVal? "start_lang_item"
  let selection ← entrySelection document.source
  let some selected := selection.compilerEntry
    | return (initial, ⟨selection, #[]⟩)
  let prepared ← prepareItem document selected.definition #[]
  let signature := prepared.signature
  unless (← signature.getObjValAs? (Array Nat) "inputs").isEmpty do
    throw "compiler main signature has arguments"
  let abi ← signature.getObjVal? "abi"
  unless (← abi.getObjValAs? String "kind") == "rust" &&
      (← abi.getObjVal? "unwind") == Json.null &&
      !(← signature.getObjValAs? Bool "c_variadic") do
    throw "compiler main requires ordinary Rust nonvariadic signature"
  let safety ← signature.getObjValAs? String "safety"
  unless safety == "safe" || safety == "unsafe" do throw "compiler main safety unsupported"
  let some result := prepared.item.localTypes[0]? | throw "compiler main return local absent"
  let (pool, mainNode, _) ← initial.internItem selected.definition #[]
  let (physical, returnType) ← pool.registry.physical.intern result
  let functionPointer := ConcreteType.functionPointer #[] result safety "rust" false
  let (physical, functionPointerType) ← physical.intern functionPointer
  let mut pool := { pool with registry := { pool.registry with physical } }
  let mut startInstance := none
  let mut startFunctionOrdinal := none
  if let some start := selection.startLangItem then
    -- Instance::try_resolve for DefKind::Fn is a direct Item construction;
    -- DirectCallPool rejects associated/trait/intrinsic kinds and checks every
    -- retained generic parameter and predicate before returning an instance.
    let (next, node, _) ← pool.internItem start #[.type result]
    pool := next
    let ordinal := (pool.functionInstances.findIdx? (· == node.id)).getD pool.functionInstances.size
    if ordinal == pool.functionInstances.size then
      pool := { pool with functionInstances := pool.functionInstances.push node.id }
    startInstance := some node.id
    startFunctionOrdinal := some ordinal
  let entry := PendingMainEntry.mk selected.definition mainNode.id returnType functionPointerType
    startInstance startFunctionOrdinal
  return (pool, ⟨selection, #[entry]⟩)

/-- Join the computed start instance with the final FnDef physical identity.
Missing link-section evidence is retained as none for the separate source
link-section builder to fill; it is never replaced by an empty answer here. -/
def finishMainEntries (pending : PendingMainEntries) (types : DirectCallPool.FunctionTypes) :
    Except String Input.Catalog.Main := do
  let mut entries := #[]
  for entry in pending.entries do
    let startResolution ← match entry.startInstance, entry.startFunctionOrdinal with
      | none, none => pure none
      | some id, some ordinal => do
        let some functionType := types.typeIds[ordinal]? | throw "main start FnDef identity absent"
        let some node := types.types[functionType]? | throw "main start FnDef physical type absent"
        unless node.shapeKind == .functionDefinition do throw "main start physical type is not FnDef"
        pure (some (⟨id, functionType⟩ : Input.Catalog.StartResolution))
      | _, _ => throw "main start instance/function identity mismatch"
    entries := entries.push {
      definition := entry.definition
      genericParameters := #[]
      signature := {
        compilerSelectedEntry := true
        hasBoundVariables := false
        outputHasBoundVariables := false
        returnType := entry.returnType
        functionPointerType := entry.functionPointerType
        startResolution } }
  let compilerEntry := pending.selection.compilerEntry.map fun selected => selected.definition
  let compilerEntryType := pending.selection.compilerEntry.map fun selected => {
    definition := selected.definition
    kind := "rustc_main"
    sigpipe := selected.sigpipe.toNat : Input.Catalog.CompilerEntry }
  return ⟨pending.selection.startLangItem, compilerEntry, compilerEntryType, entries, none⟩

end Miri.Frontend.Foundation
