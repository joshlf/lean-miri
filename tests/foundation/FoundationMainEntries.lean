import Miri.Frontend.FoundationMainEntries

open Lean Miri.Frontend.Foundation

private def checked {α : Type} : Except String α → IO α
  | .ok value => pure value
  | .error e => throw (IO.userError e)

private def sourceIdentity (document : Document) (id : Nat) : Except String (Nat × Nat) := do
  let some row := document.definitions[id]? | throw "source definition absent"
  return (← row.getObjValAs? Nat "crate_index", ← row.getObjValAs? Nat "index")

private def referenceIdentity (definitions : Array Json) (id : Nat) : Except String (Nat × Nat) := do
  let some row := definitions[id]? | throw "reference definition absent"
  return (← row.getObjValAs? Nat "crate", ← row.getObjValAs? Nat "index")

/-- Fresh no_std custom #[lang=start] finite material versus independent schema12
main query answers. Pool IDs are compared through exact source DefIds/type shapes. -/
def main (paths : List String) : IO Unit := do
  let [sourcePath, referencePath] := paths | throw (IO.userError "expected finite and schema12 custom-start exports")
  let document ← checked (Json.parse (← IO.FS.readFile sourcePath) >>= decode)
  let pool ← checked (DirectCallPool.start (PhysicalTypeRegistry.start document))
  let (pool, pending) ← checked (prepareMainEntries pool)
  let frozen ← checked pool.finishFunctionTypes
  let main ← checked (finishMainEntries pending frozen)
  let some entry := main.entries[0]? | throw (IO.userError "computed main entry absent")
  let some resolution := entry.signature.startResolution | throw (IO.userError "computed start resolution absent")
  let some start := main.startLangItem | throw (IO.userError "source start lang item absent")
  let some compilerType := main.compilerEntryType | throw (IO.userError "source EntryFnType absent")
  let reference ← checked (Json.parse (← IO.FS.readFile referencePath))
  let referenceMain ← checked (reference.getObjVal? "compiler_main_queries")
  let definitions ← checked (reference.getObjValAs? (Array Json) "definitions")
  let referenceEntry ← checked (referenceMain.getObjValAs? Nat "compiler_entry")
  unless (← checked (sourceIdentity document entry.definition)) == (← checked (referenceIdentity definitions referenceEntry)) do
    throw (IO.userError "compiler-selected entry DefId mismatch")
  let referenceStart ← checked (referenceMain.getObjValAs? Nat "start_lang_item")
  unless (← checked (sourceIdentity document start)) == (← checked (referenceIdentity definitions referenceStart)) do
    throw (IO.userError "start lang item DefId mismatch")
  let entryType ← checked (referenceMain.getObjVal? "compiler_entry_type")
  unless compilerType.kind == (← checked (entryType.getObjValAs? String "kind")) &&
      compilerType.sigpipe == (← checked (entryType.getObjValAs? Nat "sigpipe")) do
    throw (IO.userError "compiler EntryFnType payload mismatch")
  let entries ← checked (referenceMain.getObjValAs? (Array Json) "entries")
  let some referenceEntry := entries[0]? | throw (IO.userError "reference main entry absent")
  let signature ← checked (referenceEntry.getObjVal? "signature_query")
  for (key, value) in #[("compiler_selected_entry", entry.signature.compilerSelectedEntry),
      ("has_bound_variables", entry.signature.hasBoundVariables),
      ("output_has_bound_variables", entry.signature.outputHasBoundVariables)] do
    unless value == (← checked (signature.getObjValAs? Bool key)) do throw (IO.userError s!"entry signature mismatch: {key}")
  let some pointer := frozen.types[entry.signature.functionPointerType]? | throw (IO.userError "computed main fnptr absent")
  match pointer.shape with
  | .functionPointer sig bound =>
    unless sig.inputs.isEmpty && sig.output == entry.signature.returnType && bound.isEmpty &&
        sig.abi == .Rust && !sig.cVariadic do throw (IO.userError "computed main FnPtr signature mismatch")
  | _ => throw (IO.userError "computed main type is not FnPtr")
  let some computedStart := frozen.types[resolution.functionType]? | throw (IO.userError "computed start FnDef absent")
  let referenceTypes ← checked (reference.getObjValAs? (Array Json) "types")
  let referenceReturnId ← checked (signature.getObjValAs? Nat "return_type")
  let referencePointerId ← checked (signature.getObjValAs? Nat "function_pointer_type")
  let some refReturn := referenceTypes[referenceReturnId]? | throw (IO.userError "reference main return type absent")
  let refReturn ← checked (refReturn.getObjVal? "shape")
  unless (← checked (refReturn.getObjValAs? String "kind")) == "tuple" &&
      (← checked (refReturn.getObjValAs? (Array Nat) "elements")).isEmpty do
    throw (IO.userError "genuine main return type is not unit")
  let some refPointer := referenceTypes[referencePointerId]? | throw (IO.userError "reference main FnPtr absent")
  let refPointer ← checked (refPointer.getObjVal? "shape")
  unless (← checked (refPointer.getObjValAs? String "kind")) == "function_pointer" do
    throw (IO.userError "genuine main type is not FnPtr")
  let refPointerSignature ← checked (refPointer.getObjVal? "signature")
  unless (← checked (refPointerSignature.getObjValAs? (Array Nat) "inputs")).isEmpty &&
      (← checked (refPointerSignature.getObjValAs? Nat "output")) == referenceReturnId &&
      !(← checked (refPointerSignature.getObjValAs? Bool "c_variadic")) do
    throw (IO.userError "genuine main FnPtr signature mismatch")
  let refStart ← checked (signature.getObjVal? "start_resolution")
  let refStartType ← checked (refStart.getObjValAs? Nat "function_type")
  let some refStartType := referenceTypes[refStartType]? | throw (IO.userError "reference start FnDef absent")
  unless computedStart.display == (← checked (refStartType.getObjValAs? String "display")) do
    throw (IO.userError "computed start FnDef signature/display mismatch")
  let some instanceNode := pool.registry.instances[resolution.instanceId]? | throw (IO.userError "computed start instance absent")
  unless instanceNode.instanceKind == .Item start && instanceNode.genericArgs == #[.Type entry.signature.returnType] do
    throw (IO.userError "computed start generic argument identity mismatch")
  let missing := { document with bodies := document.bodies.filter fun body =>
    (body.getObjValAs? Nat "definition").toOption != some start }
  let missingPool ← checked (DirectCallPool.start (PhysicalTypeRegistry.start missing))
  match prepareMainEntries missingPool with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "missing start body accepted")
  let missing := { document with source := document.source.setObjVal! "entry_selection" Json.null }
  let missingPool ← checked (DirectCallPool.start (PhysicalTypeRegistry.start missing))
  match prepareMainEntries missingPool with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "missing entry selection accepted")
  IO.println "foundation main entries: genuine custom-start signature/DefId/FnPtr/FnDef joins and missing-material controls passed"
