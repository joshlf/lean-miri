import Miri.Frontend.FoundationLinkInitializers
open Lean Miri Miri.Frontend.Foundation
private def checked (value : Except String α) : IO α := do
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def rejected (value : Except String α) : IO Unit := do
  match value with | .error _ => pure () | .ok _ => throw (IO.userError "unavailable initializer accepted")

def main (paths : List String) : IO Unit := do
  let [localPath,stdPath,referencePath] := paths | throw (IO.userError "expected local/std source and genuine CTFE graph reference")
  let localDoc ← checked (Json.parse (← IO.FS.readFile localPath) >>= decode)
  let stdDoc ← checked (Json.parse (← IO.FS.readFile stdPath) >>= decode)
  let references ← checked (Json.parse (← IO.FS.readFile referencePath) >>= fun j => j.getArr?)
  let sections ← checked (sourceLinkSections localDoc.source)
  let locals := sections.filter (·.crateIndex == 0)
  unless locals.size == 2 do throw (IO.userError "local static source count mismatch")
  for entry in locals do
    let plan ← checked (sourceCInitializer localDoc entry)
    let some function := localDoc.definitions[plan.functionDefinition]? | throw (IO.userError "target source definition absent")
    let some static := localDoc.definitions[plan.staticDefinition]? | throw (IO.userError "static source definition absent")
    let index ← checked (static.getObjValAs? Nat "index")
    let some reference := references.find? (fun row => (row.getObjValAs? Nat "static_index").toOption == some index)
      | throw (IO.userError "compiler CTFE graph reference absent")
    unless (← checked (function.getObjValAs? Nat "index")) == (← checked (reference.getObjValAs? Nat "function_index")) &&
        plan.pointerSizeBytes == (← checked (reference.getObjValAs? Nat "size_bytes")) &&
        plan.pointerAlignBytes == (← checked (reference.getObjValAs? Nat "align_bytes")) && plan.pointerOffsetBytes == 0 do
      throw (IO.userError "symbolic source initializer disagrees with genuine compiler CTFE graph")
    let source ← checked (entry.source.getObjVal? "initializer_source")
    let expression ← checked (source.getObjVal? "expression")
    let header ← checked (source.getObjVal? "function_header")
    let signature ← checked (header.getObjVal? "signature")
    let wrongAbi := Json.mkObj [("kind",toJson "c"),("unwind",toJson true)]
    for changed in #[source.setObjVal! "allocation_identity_status" (toJson "resolved"),
        source.setObjVal! "static_mutable" (toJson true),
        source.setObjVal! "expression" (expression.setObjVal! "function_definition" (toJson localDoc.definitions.size)),
        source.setObjVal! "function_header" (header.setObjVal! "signature" (signature.setObjVal! "abi" wrongAbi))] do
      rejected (sourceCInitializer localDoc {entry with source := entry.source.setObjVal! "initializer_source" changed})
  let localCtors ← checked (sourceConstructorSections localDoc.source .elf)
  unless localCtors.size == 1 && (localCtors[0]?.map (·.name)) == some ".init_array" do
    throw (IO.userError "constructor predicate did not select only exact .init_array")
  rejected (guardedEmptySourceLinkLookup (α := Nat) localDoc (Interpreter.constructorSectionMatches .elf))
  let stdSelected ← checked (sourceLinkSections stdDoc.source)
  unless stdSelected.size == 1 do throw (IO.userError "expected genuine ARGV_INIT_ARRAY section")
  let some argv := stdSelected[0]? | throw (IO.userError "ARGV section absent")
  unless argv.name == ".init_array.00099" do throw (IO.userError "unexpected genuine std section")
  let declaration ← checked (sourceCStaticSignature stdDoc argv)
  unless declaration.inputs.size == 3 && declaration.pointerSizeBytes == 8 && declaration.pointerAlignBytes == 8 do
    throw (IO.userError "genuine ARGV C type/storage metadata mismatch")
  let empty ← checked (guardedEmptySourceLinkLookup (α := Nat) stdDoc (Interpreter.constructorSectionMatches .elf))
  unless empty.isEmpty do throw (IO.userError "priority section incorrectly selected as ELF constructor")
  rejected (sourceCInitializer stdDoc argv)
  rejected (guardedEmptySourceLinkLookup (α := Nat) stdDoc (· == ".init_array.00099"))
  rejected (guardedEmptySourceLinkLookup (α := Nat) stdDoc (·.startsWith ".init_array"))
  IO.println "local initializer/real CTFE graph comparison; exact std constructor predicate and unavailable identity guards passed"
