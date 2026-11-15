import Miri.Frontend.FoundationClosureVtableImage

open Lean Miri Miri.Frontend.Foundation Miri.Interpreter Miri.Memory Miri.ABI
private def checked (value : Except String α) : IO α :=
  match value with | .ok result => pure result | .error e => throw (IO.userError e)
private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def demandChecks (target : RuntimeTargetDataLayout) : IO Unit := do
  let f : FunctionPointers.Hooks Unit VTableMachine.Registry Unit := {
    registry := fun _ => .empty, putRegistry := fun user _ => user,
    crossCrateInlineAlways := true, instanceArgs := fun _ => pure #[],
    inlineNever := fun _ => pure false, chooseSalt := pure ⟨0,by decide⟩,
    ptrGetAlloc := fun _ => pure none,
    adjustRootPointer := fun id tag => pure (Pointer.new (Provenance.concrete id tag) Size.ZERO),
    importedFunction := fun _ => pure none }
  let h : VTableMachine.Hooks Unit VTableMachine.Registry Unit := {
    functions := f, registry := id, putRegistry := fun _ rows => rows,
    target, importedVTable := fun _ => pure none }
  for sourceWorld in #[false,true] do
    let memory : MemoryState Provenance TreeBorrows.BorrowTree Unit :=
      {MemoryState.empty with sourceAllocIdWorldActive := sourceWorld}
    let initial : MachineHooks.State Unit VTableMachine.Registry := ⟨Stack.empty,{
      memory, borrowTracker := none, dataRace := none,
      threads := Concurrency.ThreadManager.initial false,
      raceAllocations := #[], allocationSpans := #[], user := .empty}⟩
    for salt in List.finRange 32 do
      let (after,result) := MachineHooks.run (demandSourceClosureVtableIdentity h 0 #[] salt) initial
      let expected := if sourceWorld then
        "source vtable AllocId key/salt is not captured by the prepared raw-world profile"
        else "foundation closure vtable requires a source allocation identity world"
      match result with
      | .error (.unsupported message) => check (message == expected) "wrong identity boundary error"
      | _ => throw (IO.userError "unwitnessed vtable identity succeeded")
      check (after.machine.memory.sourceAllocIdNext == memory.sourceAllocIdNext &&
        after.machine.memory.nextAllocId == memory.nextAllocId &&
        after.machine.memory.globals.size == memory.globals.size &&
        after.machine.user.entries.isEmpty) "failed demand mutated identity world"

def main (paths : List String) : IO Unit := do
  let [sourcePath,oraclePath] := paths | throw (IO.userError "expected closure source/projected schema12")
  let document ← checked (Json.parse (← IO.FS.readFile sourcePath) >>= decode)
  let oracle ← checked (Json.parse (← IO.FS.readFile oraclePath))
  check ((← checked (oracle.getObjValAs? String "rustc_commit")) ==
    "8144389c895da997dbdecaa635e41d6a50be6ffd") "oracle pin differs"
  let some closure := document.definitions.findIdx? (fun row =>
      (row.getObjValAs? String "path").toOption == some "std::rt::lang_start::{closure#0}")
    | throw (IO.userError "std start closure absent")
  let candidate ← checked (closureVtableImageCandidate document closure
    #[.type (.tuple #[])] .fn (.tuple #[]) (.primitive "int" "i32"))
  let queries ← checked (oracle.getObjValAs? (Array Json) "compiler_vtable_queries")
  let some query := queries[0]? | throw (IO.userError "schema12 metadata absent")
  let metadata ← checked (query.getObjVal? "vtable_metadata")
  check (candidate.selfLayout.size == (← checked (metadata.getObjValAs? Nat "size_bytes")) &&
    candidate.selfLayout.align == (← checked (metadata.getObjValAs? Nat "align_bytes")))
    "source closure layout differs from compiler"
  let entries ← checked (metadata.getObjValAs? (Array Json) "entries")
  check (entries.size == candidate.cells.size && candidate.byteLength == candidate.pointerBytes * entries.size)
    "symbolic image extent differs"
  for (cell,row) in candidate.cells.zip entries do
    let kind ← checked (row.getObjValAs? String "kind")
    match cell with
    | .nullDrop => check (kind == "drop_in_place_null") "drop source differs"
    | .unsigned n => check ((kind == "size_bytes" && n == candidate.selfLayout.size) ||
        (kind == "align_bytes" && n == candidate.selfLayout.align)) "metadata cell differs"
    | .methodOrVacant _ => check (kind == "method") "genuine method candidate differs"
  check (candidate.relocations.size == 3) "relocation candidates lost methods"
  for (relocation,index) in candidate.relocations.toList.zipIdx do
    check (relocation.offset == (index + 3) * candidate.pointerBytes &&
      relocation.width == candidate.pointerBytes) "relocation source offset differs"
  check (!(← checked ((← checked (flattenEnvironment document candidate.parentEnvironment)).getObjValAs? (Array Json) "clauses")).isEmpty)
    "parent obligations discarded"
  match closureVtableImageCandidate document closure #[] .fn (.tuple #[]) (.primitive "int" "i32") with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "missing parent source accepted")
  demandChecks (← checked (runtimeTargetOfTarget document.target))
  IO.println "closure symbolic vtable: compiler drop/layout/extent match; conditional method recipes retained; all 32 unwitnessed fixed reservations reject without mutation"
