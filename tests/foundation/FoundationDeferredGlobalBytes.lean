import Miri.Frontend.FoundationDeferredGlobalBytes
import Miri.Frontend.FoundationAllocations
import Miri.Frontend.FoundationProgram

open Lean Miri Miri.Frontend.Foundation Miri.Interpreter Miri.Memory

private def expect (r : Except String α) : IO α :=
  match r with | .ok a => pure a | .error e => throw (IO.userError e)
private def check (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)
private def rejects (r : Except String α) : IO Unit :=
  match r with | .error _ => pure () | .ok _ => throw (IO.userError "attached byte keys accepted as deferred")
private def load (path : String) : IO Document := do
  let text ← IO.FS.readFile path
  expect (Json.parse text >>= decode)

def main (paths : List String) : IO Unit := do
  let [identityPath, allocationsPath] := paths
    | throw (IO.userError "usage: FoundationDeferredGlobalBytes IDENTITY_JSON ALLOCATION_JSON")
  let document ← load identityPath
  let some body := document.bodies[0]? | throw (IO.userError "identity source body missing")
  let definition ← expect (body.getObjValAs? Nat "definition")
  let program ← expect (restrictedLibraryProgram document definition #[.type (.primitive "uint" "u8")])
  let runtime ← expect ((Input.RuntimeMetadata.ofDocument program.input).mapError toString)
  let allocationDocument ← load allocationsPath
  let imported ← expect (importSourceMemory allocationDocument
    (MemoryState.empty : MemoryState Provenance Miri.TreeBorrows.BorrowTree Unit))
  let _ ← expect imported.outcome
  let memory := imported.memory
  let view ← expect (deferredGlobalBytes runtime memory)
  check (view.strType == program.input.queries.globalBytes.strType && view.keys.isEmpty) "deferred str view mismatch"
  check (!memory.byteGlobalKeysReady && memory.byteGlobalKeys.isEmpty && memory.globals.size == 2)
    "source images incorrectly attached interner keys"
  let state : MachineHooks.State Unit Unit := ⟨.empty, {
    memory, borrowTracker := none, dataRace := none,
    threads := Miri.Concurrency.ThreadManager.initial false,
    raceAllocations := #[], allocationSpans := #[], user := () }⟩
  for bytes in #["foundation-bytes".toUTF8.data, "new-key".toUTF8.data] do
    let (after, result) := MachineHooks.run (GlobalByteMachine.reserve bytes ⟨0, by decide⟩) state
    match result with
    | .error (.unsupported "exact imported compiler-global byte salt catalog has not been attached") => pure ()
    | _ => throw (IO.userError "unprepared byte interner demand did not stop Unsupported")
    check (after.machine.memory.nextAllocId == memory.nextAllocId &&
      after.machine.memory.globals.size == memory.globals.size &&
      !after.machine.memory.byteGlobalKeysReady && after.machine.memory.byteGlobalKeys.isEmpty)
      "unsupported interner demand consumed allocation identity or attached keys"
  rejects (deferredGlobalBytes runtime {memory with byteGlobalKeysReady := true})
  IO.println "deferred global bytes: existing source images retained; actual interner demands stop Unsupported"
