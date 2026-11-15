import Miri.Frontend.FoundationDeferredGlobalBytes
import Miri.Frontend.FoundationAllocations
import Miri.Frontend.FoundationProgram
import Miri.Input.ValidateTables

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
  check program.input.queries.globalBytes.evidenceAvailable "complete foundation catalog lost default availability"
  let completeRuntime ← expect ((Input.RuntimeMetadata.ofDocument program.input).mapError toString)
  let unavailable := Input.Catalog.GlobalBytes.unavailable program.input.queries.globalBytes.strType
  let unavailableProgram := {program with input := {program.input with queries :=
    {program.input.queries with globalBytes := unavailable}}}
  let _ ← expect (Input.validateParsedTables unavailableProgram.input)
  let runtime ← expect ((Input.RuntimeMetadata.ofDocument unavailableProgram.input).mapError toString)
  let completePrepared ← expect (Input.CompilerGlobalBytes.prepare program completeRuntime
    (MemoryState.empty : MemoryState Provenance Miri.TreeBorrows.BorrowTree Unit))
  check completePrepared.keys.isEmpty "existing empty-graph preparation behavior changed"
  let allocationDocument ← load allocationsPath
  let imported ← expect (importSourceMemory allocationDocument
    (MemoryState.empty : MemoryState Provenance Miri.TreeBorrows.BorrowTree Unit))
  let _ ← expect imported.outcome
  let memory := imported.memory
  rejects (deferredGlobalBytes completeRuntime memory)
  let view ← expect (deferredGlobalBytes runtime memory)
  match Input.CompilerGlobalBytes.prepare unavailableProgram runtime memory with
  | .error "compiler-global byte interner source evidence is unavailable" => pure ()
  | _ => throw (IO.userError "unavailable interner evidence was interpreted as answers")
  let contradictory := {unavailable with saltCount := 32}
  rejects contradictory.validateAvailability
  let contradictoryProgram := {unavailableProgram with input := {unavailableProgram.input with queries :=
    {unavailableProgram.input.queries with globalBytes := contradictory}}}
  match Input.validateParsedTables contradictoryProgram.input with
  | .error "unavailable global byte evidence carries answer payload" => pure ()
  | .error error => throw (IO.userError s!"wrong unavailable table validation error: {error}")
  | .ok _ => throw (IO.userError "table validator accepted unavailable answer payload")
  match Input.CompilerGlobalBytes.prepare contradictoryProgram runtime memory with
  | .error "unavailable global byte evidence carries answer payload" => pure ()
  | _ => throw (IO.userError "contradictory unavailable payload bypassed validation")
  rejects ({unavailable with coveredAllocations := #[0]}.validateAvailability)
  rejects ({unavailable with candidates := #[⟨"00", #[]⟩]}.validateAvailability)
  let decoded ← expect (Input.JsonReader.run Input.CatalogDecoder.globalBytes
    "{\"salt_count\":32,\"str_type\":0,\"covered_allocation_ids\":[],\"candidates\":[]}")
  check decoded.evidenceAvailable "legacy serialized evidence no longer defaults to available"
  check (view.strType == program.input.queries.globalBytes.strType && view.keys.isEmpty) "deferred str view mismatch"
  check (!memory.byteGlobalKeysReady && memory.byteGlobalKeys.isEmpty && memory.globals.size == 2)
    "source images incorrectly attached interner keys"
  let state : MachineHooks.State Unit Unit := ⟨.empty, {
    memory, borrowTracker := none, dataRace := none,
    threads := Miri.Concurrency.ThreadManager.initial false,
    raceAllocations := #[], allocationSpans := #[], user := () }⟩
  let (afterAttach, attachResult) := MachineHooks.run
    (Input.CompilerGlobalBytes.attach unavailableProgram runtime) state
  match attachResult with
  | .error (.unsupported "compiler-global byte interner source evidence is unavailable") => pure ()
  | _ => throw (IO.userError "unavailable byte keys were attached")
  check (!afterAttach.machine.memory.byteGlobalKeysReady && afterAttach.machine.memory.byteGlobalKeys.isEmpty)
    "failed byte attachment modified key readiness"
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
