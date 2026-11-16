import Miri.Input.EvalPreparation

open Lean Miri Miri.Input Miri.Memory Miri.Interpreter

private def must {α : Type} (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def main (args : List String) : IO Unit := do
  let path :: mode :: extra := args |
    throw (IO.userError "expected fresh input, identity|nonidentity and optional predicate-contrast/trait-vptr/trace-map")
  check (mode == "identity" || mode == "nonidentity") "unknown erasure expectation"
  check (extra.all fun flag => flag == "predicate-contrast" || flag == "trait-vptr" || flag == "trace-map")
    "unknown coverage expectation"
  let text ← IO.FS.readFile path
  let decoded ← must (decodeJson text)
  let program ← must (lowerProgram decoded.document)
  let attempt := EvalPreparation.prepare program
  let prepared ← must attempt.outcome
  let queries := prepared.compiler.vtables.queries
  let document := program.input
  let mut keys : Array (Nat × PredicateList) := #[]
  for node in document.allocations do
    if let some (.vtable source) := node.data then
      let key := (source.typeId, source.predicates)
      unless keys.contains key do keys := keys.push key
  for binding in document.sourceVtables.bindings do
    let key := (binding.typeId, binding.principal.toArray)
    unless keys.contains key do keys := keys.push key
  check (!keys.isEmpty) "no actual vtable source keys: no coverage"
  let mut mappings := #[]
  let mut changed := 0
  for (ty, predicates) in keys do
    let output ← must (CompilerVTableQueries.eraseAndAnonymize queries ty predicates)
    check ((← must (CompilerVTableQueries.eraseAndAnonymize queries output.1 output.2)) == output)
      "source erasure is not idempotent"
    if (ty, predicates) != output then changed := changed + 1
    mappings := mappings.push ((ty, predicates), output)
    if extra.contains "trace-map" then
      IO.println s!"vtable_source_map input_type={ty} input_predicates={reprStr predicates} output_type={output.1} output_predicates={reprStr output.2}"
  check (if mode == "identity" then changed == 0 else changed > 0)
    s!"erasure expectation {mode} failed: nonidentity={changed}"
  if extra.contains "predicate-contrast" then
    check (mappings.any fun first => mappings.any fun second =>
      first.1.1 == second.1.1 && first.1.2 != second.1.2 &&
      first.2.1 == second.2.1 && first.2.2 != second.2.2)
      "control lost its same-type/distinct-predicate contrast"
  check (!(CompilerVTableQueries.eraseAndAnonymize queries document.types.size #[]).isOk)
    "erasure accepted an absent source type"
  if let some (ty, predicates) := keys.find? (fun key => !key.2.isEmpty) then
    let missingProgram := {program with input := {document with compilerPredicates := #[]}}
    let missing := {queries with facts := {queries.facts with
      context := queries.facts.context.withProgram missingProgram}}
    check (!(CompilerVTableQueries.eraseAndAnonymize missing ty predicates).isOk)
      "erasure succeeded without predicate source material"
  if let some binding := document.sourceVtables.bindings[0]? then
    let duplicate := {document.sourceVtables with bindings := document.sourceVtables.bindings.push binding}
    match SourceVTablesDecoder.validate document.types document.definitions document.predicates document.instances duplicate with
    | .error error =>
      check (error == "duplicate concrete vtable executable binding")
        s!"duplicate binding returned an unrelated error: {error}"
    | .ok _ => throw (IO.userError "duplicate source vtable executable binding was accepted")
  if extra.contains "trait-vptr" then
    let mut found := false
    for binding in document.sourceVtables.bindings do
      let entries ← must (ConcreteVTable.entries document binding.principal binding.typeId)
      if entries.any (fun entry => match entry with | .traitVPtr _ => true | _ => false) then
        found := true
        let absent := {document with sourceVtables := {document.sourceVtables with
          bindings := document.sourceVtables.bindings.filter fun other =>
            !(other.typeId == binding.typeId && other.principal == binding.principal)}}
        check (!(ConcreteVTable.entries absent binding.principal binding.typeId).isOk)
          "vtable entries succeeded without their concrete executable binding"
    check found "control has no consumer-computed TraitVPtr entry"
    let mut memoryTargets := #[]
    for node in document.allocations do
      if let some (.vtable source) := node.data then
        for entry in source.entries do
          if entry.kind == .supertraitVtablePointer then
            if let some target := entry.allocationId then
              if document.allocations.any (fun node => node.id == target && node.kind == .memory) then
                memoryTargets := memoryTargets.push target
    check (memoryTargets.any fun target => (memoryTargets.filter (· == target)).size >= 2)
      "control lost its shared memory-backed TraitVPtr allocation"
    IO.println "vtable-erasure: computed TraitVPtr, shared memory identity and missing-binding control PASS"
  let memory := attempt.memory
  let some world := document.compilerAllocIdWorld | throw (IO.userError "missing prepared allocation world")
  let registry ← must (CompilerVTableMachine.seedImported
    prepared.compiler.vtables prepared.image memory VTableMachine.Registry.empty)
  let rows := world.dedupCatalog.filter (·.keyKind == .vtable)
  check (!rows.isEmpty) "no prepared vtable salt rows"
  for row in rows do
    let keyRuntime ← must (AllocationImage.runtimeId memory row.keyAllocationId)
    let some key ← must (CompilerVTableRuntime.globalVTable
      prepared.compiler.vtables.calls.symbols prepared.image memory keyRuntime) |
      throw (IO.userError "catalog key has no exact type/predicate identity")
    check ((← must (CompilerVTableQueries.eraseAndAnonymize queries key.1 key.2)) == key)
      "catalog key is not canonical"
    check (row.salts.size == 32) "vtable row does not cover 32 salts"
    for salt in List.range 32 do
      let results := row.salts.filter (·.salt == salt)
      check (results.size == 1) s!"missing/duplicate salt {salt}"
      for result in results do
        let runtime ← must (AllocationImage.runtimeId memory result.allocationId)
        check (memory.sourceAllocIdForRuntime? runtime == some result.sourceAllocId)
          "raw/dense/runtime allocation crosswalk differs"
        check (registry.entries.any fun entry => entry.typeId == key.1 &&
          entry.dynamicType == key.2 && entry.salt.val == salt && entry.allocation == runtime)
          "salt result does not join the exact type/predicate runtime key"
  IO.println s!"vtable-erasure: source-keys={keys.size}; nonidentity={changed}; exact catalog joins PASS; keys={rows.size}; salts-per-key=32"
