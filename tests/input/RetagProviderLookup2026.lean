import Miri.Input.CompilerRetagOptions
import Miri.Input.Decoder
import MiriTests.Input.CompilerRetagQueries

/-! Production preparation and source attribute demands on an accepted export,
plus typed malformed-table controls that retain demand-local errors. -/
open Miri.Input

private def must (value : Except String α) : IO α :=
  match value with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: RetagProviderLookup2026 <export.json>")
  let input ← must (← decodeFile path)
  let program ← must (lowerProgram input.document)
  let baseline ← must (CompilerProviders.prepare program)
  let count := baseline.program.compilerTables.definitions.size
  check (count > 0) "fixture needs compiler definitions"
  for id in [:count + 1] do
    check (CompilerRetagOptions.rustcNoWritable baseline id ==
      MiriTests.Input.CompilerRetagQueries.reference count baseline.program.input.queries.retag id)
      "production retag lookup differs from the original scan"
  let controls : Array (Array Catalog.RetagQuery) := #[
    #[], #[⟨0,false⟩], #[⟨0,true⟩],
    #[⟨0,false⟩,⟨0,false⟩], #[⟨0,false⟩,⟨0,true⟩],
    #[⟨0,true⟩,⟨count,false⟩], #[⟨count,false⟩,⟨0,true⟩],
    #[⟨0,false⟩,⟨0,true⟩,⟨count,false⟩],
    #[⟨count,false⟩,⟨0,false⟩,⟨0,true⟩]]
  for rows in controls do
    let document := {program.input with queries := {program.input.queries with retag := rows}}
    -- Preparation must succeed even for malformed tables; errors belong to
    -- the source attribute operation, including when another frame is queried.
    let prepared ← must (CompilerProviders.prepare {program with input := document})
    for id in #[0, count - 1, count, count + 1] do
      check (CompilerRetagOptions.rustcNoWritable prepared id ==
        MiriTests.Input.CompilerRetagQueries.reference count rows id)
        s!"production malformed-table error changed: rows={reprStr rows}, id={id}"
  IO.println "retag provider: accepted export and 9 demand-local table controls passed"
