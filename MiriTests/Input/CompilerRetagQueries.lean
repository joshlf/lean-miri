import Miri.Input.CompilerRetagQueries

namespace MiriTests.Input.CompilerRetagQueries
open Miri.Input

/-- The pre-index implementation, retained as a finite comparison oracle. -/
@[noinline] def reference (definitionCount : Nat) (rows : Array Catalog.RetagQuery)
    (id : Nat) : Except String Bool := do
  unless id < definitionCount do
    throw "retag frame absent from canonical compiler definition table"
  let mut selected : Option Bool := none
  let mut seen : Array Nat := #[]
  for row in rows do
    unless row.definition < definitionCount do
      throw "retag compiler definition ID out of bounds"
    if seen.contains row.definition then throw "duplicate compiler retag definition query"
    seen := seen.push row.definition
    if row.definition == id then selected := some row.rustcNoWritable
  let some value := selected | throw "exact compiler retag frame attribute query absent"
  pure value

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def runTests : IO Unit := do
  -- Every ordered table of up to three rows, with four possible IDs and
  -- both attribute values. Includes equal/conflicting duplicates, invalid
  -- suffixes after selected rows, and competing duplicate/bounds failures.
  let alphabet : Array Catalog.RetagQuery := (List.range 4).toArray.flatMap fun id =>
    #[⟨id,false⟩,⟨id,true⟩]
  let mut tables : Array (Array Catalog.RetagQuery) := #[#[]]
  let mut level : Array (Array Catalog.RetagQuery) := #[#[]]
  for _ in [:3] do
    level := level.flatMap fun rows => alphabet.map rows.push
    tables := tables ++ level
  let mut comparisons := 0
  for definitionCount in [:5] do
    for rows in tables do
      let prepared := CompilerRetagQueries.prepare definitionCount rows
      for id in [:6] do
        let expected := reference definitionCount rows id
        let actual := CompilerRetagQueries.lookup definitionCount prepared id
        check (actual == expected)
          s!"retag lookup mismatch: definitions={definitionCount}, rows={reprStr rows}, id={id}"
        comparisons := comparisons + 1
  check (CompilerRetagQueries.lookup 2 (CompilerRetagQueries.prepare 2 #[⟨1,false⟩]) 1 == .ok false)
    "explicit false attribute became missing"
  check (CompilerRetagQueries.lookup 2 (CompilerRetagQueries.prepare 2 #[⟨1,true⟩]) 1 == .ok true)
    "explicit true attribute changed"
  IO.println s!"retag lookup: {comparisons} scan/index comparisons passed"

#eval runTests
end MiriTests.Input.CompilerRetagQueries
