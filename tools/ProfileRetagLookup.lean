import MiriTests.Input.CompilerRetagQueries

/-! Native microbenchmark of the unchanged reference scan and indexed lookup.
Both paths consume identical rows and demand IDs; preparation is measured
separately. This does not measure whole-program execution. -/
open Miri.Input

@[noinline] private def indexed (count : Nat)
    (prepared : Except String CompilerRetagQueries.Prepared) (id : Nat) : Except String Bool :=
  CompilerRetagQueries.lookup count prepared id

/-- Keep preparation inside each timed iteration instead of allowing the
compiler to share a loop-invariant pure preparation expression. -/
@[noinline] private def prepareOnce (count : Nat) (rows : Array Catalog.RetagQuery) :
    IO (Except String CompilerRetagQueries.Prepared) :=
  pure (CompilerRetagQueries.prepare count rows)

def main (args : List String) : IO Unit := do
  let [mode, countText, repetitionsText] := args
    | throw (IO.userError "usage: profile_retag_lookup scan|index|prepare ROWS REPETITIONS")
  let some count := countText.toNat? | throw (IO.userError "invalid row count")
  let some repetitions := repetitionsText.toNat? | throw (IO.userError "invalid repetition count")
  unless count > 0 do throw (IO.userError "row count must be positive")
  let rows : Array Catalog.RetagQuery := (List.range count).toArray.map fun id => ⟨id,id % 2 == 0⟩
  let prepared := CompilerRetagQueries.prepare count rows
  let mut checksum := 0
  let start ← IO.monoNanosNow
  for iteration in [:repetitions] do
    let id := iteration % count
    let current ← if mode == "prepare" then prepareOnce count rows else pure prepared
    let result := match mode with
      | "scan" => MiriTests.Input.CompilerRetagQueries.reference count rows id
      | "index" => indexed count prepared id
      | "prepare" => indexed count current id
      | _ => .error "unknown mode"
    match result with
    | .ok value => checksum := checksum + if value then 1 else 0
    | .error error => throw (IO.userError error)
  let elapsed := (← IO.monoNanosNow) - start
  IO.println s!"{mode} rows={count} repetitions={repetitions} ns={elapsed} checksum={checksum}"
