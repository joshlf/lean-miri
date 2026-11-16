import Miri.Input.ConcreteFieldShuffle
def main : IO Unit := do
  for seed in #[0,1,42,2^64-1] do
    for size in #[0,1,2,3,4,7,13,32,257] do
      let values ← match Miri.Input.ConcreteFieldShuffle.shuffle (List.range size).toArray (UInt64.ofNat seed) with
        | .ok values => pure values
        | .error error => throw (IO.userError error)
      IO.println s!"{seed} {size} [{String.intercalate ", " (values.toList.map toString)}]"
