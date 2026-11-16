import Miri.Concurrency.SyncObject

open Miri.ABI Miri.Memory Miri.Interpreter Miri.Concurrency.SyncObject

private structure State where
  objects : Array (AllocRange × Nat)
  events : Array Nat := #[]
  fail : Option Nat := none

private def allocation : AllocId := ⟨1, by decide⟩
private def hooks : AccessHooks State Nat where
  entries := fun _ => do
    let state ← get
    return state.objects.map fun (range,id) => (range, {
      payload := id, deleteOnWrite := true, onAccess := fun _ => do
        modify fun s => {s with events := s.events.push id}
        if state.fail == some id then throw (.undefinedBehavior "queued metadata")})
  remove := fun _ offset => modify fun s =>
    {s with objects := s.objects.filter (·.1.start != offset)}

private def initial (fail : Option Nat := none) : State :=
  ⟨#[⟨⟨Size.ofBytes 8,Size.ofBytes 4⟩,2⟩,
      ⟨⟨Size.ofBytes 0,Size.ofBytes 8⟩,1⟩],#[],fail⟩

def main : IO Unit := do
  -- The write begins inside object 1 and crosses into object 2. Both guards
  -- must run, in source range order, before either object can be removed.
  match onMemoryAccess hooks allocation (Size.ofBytes 7) (Size.ofBytes 2) .write (initial (some 2)) with
  | .error (.undefinedBehavior _) state =>
    unless state.events == #[1,2] && state.objects.size == 2 do
      throw (IO.userError "overlapping access lost callbacks or removed metadata before failure")
  | _ => throw (IO.userError "queued overlapping metadata did not reject the write")
  match onMemoryAccess hooks allocation (Size.ofBytes 7) (Size.ofBytes 2) .write (initial) with
  | .ok () state =>
    unless state.events == #[1,2] && state.objects.isEmpty do
      throw (IO.userError "successful overlapping write did not remove both opaque objects")
  | _ => throw (IO.userError "successful overlapping write failed")
  for (start,size) in #[(12,1),(8,0)] do
    match onMemoryAccess hooks allocation (Size.ofBytes start) (Size.ofBytes size) .read (initial) with
    | .ok () state =>
      unless state.events.isEmpty do throw (IO.userError "empty or disjoint access visited metadata")
    | _ => throw (IO.userError "empty or disjoint access failed")
  match onMemoryAccess hooks allocation (Size.ofBytes 7) (Size.ofBytes 1) .read (initial) with
  | .ok () state =>
    unless state.events == #[1] && state.objects.size == 2 do
      throw (IO.userError "read did not retain the intersecting object")
  | _ => throw (IO.userError "read failed")
  IO.println "metadata range guards PASS"
