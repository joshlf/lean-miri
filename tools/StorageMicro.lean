import Miri.Memory.MemoryState
open Miri.ABI Miri.Memory
abbrev Mem := MemoryState Provenance Unit Unit
private def need (x : Except ε α) : IO α := match x with
  | .ok a => pure a
  | .error _ => throw (IO.userError "public memory API failed")
private def initExtra (m : Mem) (s : Unit) (_ : AllocId) (_ : MemoryKind Unit) (_ : Size) (_ : Align) :
    MemoryStateHookResult Provenance Unit Unit Unit Unit := ⟨m,s,.ok ()⟩
private def rootPtr (m : Mem) (s : Unit) (id : AllocId) (_ : MemoryKind Unit) :
    MemoryStateHookResult Provenance Unit Unit Unit (Pointer Provenance) :=
  ⟨m,s,.ok (Pointer.new (.concrete id BorTag.one) Size.ZERO)⟩
private def globals : GlobalAllocationHooks Provenance Unit Unit Unit := {
  synchronizeMemory := fun _ s => s
  evaluateStaticInitializer := fun m s _ => ⟨m,s,.error "unexpected global"⟩
  beforeAccessGlobal := fun m s _ _ _ _ => ⟨m,s,.error "unexpected global"⟩
  adjustGlobalAllocation := fun m s _ _ => ⟨m,s,.error "unexpected global"⟩ }
private def deallocHooks : MemoryDeallocationHooks Provenance Unit Unit Unit Unit := {
  synchronizeMemory := fun _ s => s
  resolvePointer := fun m s p _ => match p.provenance with
    | some (.concrete id _) => ⟨m,s,.ok (id,p.offset,())⟩
    | _ => ⟨m,s,.error p.offset.bytes⟩
  beforeDeallocation := fun m s _ _ _ _ _ _ _ => ⟨m,s,.ok ()⟩ }
@[noinline] private def allocOne (m : Mem) : IO (Mem × AllocId × Pointer (Option Provenance)) := do
  let r := MemoryLifecycle.allocatePtr m () (fun _ s => s) (Size.ofBytes 4) Align.ONE
    (.machine ()) .Zero (Size.ofBytes 32) none
    (fun size _ => some (Array.replicate size.bytes.toNat 0)) initExtra rootPtr
  let ptr ← need r.outcome
  let .concrete id _ := ptr.provenance | throw (IO.userError "nonconcrete root")
  return (r.memory,id,Pointer.new (some ptr.provenance) ptr.offset)
@[noinline] private def setup (n : Nat) : IO (Mem × Array AllocId × Array (Pointer (Option Provenance))) := do
  let mut m : Mem := .empty
  let mut ids := #[]
  let mut ptrs := #[]
  for _ in [:n] do
    let (next,id,p) ← allocOne m
    m := next; ids := ids.push id; ptrs := ptrs.push p
  return (m,ids,ptrs)
@[noinline] private def liveOps (initial : Mem) (ids : Array AllocId) (ops : Nat) : IO (Mem × UInt64) := do
  let mut m := initial
  let mut checksum : UInt64 := 0
  for i in [:ops] do
    let some id := ids[i % ids.size]? | throw (IO.userError "missing generated ID")
    let info ← need (m.getAllocInfo id)
    let byte := UInt8.ofNat (i % 251)
    let allocation ← need (Allocation.fromBytes (Prov := Provenance) #[byte,0,0,0] Align.ONE .Mut)
    m ← need (m.setLiveAllocation id allocation)
    checksum := checksum + info.size.bytes + byte.toUInt64 + id.value
  return (m,checksum)
@[noinline] private def freeAll (initial : Mem) (ptrs : Array (Pointer (Option Provenance))) : IO Mem := do
  let mut m := initial
  for ptr in ptrs do
    let r := MemoryLifecycle.deallocatePtrWith m () ptr none (.machine ()) deallocHooks
    let _ ← need r.outcome
    m := r.memory
  return m
@[noinline] private def deadOps (m : Mem) (ids : Array AllocId) (ops : Nat) : IO UInt64 := do
  let mut checksum : UInt64 := 0
  for i in [:ops] do
    let some id := ids[i % ids.size]? | throw (IO.userError "missing generated ID")
    let info ← need (m.getAllocInfo id)
    checksum := checksum + info.size.bytes + id.value
  return checksum
private def payloadSum (m : Mem) (ids : Array AllocId) : IO UInt64 := do
  let mut sum : UInt64 := 0
  for id in ids do
    let r := MemoryLifecycle.getAllocRaw m () id none globals
    let a ← need r.outcome
    let bytes ← need (a.inspectWithUninitAndPtrOutsideInterpreter 0 4)
    sum := sum + (bytes[0]!).toUInt64 + id.value
  return sum
private def phase (label : String) (action : IO α) : IO α := do
  let w ← IO.monoNanosNow
  let value ← action
  let w2 ← IO.monoNanosNow
  IO.println s!"{label} wall_ns={w2-w}"
  return value
 def main (args : List String) : IO Unit := do
  let n := (args[0]!).toNat!
  let ops := (args[1]!).toNat!
  let mode := args[2]!
  if n == 0 then throw (IO.userError "n must be positive")
  let (m,ids,ptrs) ← phase "setup" (setup n)
  let keys := ids.foldl (fun a id => a + id.value) (0 : UInt64)
  if mode == "live" then
    let (m,checksum) ← phase "live" (liveOps m ids ops)
    let payload ← phase "verify" (payloadSum m ids)
    IO.println s!"result n={n} ops={ops} keys={keys} checksum={checksum} payload={payload}"
  else
    let dead ← phase "free" (freeAll m ptrs)
    let checksum ← phase "dead" (deadOps dead ids ops)
    IO.println s!"result n={n} ops={ops} keys={keys} checksum={checksum} dead={ids.size}"
