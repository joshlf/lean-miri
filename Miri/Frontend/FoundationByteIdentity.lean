/-! A finite component model of the pinned allocation-identity distinction.
rustc_middle/mir/interpret/mod.rs::AllocMap stores to_alloc and dedup separately.
reserve_and_set_memory_alloc always reserves; reserve_and_set_dedup reuses only
its (GlobalAlloc,salt) key. Identical byte images and a frontier therefore do not
recover interner membership. This executable model records those two operations;
it is not a proof of compiler correspondence or a replacement runtime allocator.
A future source construction trace could drive this pure transition, but the
current compiler snapshot does not retain that trace. Exporting its dedup map
as byte/salt answers is deliberately outside the foundation implementation.

Canonical identities could name imported nodes by graph position and generated
byte keys structurally by (bytes,salt), while preserving distinct direct-memory
nodes. Joining those names requires a complete source construction history
(reservation, direct-memory installation and keyed interning), not just images.
The current source capture has no such history. A raw-ID renaming also needs a
simulation for allocation supply, provenance, address exposure and borrow state;
content deduplication alone would collapse distinct source allocations. Until
that material/proof exists, deferredGlobalBytes leaves byte reservation disabled
at the existing fixed-interpreter Unsupported guard. -/
namespace Miri.Frontend.Foundation.ByteIdentity

abbrev Bytes := Array UInt8

structure State where
  next : Nat := 1
  images : Array (Nat × Bytes) := #[]
  keys : Array (Bytes × Nat × Nat) := #[]
  deriving DecidableEq

inductive Event where
  | memory (bytes : Bytes)
  | intern (bytes : Bytes) (salt : Nat)
  deriving DecidableEq

def lookup (state : State) (bytes : Bytes) (salt : Nat) : Option Nat :=
  (state.keys.find? (fun entry => entry.1 == bytes && entry.2.1 == salt)).map (·.2.2)

def direct (state : State) (bytes : Bytes) : State × Nat :=
  ({state with next := state.next + 1, images := state.images.push (state.next, bytes)}, state.next)

def intern (state : State) (bytes : Bytes) (salt : Nat) : State × Nat :=
  match lookup state bytes salt with
  | some id => (state, id)
  | none =>
    let (next, id) := direct state bytes
    ({next with keys := next.keys.push (bytes, salt, id)}, id)

def apply (state : State) : Event → State
  | .memory bytes => (direct state bytes).1
  | .intern bytes salt => (intern state bytes salt).1

def run (events : List Event) : State := events.foldl apply {}

/-- Exactly the retained source image/identity universe and frontier, with the
unretained construction-key relation erased. -/
def observe (state : State) : Nat × Array (Nat × Bytes) := (state.next, state.images)

private def bytes : Bytes := #[42]
def firstInterned : State := run [.intern bytes 0, .memory bytes]
def secondInterned : State := run [.memory bytes, .intern bytes 0]

theorem same_source_images : observe firstInterned = observe secondInterned := by decide

theorem different_source_reuse :
    lookup firstInterned bytes 0 = some 1 ∧ lookup secondInterned bytes 0 = some 2 := by decide

/-- No function of these source images/frontier can reconstruct both histories'
reuse identity. This local non-identifiability result does not assert that a
particular compiler fixture realizes every modeled history. -/
theorem no_image_only_resolver (resolve : (Nat × Array (Nat × Bytes)) → Option Nat) :
    ¬ (resolve (observe firstInterned) = lookup firstInterned bytes 0 ∧
       resolve (observe secondInterned) = lookup secondInterned bytes 0) := by
  intro h
  have same := congrArg resolve same_source_images
  have impossible := h.1.symm.trans (same.trans h.2)
  rw [different_source_reuse.1, different_source_reuse.2] at impossible
  cases impossible

end Miri.Frontend.Foundation.ByteIdentity
