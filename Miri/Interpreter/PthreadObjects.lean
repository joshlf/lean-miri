import Miri.Concurrency.SyncRuntime
import Miri.Concurrency.SyncObject

/-! Object lifecycle from pinned shims/unix/sync.rs:1–529. Compiler initializer
bytes/layouts and actual memory operations are mandatory queries. -/
namespace Miri.Interpreter.PthreadObjects
open Miri.ABI Miri.Memory Miri.Concurrency
abbrev M := EStateM StepError
inductive Kind where | mutex | rwlock | condvar | semaphore | mutexAttr | condAttr deriving DecidableEq, Repr
inductive MutexKind where | Normal | Default | Recursive | ErrorCheck deriving DecidableEq, Repr
inductive Clock where | realTime | monotonic deriving DecidableEq, Repr
inductive Payload (R : Type) where
  | mutex (ref : R) (kind : MutexKind)
  | rwlock (ref : R)
  | condvar (ref : R) (clock : Clock)
  | semaphore (ref : R)
  | mutexAttr (kind : Option MutexKind)
  | condAttr (clock : Clock)
def Payload.kind : Payload R → Kind
  | .mutex .. => .mutex | .rwlock .. => .rwlock | .condvar .. => .condvar | .semaphore .. => .semaphore
  | .mutexAttr .. => .mutexAttr | .condAttr .. => .condAttr
structure Hooks (S R : Type) where
  os : String
  sync : SyncObject.Hooks S (Payload R)
  runtime : SyncRuntime.Hooks S R Int32 (MPlaceTy Provenance)
  deref : OpTy Provenance → Kind → M S (MPlaceTy Provenance)
  initializer : String → M S (MPlaceTy Provenance)
  readBytes : MPlaceTy Provenance → Size → M S ByteArray
  newMutex : M S R
  newRwlock : M S R
  newCondvar : M S R
  newSemaphore : UInt64 → M S R

private def compareInitializer (h : Hooks S R) (object : MPlaceTy Provenance)
    (name : String) : M S Bool := do
  let initializer ← h.initializer name
  if initializer.layout.layout.size != object.layout.layout.size then
    throw (.invalidProgram "pthread static initializer layout size mismatch")
  let size := if h.os == "android" then Size.ofBytes 4 else object.layout.layout.size
  let left ← h.readBytes object size
  let right ← h.readBytes initializer size
  if left == right then
    unless right.data.any (· != 0x42) do
      throw (.invalidProgram "pthread initializer equals opaque metadata cookie")
    return true
  return false

def mutexKindFromInitializer (h : Hooks S R) (object : MPlaceTy Provenance) : M S MutexKind := do
  if ← compareInitializer h object "PTHREAD_MUTEX_INITIALIZER" then return .Default
  if h.os == "linux" then
    if ← compareInitializer h object "PTHREAD_RECURSIVE_MUTEX_INITIALIZER_NP" then return .Recursive
    if ← compareInitializer h object "PTHREAD_ERRORCHECK_MUTEX_INITIALIZER_NP" then return .ErrorCheck
  throw (.undefinedBehavior "pthread_mutex_t not properly initialized at this location or overwritten")
private def metadata (h : Hooks S R) (payload : Payload R) : SyncObject.Object S (Payload R) := {
  payload := payload
  deleteOnWrite := true
  onAccess := fun _ => do
    let empty : Bool ← match payload with
      | .mutex ref _ => (h.runtime.mutex ref).map MutexState.queueIsEmpty
      | .rwlock ref => (h.runtime.rwlock ref).map RwLockState.queueIsEmpty
      | .condvar ref _ => (h.runtime.condvar ref).map CondvarState.queueIsEmpty
      | .semaphore ref => (h.runtime.semaphore ref).map SemaphoreState.queueIsEmpty
      | .mutexAttr _ | .condAttr _ => pure true
    if !empty then throw (.undefinedBehavior "access of pthread synchronization storage forbidden while queue non-empty") }
private def typed (h : Hooks S R) (kind : Kind) : SyncObject.Hooks S (Payload R) := {
  h.sync with
  lookup := fun address => do
    let some value ← h.sync.lookup address | return none
    return if value.payload.kind == kind then some value else none
  remove := fun address size => do
    let value ← h.sync.remove address size
    return value.filter (·.payload.kind == kind) }

def get (h : Hooks S R) (kind : Kind) (operand : OpTy Provenance) : M S (Payload R) := do
  let object ← h.deref operand kind
  let value ← SyncObject.getOrInsert (typed h kind) object do
    let payload : Payload R ← match kind with
      | .mutex => do
        let mutexKind ← mutexKindFromInitializer h object
        pure (Payload.mutex (← h.newMutex) mutexKind)
      | .rwlock => do
        if !(← compareInitializer h object "PTHREAD_RWLOCK_INITIALIZER") then
          throw (.undefinedBehavior "pthread_rwlock_t not properly initialized at this location or overwritten")
        pure (Payload.rwlock (← h.newRwlock))
      | .condvar => do
        if !(← compareInitializer h object "PTHREAD_COND_INITIALIZER") then
          throw (.undefinedBehavior "pthread_cond_t not properly initialized at this location or overwritten")
        pure (Payload.condvar (← h.newCondvar) .realTime)
      | .semaphore => throw (.undefinedBehavior "sem_t not initialized with sem_init")
      | .mutexAttr => throw (.undefinedBehavior "pthread_mutexattr_t has not been initialized or has been tampered with")
      | .condAttr => throw (.undefinedBehavior "pthread_condattr_t has not been initialized or has been tampered with")
    return metadata h payload
  return value.payload

def createAt (h : Hooks S R) (object : MPlaceTy Provenance) (payload : Payload R) : M S Unit := do
  SyncObject.insert (typed h payload.kind) object (metadata h payload)
def create (h : Hooks S R) (operand : OpTy Provenance) (payload : Payload R) : M S Unit := do
  createAt h (← h.deref operand payload.kind) payload
/-- Attribute changes update interpreter metadata without touching guest bytes. -/
def put (h : Hooks S R) (operand : OpTy Provenance) (payload : Payload R) : M S Unit := do
  let place ← h.deref operand payload.kind
  let address ← h.sync.resolve place.mplace.ptr
  h.sync.insert address place.layout.layout.size (metadata h payload)

def remove (h : Hooks S R) (kind : Kind) (operand : OpTy Provenance) : M S Unit := do
  let place ← h.deref operand kind
  let address ← h.sync.resolve place.mplace.ptr
  let some _ ← (typed h kind).remove address place.layout.layout.size
    | throw (.undefinedBehavior "pthread attribute has not been initialized or has been tampered with")

end Miri.Interpreter.PthreadObjects
