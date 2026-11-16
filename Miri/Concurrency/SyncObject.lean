import Miri.Interpreter.PlaceTypes
import Miri.Interpreter.Step
import Miri.Memory.Pointer

/-! Allocation-local metadata from upstream 93c45ede meta_obj.rs. Dynamic
payload types belong to the caller; a failed downcast is absence. Objects cover
the full storage range, including accesses that start inside that range. -/
namespace Miri.Concurrency.SyncObject
open Miri.ABI Miri.Memory Miri.Interpreter
abbrev M := EStateM StepError
inductive AccessKind where | read | write | deallocation deriving DecidableEq, Repr
structure Object (S Payload : Type) where
  payload : Payload
  onAccess : AccessKind → M S Unit
  deleteOnWrite : Bool
structure Address where
  allocation : AllocId
  offset : Size
structure Info where
  liveData : Bool
  mutable : Bool
  size : Size
structure MetadataHooks (S T : Type) where
  tryResolve : Pointer (Option Provenance) → M S (Option Address)
  resolve : Pointer (Option Provenance) → M S Address
  info : AllocId → M S Info
  lookup : Address → M S (Option (Object S T))
  insert : Address → Size → Object S T → M S Unit
  remove : Address → Size → M S (Option (Object S T))
  checkAccess : Pointer (Option Provenance) → Size → M S Unit
structure Hooks (S T : Type) extends MetadataHooks S T where
  writeBytes : Pointer (Option Provenance) → Size → UInt8 → M S Unit

inductive GetMetaError where | noMem | noObj deriving DecidableEq, Repr

def tryGetMetadata (h : MetadataHooks S T) (pointer : Pointer (Option Provenance)) :
    M S (Except GetMetaError (Object S T)) := do
  let some address ← h.tryResolve pointer | return .error .noMem
  let info ← h.info address.allocation
  if !info.liveData || address.offset.bytes >= info.size.bytes then return .error .noMem
  match ← h.lookup address with
  | some value => return .ok value
  | none => return .error .noObj

/-- Nonopaque metadata, used by address wait queues. An existing object is
looked up before checking the full range, as get_or_insert_meta does upstream. -/
def getOrInitMetadata (h : MetadataHooks S T) (pointer : Pointer (Option Provenance))
    (size : Size) (new : M S (Object S T)) : M S (Object S T) := do
  let address ← h.resolve pointer
  if let some value ← h.lookup address then return value
  let value ← new
  if size == Size.ZERO then throw (.invalidProgram "metadata object has zero-sized storage")
  h.checkAccess pointer size
  h.insert address size value
  return value

/-- Opaque storage is filled with the source cookie before its new metadata is
installed. This write runs the ordinary race/borrow/old-metadata access hooks. -/
def insert (h : Hooks S T) (place : MPlaceTy Provenance) (value : Object S T) : M S Unit := do
  let size := place.layout.layout.size
  if size == Size.ZERO then throw (.invalidProgram "metadata object has zero-sized storage")
  if value.deleteOnWrite then h.writeBytes place.mplace.ptr size 0x42
  else h.checkAccess place.mplace.ptr size
  let address ← h.resolve place.mplace.ptr
  h.insert address size value

def getOrInsert (h : Hooks S T) (place : MPlaceTy Provenance)
    (new : M S (Object S T)) : M S (Object S T) := do
  let address ← h.resolve place.mplace.ptr
  if let some value ← h.lookup address then return value
  let value ← new
  insert h place value
  return value

structure AccessHooks (S T : Type) where
  entries : AllocId → M S (Array (AllocRange × Object S T))
  remove : AllocId → Size → M S Unit

def onMemoryAccess (h : AccessHooks S T) (allocation : AllocId)
    (start size : Size) (kind : AccessKind) : M S Unit := do
  let entries := (← h.entries allocation).qsort (fun left right => left.1.start.bytes < right.1.start.bytes)
  let mut deletions := #[]
  for (range,obj) in entries do
    if kind == .deallocation || (size != Size.ZERO &&
        start.bytes.toNat < range.start.bytes.toNat + range.size.bytes.toNat &&
        range.start.bytes.toNat < start.bytes.toNat + size.bytes.toNat) then
      obj.onAccess kind
      if kind == .write && obj.deleteOnWrite then deletions := deletions.push range.start
  -- All callbacks run before any removals. Failure preserves every entry.
  for offset in deletions do h.remove allocation offset
end Miri.Concurrency.SyncObject
