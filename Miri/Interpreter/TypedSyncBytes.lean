import Miri.Interpreter.TypedSyncFactories
import Miri.Interpreter.RawMemoryMachine

/-! Synchronization marker bytes use the canonical atomic scalar operations and shared memory state. -/

namespace Miri.Interpreter.TypedSyncBytes
open Miri.ABI Miri.Memory Miri.Concurrency
private def lift (result : Except StepError A) : EStateM StepError S A :=
  match result with | .ok value => pure value | .error error => throw error
private def byte (value : UInt8) : EStateM StepError S (Scalar Provenance) :=
  lift (Scalar.fromUInt (BitVec.ofNat 128 value.toNat) (Size.ofBytes 1) |>.mapError ScalarOps.scalarError)

def bindObjectHooks [DecidableEq K]
    (h : LinuxFutexMachine.ObjectHooks K U C P O B) (choice : C)
    (u8Layout : LocalLayout) : TypedSyncObjectMachine.Bytes (LinuxFutexMachine.State K U) where
  writeBytes := fun ptr size value => RawMemoryMachine.writeRepeatedByte h.access h.pointers.arithmetic ptr value size.bytes

def bind [DecidableEq K]
    (h : LinuxFutexMachine.Hooks K U C P O B H Y Z T E) (choice : C)
    (u8Layout : LocalLayout) : TypedSyncObjectMachine.Bytes (LinuxFutexMachine.State K U) :=
  bindObjectHooks (LinuxFutexMachine.objectHooks h) choice u8Layout
/-- Pthread object compiler globals remain required by their exact source names;
all operand dereferences and byte reads are the canonical physical operations. -/
def pthreadMemoryFromObjectHooks [DecidableEq K]
    (h : LinuxFutexMachine.ObjectHooks K U C P O B) (choice : C)
    (os : String) (initializer : String → LinuxFutexMachine.M K U TypedSyncRuntime.Dest) :
    TypedSyncFactories.PthreadMemory (LinuxFutexMachine.State K U) where
  os := os
  initializer := initializer
  deref := fun op _ => PointerPlaceMachine.dereference h.access h.pointerCompiler h.dynamic h.vtable h.dynamicFuel choice op
  readBytes := fun place size => RawMemoryMachine.readBytes h.access h.pointers.arithmetic place.mplace.ptr size.bytes

def pthreadMemory [DecidableEq K]
    (h : LinuxFutexMachine.Hooks K U C P O B H Y Z T E) (choice : C)
    (os : String) (initializer : String → LinuxFutexMachine.M K U TypedSyncRuntime.Dest) :
    TypedSyncFactories.PthreadMemory (LinuxFutexMachine.State K U) :=
  pthreadMemoryFromObjectHooks (LinuxFutexMachine.objectHooks h) choice os initializer
end Miri.Interpreter.TypedSyncBytes
