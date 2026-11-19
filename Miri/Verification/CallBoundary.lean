import Miri.Interpreter.ExecutionMachine

namespace Miri.Verification

open Miri.ABI Miri.MIR Miri.Memory Miri.Interpreter

/-- A resolved MIR call with the compiler ABI for its instantiated prototype. -/
structure ResolvedCall where
  callee : CallInstance
  body : LoadedBody
  callerAbi : FnAbi TyId
  arguments : Array (FnArg Provenance)
  withCallerLocation : Bool
  destination : RuntimeStackPlace Provenance
  continuation : ReturnContinuation

/-- Run the interpreter's frame preparation, including the FnEntry checks. -/
def ResolvedCall.prepare {K U C O X : Type} (call : ResolvedCall)
    (hooks : ExecutionMachine.Calls K U C O X) (choice : C) :
    CallM (MachineHooks.State K U) Unit :=
  Call.initStackFrame hooks choice call.callee call.body call.callerAbi call.arguments
    call.withCallerLocation call.destination call.continuation

/-- Every permitted choice prepares one new frame. Includes the ABI and
return-place checks performed at entry, argument copying and retagging.
The interpreter may consult its resource limits during preparation. -/
def CallWellFormed {K U C O X : Type} (call : ResolvedCall)
    (hooks : ExecutionMachine.Calls K U C O X)
    (allowed : MachineHooks.State K U → C → Prop) (before : MachineHooks.State K U) : Prop :=
  (∃ choice, allowed before choice) ∧
    ∀ choice, allowed before choice → ∃ entry,
      call.prepare hooks choice before = .ok () entry ∧
      entry.stack.frames.size = before.stack.frames.size + 1

end Miri.Verification
