import Miri.Input.CompilerValueConstants
import Miri.Interpreter.FunctionPointers
import Miri.Input.CallerLocationConstruction
import Miri.Interpreter.GlobalByteMachine

namespace Miri.Input.EvalCallerLocationConstruction
open Lean Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

def hook (p : CompilerProviders.Prepared)
    (functions : FunctionPointers.Hooks K User Other)
    (currentLocation : MachineHooks.M K User SpanRef)
    (pointee : TyId → Except String (Option TyId))
    (classifyError : ConstantError → StepError)
    (checkKnown : LocalLayout → LocalLayout → MachineHooks.M K User Bool)
    (_ : C) (destination : LocalLayout) : MachineHooks.M K User (OpTy Provenance) := do
  let span ← currentLocation
  let some source := p.program.input.spans[span.id]? |
    throw (.unsupported "caller-location source span is absent")
  let some currentFrame := (← get).stack.currentFrame? | throw (.stack .emptyStack)
  let policy := p.program.input.queries.session.locationDetail
  let some filename := p.program.input.files[source.expansionLocation.file]? |
    throw (.unsupported "caller-location expansion filename is absent")
  if filename.toUTF8.data.contains 0 then
    throw (.invalidProgram "caller-location filename contains a NUL byte")
  let filename := if policy.file then filename else "<redacted>"
  let data := filename.toUTF8.data
  -- This is CTFE salt zero, not Miri’s random global-byte salt. Keep the
  -- filename pointer unadjusted until the Location global is imported.
  let fileId ← GlobalByteMachine.reserve (data.push 0) ⟨0,by decide⟩
  if data.size >= 2^64 then throw (.invalidProgram "caller-location filename length exceeds u64")
  let ty ← match p.callerLocationType with
    | .ok ty => pure ty
    | .error error => throw (.unsupported error)
  let pointeeTy ← match pointee ty with
    | .ok (some id) => pure id
    | .ok none => throw (.invalidProgram "caller-location result is not a pointer type")
    | .error reason => throw (.unsupported reason)
  let pointeeLayout ← match p.runtime.lookup pointeeTy with
    | .ok layout => pure layout
    | .error error => throw (.unsupported (toString error))
  -- Allocation construction precedes reservation; field projection and writes
  -- follow it (interpret/memory.rs allocate_ptr/insert_allocation).
  let allocation ← match Allocation.tryNew pointeeLayout.layout.size pointeeLayout.layout.align.abi .Uninit
      (fun size _ => some (Array.replicate size.bytes.toNat 0)) with
    | .ok allocation => pure allocation
    | .error error => throw (.resourceExhaustion s!"caller-location allocation: {reprStr error}")
  let state ← get
  let (memory,reserved) := state.machine.memory.reserveAllocId
  set {state with machine := {state.machine with memory}}
  let freshId ← match reserved with
    | .ok id => pure id
    | .error error => throw (.resourceExhaustion s!"caller-location global identity: {reprStr error}")
  let allocation ← match CallerLocationConstruction.initializeFields p.runtime pointeeLayout allocation fileId data.size
      (if policy.line then source.expansionLocation.line else 0)
      (if policy.column then source.expansionLocation.column else 0) with
    | .ok value => pure value
    | .error error => throw (.unsupported error)
  let state ← get
  let memory := MemoryState.pushGlobal state.machine.memory
    ⟨freshId,.memory,allocation.byteSize,allocation.align,.Not,some (.memory allocation)⟩
  set {state with machine := {state.machine with memory}}
  let computed ← match p.runtime.lookup ty with
    | .ok layout => pure layout
    | .error error => throw (classifyError (.metadata (toString error)))
  unless ← checkKnown ⟨computed.ty,computed.layout⟩ destination do
    throw (.invalidProgram "known constant layout differs from compiler layout")
  let pointer ← FunctionPointers.rootPointer functions freshId
  let scalar ← match Scalar.fromMaybePointer p.runtime.target.base pointer.withOptionalProvenance with
    | .ok scalar => pure scalar
    | .error error => throw (ScalarOps.scalarError error)
  -- Keep the current frame alive through this operation, just as the ordinary
  -- ConstValue conversion path requires before returning a typed operand.
  let _ := currentFrame
  pure ⟨.immediate (.scalar scalar), destination⟩
end Miri.Input.EvalCallerLocationConstruction
