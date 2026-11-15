import Miri.Frontend.FoundationProgram
import Miri.Input.EvalConfigurationCore
import Miri.Input.CompilerGlobals
import Miri.Input.CompilerAllocIdWorld
import Miri.Input.CompilerFunctionPointers
import Miri.Input.CompilerVTableMachine
import Miri.Input.CompilerIntrinsicSymbols
import Miri.Input.EvalCompilerMachine
import Miri.Input.EvalTerminatorMachine

/-! A bounded u8 identity call in the existing fixed interpreter. The caller
supplies a prepared source program; unavailable host operations fail explicitly.
This is a finite call/return observation, not a process run or safety theorem. -/
namespace Miri.Frontend.Foundation.FixedIdentityRun
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
private abbrev Host := Input.HostRuntime.Storage Unit Unit Unit Unit Unit String Unit Unit
private abbrev World := Input.EvalWorld.World Unit Unit Unit Unit Unit String Unit Unit Host
private abbrev CoreUser := Input.EvalCoreMachine.User Unit Unit Unit Unit Unit String Unit Unit Host
private abbrev InnerState := MachineHooks.State MiriMemoryKind
  (ExecutionStateTransport.Inner World)
private abbrev OuterState := MachineHooks.State MiriMemoryKind
  (ExecutionStateTransport.Outer World)
private abbrev CoreOptions := Input.EvalConfigurationCore.Options
private abbrev CoreLeaves := Input.EvalConfigurationCore.Leaves
  Unit Unit Unit Unit Unit String Unit Unit Host Unit Unit

private def checkedState {S A : Type} (result : StepResult S A) : Except String (S × A) :=
  match result with
  | (state, .ok value) => .ok (state, value)
  | (_, .error error) => .error s!"source prefix failed: {reprStr error}"

private def options : CoreOptions := {
  place := {debugAssertions := false, dynamicFuel := 256, validation := .Shallow}
  limits := {callDispatch := 128, casts := 128, retag := 128, validation := 128}
  compatibilityBudget := 128, varArgsBudget := 128, callbackCapacity := 128
  floatNondeterministic := false, weakFailureRate := 0, crossCrateInlineAlways := false
  userRelevantCrates := #[], ignoreOptionalOverflowChecks := false, panicUnwinds := true
  retag := {implicitWrites := false, preciseInteriorMut := true} }

private def unknownSync : Unit → Concurrency.SyncObject.AccessKind →
    PlaceMachine.MachineM MiriMemoryKind CoreUser Unit :=
  fun _ _ => fun machine => .error (.unsupported "sync payload access unavailable in isolated smoke") machine

private def leaves (dummy : SpanRef) : CoreLeaves := {
  pointerSource := {
    nativeLibraryPaths := fun host => host.nativeLibraries.map Prod.fst
    nativeHost := none

  }
  sync := unknownSync
  storage := fun size _ => some (Array.replicate size.bytes.toNat 0)
  spans := ⟨dummy, false⟩
  foreign := none
  dynSymName := fun _ => ""
  checkLlvmSymbolClash := fun _ => throw (.unsupported "LLVM symbol registry unavailable in isolated smoke")
  math := none
  mathError := .none
  control := Input.EvalTerminatorMachine.controlAccess
  blockingSources := Input.EvalTerminatorMachine.ioSourcesAccess }

private def rootCall (p : Input.CompilerProviders.Prepared) (body : LoadedBody)
    (rootInstance : CallInstance) (config : ExecutionMachine.Config MiriMemoryKind
      CoreUser
      Unit String ABI.ExternAbi Unit) (state : InnerState) : Except String (InnerState × RuntimeStackPlace Provenance) := do
  let abi ← Input.CompilerInstanceAbi.abiOfInstance p.lifecycle.instances rootInstance #[]
  let some returnTy := body.body.locals[0]? | throw "root has no return local"
  let returnLayout ← (p.runtime.lookup returnTy).mapError toString
  let some argumentTy := body.body.locals[1]? | throw "identity argument absent"
  let argumentLayout ← (p.runtime.lookup argumentTy).mapError toString
  unless body.body.argumentCount == 1 && argumentLayout.layout.size.bytes == 1 &&
      argumentTy == p.program.input.queries.primitives.u8 && returnTy == argumentTy do
    throw "bounded runner requires exactly one byte argument"
  let argument : FnArg Provenance := .Copy ⟨.immediate (.scalar (.fromScalarInt (.ofUInt8 42))), argumentLayout⟩
  let hooks := ExecutionMachine.callHooks config options.limits
  let action : MachineHooks.M MiriMemoryKind
      CoreUser
      (RuntimeStackPlace Provenance) := do
    let destination ← hooks.allocateStack () returnLayout
    Call.initStackFrame hooks () rootInstance body abi #[argument] false (.memory destination) (.stop true)
    pure (.memory destination)
  checkedState (MachineHooks.run action state)

/-- Execute one direct u8 frame under the explicit fixed-scheduling, shallow
validation, vclock profile below. Only the observed finite call is asserted;
startup, process exit and other permitted choices are outside this check. -/
def runPrepared (prepared : Input.CompilerProviders.Prepared) : Except String String := do
  let dummy ← Input.CompilerContextSpan.rootSpan prepared.program
  let definition ← prepared.program.rootDefinitionId 0
  let some root := prepared.program.input.bodyRoots[0]? | throw "root absent"
  unless root.definitionId == definition do throw "root definition mismatch"
  let rootInstance := root.entryInstance
  let body ← Input.CallResolution.loadedBodyOfInstance prepared.lifecycle.calls.calls rootInstance
  let some returnTy := body.body.locals[0]? | throw "root has no return local"
  let imported := Input.CompilerGlobals.importGraph prepared.runtime.target prepared.program
    (MemoryState.empty : MemoryState Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind)
  let image ← imported.outcome
  -- Match canonical EvalPreparation: preserve the supplied raw-ID frontier
  -- and crosswalk before any runtime allocation or byte-key attachment.
  let memory ← Input.CompilerAllocIdWorld.install
    prepared.program.input.compilerAllocIdWorld prepared.program.input.allocations imported.memory
  let arrays ← prepared.initialArrays
  let host : Host := {
    blocking := ⟨none, #[]⟩, clock := .virtual 0, deadlines := .empty
    readiness := {}, futex := {}, sync := {}, io := {}, events := #[]
    virtualSockets := #[], tcpSockets := #[], nativeLibraries := #[], profiler := none
    control := TerminatorControl.initial ⟨0, 0x3f847ae147ae147b, true⟩ }
  let arch ← Input.EvalArchitectureMachine.targetArch prepared.intrinsics
  let targetBits := prepared.runtime.target.base.pointerWidth.bits.toNat
  let targetTriple := prepared.program.input.producer.targetTriple
  unless targetTriple == "x86_64-unknown-linux-gnu" && arch == "x86_64" && targetBits == 64 do
    throw s!"fixture target differs from this source runner setup: triple={targetTriple}, arch={arch}, pointer_bits={targetBits}"
  let geometry ← (Input.InitialMachine.geometry targetBits arch false none).mapError reprStr
  let dummySpan := dummy
  let machineConfig : Input.InitialMachine.Configuration Unit Unit := {
    geometry, dummySpan, provenance := .default, addressMode := .managed
    addressStop := 18446744073709551615, addressReuse := ⟨0.5, 0.1⟩
    fixedScheduling := true, trackOutdatedLoads := false, weakMemory := true
    backend := .vclocks, trackedTags := some #[], validation := .Shallow
    alignment := .Int, affinity := none, muteOutput := true, hostUsizeBits := 64 }
  -- Finite actual source address choices for this stack-allocation prefix.
  -- Any other source choice site or tape exhaustion remains an execution error.
  let initial ← (Input.InitialMachine.create (Os := Unit) (R := Unit) (P := Unit)
    (H := Unit) (D := Unit) (O := String) (Aff := Unit) (B := Unit)
    machineConfig memory arrays
      { inputs := Array.replicate 128 (.index .addressSlack 0), cursor := 0 } host).mapError reprStr
  let initial : OuterState := initial
  let inner := ExecutionStateTransport.inward initial
  let bytesAction : MachineHooks.M MiriMemoryKind
      CoreUser
      Input.CompilerGlobalBytes.Prepared :=
    Input.CompilerGlobalBytes.attach prepared.program prepared.runtime
  let (inner, bytes) ← checkedState (MachineHooks.run bytesAction inner)
  let coreLeaves := leaves dummy
  match Input.EvalConfigurationCore.make prepared image bytes options coreLeaves () 256 with
  | .error error => throw (reprStr error)
  | .ok config => do
    let registryAttach : MachineHooks.M MiriMemoryKind
        CoreUser Unit := do
      Input.CompilerFunctionPointers.attach prepared.pointers image config.functions
      let vtableRuntime := Input.EvalCompilerMachine.vtables prepared image config.functions
      Input.CompilerVTableMachine.attach prepared.vtables image vtableRuntime
      Input.CompilerIntrinsicSymbols.attach prepared image Input.EvalConfiguration.symbols
    let (inner, _) ← checkedState (MachineHooks.run registryAttach inner)
    let (inner, returnPlace) ← rootCall prepared body rootInstance config inner
    unless returnPlace.layout.ty == returnTy do
      throw "root return place lost its compiler type identity"
    unless (match returnPlace with | .memory _ => true | _ => false) do
      throw "non-unit root return place was not backed by real memory"
    let ready : OuterState := ExecutionStateTransport.outward inner
    let (after, stepped) ← checkedState
      (Input.EvalConfigurationCore.step prepared image bytes options coreLeaves () ready)
    let some frame := after.stack.currentFrame? | throw "source Step.step removed the root frame"
    unless frame.bodyIdentity == body.identity && frame.functionInstance == rootInstance do
      throw "source call frame lost the loaded body or complete root instance identity"
    unless frame.returnPlace == returnPlace do
      throw "source call frame did not retain its allocated return place"
    unless frame.location == .mir ⟨0, 1⟩ do
      throw s!"source step did not advance past the exported assignment: {reprStr frame.location}"
    let (inner, localOp) ← checkedState (MachineHooks.run
      (PlaceMachine.localToOp config.compiler () 0) (ExecutionStateTransport.inward after))
    let (_, value) ← checkedState (MachineHooks.run (PlaceMachine.readImmediate config.access localOp) inner)
    let scalar ← (value.imm.toScalar.mapError reprStr)
    let result ← (scalar.toUInt8.mapError reprStr)
    unless result == 42 do
      throw s!"actual exported root returned {result}, expected 42"
    unless stepped do throw "source Step.step returned no performed step"
    let (returned, _) ← checkedState
      (Input.EvalConfigurationCore.step prepared image bytes options coreLeaves () after)
    unless returned.stack.frames.isEmpty && returned.stack.currentFrame?.isNone do
      throw "fixed interpreter Return did not empty identity stack"
    pure s!"fixed interpreter identity(42_u8)={result}; assignment and Return executed; stack empty"

end Miri.Frontend.Foundation.FixedIdentityRun
