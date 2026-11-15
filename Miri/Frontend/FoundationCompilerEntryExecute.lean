import Miri.Frontend.FoundationCompilerEntryProgram
import Miri.Input.EvalConfigurationCore
import Miri.Input.EvalStartupAssembly
import Miri.Input.EvalStartupMemoryConstruction
import Miri.Input.CompilerGlobalBytes
import Miri.Input.EvalTerminatorMachine

/-! Actual compiler-selected custom lang-start execution from finite material.
The fixed startup factory allocates argv, installs entry callbacks, constructs
main's function pointer and calls the source start body, then runs TLS and
thread/process termination. Empty argv, isolated host and fixed scheduling are
explicit chosen configuration, with bounded diagnostic-zero source choices. This is one finite run, not a safety theorem. -/
namespace Miri.Frontend.Foundation.CompilerEntryRun
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
private abbrev Os := ByteArray
private abbrev Host := Input.HostRuntime.Storage Unit Unit Unit Unit Unit String Unit Unit
private abbrev World := Input.EvalWorld.World Os Unit Unit Unit Unit String Unit Unit Host
private abbrev CoreUser := Input.EvalCoreMachine.User Os Unit Unit Unit Unit String Unit Unit Host
private abbrev CoreConfig := ExecutionMachine.Config MiriMemoryKind CoreUser Unit String ABI.ExternAbi Unit
private abbrev EntryUser := Input.EvalExecutable.U Os Unit Unit Unit Unit String Unit Unit Host
private abbrev InnerState := MachineHooks.State MiriMemoryKind
  (ExecutionStateTransport.Inner World)
private abbrev OuterState := MachineHooks.State MiriMemoryKind
  (ExecutionStateTransport.Outer World)
private abbrev CoreOptions := Input.EvalConfigurationCore.Options
private abbrev CoreLeaves := Input.EvalConfigurationCore.Leaves
  Os Unit Unit Unit Unit String Unit Unit Host Unit Unit
private abbrev LoopHooks := RunLoopHooks OuterState Unit MainMachine.Callback

private def options : CoreOptions := {
  place := {debugAssertions := false, dynamicFuel := 256, validation := .Shallow}
  limits := {callDispatch := 128, casts := 128, retag := 128, validation := 128}
  compatibilityBudget := 128, varArgsBudget := 128, callbackCapacity := 128
  floatNondeterministic := false, weakFailureRate := 0, crossCrateInlineAlways := false
  userRelevantCrates := #[], ignoreOptionalOverflowChecks := false, panicUnwinds := false
  retag := {implicitWrites := false, preciseInteriorMut := true} }

private def unknownSync : Unit → Concurrency.SyncObject.AccessKind →
    PlaceMachine.MachineM MiriMemoryKind CoreUser Unit :=
  fun _ _ => fun machine => .error (.unsupported "sync payload access unavailable in isolated startup run") machine

private def leaves (dummy : SpanRef) : CoreLeaves := {
  pointerSource := {
    nativeLibraryPaths := fun host => host.nativeLibraries.map Prod.fst
    nativeHost := none
     }
  sync := unknownSync
  storage := fun size _ => some (Array.replicate size.bytes.toNat 0)
  spans := ⟨dummy, false⟩
  foreign := none
  dynSymName := id
  checkLlvmSymbolClash := fun _ => throw (.unsupported "LLVM symbol registry unavailable in isolated startup run")
  math := none
  mathError := .none
  control := Input.EvalTerminatorMachine.controlAccess
  blockingSources := Input.EvalTerminatorMachine.ioSourcesAccess }

private def absentLoopHooks : LoopHooks := Id.run do
  let absent : StepError := .unsupported "stack-empty/main callbacks are unavailable in this finite startup prefix"
  return {
    coreStep := fun _ state => (state,.error absent)
    takeStackEmptyCallback := fun state => (state,.error absent)
    invokeStackEmptyCallback := fun _ _ state => (state,.error absent)
    restoreStackEmptyCallback := fun _ state => (state,.error absent)
    terminateActiveThread := fun _ _ state => (state,.error absent)
    interrupted := fun _ => false
    handleAbnormalTermination := id
    schedule := fun _ state => (state,.ok .executeStep)
    communicate := fun _ => false
    pollAndUnblock := fun _ _ state => (state,.error absent)
    sleep := fun _ _ state => (state,.error absent) }

private def isolatedScheduler : Unit → ThreadStacks.LocalSchedulerHooks MiriMemoryKind EntryUser :=
  fun _ => Id.run do
    let unavailable : StepError := .unsupported "isolated startup scheduler encountered pending host work"
    return {
      processDelayedReadiness := do
        let world := (← get).machine.user.user.payload.payload
        unless world.host.readiness.delayed.isEmpty do throw unavailable
      -- This fixture selects Miri's isolated configuration (`communicate =
      -- false`), so the source scheduler does not communicate with host IO.
      communicate := pure false
      pollHostIoNonBlocking := throw unavailable
      unblockExpiredDeadlines := do
        let state ← get
        let world := state.machine.user.user.payload.payload
        let timedWait := state.machine.threads.threads.any fun thread =>
          match thread.state with
          | .Blocked _ (some _) _ => true
          | _ => false
        if timedWait || !(world.host.deadlines.entries.isEmpty) then throw unavailable
        pure none
      -- Fixed scheduling is source-configured; this callback is unreachable.
      choose := fun _ => throw unavailable
      anyThreadBlockedOnHost := do
        let world := (← get).machine.user.user.payload.payload
        unless world.host.blocking.sources.isEmpty do throw unavailable
        pure false }

private def linuxHost : Input.EvalHostRuntimeConstruction.OsHostEffects Os := {
  hostWindows := false, hostUnix := true, targetWindows := false
  fromUnixBytes := id
  fromUtf8 := fun bytes =>
    match String.fromUTF8? bytes with
    | some _ => .ok bytes
    | none => .error (.invalidProgram "invalid UTF-8 in startup argument")
  fromWide := fun _ => .error (.unsupported "wide OS strings are unavailable on this Linux host")
  toWide := fun _ => .error (.unsupported "wide OS strings are unavailable on this Linux host")
  encodedBytes := id
  encodedLength := fun value => value.size
  decodeUnixBytes := .ok
  empty := ByteArray.empty, concat := fun left right => left ++ right
  ascii := fun value => value.toUTF8
  isEmpty := fun value => value.isEmpty
  containsEquals := fun value => value.data.contains 61 }

private def runWithConfiguration (prepared : Input.EvalPreparation.Prepared)
    (definition : DefId) (sigpipe : UInt8) (initial : OuterState)
    (config : CoreConfig) (coreLeaves : CoreLeaves) : Except String String := do
  let compiler := prepared.compiler
  let dummy := prepared.dummySpan
  let configs : Unit → Input.EvalExecutable.Core Os Unit Unit Unit Unit String Unit Unit Host Unit Unit :=
    fun _ => config
  let spans : AllocationDriver.SpanHooks := ⟨dummy,false⟩
  let memory := Input.EvalStartupMemoryConstruction.environmentMemory prepared (configs ()) coreLeaves spans ()
    .Int 1024
  let usizeLayout ← (Input.CompilerPrimitiveFacts.primitiveLayout compiler.runtime "usize").mapError toString
  let hostEffects : Input.EvalHostRuntimeConstruction.EnvironmentHostEffects
      (Input.EvalStartupAssembly.InnerControl Os Unit Unit Unit Unit String Unit Unit Host) := {
    invalidArgument := throw (.unsupported "host invalid-argument errno unavailable in isolated entry run")
    envVarNotFound := throw (.unsupported "Windows environment lookup is unavailable on Linux") }
  let startup : Input.EvalBootstrap.Configuration Os := {
    arguments := #[], entry := definition, entryType := .rustcMain sigpipe
    communicate := false, forwarded := #[], environment := #[], overrides := #[] }
  let started := Input.EvalStartupAssembly.startFromSourceExecutionPrefix
    prepared configs options.limits () spans linuxHost hostEffects memory id
    prepared.layouts.arguments.u8 usizeLayout
    startup absentLoopHooks isolatedScheduler
    (fun _ => false)
    (List.replicate 4096 ()) initial
  unless started.1.machine.threads.threads.length == 1 do
    throw "isolated startup fixture did not retain its expected single source thread"
  match started.2 with
  | .ok () => throw "bounded compiler-entry execution exhausted choices before source termination"
  | .error (.termination (.exit 0 true)) =>
    let rootInstance ← Input.CompilerInstance.item compiler.program.input.instances definition #[]
    let world := started.1.machine.user.user.payload.payload
    let some mainPointer := world.functions.functions.find? (fun function =>
        function.callee == rootInstance && function.salt.val == 0)
      | throw "compiler startup did not construct main function pointer"
    let info ← (started.1.machine.memory.getAllocInfo mainPointer.allocation).mapError reprStr
    unless info.kind == .function do throw "compiler main pointer allocation is not a function"
    pure "fixed compiler-selected entry reached source exit 0 after custom start(argc=0), TLS cleanup and thread termination; main function pointer constructed (empty argv, isolated host, fixed scheduling)"
  | .error error =>
    let frame := started.1.stack.currentFrame?.map fun frame =>
      s!"instance={reprStr frame.functionInstance}, location={reprStr frame.location}, body={reprStr frame.bodyIdentity}"
    let world := started.1.machine.user.user.payload.payload
    let stage := world.main.map fun data => match data.stage with
      | .globalConstructors .. => "globalConstructors"
      | .running => "running"
      | .exiting .. => "exiting"
    let envState := match world.runtime.environment with
      | .uninit => "uninit"
      | .unix vars => s!"unix(vars={vars.variables.size})"
      | .windows vars => s!"windows(vars={vars.size})"
    throw s!"source startup ended with {reprStr error}; active-frame={frame}; main-stage={stage}; argc={reprStr world.runtime.entry.argc}; argv={reprStr world.runtime.entry.argv}; mainReturn={reprStr world.runtime.entry.mainReturn}; env={envState}; extern={reprStr world.runtime.externStatics}"

def runPrepared (prepared : Input.EvalPreparation.Prepared)
    (initialMemory : MemoryState Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind) :
    Except String String := do
  let compiler := prepared.compiler
  unless compiler.program.input.producerSettings.effectivePanicStrategy == "abort" do
    throw "isolated compiler-entry runner requires source panic=abort"
  let dummy := prepared.dummySpan
  let definition ← compiler.program.rootDefinitionId 0
  let rootInstance ← Input.CompilerInstance.item compiler.loweringContext.instances definition #[]
  let _body ← Input.CallResolution.loadedBodyOfInstance compiler.lifecycle.calls.calls rootInstance
  let image := prepared.image
  let arrays ← compiler.initialArrays
  let host : Host := {
    blocking := ⟨none, #[]⟩, clock := .virtual 0, deadlines := .empty
    readiness := {}, futex := {}, sync := {}, io := {}, events := #[]
    virtualSockets := #[], tcpSockets := #[], nativeLibraries := #[], profiler := none
    control := TerminatorControl.initial ⟨0, 0x3f847ae147ae147b, true⟩ }
  let arch ← (Input.EvalArchitectureMachine.targetArch compiler.intrinsics).mapError toString
  let targetBits := compiler.runtime.target.base.pointerWidth.bits.toNat
  let targetTriple := compiler.program.input.producer.targetTriple
  unless targetTriple == "x86_64-unknown-linux-gnu" && arch == "x86_64" && targetBits == 64 do
    throw s!"startup fixture differs from runner setup: triple={targetTriple}, arch={arch}, pointer_bits={targetBits}"
  let geometry ← (Input.InitialMachine.geometry targetBits arch false none).mapError reprStr
  let machineConfig : Input.InitialMachine.Configuration Unit Unit := {
    geometry, dummySpan := dummy, provenance := .default, addressMode := .managed
    addressStop := 18446744073709551615, addressReuse := ⟨0.5, 0.1⟩
    fixedScheduling := true, trackOutdatedLoads := false, weakMemory := true
    backend := .vclocks, trackedTags := some #[], validation := .Shallow
    alignment := .Int, affinity := none, muteOutput := true, hostUsizeBits := 64 }
  -- The fixed source choice provider records each domain-valid generated draw,
  -- including main's function-allocation salt. Exhaustion remains an error.
  let initial ← (Input.InitialMachine.create (Os := Os) (R := Unit) (P := Unit)
    (H := Unit) (D := Unit) (O := String) (Aff := Unit) (B := Unit)
    machineConfig initialMemory arrays
      { inputs := #[], cursor := 0, policy := .boundedDiagnostic 4096 4096 } host).mapError reprStr
  let initial : OuterState := initial
  let bytes ← (Input.CompilerGlobalBytes.prepare compiler.program compiler.runtime initialMemory).mapError toString
  let coreLeaves := leaves dummy
  match Input.EvalConfigurationCore.make compiler image bytes options coreLeaves () 256 with
  | .error error => .error (reprStr error)
  | .ok config => do
    let some (selected, entryType) ← Input.CompilerMain.sourceCompilerEntry compiler.main
      | throw "source compiler entry absent"
    unless selected == definition do throw "source compiler entry differs from root"
    let .rustcMain sigpipe := entryType | throw "source compiler entry kind unsupported"
    runWithConfiguration prepared definition sigpipe initial config coreLeaves

end Miri.Frontend.Foundation.CompilerEntryRun
