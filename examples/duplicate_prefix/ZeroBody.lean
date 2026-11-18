import duplicate_prefix.RootZeroComplete
import duplicate_prefix.VCGen

/-! Whole prepared-body verification for the zero-count path of the pinned
duplicate_prefix MIR, using the existing memory and frame preconditions. -/
namespace DuplicatePrefix.VCGen

open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open PhysicalMachineWrite Miri.Verification Std.WP
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

/-- The zero-count body returns a physical true Boolean. The verified driver
program and scoped contracts describe the same final machine state. -/
theorem zero_count (context validationContext : Context)
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (accessEq : (PreparedContracts.actualConfig options () remaining span).access = validationContext.access)
    (validationWidth : validationContext.pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (validationRuntimeSize : validationContext.access.runtime.pointerSize = Size.ofBytes 8)
    (sameRuntime : validationContext.access.runtime.base = context.access.runtime.base)
    (limits : ExecutionMachine.Limits) (fuel : Nat)
    (debugOff : options.place.debugAssertions = false)
    (validationFuel : options.limits.validation = fuel+1)
    (frame : CompilerFrameContext.ActualFrame)
    (initialMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (beforeMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (beforeEq : beforeMachine = RootZeroCompleteState.tick options remaining span
      (RootZeroCompleteState.tick options remaining span (RootZeroCompleteState.tick options remaining span initialMachine)))
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl initialMachine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl initialMachine.user).gcInterval = 0)
    (fixed : initialMachine.threads.fixedScheduling = true)
    (beforeTracker : MachineHooks.BorrowState) (borrowFrame : FrameState)
    (beforeTracked : beforeMachine.borrowTracker = some beforeTracker)
    (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (releasedMemory : MemoryState Provenance BorrowTree MiriMemoryKind)
    (plan : RootPhysicalReturnPlan.Profile beforeTracker.global.protectedTags borrowFrame.protectedTags.toList
      beforeMachine.memory releasedMemory)
    (thread : ThreadRecord) (active : beforeMachine.threads.activeThread? = some thread)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (stateEq : state = ⟨⟨#[]⟩, GenericPopFrame.afterRelevanceAt #[] frame
      (ActualPopPlan.released beforeMachine releasedMemory beforeTracker borrowFrame) (thread.topUserRelevantFrame.getD 0)⟩)
    (sourceBody : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity=RootBody.reflected.body.identity)
    (callee : frame.functionInstance=RootBody.reflected.functionInstance)
    (location : frame.location = .mir ⟨0,0⟩)
    (frameSize : frame.locals.size=25)
    (source : PreparedContracts.SourceComparator)
    (dead3 : (frame.locals[3]'(by omega)).value=.dead)
    (dead4 : (frame.locals[4]'(by omega)).value=.dead) (dead5 : (frame.locals[5]'(by omega)).value=.dead)
    (uncached4 : (frame.locals[4]'(by omega)).layout=none) (uncached5 : (frame.locals[5]'(by omega)).layout=none)
    (live2 : (frame.locals[2]'(by omega)).value=.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 0)))))
    (cached2 : (frame.locals[2]'(by omega)).layout=some RootCompilerFacts.usizeLayout)
    (initialGhost : initialMachine.user.payload.ghost=false)
    (initialShallow : initialMachine.user.payload.validation=.Shallow)
    (defaultMode : beforeTracker.retagMode=.Default)
    (valid0 : (0 : MIR.LocalId) < frame.locals.size)
    (noLocalClocks : frame.extra.dataRace = none)
    (continuation : frame.returnContinuation = .stop true)
    (immediateLocals : ∀ slot ∈ frame.locals, ∀ memory, slot.value ≠ .live (.indirect memory))
    (varargs : frame.vaList = #[])
    (place : MPlaceTy Provenance) (id : AllocId) (root child : BorTag) (written : Bool) (base count : UInt64)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (tracker : MachineHooks.BorrowState)
    (live0 : frame.locals[0].value = .live (.immediate  .uninit))
    (cached0 : frame.locals[0].layout = none)
    (one : count = 1)
    (layout : place.layout = RootCompilerFacts.boolLayout)
    (width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (positive : (0 : UInt64) < count) (signedFits : count.toNat < 9223372036854775808)
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (initialPresent : initialMachine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (size : entry.allocation.byteSize = Size.ofBytes count)
    (mutable : entry.allocation.mutability = .Mut)
    (maskValid : InitMaskCopy.WellFormed entry.allocation.initializationMask)
    (runtimeWidth : context.access.runtime.base.pointerWidth = .w64)
    (storage : entry.allocation.len = entry.allocation.byteSize.bytes.toNat)
    (maskLength : entry.allocation.initializationMask.len = entry.allocation.byteSize)
    (provenance : entry.allocation.provenanceMap = ProvenanceMap.new)
    (noClocks : state.machine.dataRace = none)
    (noBackend : state.machine.user.payload.payload.user.backend = .none)
    (enabled : state.machine.borrowTracker = some tracker)
    (extras : (context.extras.get state.machine.user).allocations.find? (fun row => row.1 == id) = some (id,{ weakMemory := none, backtrace := AllocationBacktrace.get ((context.extras.get state.machine.user).allocations) (id) }))
    (rootFree : tracker.global.protectedTags.contains root = false)
    (childFree : tracker.global.protectedTags.contains child = false)
    (initialTree : entry.allocation.extra = slotTree root child count written)
    (pointer : place.mplace.ptr = Pointer.new (some (.concrete id root)) (Size.ofBytes base))
    (aligned : place.mplace.misaligned = none)
    (runtimeSize : context.access.runtime.pointerSize = Size.ofBytes 8)
    (outerAccessEq : (PreparedContracts.actualConfig options () (remaining+1) span).access = context.access)
    (ghost : state.machine.user.payload.ghost = false)
    (shallow : state.machine.user.payload.validation = .Shallow)
    (destination : frame.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩)
    (finish : Size) (endpoint : (allocRange place.mplace.ptr.offset (Size.ofBytes 1)).endExclusive = .ok finish) :
    let config := PreparedContracts.actualConfig options () (remaining + 1) span
    let initial := Storage.withCurrent #[] frame initialMachine
    ∃ updated steps,
      let final := CanonicalCopy.replaceAllocation state id entry.kind updated
      Triple (rootProgram config limits steps) (· = initial) (fun _ => (· = final))
        (fun _ _ => False) ∧
      FunctionBody.UBFree (ExecutionMachine.step config limits) (·.stack.frames.size)
        (fun _ _ => True) 1 initial ∧
      FunctionBody.NormalPost (ExecutionMachine.step config limits) (·.stack.frames.size)
        (fun _ _ => True) 1 initial (· = final) ∧
      target_bytes context.access.runtime.base entry.allocation.byteSize 1 =
        .ok (AllocationCopy.snapshot updated) := by
  obtain ⟨updated, trace, stopped, _, _, _, _, _, _, bytes, _⟩ := RootZeroComplete.complete
    context validationContext options remaining span accessEq validationWidth validationRuntimeSize
    sameRuntime limits fuel debugOff validationFuel frame initialMachine beforeMachine beforeEq
    unchecked noGc fixed beforeTracker borrowFrame beforeTracked frameTracked releasedMemory plan
    thread active state stateEq sourceBody identity callee location frameSize source dead3 dead4
    dead5 uncached4 uncached5 live2 cached2 initialGhost initialShallow defaultMode valid0
    noLocalClocks continuation immediateLocals varargs place id root child written base count entry
    tracker live0 cached0 one layout width positive signedFits cached initialPresent size mutable
    maskValid runtimeWidth storage maskLength provenance noClocks noBackend enabled extras rootFree
    childFree initialTree pointer aligned runtimeSize outerAccessEq ghost shallow destination finish
    endpoint
  obtain ⟨steps, verified⟩ := program_of_trace trace stopped
  have empty : (CanonicalCopy.replaceAllocation state id entry.kind updated).stack.frames = #[] := by
    rw [stateEq]
    rfl
  obtain ⟨safe, returned⟩ := contracts_of_trace trace empty
  exact ⟨updated, steps, verified, safe, returned, bytes⟩

end DuplicatePrefix.VCGen

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.VCGen.").length > 1 then
      count := count + 1
      for axiomName in ← collectAxioms name do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains axiomName do
          throwError "unapproved axiom {axiomName} in {name}"
  if count == 0 then throwError "no duplicate_prefix vcgen declarations found"
  logInfo m!"Audited {count} duplicate_prefix vcgen declarations"
