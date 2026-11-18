import duplicate_prefix.DuplicatePrefixArgumentCallResult
import duplicate_prefix.VCGen

namespace DuplicatePrefix.VCGen

open Miri Miri.Input Miri.Memory Miri.MIR Miri.Interpreter
open Miri.Verification Miri.Verification.StepWP Std.WP ActualReferenceContext

noncomputable def ordinaryPreparation (options : EvalConfigurationCore.Options)
    (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (argument : DuplicatePrefixSliceArgument.Argument) (len count : UInt64)
    (place : MPlaceTy Provenance) :
    Unit → MachineHooks.State MiriMemoryKind Machine.RootUser →
      EStateM.Result StepError (MachineHooks.State MiriMemoryKind Machine.RootUser) Unit :=
  let cfg := config options (remaining + 1) span
  fun choice before => Call.initStackFrame (ExecutionMachine.callHooks cfg limits) choice
    RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
    #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
      argument len), .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true) before

/-- A resolved root call and its finite body program agree on the final state. -/
noncomputable def OrdinaryContract (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (argument : DuplicatePrefixSliceArgument.Argument) (len count : UInt64)
    (place : MPlaceTy Provenance) : Prop :=
  let cfg := config options (remaining + 1) span
  let step := ExecutionMachine.step cfg limits
  let initial : MachineHooks.State MiriMemoryKind Machine.RootUser := ⟨⟨#[]⟩, before⟩
  let prepare := ordinaryPreparation options limits remaining span argument len count place
  ∃ entry final steps, prepare () initial = .ok () entry ∧ final.stack.frames = #[] ∧
    step () final = (final, .ok false) ∧
    FunctionBody.CallNoUB step (·.stack.frames.size) (fun _ _ => True) 1 (prepare () initial) ∧
    FunctionBody.UBFree step (·.stack.frames.size) (fun _ _ => True) 1 entry ∧
    FunctionBody.NormalPost step (·.stack.frames.size) (fun _ _ => True) 1 entry (· = final) ∧
    Triple (Program.call (hooks := ExecutionMachine.stepHooks cfg limits) (allowed := fun _ _ => True)
      prepare) (· = initial) (fun _ => (· = final)) (fun error _ => RunLoop.reportsUB error = false) ∧
    Triple (rootProgram cfg limits steps) (· = entry) (fun _ => (· = final)) (fun _ _ => False)

theorem ordinary_contract_of_result {options limits remaining span before argument len count place}
    (result : DuplicatePrefixArgumentCallResult.Result options limits remaining span before
      argument len count place) :
    OrdinaryContract options limits remaining span before argument len count place := by
  obtain ⟨entry, final, initialized, trace, stopped, empty, noErrors, _, _⟩ := result
  let prepare := ordinaryPreparation options limits remaining span argument len count place
  let initial : MachineHooks.State MiriMemoryKind Machine.RootUser := ⟨⟨#[]⟩, before⟩
  have setup : prepare () initial = .ok () entry := initialized
  have depth : entry.stack.frames.size = 1 := noErrors.1.2
  obtain ⟨safe, returned⟩ := contracts_of_trace trace empty
  obtain ⟨steps, body⟩ := program_of_trace trace stopped
  have call := prepared_root_call prepare rfl depth setup trace empty
  refine ⟨entry, final, steps, setup, empty, stopped, ?_, safe, returned, call, body⟩
  apply FunctionBody.CallNoUB.of_preparation (prepare () initial) (· = entry)
  · intro failed error outcome
    rw [setup] at outcome
    cases outcome
  · intro state outcome
    rw [setup] at outcome
    cases outcome
    exact ⟨Nat.le_of_eq depth.symm, rfl⟩
  · rintro state rfl
    exact safe

end DuplicatePrefix.VCGen
