import duplicate_prefix.CurrentCallOrdinarySafety
import duplicate_prefix.ResultCall

namespace DuplicatePrefix.VCGen

open Miri Miri.Input Miri.Memory Miri.Interpreter Miri.Verification ActualReferenceContext

/-- Call-boundary validity and the hypotheses of the existing whole-body proof.
This proof covers every count under the same body hypotheses. -/
noncomputable def CallPre (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (argument : DuplicatePrefixSliceArgument.Argument) (len count : UInt64)
    (place : MPlaceTy Provenance) : Prop :=
  CallWellFormed (resolvedCall options remaining span argument len count place)
    (ExecutionMachine.callHooks (config options (remaining + 1) span) limits)
    (fun _ _ => True) ⟨⟨#[]⟩, before⟩ ∧
    Nonempty (CurrentCallOrdinaryInput.OrdinaryInput options limits remaining span before
      argument len place)

/-- The published input domain already certifies the resolved call boundary. -/
theorem callPre_of_ordinary_input {options limits remaining span before argument len place}
    (input : CurrentCallOrdinaryInput.OrdinaryInput options limits remaining span before
      argument len place) (count : UInt64) :
    CallPre options limits remaining span before argument len count place := by
  obtain ⟨entry, _, initialized, _, _, _, noErrors, _, _⟩ :=
    CurrentCallOrdinarySafety.invoke input count
  refine ⟨⟨⟨(), trivial⟩, ?_⟩, ⟨input⟩⟩
  rintro ⟨⟩ _
  exact ⟨entry, initialized, noErrors.1.2⟩

/-- Every count in the pinned ordinary-input domain has a verified call
and body program with the same normal return state. -/
theorem ordinary_call {options limits remaining span before argument len place}
    (input : CurrentCallOrdinaryInput.OrdinaryInput options limits remaining span before
      argument len place) (count : UInt64) :
    OrdinaryContract options limits remaining span before argument len count place :=
  ordinary_contract_of_result (CurrentCallOrdinarySafety.invoke input count)

/-- The existing body proof discharges the call contract under `CallPre`. -/
theorem call_of_precondition {options limits remaining span before argument len count place}
    (ready : CallPre options limits remaining span before argument len count place) :
    OrdinaryContract options limits remaining span before argument len count place := by
  obtain ⟨input⟩ := ready.2
  exact ordinary_call input count

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
