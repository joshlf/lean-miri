import duplicate_prefix.CurrentCallOrdinarySafety
import duplicate_prefix.ResultCall

namespace DuplicatePrefix.VCGen

/-- Every count in the pinned ordinary-input domain has a verified call
and body program with the same normal return state. -/
theorem ordinary_call {options limits remaining span before argument len place}
    (input : CurrentCallOrdinaryInput.OrdinaryInput options limits remaining span before
      argument len place) (count : UInt64) :
    OrdinaryContract options limits remaining span before argument len count place :=
  ordinary_contract_of_result (CurrentCallOrdinarySafety.invoke input count)

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
