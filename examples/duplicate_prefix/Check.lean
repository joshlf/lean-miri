import duplicate_prefix.CurrentCallOrdinaryWitnessSafety
import duplicate_prefix.GenericFunctionPoolSafety
import duplicate_prefix.GeneralBorrowPositiveConcreteWindowAllCountSafety
import duplicate_prefix.S03EmptyContract
import duplicate_prefix.S05ZeroCellActualCallRepaired
import duplicate_prefix.Alignment
import duplicate_prefix.Borrows
import duplicate_prefix.Initial

/-! Kernel compilation and transitive axiom audit of the imported program,
component lemmas and complete-call theorems, each within its declared domain. -/

namespace DuplicatePrefix.Program

theorem pinnedTarget : imported.document.producer.targetTriple =
    "x86_64-unknown-linux-gnu" := by rfl

theorem pinnedMiri : imported.document.producer.miriCommit =
    "7fa591d7d4dd9af8154becbc8332f8096f8323b1" := by rfl

/-- Typed executable data is available for the retained document. The importer
returns this value directly after accepting the document; this presence fact
makes no semantic-coverage claim. -/
theorem structurallyReady :
    ∃ executable : Miri.Input.ExecutionInput, executable.document = imported.document :=
  ⟨imported, rfl⟩

end DuplicatePrefix.Program

-- Audit every imported theorem and all owned declarations, including private/generated definitions.
open Lean Elab Command in
run_cmd do
  let mut theorems : Nat := 0
  let mut owned : Nat := 0
  for (name, info) in (← getEnv).constants.toList do
    let theoremDecl := match info with | .thmInfo _ => true | _ => false
    let own := (name.toString.splitOn "DuplicatePrefix.").length != 1
    if theoremDecl then theorems := theorems + 1
    if own then owned := owned + 1
    if theoremDecl || own then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "{name} depends on unapproved axiom {dependency}"
  logInfo m!"PASS: audited {theorems} imported theorems and {owned} owned declarations"
