import Miri.Input.CompilerProviders
import Miri.Input.EvalRetagMachine

/-! Tree Borrows machine parameters and the exact protected-frame attribute
query from tree_borrows/mod.rs:143–148,329. Missing evidence fails on demand.
The omitted CreatedPointerTag emission is diagnostics.rs::emit_diagnostic,
which returns unit and changes no interpreter state. Tag allocation and
protector registration remain in the actual retag implementation. -/
namespace Miri.Input.CompilerRetagOptions
open Lean Miri.MIR Miri.Interpreter

/-- These are the two actual TreeBorrowsParams, fixed for an execution. -/
structure Options where
  implicitWrites : Bool
  preciseInteriorMut : Bool

def rustcNoWritable (p : CompilerProviders.Prepared) (id : DefId) : Except String Bool :=
  CompilerRetagQueries.lookup p.program.compilerTables.definitions.size p.retagQueries id

def make (p : CompilerProviders.Prepared) (options : Options) : EvalRetagMachine.Leaves K U where
  implicitWrites := pure options.implicitWrites
  preciseInteriorMut := pure options.preciseInteriorMut
  rustcNoWritable := fun id =>
    match rustcNoWritable p id with
    | .ok value => pure value
    | .error reason => throw (.unsupported reason)
  logCreation := fun _ _ _ _ _ => pure ()
end Miri.Input.CompilerRetagOptions
