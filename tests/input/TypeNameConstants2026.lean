import Miri.Input.EvalPreparation
import Miri.Input.CompilerValueConstants

open Lean Miri.Input Miri.Interpreter

private def must (value : Except String α) : IO α :=
  match value with | .ok x => pure x | .error e => throw (IO.userError e)
private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def withNames (p : CompilerProviders.Prepared) (rows : Array Catalog.TypeName) :
    CompilerProviders.Prepared :=
  let queries := {p.program.input.queries with typeNames := rows}
  {p with program := {p.program with input := {p.program.input with queries}}, lowering := none}

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected ordinary export fixture")
  let decoded ← must (decodeJson (← IO.FS.readFile path))
  let program ← must (lowerProgram decoded.document)
  let p := (← must (EvalPreparation.prepare program).outcome).compiler
  let some memory := p.program.input.allocations.find? (fun node => match node.data with
      | some (.memory _) => true | _ => false) |
    throw (IO.userError "fixture has no constant memory")
  let some (.memory image) := memory.data | throw (IO.userError "constant memory invariant")
  let row : Catalog.TypeName := ⟨0, p.program.input.queries.primitives.typeNameResultType,
    .Slice memory.id image.sizeBytes⟩
  let expected ← must (CompilerValueConstants.typeName (withNames p #[row]) row.inputType)
  let duplicate ← must (CompilerValueConstants.typeName (withNames p #[row,row]) row.inputType)
  check (decide (duplicate = expected)) "duplicate type-name row changed result"
  let conflict := {row with resultType := p.program.input.types.size}
  check (!(CompilerValueConstants.typeName (withNames p #[row,conflict]) row.inputType).isOk)
    "conflicting type-name rows were accepted"
  check (!(CompilerValueConstants.typeName (withNames p #[]) row.inputType).isOk)
    "missing type-name row was accepted"
  check (!(CompilerValueConstants.typeName (withNames p #[conflict]) row.inputType).isOk)
    "invalid type-name result type was accepted"
  IO.println "synthetic type-name catalog controls retain duplicate, conflicting, missing and result-type controls"
