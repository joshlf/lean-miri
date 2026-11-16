import Miri.Input.CallResolution
import Miri.Input.SourceAbiRuntime

namespace Miri.Input.CompilerInstanceAbi
open Lean Miri.ABI Miri.Interpreter
structure Prepared where
  runtime : RuntimeMetadata
  program : LoweredProgram

def prepare (runtime : RuntimeMetadata) (program : LoweredProgram) : Except String Prepared :=
  pure ⟨runtime, program⟩

def abiOfInstance (prepared : Prepared) (callee : CallInstance) (extra : Array MIR.TyId) :
    Except String (FnAbi MIR.TyId) := do
  let context : CompilerFacts.Context := ⟨prepared.runtime, prepared.program, none⟩
  SourceAbiRuntime.ofInstance context callee extra

def hooks (prepared : Prepared)
    (base : CallHooks P S C E Other Extern (FnAbi MIR.TyId) (ArgAbi MIR.TyId)) :
    CallHooks P S C E Other Extern (FnAbi MIR.TyId) (ArgAbi MIR.TyId) :=
  { base with fnAbiOfInstance := fun _ callee extra =>
      match abiOfInstance prepared callee extra with
      | .ok abi => pure abi
      | .error error => throw (.invalidProgram error) }
end Miri.Input.CompilerInstanceAbi
