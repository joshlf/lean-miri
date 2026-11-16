import Miri.Input.CompilerProviders
import Miri.Input.ConcreteCovariance

namespace Miri.Input.CompilerCovariance
open Lean Miri.ABI Miri.Interpreter
def relation (p : CompilerProviders.Prepared) (source target : MIR.TyId) : Except String Bool :=
  ConcreteCovariance.relation p.runtime source target

def compatible (p : CompilerProviders.Prepared) (debugAssertions : Bool)
    (source target : LocalLayout) : Except StepError Bool := do
  let related ← relation p source.ty target.ty |>.mapError StepError.unsupported
  if !related then return false
  if debugAssertions || source.ty != target.ty then
    unless source.layout == target.layout do
      throw (.invalidProgram "covariant MIR assignment has unequal layouts")
  pure true

def hook (p : CompilerProviders.Prepared) (debugAssertions : Bool)
    (source target : LocalLayout) : EStateM StepError S Bool :=
  match compatible p debugAssertions source target with
  | .ok value => pure value
  | .error error => throw error
end Miri.Input.CompilerCovariance
