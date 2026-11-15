import Miri.Input.CompilerProviders

/-! Distinct types require the exact rustc covariance relation. Successful
relations also require equal source layouts. -/
namespace Miri.Input.CompilerCovariance
open Lean Miri.ABI Miri.Interpreter
def relationWithIndex (index : CompilerQueryIndices.Covariance)
    (source target : MIR.TyId) : Except String Bool := do
  if source == target then return true
  let mut found := none
  for entry in CompilerQueryIndices.covarianceRows index source target do
    if let some old := found then
      unless old == entry.value do
        throw s!"conflicting compiler covariance query results (source={source}, target={target})"
    found := some entry.value
  let some value := found |
    throw s!"missing exact rustc covariance relation query (source={source}, target={target})"
  pure value

def relation (p : CompilerProviders.Prepared) (source target : MIR.TyId) : Except String Bool := do
  if source == target then return true
  let some _sourceNode := p.program.input.types[source]? |
    throw s!"covariance source type is absent from material prefix: {source}"
  let some _targetNode := p.program.input.types[target]? |
    throw s!"covariance target type is absent from material prefix: {target}"
  relationWithIndex p.covarianceIndex source target

def compatible (p : CompilerProviders.Prepared) (debugAssertions : Bool)
    (source target : LocalLayout) : Except StepError Bool := do
  let related ← relation p source.ty target.ty |>.mapError StepError.unsupported
  if !related then return false
  if debugAssertions || source.ty != target.ty then
    unless source.layout == target.layout do
      throw (.invalidProgram "covariant MIR assignment has unequal layouts")
  pure true

def hook (p : CompilerProviders.Prepared) (access : RuntimeArrayQueries.Access S)
    (debugAssertions : Bool) (source target : LocalLayout) : EStateM StepError S Bool := do
  let related ← match relation p source.ty target.ty with
    | .ok value => pure value | .error error => throw (.unsupported error)
  if !related then return false
  if debugAssertions || source.ty != target.ty then
    unless source.layout == target.layout do
      throw (.invalidProgram "covariant MIR assignment has unequal layouts")
  pure true
end Miri.Input.CompilerCovariance
