import Miri.Input.CompilerCastLeaves
import Miri.Input.ConcreteCastQueries
import Miri.Input.ConcreteVTable
import Miri.Input.CompilerVTableFacts

namespace Miri.Input.CompilerCastQueries
open Lean Miri.ABI Miri.MIR Miri.Memory Miri.Interpreter
abbrev Result := Except String
private def facts (p : CompilerProviders.Prepared) := p.lifecycle.calls.symbols.facts
private def layout (p : CompilerProviders.Prepared) (id : TyId) : Result LocalLayout :=
  ((facts p).context.runtime.lookup id).mapError toString

private def resolutionRecord (p : CompilerProviders.Prepared) (closure : Bool)
    (definition : DefId) (args : Array GenericArg) : Result SourceCastTarget := do
  for record in p.program.input.sourceCastTargets do
    let input ← match record with
      | .functionPointer input _ => if closure then continue else pure input
      | .closureOnce input _ => if closure then pure input else continue
    let inputKind ← CompilerFactAdapters.castTypeInfo (facts p) input
    let matchesInput := match inputKind with
      | .fnDefinition source actual => !closure && source == definition && actual == args
      | .closure source actual _ => closure && source == definition && actual == args
      | _ => false
    if matchesInput then return record
  throw "missing concrete source cast target"

def resolveFunction (p : CompilerProviders.Prepared) (definition : DefId)
    (args : Array GenericArg) : Result (Option CallInstance) := do
  let .functionPointer _ result ← resolutionRecord p false definition args
    | throw "function resolution query kind mismatch"
  pure result

def resolveClosureFnOnce (p : CompilerProviders.Prepared) (definition : DefId)
    (args : Array GenericArg) : Result CallInstance := do
  let .closureOnce _ result ← resolutionRecord p true definition args
    | throw "closure resolution query kind mismatch"
  pure result

def noBoundVars (p : CompilerProviders.Prepared) (args : Array GenericArg) : Result Bool :=
  ConcreteCastQueries.noBoundVars p.runtime args

def lockstepTails (p : CompilerProviders.Prepared) (source target : TyId) : Result (TyId × TyId) :=
  ConcreteCastQueries.lockstepTails p.runtime source target

def boxLayout (p : CompilerProviders.Prepared) (pointee : TyId) : Result LocalLayout := do
  layout p (← ConcreteCastQueries.boxType (facts p).context pointee)

def supertraitSlot (p : CompilerProviders.Prepared) (source target : TyId) : Result (Option Nat) :=
  ConcreteVTable.supertraitSlot p.runtime.source source target

def principal (p : CompilerProviders.Prepared) (predicates : PredicateList) : Result (Option Nat) := do
  let mut principal := none
  for id in predicates do
    let some predicate := p.runtime.source.predicates[id]? | throw "missing existential predicate"
    if predicate.kind == .trait then
      if principal.isSome then throw "existential predicate list has multiple principal traits"
      principal := some id
  return principal

def normalizePrincipal (p : CompilerProviders.Prepared) (predicates : PredicateList) : Result (Option Nat) := do
  let some id ← principal p predicates | return none
  some <$> ConcreteVTable.normalizedPredicate p.runtime.source id

def eraseSelfTraitRef (p : CompilerProviders.Prepared) (token : Nat) : Result Nat := do
  unless p.runtime.source.sourceVtables.objectTraits.any (·.principal == token) do
    throw "TraitVPtr references an absent normalized object trait declaration"
  return token
private def lift (query : Result A) : RvalueM S A :=
  match query with | .ok value => pure value | .error error => throw (.unsupported s!"cast compiler query: {error}")

def required (p : CompilerProviders.Prepared) : CompilerCastLeaves.Required S C where
  requireNoBoundVars := fun _ args => do
    unless ← lift (noBoundVars p args) do
      throw (.invalidProgram "source no_bound_vars assertion failed")
  resolveFunction := fun _ definition args => lift (resolveFunction p definition args)
  resolveClosureFnOnce := fun _ definition args => lift (resolveClosureFnOnce p definition args)
  lockstepTails := fun _ source target => lift (lockstepTails p source target)
  boxLayout := fun _ ty => lift (boxLayout p ty)
  principal := fun _ token => lift (principal p token)
  supertraitSlot := fun _ source target => lift (supertraitSlot p source target)
  eraseSelfTraitRef := fun _ token => lift (eraseSelfTraitRef p token)
  normalizePrincipal := fun _ token => lift (normalizePrincipal p token)

end Miri.Input.CompilerCastQueries
