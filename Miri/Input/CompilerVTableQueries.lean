import Miri.Input.CompilerVTableFacts

namespace Miri.Input.CompilerVTableQueries
open Lean Miri.Interpreter

structure Prepared where
  facts : CompilerFactAdapters.Prepared
  traceQueries : Bool := false

def prepare (facts : CompilerFactAdapters.Prepared) : Except String Prepared :=
  pure ⟨facts,false⟩

def eraseAndAnonymize (prepared : Prepared) (ty : TypeId) (inputPredicates : PredicateList) :
    Except String (TypeId × PredicateList) := do
  let document := prepared.facts.context.program.input
  let source ← prepared.facts.context.runtime.node ty |>.mapError toString
  let output := source.sourceLayout.normalizedType
  let predicates ← inputPredicates.mapM fun id => do
    let some source := document.compilerPredicates[id]? | throw "predicate erasure material is absent"
    pure source.erasedId
  if prepared.traceQueries then
    dbg_trace s!"vtable_query input_type={ty} input_predicates={reprStr inputPredicates} output_type={output} output_predicates={reprStr predicates}"
  pure (output,predicates)

theorem eraseAndAnonymize_trace_identity (prepared : Prepared) (ty : TypeId) (predicates : PredicateList) :
    eraseAndAnonymize {prepared with traceQueries := true} ty predicates =
      eraseAndAnonymize {prepared with traceQueries := false} ty predicates := by
  rfl

def ensureMonomorphicType (prepared : Prepared) (ty : TypeId) : Except String Unit := do
  unless (← CompilerFacts.boolean prepared.facts.context ty "is_monomorphic_enough") do
    throw "source TooGeneric: vtable concrete type has parameters"

def ensureMonomorphicDyn (prepared : Prepared) (predicates : PredicateList) : Except String Unit := do
  let document := prepared.facts.context.program.input
  for id in predicates do
    let some predicate := document.predicates[id]? | throw "vtable predicate is absent"
    for argument in predicate.genericArgs do
      match argument with
      | .Type id => ensureMonomorphicType prepared id
      | .Lifetime (.EarlyParameter ..) => throw "source TooGeneric: vtable lifetime parameter"
      | .Const id =>
        let some constant := document.typeConstants[id]? | throw "vtable constant argument is absent"
        if let .Param .. := constant then throw "source TooGeneric: vtable constant parameter"
      | _ => pure ()

private def lift (result : Except String A) : EStateM StepError S A :=
  match result with
  | .ok value => pure value
  | .error reason => throw (.unsupported s!"compiler vtable query: {reason}")

def hooks (prepared : Prepared) (base : VTableHooks P S C Fn Abi) : VTableHooks P S C Fn Abi :=
  { base with
    eraseAndAnonymize := fun _ ty dyn => lift (eraseAndAnonymize prepared ty dyn)
    ensureMonomorphicType := fun _ ty => lift (ensureMonomorphicType prepared ty)
    ensureMonomorphicDyn := fun _ dyn => lift (ensureMonomorphicDyn prepared dyn) }

end Miri.Input.CompilerVTableQueries
