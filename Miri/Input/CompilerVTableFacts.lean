import Miri.Input.CompilerFactAdapters

/-! Source interpret/traits.rs::check_vtable_for_type (67-103): complete-binder
predicate identities, real compiler stable_cmp ranks, and exact normalized
identity after late-bound-region erasure. Dyn types and exported symbolic
vtables own ordered lists of canonical predicate IDs. No Debug string is a key. -/
namespace Miri.Input.CompilerVTableFacts
open Lean Miri.Memory Miri.Interpreter
abbrev Result := Except String
private def evidence (prepared : CompilerFactAdapters.Prepared) (id : Nat) : Result CompilerPredicateEvidence := do
  let some entry := prepared.context.program.input.compilerPredicates[id]?
    | throw "predicate normalization identity is absent"
  pure entry

def predicates (prepared : CompilerFactAdapters.Prepared) (values : PredicateList) : Result (Array VTablePredicate) := do
  values.mapM fun id => do
    let entry ← evidence prepared id
    pure ⟨id,entry.stableKey,entry.autoTrait⟩

def normalizePredicate (prepared : CompilerFactAdapters.Prepared) (predicate : VTablePredicate) : Result Nat := do
  let entry ← evidence prepared predicate.id
  let some id := entry.normalizedId | throw "compiler predicate normalization has no result identity"
  pure id

private def lift (result : Result A) : EStateM StepError S A :=
  match result with | .ok value => pure value | .error error => throw (.invalidProgram error)

def hooks (prepared : CompilerFactAdapters.Prepared) (machine : VTableHooks P S C Fn Abi) : VTableHooks P S C Fn Abi :=
  { machine with
    isDynamic := fun _ ty => lift (CompilerFacts.boolean prepared.context ty "is_dynamic")
    layoutOf := fun _ ty => lift (CompilerFacts.layoutOf prepared.context ty)
    predicates := fun _ token => lift (predicates prepared token)
    normalizePredicate := fun _ predicate => lift (normalizePredicate prepared predicate) }
end Miri.Input.CompilerVTableFacts
