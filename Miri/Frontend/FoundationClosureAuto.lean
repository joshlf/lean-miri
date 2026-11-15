import Miri.Frontend.FoundationClosure

/-! Automatic candidates for ordinary closure environments containing only
function pointers. Pinned select/candidate_assembly.rs first excludes relevant
manual impls; select/mod.rs decomposes closure→tupled upvars→tuple fields, while
FnPtr has no constituents (its input/output types are not captures). This module
requires the complete finite manual-header inventory, not a type-name default. -/
namespace Miri.Frontend.Foundation
open Lean

private def rawIdentity (source : Json) : Except String (Nat × Nat) := do
  let crateId ← source.getObjValAs? Nat "crate_index"
  let index ← source.getObjValAs? Nat "index"
  unless crateId < 2^32 && index < 2^32 do throw "auto impl raw definition out of bounds"
  return (crateId,index)

private def autoDeclaration (document : Document) (traitDefinition : Nat) : Except String Json := do
  let material ← document.source.getObjVal? "closure_auto_source"
  let declarations ← material.getObjValAs? (Array Json) "declarations"
  let records ← declarations.filterM fun declaration => do
    return (← declaration.getObjValAs? Nat "definition") == traitDefinition
  unless records.size == 1 do throw "auto trait declaration missing or ambiguous"
  let some declaration := records[0]? | throw "auto trait declaration absent"
  let some definition := document.definitions[traitDefinition]? | throw "auto trait definition absent"
  unless (← definition.getObjValAs? String "kind") == "Trait" &&
      (← definition.getObjValAs? Bool "trait_is_auto") &&
      (← declaration.getObjValAs? Bool "is_auto") && (← declaration.getObjValAs? Bool "has_self") &&
      (← declaration.getObjValAs? Nat "associated_item_count") == 0 do
    throw "unsupported auto trait declaration"
  let safety ← declaration.getObjValAs? String "safety"
  unless safety == "Safe" || safety == "Unsafe" do throw "unknown auto trait safety"
  let parameters ← declaration.getObjValAs? (Array Json) "parameters"
  unless parameters.size == 1 do throw "generic auto trait declaration unsupported"
  let some self := parameters[0]? | throw "auto trait Self absent"
  unless (← self.getObjValAs? Nat "index") == 0 && (← self.getObjValAs? String "kind") == "type" &&
      !(← self.getObjValAs? Bool "has_default") do throw "noncanonical auto trait Self"
  for clause in (← declaration.getObjValAs? (Array Json) "clauses") do
    unless (← clause.getObjValAs? String "kind") == "meta_sized_self" do
      throw "unresolved auto trait declaration clause"
    let id ← clause.getObjValAs? Nat "definition"
    let some row := document.definitions[id]? | throw "auto declaration MetaSized source absent"
    unless (← row.getObjValAs? String "kind") == "Trait" do throw "auto MetaSized definition category mismatch"
  return declaration

/-- Rigid source constructors exclude manual impls without normalizing their
arguments. Unknown, alias or parameter roots have no exclusion certificate. -/
private def excludeManual (declaration : Json) (goal : String) (tupleArity : Nat)
    (closureIdentity : Nat × Nat) : Except String Unit := do
  unless (← declaration.getObjValAs? Bool "complete_manual_headers") do
    throw "incomplete auto trait manual impl source"
  let headers ← declaration.getObjValAs? (Array Json) "manual_impl_headers"
  unless headers.size ≤ 4096 do throw "auto manual header source budget exceeded"
  let mut seen : Array (Nat × Nat) := #[]
  let mut candidates : Array String := #[]
  for header in headers do
    let identity ← rawIdentity (← header.getObjVal? "definition")
    unless !(seen.contains identity) do throw "duplicate auto manual impl source identity"
    seen := seen.push identity
    let polarity ← header.getObjValAs? String "polarity"
    unless polarity == "Positive" || polarity == "Negative" do throw "unknown auto impl polarity"
    let constructor ← header.getObjVal? "self_constructor"
    let kind ← constructor.getObjValAs? String "kind"
    let relevant ← match kind with
      | "closure" =>
        let identity ← rawIdentity (← constructor.getObjVal? "definition")
        pure (goal == "closure" && identity == closureIdentity)
      | "tuple" =>
        let arity ← constructor.getObjValAs? Nat "arity"
        pure (goal == "tuple" && arity == tupleArity)
      | "fn_pointer" => pure (goal == "fn_pointer")
      | "adt" | "fn_def" | "coroutine_closure" =>
        let _ ← rawIdentity (← constructor.getObjVal? "definition")
        pure false
      | "raw_pointer" | "reference" | "array" | "slice" | "str" | "bool" | "char" |
          "int" | "uint" | "float" | "never" => pure false
      | _ => throw "unknown auto impl self constructor cannot be excluded"
    if relevant then candidates := candidates.push polarity
  unless candidates.size ≤ 1 do throw "ambiguous auto trait manual impl candidates"
  if candidates.contains "Negative" then throw "negative auto trait manual impl candidate"
  unless candidates.isEmpty do throw "positive manual auto impl requires unsupported selection"

/-- Derive one requested auto bound from a selected finite closure/capture
source. Only a tuple of FnPtr fields is supported. All fields are checked, and
unknown captures/impls/clauses fail closed. Parent obligations and closure trait
shims remain separate; this does not establish whole-program safety. -/
def checkClosureCaptureAuto (document : Document) (closureDefinition : Nat)
    (parentArguments : Array ItemArgument) (traitDefinition : Nat) : Except String Unit := do
  let closure ← selectClosureTemplate document closureDefinition parentArguments
  let declaration ← autoDeclaration document traitDefinition
  let some definition := document.definitions[closureDefinition]? | throw "closure raw identity absent"
  let identity ← rawIdentity definition
  let .tuple captures := closure.tupledUpvars | throw "closure upvars are not tuple source"
  unless captures.size ≤ 2048 do throw "closure auto capture source budget exceeded"
  excludeManual declaration "closure" 0 identity
  excludeManual declaration "tuple" captures.size identity
  for capture in captures do
    let .functionPointer _ _ safety abi variadic := capture
      | throw "unknown closure capture auto trait constituents"
    unless (safety == "safe" || safety == "unsafe") && abi == "rust" && !variadic do
      throw "unsupported closure capture function pointer signature"
    -- A function-pointer type has no unsafe fields or auto constituents. Its
    -- return type may itself be non-Sync/non-RefUnwindSafe without affecting it.
    excludeManual declaration "fn_pointer" 0 identity

/-- Check every explicitly requested target auto bound. This is only the auto
component of closure unsizing; Fn impl/shim and projection joins are separate. -/
def checkClosureTargetAutos (document : Document) (closureDefinition : Nat)
    (parentArguments : Array ItemArgument) (autoTraits : Array Nat) : Except String Unit := do
  for traitDefinition in autoTraits do
    checkClosureCaptureAuto document closureDefinition parentArguments traitDefinition

end Miri.Frontend.Foundation
