import Miri.Frontend.FoundationObligations

/-! Demand-time substitution for explicitly selected item MIR templates.
Pinned `rustc_middle/src/ty/instance.rs` distinguishes `Instance::new_raw`
(item identity plus arguments) from `try_resolve` (trait/shim dispatch). This
module implements the former boundary only. Selecting a template is not evidence
that a trait method call resolves to it. All material is local to one document. -/

namespace Miri.Frontend.Foundation
open Lean

inductive ItemArgument where
  | type (value : ConcreteType)
  | constant (value : Nat)
  deriving Repr

/-- A substituted template, not yet an executable fixed-interpreter body.
The original MIR is retained so later lowering must account for every source
instruction and its generic operands rather than silently discarding them. -/
structure ItemTemplate where
  definition : Nat
  arguments : Array ItemArgument
  localTypes : Array ConcreteType
  argumentCount : Nat
  source : Json

/-- Construct an explicit item template on demand, checking the complete
supported generic environment. No substitutions or instances are enumerated.
Lifetimes, inherited environments and arbitrary trait resolution are unsupported.
The exported parameter indices must be the canonical unified argument order. -/
def instantiateItem (d : Document) (definition : Nat)
    (arguments : Array ItemArgument) : Except String ItemTemplate := do
  let some _ := d.definitions[definition]? | throw "missing item definition"
  let candidates ← d.bodies.filterM fun b =>
    return (← b.getObjValAs? Nat "definition") == definition
  unless candidates.size == 1 do throw "missing or duplicate item template"
  let some body := candidates[0]? | throw "missing item template"
  let environment ← body.getObjVal? "environment"
  let parameters ← environment.getObjValAs? (Array Json) "parameters"
  unless parameters.size == arguments.size do throw "item generic argument count mismatch"
  let mut types : Array (Option ConcreteType) := #[]
  let mut constants : Array (Option Nat) := #[]
  for h : i in [:parameters.size] do
    unless (← parameters[i].getObjValAs? Nat "index") == i do
      throw "noncanonical item generic parameter index"
    let some argument := arguments[i]? | throw "missing item generic argument"
    match ← parameters[i].getObjValAs? String "kind", argument with
    | "type", .type ty =>
      types := types.push (some ty)
      constants := constants.push none
    | "const", .constant n =>
      types := types.push none
      constants := constants.push (some n)
    | _, _ => throw "unsupported or wrong-kind item generic argument"
  checkEnvironment d types constants environment
  for parameter in parameters do
    if (← parameter.getObjValAs? String "kind") == "const" then
      let index ← parameter.getObjValAs? Nat "index"
      let ty ← instantiate types constants
        (← typeExpr d (← parameter.getObjValAs? Nat "type"))
      let .primitive "uint" "usize" := ty
        | throw "unsupported item const parameter type"
      let some value := constants[index]?.bind id | throw "missing item const argument"
      unless value < 2 ^ d.target.pointerSizeBits do throw "item const argument exceeds usize"
  -- Required constants are evaluated at frame entry by pinned stack.rs even
  -- when their instructions are unreachable. No const evaluator exists here.
  unless (← body.getObjValAs? (Array Json) "required_consts").isEmpty do
    throw "item template has unresolved required constants"
  let mut localTypes := #[]
  for entry in (← body.getObjValAs? (Array Json) "locals") do
    localTypes := localTypes.push (← instantiate types constants (← typeExpr d (← entry.getNat?)))
  let argumentCount ← body.getObjValAs? Nat "argument_count"
  unless argumentCount < localTypes.size do throw "missing item return or argument locals"
  unless !(← body.getObjValAs? (Array Json) "blocks").isEmpty do
    throw "item template has no entry block"
  return { definition, arguments, localTypes, argumentCount, source := body }

end Miri.Frontend.Foundation
