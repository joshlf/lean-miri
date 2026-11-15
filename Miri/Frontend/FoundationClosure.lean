import Miri.Frontend.FoundationInstance
import Miri.Frontend.FoundationGenericEnvironment

/-! Finite ordinary closure source selection, not closure trait/shim resolution
or execution. Pinned generic_args.rs::split_closure_args retains inherited args
followed by kind, RustCall signature and tupled upvars. sty.rs encodes Fn/FnMut/
FnOnce by i8/i16/i32 respectively. Parent predicates remain explicit obligations;
selecting a template does not establish them or produce an executable Instance. -/
namespace Miri.Frontend.Foundation
open Lean

inductive SourceClosureKind where
  | fn | fnMut | fnOnce
  deriving Repr, DecidableEq

structure SourceClosureSignature where
  inputs : Array ConcreteType
  output : ConcreteType
  safety : String
  /-- Exact retained source ExternAbi payload, including rust_call. -/
  abi : Json
  cVariadic : Bool

structure SelectedClosureTemplate where
  definition : Nat
  parentDefinition : Nat
  parentArguments : Array ItemArgument
  fullArguments : Array ItemArgument
  kind : SourceClosureKind
  signature : SourceClosureSignature
  tupledUpvars : ConcreteType
  spreadArgument : Option Nat
  parentEnvironment : Json
  body : Json

/-- Demand one generic closure source template by definition and inherited type
arguments. This partial reader accepts only a single non-inherited parent
parameter environment and three synthetic type parameters. It preserves the
RustCall signature exactly, without passing it through Rust-ABI-only layout or
instance APIs. Local types and instructions remain source references for later
closure-aware lowering; no trait, allocation or ABI answer is fabricated. -/
def selectClosureTemplate (document : Document) (definition : Nat)
    (parentArguments : Array ItemArgument) : Except String SelectedClosureTemplate := do
  let some row := document.definitions[definition]? | throw "closure definition absent"
  unless (← row.getObjValAs? String "kind") == "closure" do throw "source definition is not closure"
  let templates ← document.source.getObjValAs? (Array Json) "closure_templates"
  let candidates ← templates.filterM fun body => return (← body.getObjValAs? Nat "definition") == definition
  unless candidates.size == 1 do throw "missing or duplicate closure template"
  let some body := candidates[0]? | throw "closure template absent"
  validateSourceMetadata body
  let parentDefinition ← body.getObjValAs? Nat "parent_definition"
  let some parent := document.definitions[parentDefinition]? | throw "closure parent definition absent"
  unless (← parent.getObjValAs? String "kind") == "fn" do throw "closure parent kind unsupported"
  let parentCount ← body.getObjValAs? Nat "parent_count"
  unless parentCount == parentArguments.size do throw "closure inherited argument count mismatch"
  let environment ← body.getObjVal? "parent_environment"
  let flat ← flattenEnvironment document environment
  let parameters ← flat.getObjValAs? (Array Json) "parameters"
  let _ ← flat.getObjValAs? (Array Json) "clauses"
  unless parameters.size == parentCount do throw "closure parent parameter count mismatch"
  let mut types : Array (Option ConcreteType) := #[]
  for h : i in [:parameters.size] do
    unless (← parameters[i].getObjValAs? Nat "index") == i &&
        (← parameters[i].getObjValAs? String "kind") == "type" do
      throw "closure parent generic parameter unsupported"
    let some (.type ty) := parentArguments[i]? | throw "closure inherited type argument absent"
    types := types.push (some ty)
  let constants := Array.replicate parentCount (none : Option Nat)
  let own ← body.getObjValAs? (Array Json) "own_parameters"
  unless own.size == 3 && (← body.getObjValAs? (Array Json) "own_clauses").isEmpty do
    throw "closure synthetic parameter/predicate shape unsupported"
  for h : i in [:own.size] do
    unless (← own[i].getObjValAs? Nat "index") == parentCount + i &&
        (← own[i].getObjValAs? String "kind") == "type" do
      throw "closure synthetic generic index/kind mismatch"
  let sourceType ← body.getObjValAs? Nat "source_type"
  let some source := document.types[sourceType]? | throw "closure source type absent"
  let shape ← source.getObjVal? "shape"
  unless (← shape.getObjValAs? String "kind") == "closure" &&
      (← shape.getObjValAs? Nat "definition") == definition &&
      (← shape.getObjValAs? Nat "parent_definition") == parentDefinition &&
      (← shape.getObjValAs? Nat "parent_count") == parentCount do
    throw "closure source type identity mismatch"
  let arguments ← shape.getObjValAs? (Array Json) "arguments"
  unless arguments.size == parentCount + 3 do throw "closure complete argument count mismatch"
  for h : i in [:parentCount] do
    let some sourceArgument := arguments[i]? | throw "closure inherited source argument absent"
    unless (← sourceArgument.getObjValAs? String "kind") == "type" do throw "closure source argument kind unsupported"
    let typeId ← sourceArgument.getObjValAs? Nat "type"
    let .parameter index ← typeExpr document typeId | throw "closure source parent argument is not parameter"
    unless index == i do throw "closure source inherited parameter order mismatch"
  let kindType ← body.getObjValAs? Nat "kind_type"
  let signatureType ← body.getObjValAs? Nat "signature_type"
  let upvarType ← body.getObjValAs? Nat "tupled_upvars_type"
  for (expected, ordinal) in #[kindType, signatureType, upvarType].toList.zipIdx do
    let some argument := arguments[parentCount + ordinal]? | throw "closure synthetic source argument absent"
    unless (← argument.getObjValAs? String "kind") == "type" &&
        (← argument.getObjValAs? Nat "type") == expected do throw "closure synthetic source argument identity mismatch"
  for (name, expected) in #[("kind_type", kindType), ("signature_type", signatureType), ("tupled_upvars_type", upvarType)] do
    unless (← shape.getObjValAs? Nat name) == expected do throw "closure shape/template synthetic identity mismatch"
  let kindConcrete ← instantiate types constants (← typeExpr document kindType)
  let kind ← match kindConcrete with
    | .primitive "int" "i8" => pure SourceClosureKind.fn
    | .primitive "int" "i16" => pure .fnMut
    | .primitive "int" "i32" => pure .fnOnce
    | _ => throw "closure kind encoding unsupported"
  let some sigRow := document.types[signatureType]? | throw "closure signature type absent"
  let sigShape ← sigRow.getObjVal? "shape"
  unless (← sigShape.getObjValAs? String "kind") == "function_pointer" do throw "closure signature is not FnPtr"
  let sig ← sigShape.getObjVal? "signature"
  unless (← sig.getObjValAs? (Array Json) "bound_variables").isEmpty do throw "closure signature binders unsupported"
  let abi ← sig.getObjVal? "abi"
  unless (← abi.getObjValAs? String "kind") == "rust_call" && (← abi.getObjVal? "unwind") == Json.null do
    throw "closure signature must preserve RustCall ABI"
  let safety ← sig.getObjValAs? String "safety"
  unless safety == "safe" || safety == "unsafe" do throw "closure signature safety unsupported"
  let cVariadic ← sig.getObjValAs? Bool "c_variadic"
  unless !cVariadic do throw "variadic closure signature unsupported"
  let mut inputs := #[]
  for id in (← sig.getObjValAs? (Array Nat) "inputs") do
    inputs := inputs.push (← instantiate types constants (← typeExpr document id))
  let output ← instantiate types constants (← typeExpr document (← sig.getObjValAs? Nat "output"))
  let upvars ← instantiate types constants (← typeExpr document upvarType)
  let .tuple _ := upvars | throw "closure upvars source is not tuple"
  let _ ← body.getObjVal? "spread_argument"
  let spreadArgument ← body.getObjValAs? (Option Nat) "spread_argument"
  let locals ← body.getObjValAs? (Array Nat) "locals"
  let argumentCount ← body.getObjValAs? Nat "argument_count"
  unless argumentCount < locals.size do throw "closure return/argument local absent"
  if let some spread := spreadArgument then
    unless spread > 0 && spread <= argumentCount && spread < locals.size do throw "closure spread local out of bounds"
  unless (← body.getObjValAs? Nat "promoted_count") == 0 do throw "closure promoted body selection unsupported"
  let _ ← body.getObjValAs? (Array Json) "required_consts"
  let complete := parentArguments ++ #[.type kindConcrete,
    .type (.functionPointer inputs output safety "rust_call" cVariadic), .type upvars]
  return ⟨definition, parentDefinition, parentArguments, complete, kind,
    ⟨inputs, output, safety, abi, cVariadic⟩, upvars, spreadArgument, environment, body⟩

end Miri.Frontend.Foundation
