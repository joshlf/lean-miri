import Miri.Frontend.FoundationLinkSections
import Miri.Frontend.FoundationTypeRegistry
import Miri.Frontend.FoundationGenericEnvironment
import Miri.Interpreter.GlobalConstructors

/-! Demand-selected static initializer syntax. Function reification remains a
symbolic request: source MIR provides no original compiler function/static
AllocId. No fabricated graph identity, function address or empty global catalog
is produced. Constructor-name filtering precedes all initializer demands. -/
namespace Miri.Frontend.Foundation
open Lean

structure SourceCInitializer where
  linkSection : SourceLinkSection
  staticDefinition : Nat
  pointerType : Nat
  functionDefinition : Nat
  inputs : Array ConcreteType
  pointerSizeBytes : Nat
  pointerAlignBytes : Nat
  /-- ReifyFnPointer produces an offset-zero pointer, not an integer address. -/
  pointerOffsetBytes : Nat := 0

/-- Retain exactly the requested section domain. In particular, `.init_array.N`
is not an ELF constructor section in the pinned Miri source. -/
def sourceLinkSectionsMatching (document : Json) (includeName : String → Bool) :
    Except String (Array SourceLinkSection) := do
  return (← sourceLinkSections document).filter (fun entry => includeName entry.name)

def sourceConstructorSections (document : Json) (format : Interpreter.ConstructorBinaryFormat) :
    Except String (Array SourceLinkSection) :=
  sourceLinkSectionsMatching document (Interpreter.constructorSectionMatches format)

private def sourceType (document : Document) (id : Nat) : Except String ConcreteType := do
  instantiate #[] #[] (← typeExpr document id)

private def cSignature (document : Document) (signature : Json) : Except String (Array ConcreteType) := do
  unless (← signature.getObjValAs? (Array Json) "bound_variables").isEmpty &&
      (← signature.getObjValAs? String "safety") == "safe" &&
      !(← signature.getObjValAs? Bool "c_variadic") do throw "unsupported initializer C signature binder/safety/variadic"
  let abi ← signature.getObjVal? "abi"
  unless (← abi.getObjValAs? String "kind") == "c" && (← abi.getObjValAs? (Option Bool) "unwind") == some false do
    throw "initializer requires exact non-unwind C ABI source"
  let output ← sourceType document (← signature.getObjValAs? Nat "output")
  unless sameConcrete 1024 output (.tuple #[]) do throw "initializer C return type is not unit"
  let inputs ← (← signature.getObjValAs? (Array Nat) "inputs").mapM (sourceType document)
  -- This component parses scalar C declarations, not the general FnAbi query.
  for input in inputs do
    match input with
    | .primitive "int" "i32" => pure ()
    | .pointer "raw_pointer_const" (.pointer "raw_pointer_const" (.primitive "uint" "u8")) => pure ()
    | _ => throw "initializer C input type unsupported"
  return inputs

structure SourceCStaticSignature where
  staticDefinition : Nat
  pointerType : Nat
  inputs : Array ConcreteType
  pointerSizeBytes : Nat
  pointerAlignBytes : Nat

/-- Read the actual static type even if external initializer MIR is unavailable.
This establishes a declaration/storage plan, not a global allocation or FnAbi. -/
def sourceCStaticSignature (document : Document) (linkSection : SourceLinkSection) : Except String SourceCStaticSignature := do
  let source ← linkSection.source.getObjVal? "initializer_source"
  unless !(← source.getObjValAs? Bool "static_mutable") && !(← source.getObjValAs? Bool "thread_local") do
    throw "mutable or thread-local initializer source unsupported"
  let staticDefinition ← source.getObjValAs? Nat "static_definition"
  let some staticRow := document.definitions[staticDefinition]? | throw "initializer static definition absent"
  unless (← staticRow.getObjValAs? Nat "crate_index") == linkSection.crateIndex &&
      (← staticRow.getObjValAs? Nat "index") == linkSection.definitionIndex &&
      (← staticRow.getObjValAs? String "kind").startsWith "Static" do throw "initializer static identity mismatch"
  let pointerType ← source.getObjValAs? Nat "static_type"
  let some pointerRow := document.types[pointerType]? | throw "initializer pointer type absent"
  let shape ← pointerRow.getObjVal? "shape"
  unless (← shape.getObjValAs? String "kind") == "function_pointer" do throw "initializer static is not function pointer"
  let inputs ← cSignature document (← shape.getObjVal? "signature")
  let target ← runtimeTargetOfTarget document.target
  let spec ← (target.pointerSpecIn target.instructionAddressSpace).mapError toString
  return ⟨staticDefinition,pointerType,inputs,spec.pointerSize.bytes.toNat,
    (← spec.pointerAlign.bytes.mapError toString).toNat⟩

/-- Compute the source function-pointer initializer request and its storage
geometry. CTFE execution, FnPtr instance/shim resolution and original allocation
identity remain separate demands; a successful plan is not an initialized graph. -/
def sourceCInitializer (document : Document) (linkSection : SourceLinkSection) : Except String SourceCInitializer := do
  let source ← linkSection.source.getObjVal? "initializer_source"
  unless (← source.getObjValAs? String "status") == "source" do throw "selected static initializer source unsupported/unavailable"
  unless (← source.getObjValAs? String "allocation_identity_status") == "not_observed_from_initializer_mir" do
    throw "unrecognized static allocation identity evidence"
  let declaration ← sourceCStaticSignature document linkSection
  let staticDefinition := declaration.staticDefinition
  let pointerType := declaration.pointerType
  let inputs := declaration.inputs
  let expression ← source.getObjVal? "expression"
  unless (← expression.getObjValAs? String "kind") == "reify_fn_pointer" &&
      (← expression.getObjValAs? Nat "target_type") == pointerType &&
      (← expression.getObjValAs? String "safety") == "safe" do throw "unsupported static initializer expression"
  unless #["implicit","as_cast"].contains (← expression.getObjValAs? String "origin") do throw "unknown initializer coercion origin"
  let functionDefinition ← expression.getObjValAs? Nat "function_definition"
  let header ← source.getObjVal? "function_header"
  unless (← header.getObjValAs? Nat "definition") == functionDefinition do throw "initializer function header identity mismatch"
  let some function := document.definitions[functionDefinition]? | throw "initializer function definition absent"
  unless (← function.getObjValAs? String "kind") == "fn" do throw "initializer target is not ordinary function source"
  let environment ← flattenEnvironment document (← header.getObjVal? "environment")
  unless (← environment.getObjValAs? (Array Json) "parameters").isEmpty &&
      (← environment.getObjValAs? (Array Json) "clauses").isEmpty do throw "generic initializer function unsupported"
  let attributes ← header.getObjVal? "function_attributes"
  unless !(← attributes.getObjValAs? Bool "track_caller") && !(← attributes.getObjValAs? Bool "is_foreign") &&
      !(← attributes.getObjValAs? Bool "is_drop_glue") do throw "initializer function reification prerequisites unsupported"
  let declared ← cSignature document (← header.getObjVal? "signature")
  unless declared.size == inputs.size && (declared.zip inputs).all (fun (a,b) => sameConcrete 1024 a b) do
    throw "initializer function/static C signature mismatch"
  let checkOperand (operand : Json) : Except String Unit := do
    unless (← operand.getObjValAs? String "kind") == "constant" &&
        (← (← operand.getObjVal? "value").getObjValAs? String "kind") == "zero_sized" do
      throw "initializer requires genuine zero-sized FnDef source"
    let id ← operand.getObjValAs? Nat "type"
    let some row := document.types[id]? | throw "initializer FnDef type absent"
    let shape ← row.getObjVal? "shape"
    unless (← shape.getObjValAs? String "kind") == "function_definition" &&
        (← shape.getObjValAs? Nat "definition") == functionDefinition &&
        (← shape.getObjValAs? (Array Json) "arguments").isEmpty do throw "initializer FnDef source identity/arguments mismatch"
  checkOperand (← expression.getObjVal? "operand")
  for operand in (← source.getObjValAs? (Array Json) "required_consts") do checkOperand operand
  return ⟨linkSection,staticDefinition,pointerType,functionDefinition,inputs,
    declaration.pointerSizeBytes,declaration.pointerAlignBytes,0⟩

/-- Only an empty answer for the actual predicate can succeed. A request matching
ARGV_INIT_ARRAY (or any other static) fails until authentic global/function
allocation identities and initializer execution are supplied. Call this as a
query guard, never turn its result into an all-section empty catalog. -/
def guardedEmptySourceLinkLookup {α : Type} (document : Document) (includeName : String → Bool) :
    Except String (Array α) := do
  let selected ← sourceLinkSectionsMatching document.source includeName
  for entry in selected do
    let _ ← sourceCInitializer document entry
  unless selected.isEmpty do throw "link initializer requires original static/function allocation identity and reification witness"
  return #[]

end Miri.Frontend.Foundation
