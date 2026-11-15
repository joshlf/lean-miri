import Miri.Frontend.FoundationPromotedEval
import Miri.Frontend.FoundationDirectCalls
import Miri.Frontend.FoundationSpanRegistry

/-! Exact fixed-MIR components for the supported symbolic promoted recipe.
The fragment has computed physical types/layouts and genuine compiler spans;
it has no fabricated parent InstanceId, function allocation or promoted-memory
identity, and is not an executable ImportDocument. -/
namespace Miri.Frontend.Foundation
open Lean

/-- Extra compiler operands share the body-local rustc Span identity namespace.
Append their exact rows; equal coordinates with distinct identities are retained. -/
def promotedSpanRegistry (body : Json) : Except String SpanRegistry := do
  let mut registry ← buildSpanRegistry body
  let metadata ← body.getObjVal? "source_metadata"
  for row in (← metadata.getObjValAs? (Array Json) "additional_spans") do
    let span ← sourceSpan row
    if let some previous := registry.compilerSpans[span.identity]? then
      unless previous == span do throw "promoted additional compiler span identity conflict"
    else
      unless span.identity == registry.compilerSpans.size do throw "promoted additional span identity gap"
      let file := (registry.files.findIdx? (· == span.file)).getD registry.files.size
      if file == registry.files.size then registry := { registry with files := registry.files.push span.file }
      let physical : Input.SourceSpanData := {
        isDummy := span.isDummy
        lo := span.lo
        hi := span.hi
        start := ⟨span.startLine, span.startColumn⟩
        «end» := ⟨span.endLine, span.endColumn⟩
        context := span.context
        file }
      registry := { registry with spans := registry.spans.push physical, compilerSpans := registry.compilerSpans.push span }
  return registry

private def exactSpan (registry : SpanRegistry) (key : Json) : Except String MIR.SpanRef := do
  let lo ← key.getObjValAs? Nat "lo"
  let hi ← key.getObjValAs? Nat "hi"
  let context ← key.getObjValAs? String "ctxt"
  let _ ← key.getObjVal? "parent_local_definition"
  let parent ← key.getObjValAs? (Option Nat) "parent_local_definition"
  let rows := registry.compilerSpans.filter fun row =>
    row.lo == lo && row.hi == hi && row.context == context && row.parentLocalDefinition == parent
  unless rows.size == 1 do throw "missing or ambiguous exact promoted operand span"
  let some span := rows[0]? | throw "promoted operand compiler span absent"
  let some _ := registry.spans[span.identity]? | throw "promoted operand physical span absent"
  return ⟨span.identity⟩

structure PromotedMIRFragment where
  recipe : SharedPromotedRecipe
  types : Array Input.TypeNode
  layouts : Array Input.Layout
  spans : SpanRegistry
  body : MIR.Body
  /-- Constant's real FnDef physical type, computed from its declaration. -/
  functionDefinitionType : Nat

/-- Interpret source into a symbolic recipe, then lower both actual instructions
into fixed MIR. Parent frame/instance identity and CTFE allocation interning are
left unresolved, so this component cannot masquerade as a runnable promoted
body. Reification and Shared Ref remain instructions, never evaluated addresses. -/
def lowerSharedPromotedMIR (document : Document) (owner index : Nat) : Except String PromotedMIRFragment := do
  let recipe ← evaluateSharedPromotedRecipe document owner index
  let registry ← promotedSpanRegistry recipe.source.source
  let physical := recipe.physical
  let (checkedPhysical, pointerType) ← physical.intern recipe.cellType
  unless checkedPhysical.types.size == physical.types.size do throw "promoted physical pool is not closed"
  let (checkedPhysical, referenceType) ← physical.intern recipe.outputType
  unless checkedPhysical.types.size == physical.types.size do throw "promoted reference physical pool is not closed"
  let headerRows ← document.source.getObjValAs? (Array Json) "source_function_signatures"
  let some header := headerRows.find? (fun h => (h.getObjValAs? Nat "definition").toOption == some recipe.function.key.definition)
    | throw "promoted original declaration absent at MIR lowering"
  let signature ← header.getObjVal? "signature"
  let safety ← signature.getObjValAs? String "safety"
  let boundVariables ← signatureBoundVariables document signature
  let runtime ← header.getObjVal? "runtime_source"
  let some name ← runtime.getObjValAs? (Option String) "item_name" | throw "promoted function item name absent"
  let some definition := document.definitions[recipe.function.key.definition]? | throw "promoted function definition absent"
  unless (← runtime.getObjValAs? Bool "is_local_root") &&
      (← definition.getObjValAs? String "path") == name do throw "promoted FnDef diagnostic path unsupported"
  let functionType := physical.types.size
  let layoutId := physical.layouts.size
  let inputs := recipe.function.abi.arguments.map (·.typeId)
  let output := recipe.function.abi.returnValue.typeId
  let sig : Input.FunctionSignature := ⟨inputs, output, if safety == "safe" then .Safe else .Unsafe, .Rust, false⟩
  let display ← concreteRuntimeDisplay recipe.cellType
  let node : Input.TypeNode := {
    id := functionType
    layoutId
    shape := .functionDefinition recipe.function.key.definition #[] sig boundVariables
    display := display ++ " {" ++ name ++ "}" }
  let target ← runtimeTargetOfTarget document.target
  let unit ← DirectCallPool.fnDefinitionLayout target
  let metadata ← recipe.source.source.getObjVal? "source_metadata"
  let sourceBlocks ← metadata.getObjValAs? (Array Json) "blocks"
  let some sourceBlock := sourceBlocks[0]? | throw "promoted source location block absent"
  let sourceStatements ← sourceBlock.getObjValAs? (Array Json) "statements"
  let sourceInfo (j : Json) : Except String MIR.SourceInfo := do
    let span ← sourceSpan (← j.getObjVal? "span")
    let some actual := registry.compilerSpans[span.identity]? | throw "promoted instruction span absent"
    unless actual == span do throw "promoted instruction compiler identity mismatch"
    return ⟨⟨span.identity⟩, ← j.getObjValAs? Nat "scope"⟩
  let blocks ← recipe.source.source.getObjValAs? (Array Json) "blocks"
  let some block := blocks[0]? | throw "promoted source body block absent"
  let statements ← block.getObjValAs? (Array Json) "statements"
  let some first := statements[0]? | throw "promoted reify source absent"
  let reify ← first.getObjVal? "value"
  let operand ← reify.getObjVal? "operand"
  unless (← operand.getObjValAs? (Option Nat) "user_type").isNone do throw "promoted operand user annotation unsupported"
  let span ← exactSpan registry (← operand.getObjVal? "source_span_key")
  let constant : MIR.ConstOperand := ⟨span, none, .Val .ZeroSized functionType⟩
  let reifySafety := if safety == "safe" then MIR.Safety.Safe else .Unsafe
  let coercion ← match ← reify.getObjValAs? String "source" with
    | "as_cast" => pure MIR.CoercionSource.AsCast
    | "implicit" => pure .Implicit
    | _ => throw "promoted coercion source unsupported"
  let some firstInfo := sourceStatements[0]? | throw "promoted reify source info absent"
  let some secondInfo := sourceStatements[1]? | throw "promoted borrow source info absent"
  let some second := statements[1]? | throw "promoted borrow source absent"
  let borrow ← second.getObjVal? "value"
  let region ← match ← borrow.getObjValAs? String "region" with
    | "erased" => pure MIR.Region.Erased
    | "static" => pure .Static
    | _ => throw "promoted borrow region unsupported"
  let statements : Array MIR.Statement := #[
    ⟨← sourceInfo firstInfo, .Assign ⟨recipe.cellLocal, #[]⟩
      (.Cast (.PointerCoercion (.ReifyFnPointer reifySafety) coercion) (.Constant constant) pointerType)⟩,
    ⟨← sourceInfo secondInfo, .Assign ⟨0, #[]⟩ (.Ref region .Shared ⟨recipe.cellLocal, #[]⟩)⟩]
  let phase ← (← metadata.getObjVal? "phase").getObjValAs? String "phase"
  let phase ← match phase with
    | "initial" => pure MIR.RuntimePhase.Initial
    | "post_cleanup" => pure .PostCleanup
    | "optimized" => pure .Optimized
    | _ => throw "promoted runtime phase unsupported"
  let body : MIR.Body := {
    phase := .Runtime phase
    argumentCount := 0
    spreadArgument := none
    locals := #[referenceType, pointerType]
    basicBlocks := #[⟨statements, ⟨← sourceInfo (← sourceBlock.getObjVal? "terminator"), .Return⟩, false⟩] }
  return ⟨recipe, physical.types.push node, physical.layouts.push unit, registry, body, functionType⟩

/-- Linking requires a canonical parent body/instance and CTFE allocation world.
The component exposes no numeric fallback for either missing identity domain. -/
def materializePromotedFragment (fragment : PromotedMIRFragment) :
    Except PromotedMaterializationError MIR.ConstValue := materializeSharedPromoted fragment.recipe

end Miri.Frontend.Foundation
