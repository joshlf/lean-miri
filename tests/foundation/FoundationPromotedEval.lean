import Miri.Frontend.FoundationPromotedMIR
import Miri.Input.Decoder

set_option maxHeartbeats 2000000
open Lean Miri Miri.Frontend.Foundation

private def checked {α : Type} : Except String α → IO α
  | .ok value => pure value
  | .error e => throw (IO.userError e)
private def rejected {α : Type} : Except String α → IO Unit
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "promoted missing/conflicting source fact accepted")

private def replaceTable (document : Document) (table : Json) : Document :=
  {document with source := document.source.setObjVal! "promoted_tables" (toJson #[table])}

def main (paths : List String) : IO Unit := do
  let [sourcePath, referencePath] := paths | throw (IO.userError "expected promoted source and genuine schema12 exports")
  let document ← checked (Json.parse (← IO.FS.readFile sourcePath) >>= decode)
  let some owner := document.definitions.findIdx? (fun row =>
      (row.getObjValAs? String "path").toOption == some "concrete_vtable") | throw (IO.userError "promoted owner absent")
  let fragment ← checked (lowerSharedPromotedMIR document owner 0)
  let recipe := fragment.recipe
  let target ← checked (runtimeTargetOfTarget document.target)
  for node in fragment.types do
    let some layout := fragment.layouts[node.layoutId]? | throw (IO.userError "fixed physical layout row absent")
    let _ ← checked ((Input.RuntimeMetadata.layout target layout).mapError toString)
  unless recipe.cellLocal == 1 && recipe.function.key.ctfeSalt.val == 0 &&
      recipe.function.key.arguments.isEmpty && recipe.requirements.size == 2 do
    throw (IO.userError "promoted symbolic identity recipe mismatch")
  match materializePromotedFragment fragment with
  | .error (.unsupported (.functionAllocation key)) =>
    unless key.definition == recipe.function.key.definition && key.ctfeSalt.val == 0 do
      throw (IO.userError "wrong unresolved CTFE function identity")
  | _ => throw (IO.userError "promoted value materialized without function/promotion allocation identities")
  let reference ← checked (Input.decodeJson (← IO.FS.readFile referencePath))
  let some root := reference.document.bodyRoots[0]? | throw (IO.userError "genuine reference root absent")
  let some promoted := root.promotedBodies[0]? | throw (IO.userError "genuine reference promoted absent")
  let some bodyId := promoted.bodyId | throw (IO.userError "genuine reference promoted body ID absent")
  let some body := reference.document.bodies[bodyId]? | throw (IO.userError "genuine reference promoted body absent")
  unless fragment.body.phase == body.mir.phase && fragment.body.argumentCount == body.mir.argumentCount &&
      fragment.body.spreadArgument == body.mir.spreadArgument && body.requiredConsts.isEmpty do
    throw (IO.userError "fixed MIR promoted header differs from genuine compiler body")
  let some sourceBlock := fragment.body.basicBlocks[0]? | throw (IO.userError "source promoted block absent")
  let some expectedBlock := body.mir.basicBlocks[0]? | throw (IO.userError "reference promoted block absent")
  unless sourceBlock.statements.size == 2 && expectedBlock.statements.size == 2 &&
      sourceBlock.terminator.kind == expectedBlock.terminator.kind do throw (IO.userError "promoted MIR spine mismatch")
  let some sourceCast := sourceBlock.statements[0]? | throw (IO.userError "source cast absent")
  let some expectedCast := expectedBlock.statements[0]? | throw (IO.userError "reference cast absent")
  let (sourceConstant, expectedConstant) ← match sourceCast.kind, expectedCast.kind with
    | .Assign p (.Cast k (.Constant c) _), .Assign q (.Cast l (.Constant d) _) => do
      unless p == q && k == l do throw (IO.userError "promoted reify kind/destination mismatch")
      pure (c,d)
    | _, _ => throw (IO.userError "promoted fixed Cast was not preserved")
  let sourceSpan := fragment.spans.spans[sourceConstant.span.id]?
  let referenceSpan := reference.document.spans[expectedConstant.span.id]?
  match sourceSpan, referenceSpan with
  | some a, some b =>
    unless a.lo == b.lo && a.hi == b.hi && a.context == b.context do throw (IO.userError "exact constant operand compiler span mismatch")
  | _, _ => throw (IO.userError "constant operand physical span absent")
  let some sourceRef := sourceBlock.statements[1]? | throw (IO.userError "source borrow absent")
  let some expectedRef := expectedBlock.statements[1]? | throw (IO.userError "reference borrow absent")
  unless sourceRef.kind == expectedRef.kind do throw (IO.userError "promoted Shared Ref region/place mismatch")
  let referenceDefinition ← match expectedConstant.value with
    | .Val .ZeroSized typeId => do
      let some node := reference.document.types[typeId]? | throw (IO.userError "genuine FnDef type absent")
      match node.shape with
      | .functionDefinition definition _ _ _ => pure definition
      | _ => throw (IO.userError "genuine reify source is not FnDef")
    | _ => throw (IO.userError "genuine reify source is not ZST")
  let some definition := reference.document.definitions[referenceDefinition]? | throw (IO.userError "genuine function DefId absent")
  unless definition == recipe.function.key.compilerDefinition do throw (IO.userError "symbolic compiler function identity mismatch")
  let some instanceRow := reference.document.instances.find? (fun node =>
      node.definitionId == some referenceDefinition && node.genericArgs.isEmpty) | throw (IO.userError "genuine function instance absent")
  let some abiMap := reference.document.queries.instanceAbis.find? (·.instanceId == instanceRow.id)
    | throw (IO.userError "genuine function ABI mapping absent")
  let some abi := reference.document.functionAbis[abiMap.abiId]? | throw (IO.userError "genuine function ABI absent")
  unless recipe.function.abi.callingConvention == abi.callingConvention &&
      recipe.function.abi.canUnwind == abi.canUnwind && recipe.function.abi.fixedCount == abi.fixedCount &&
      recipe.function.abi.arguments.isEmpty && abi.arguments.isEmpty &&
      recipe.function.abi.returnValue.mode == abi.returnValue.mode do throw (IO.userError "pure declaration ABI disagrees with compiler")
  let tables ← checked (document.source.getObjValAs? (Array Json) "promoted_tables")
  let some table := tables[0]? | throw (IO.userError "raw table absent")
  rejected (evaluateSharedPromotedRecipe (replaceTable document (table.setObjVal! "function_headers" (toJson (#[] : Array Json)))) owner 0)
  let body := recipe.source.source
  let metadata ← checked (body.getObjVal? "source_metadata")
  let missingSpans := body.setObjVal! "source_metadata" (metadata.setObjVal! "additional_spans" (toJson (#[] : Array Json)))
  rejected (lowerSharedPromotedMIR (replaceTable document (table.setObjVal! "templates" (toJson #[missingSpans]))) owner 0)
  let headers ← checked (table.getObjValAs? (Array Json) "function_headers")
  let some header := headers[0]? | throw (IO.userError "source function header absent")
  let attrs ← checked (header.getObjVal? "function_attributes")
  let tracked := header.setObjVal! "function_attributes" (attrs.setObjVal! "track_caller" (toJson true))
  let trackedDocument := replaceTable document (table.setObjVal! "function_headers" (toJson #[tracked]))
  let trackedDocument := {trackedDocument with source := trackedDocument.source.setObjVal! "source_function_signatures" (toJson #[tracked])}
  match evaluateSharedPromotedRecipe trackedDocument owner 0 with
  | .error "signature ABI requires unadjusted ordinary item" => pure ()
  | _ => throw (IO.userError "caller-location shim requirement ignored during reification")
  let signature ← checked (header.getObjVal? "signature")
  let wrongSignature := signature.setObjVal! "output" (toJson (0 : Nat))
  let changedHeader := header.setObjVal! "signature" wrongSignature
  rejected (evaluateSharedPromotedRecipe (replaceTable document (table.setObjVal! "function_headers" (toJson #[changedHeader]))) owner 0)
  let blocks ← checked (body.getObjValAs? (Array Json) "blocks")
  let some block := blocks[0]? | throw (IO.userError "source block absent")
  let statements ← checked (block.getObjValAs? (Array Json) "statements")
  let some statement := statements[0]? | throw (IO.userError "source statement absent")
  let constant ← checked ((← checked (statement.getObjVal? "value")).getObjVal? "operand")
  let required := body.setObjVal! "required_consts" (toJson #[constant])
  match evaluateSharedPromotedRecipe (replaceTable document (table.setObjVal! "templates" (toJson #[required]))) owner 0 with
  | .error "symbolic promoted required-constant evaluation unavailable" => pure ()
  | _ => throw (IO.userError "unresolved required constant was not checked before interpretation")
  IO.println "promoted recipe/fixed MIR: genuine reify/shared-ref/span/ABI match; unresolved CTFE identities remain Unsupported; missing header/span/signature/required-const controls reject"
