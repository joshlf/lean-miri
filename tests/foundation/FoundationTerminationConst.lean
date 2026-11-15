import Miri.Frontend.FoundationConstOperand
import Miri.Frontend.FoundationDirectCalls
import Miri.Frontend.FoundationBridge
import Miri.Frontend.FoundationItemResolution
open Lean Miri Miri.Frontend.Foundation
private def checked (value : Except String α) : IO α := do
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def rejected (value : Except String α) : IO Unit := do
  match value with | .error _ => pure () | .ok _ => throw (IO.userError "unsupported nominal const accepted")
def main (paths : List String) : IO Unit := do
  let [sourcePath,referencePath] := paths | throw (IO.userError "expected genuine std/report reference")
  let document ← checked (Json.parse (← IO.FS.readFile sourcePath) >>= decode)
  let references ← checked (Json.parse (← IO.FS.readFile referencePath) >>= fun j => j.getArr?)
  let material ← checked (document.source.getObjVal? "termination_source")
  let selection ← checked (sourceTerminationUnitSelection document (← checked (material.getObjValAs? Nat "definition")) (.tuple #[]))
  let prepared ← checked (prepareItem document selection.implementationMethodDefinition #[])
  let some method := document.definitions[selection.implementationMethodDefinition]? | throw (IO.userError "report method absent")
  let key := Json.mkObj [("crate",toJson (← checked (method.getObjValAs? Nat "crate_index"))),("index",toJson (← checked (method.getObjValAs? Nat "index")))]
  let some reference := references.find? (fun ref => (ref.getObjVal? "identity").toOption == some key) | throw (IO.userError "compiler Item reference absent")
  let scalars ← checked (reference.getObjValAs? (Array Json) "required_scalars")
  let operands ← checked (prepared.item.source.getObjValAs? (Array Json) "required_consts")
  unless operands.size == 1 && scalars.size == 1 do throw (IO.userError "genuine report constant count mismatch")
  let some operand := operands[0]? | throw (IO.userError "report source constant absent")
  let some scalar := scalars[0]? | throw (IO.userError "report compiler scalar absent")
  let value ← checked (evaluateSourceConstant document operand)
  let storage ← checked (sourceConstantScalar document value)
  let .structureValue _ definition _ := value | throw (IO.userError "genuine report requires nominal aggregate source")
  let some row := document.definitions[definition]? | throw (IO.userError "nominal declaration absent")
  let actual := Json.mkObj [("crate",toJson (← checked (row.getObjValAs? Nat "crate_index"))),("index",toJson (← checked (row.getObjValAs? Nat "index")))]
  unless actual == (← checked (scalar.getObjVal? "definition")) && toString storage.bits == (← checked (scalar.getObjValAs? String "bits")) &&
      storage.sizeBytes == (← checked (scalar.getObjValAs? Nat "size_bytes")) do throw (IO.userError "pure source aggregate disagrees with genuine compiler CTFE scalar")
  let spans ← checked (buildSpanRegistry prepared.item.source)
  let (_,lowered) ← checked (lowerScalarConstantOperand (PhysicalTypeRegistry.start document) spans operand)
  match lowered.value with
  | .Val (.Scalar (.Int bits size)) _ =>
    unless bits == storage.bits && size == storage.sizeBytes do throw (IO.userError "common constant operand callback changed aggregate storage")
  | _ => throw (IO.userError "common constant callback did not materialize scalar storage")
  let templates ← checked (document.source.getObjValAs? (Array Json) "closure_templates")
  let mut sawDemand := false
  for template in templates do
    for block in (← checked (template.getObjValAs? (Array Json) "blocks")) do
      let term ← checked (block.getObjVal? "terminator")
      if (term.getObjValAs? String "kind").toOption == some "call" then
        let function ← checked (term.getObjVal? "function")
        if let some typeId := (function.getObjValAs? Nat "type").toOption then
          let some type := document.types[typeId]? | throw (IO.userError "callee source type absent")
          let shape ← checked (type.getObjVal? "shape")
          if (shape.getObjValAs? Nat "definition").toOption == some selection.traitMethodDefinition then
            let pool ← checked (DirectCallPool.start (PhysicalTypeRegistry.start document))
            let (pool,demand) ← checked (pool.demand #[.type (.tuple #[])] function)
            unless demand.node.instanceKind == .Item selection.implementationMethodDefinition && demand.node.genericArgs.isEmpty &&
                pool.functionSourceDefinitions[demand.functionOrdinal]? == some selection.traitMethodDefinition do
              throw (IO.userError "actual closure FnDef demand lost source/selected Item distinction")
            let finished ← checked (pool.finishFunctionTypes)
            let some functionTypeId := finished.typeIds[demand.functionOrdinal]? | throw (IO.userError "report FnDef type absent")
            let some functionType := finished.types[functionTypeId]? | throw (IO.userError "report FnDef node absent")
            match functionType.shape with
            | .functionDefinition original arguments _ _ =>
              unless original == selection.traitMethodDefinition && arguments.size == 1 do
                throw (IO.userError "report FnDef type collapsed source identity/arguments")
            | _ => throw (IO.userError "report function type constructor mismatch")
            unless (← checked (reference.getObjValAs? (Array String) "function_type_displays")).contains functionType.display do
              throw (IO.userError "report FnDef full signature display differs from compiler")
            sawDemand := true
  unless sawDemand do throw (IO.userError "actual closure report FnDef demand absent")
  let mutate (definition : Nat) (row : Json) := {document with definitions := document.definitions.set! definition row}
  let valueSource ← checked (operand.getObjVal? "value")
  let constant ← checked (valueSource.getObjValAs? Nat "definition")
  let some constantRow := document.definitions[constant]? | throw (IO.userError "constant declaration absent")
  let expression ← checked (constantRow.getObjVal? "const_expression")
  let owner ← checked (constantRow.getObjVal? "const_owner")
  rejected (evaluateSourceConstant (mutate constant (constantRow.setObjVal! "const_owner" (owner.setObjVal! "kind" (toJson "trait_impl")))) operand)
  let cycle := Json.mkObj [("type",toJson storage.typeId),("retag",toJson true),("operand",operand)]
  rejected (evaluateSourceConstant (mutate constant (constantRow.setObjVal! "const_expression" cycle)) operand)
  rejected (evaluateSourceConstant (mutate constant (constantRow.setObjVal! "const_expression" (expression.setObjVal! "type" (toJson document.types.size)))) operand)
  let mut metadataCount := 0
  for index in [:document.definitions.size] do
    let some row := document.definitions[index]? | throw (IO.userError "definition index")
    if let some expression := (row.getObjVal? "const_expression").toOption then
      if (expression.getObjValAs? String "kind").toOption == some "aggregate_mir" then
        let mir ← checked (expression.getObjVal? "mir")
        rejected (evaluateSourceConstant (mutate index (row.setObjVal! "const_expression" (expression.setObjVal! "mir" (mir.setObjVal! "blocks" (toJson (#[] : Array Json)))))) operand)
        let blocks ← checked (mir.getObjValAs? (Array Json) "blocks")
        let some block := blocks[0]? | throw (IO.userError "aggregate MIR block absent")
        let statements ← checked (block.getObjValAs? (Array Json) "statements")
        let some assignment := statements.find? (fun statement => (statement.getObjValAs? String "kind").toOption == some "assign")
          | throw (IO.userError "aggregate MIR assignment absent")
        let place ← checked (assignment.getObjVal? "place")
        let move := Json.mkObj [("kind",toJson "move"),("place",place)]
        let badValue := Json.mkObj [("kind",toJson "use"),("operand",move),("retag",toJson true)]
        let changed := statements.map (fun statement => if statement == assignment then statement.setObjVal! "value" badValue else statement)
        let block := block.setObjVal! "statements" (toJson changed)
        let mir := mir.setObjVal! "blocks" (toJson #[block])
        rejected (evaluateSourceConstant (mutate index (row.setObjVal! "const_expression" (expression.setObjVal! "mir" mir))) operand)
      if (expression.getObjValAs? String "kind").toOption == some "metadata_trivial_literal" then
        metadataCount := metadataCount + 1
        rejected (evaluateSourceConstant (mutate index (row.setObjVal! "const_expression" (expression.setObjVal! "original_reference_chain" (toJson "reconstructed")))) operand)
        let literal ← checked (expression.getObjVal? "literal")
        let scalarValue ← checked (literal.getObjVal? "value")
        let overflow := scalarValue.setObjVal! "bits" (toJson (toString (2^128 : Nat)))
        rejected (evaluateSourceConstant (mutate index (row.setObjVal! "const_expression" (expression.setObjVal! "literal" (literal.setObjVal! "value" overflow)))) operand)
  unless metadataCount > 0 do throw (IO.userError "expected genuine pinned metadata trivial literal")
  rejected (sourceConstantScalar document (.structureValue storage.typeId definition #[]))
  IO.println "actual std report prepareItem/required const/common operand: pure nominal CTFE agrees with compiler; cycle/type/owner/literal/storage guards passed"
