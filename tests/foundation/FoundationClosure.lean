import Miri.Frontend.FoundationClosure

set_option maxHeartbeats 2000000
open Lean Miri.Frontend.Foundation

private def checked {α : Type} : Except String α → IO α
  | .ok value => pure value
  | .error e => throw (IO.userError e)

private def referenceType (fuel : Nat) (rows : Array Json) (id : Nat) (ty : ConcreteType) : Except String Bool := do
  let .succ fuel := fuel | throw "reference type comparison depth exhausted"
  let some row := rows[id]? | throw "reference type absent"
  let shape ← row.getObjVal? "shape"
  match ty with
  | .primitive "int" name =>
    return (← shape.getObjValAs? String "kind") == "int" && (← shape.getObjValAs? String "signed_kind") == name
  | .primitive "uint" name =>
    return (← shape.getObjValAs? String "kind") == "uint" && (← shape.getObjValAs? String "unsigned_kind") == name
  | .tuple elements =>
    unless (← shape.getObjValAs? String "kind") == "tuple" do return false
    let ids ← shape.getObjValAs? (Array Nat) "elements"
    unless ids.size == elements.size do return false
    for (id, element) in ids.zip elements do
      unless ← referenceType fuel rows id element do return false
    return true
  | .functionPointer inputs output safety abi variadic =>
    unless (← shape.getObjValAs? String "kind") == "function_pointer" do return false
    let sig ← shape.getObjVal? "signature"
    unless (← (← sig.getObjVal? "abi").getObjValAs? String "kind") == abi &&
        (← (← sig.getObjVal? "safety").getObjValAs? String "kind") == safety &&
        (← sig.getObjValAs? Bool "c_variadic") == variadic do return false
    let ids ← sig.getObjValAs? (Array Nat) "inputs"
    unless ids.size == inputs.size do return false
    for (id, input) in ids.zip inputs do
      unless ← referenceType fuel rows id input do return false
    referenceType fuel rows (← sig.getObjValAs? Nat "output") output
  | _ => throw "unsupported reference comparison type"

private def rejected {α : Type} (result : Except String α) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "incomplete/contradictory closure material accepted")

/-- Compare generic finite closure source against an independently exported
schema12 std-main instance, including all four actual closure arguments. This
is a finite source/material check, not executable closure or trait evidence. -/
def main (paths : List String) : IO Unit := do
  let [sourcePath, referencePath] := paths | throw (IO.userError "expected finite and schema12 closure exports")
  let document ← checked (Json.parse (← IO.FS.readFile sourcePath) >>= decode)
  let some definition := document.definitions.findIdx? (fun row =>
      (row.getObjValAs? String "path").toOption == some "std::rt::lang_start::{closure#0}")
    | throw (IO.userError "std start closure source absent")
  let selected ← checked (selectClosureTemplate document definition #[.type (.tuple #[])])
  unless selected.kind == .fn && selected.fullArguments.size == 4 && selected.spreadArgument.isNone do
    throw (IO.userError "closure kind/full argument/spread source mismatch")
  let reference ← checked (Json.parse (← IO.FS.readFile referencePath))
  let definitions ← checked (reference.getObjValAs? (Array Json) "definitions")
  let some referenceDefinition := definitions.findIdx? (fun row =>
      (row.getObjValAs? Nat "crate").toOption == some 1 &&
      (row.getObjValAs? Nat "index").toOption == some 188) | throw (IO.userError "genuine closure1:188 absent")
  let some sourceDefinition := document.definitions[definition]? | throw (IO.userError "source DefId absent")
  unless (← checked (sourceDefinition.getObjValAs? Nat "crate_index")) == 1 &&
      (← checked (sourceDefinition.getObjValAs? Nat "index")) == 188 do throw (IO.userError "source closure DefId mismatch")
  let mainQueries ← checked (reference.getObjVal? "compiler_main_queries")
  let startId ← checked (mainQueries.getObjValAs? Nat "start_lang_item")
  let some referenceParent := definitions[startId]? | throw (IO.userError "reference start definition absent")
  let some sourceParent := document.definitions[selected.parentDefinition]? | throw (IO.userError "source closure parent absent")
  unless (← checked (sourceParent.getObjValAs? Nat "crate_index")) == (← checked (referenceParent.getObjValAs? Nat "crate")) &&
      (← checked (sourceParent.getObjValAs? Nat "index")) == (← checked (referenceParent.getObjValAs? Nat "index")) do
    throw (IO.userError "closure inherited parent DefId mismatch")
  let instances ← checked (reference.getObjValAs? (Array Json) "instances")
  let some instanceRow := instances.find? (fun row =>
      (row.getObjValAs? Nat "def_id").toOption == some referenceDefinition &&
      (row.getObjValAs? String "kind").toOption == some "instance_mir") | throw (IO.userError "genuine closure instance absent")
  let args ← checked (instanceRow.getObjValAs? (Array Json) "generic_args")
  let types ← checked (reference.getObjValAs? (Array Json) "types")
  unless args.size == selected.fullArguments.size do throw (IO.userError "closure complete argument count disagrees")
  for (arg, sourceArg) in args.zip selected.fullArguments do
    let .type ty := sourceArg | throw (IO.userError "unexpected source const closure argument")
    unless (← checked (arg.getObjValAs? String "kind")) == "type" &&
        (← checked (referenceType 64 types (← checked (arg.getObjValAs? Nat "value")) ty)) do
      throw (IO.userError "pure closure argument substitution disagrees with genuine compiler instance")
  let bodies ← checked (reference.getObjValAs? (Array Json) "bodies")
  let instanceId ← checked (instanceRow.getObjValAs? Nat "instance_id")
  let some referenceBody := bodies.find? (fun body =>
      (body.getObjValAs? Nat "instance_id").toOption == some instanceId) | throw (IO.userError "genuine closure body absent")
  unless (← checked (referenceBody.getObjValAs? Nat "arg_count")) ==
      (← checked (selected.body.getObjValAs? Nat "argument_count")) &&
      (← checked (referenceBody.getObjVal? "spread_arg")) == (← checked (selected.body.getObjVal? "spread_argument")) do
    throw (IO.userError "closure body argument/spread mismatch")
  let referenceBlocks ← checked (referenceBody.getObjValAs? (Array Json) "basic_blocks")
  let blocks ← checked (selected.body.getObjValAs? (Array Json) "blocks")
  unless blocks.size == referenceBlocks.size && blocks.size == 5 do throw (IO.userError "closure body block spine mismatch")
  for (block, expected) in blocks.zip referenceBlocks do
    unless (← checked (block.getObjValAs? Bool "cleanup")) == (← checked (expected.getObjValAs? Bool "is_cleanup")) &&
        (← checked (block.getObjValAs? (Array Json) "statements")).size ==
          (← checked (expected.getObjValAs? (Array Json) "statements")).size do
      throw (IO.userError "closure body cleanup/statement spine mismatch")
    let actual ← checked ((← checked (block.getObjVal? "terminator")).getObjValAs? String "kind")
    let expected ← checked ((← checked ((← checked (expected.getObjVal? "terminator")).getObjVal? "kind")).getObjValAs? String "variant")
    unless (actual, expected) ∈ [("call", "Call"), ("return", "Return"), ("unwind_resume", "UnwindResume")] do
      throw (IO.userError "closure body terminator spine mismatch")
  rejected (selectClosureTemplate document definition #[])
  let templates ← checked (document.source.getObjValAs? (Array Json) "closure_templates")
  let missing := { document with source := document.source.setObjVal! "closure_templates" (toJson (#[] : Array Json)) }
  rejected (selectClosureTemplate missing definition #[.type (.tuple #[])])
  let duplicate := { document with source := document.source.setObjVal! "closure_templates" (toJson (templates ++ templates)) }
  rejected (selectClosureTemplate duplicate definition #[.type (.tuple #[])])
  let invalidSpread := selected.body.setObjVal! "spread_argument" (toJson (2 : Nat))
  let spreadSource := document.source.setObjVal! "closure_templates" (toJson #[invalidSpread])
  rejected (selectClosureTemplate { document with source := spreadSource } definition #[.type (.tuple #[])])
  let signatureId ← checked (selected.body.getObjValAs? Nat "signature_type")
  let some sigRow := document.types[signatureId]? | throw (IO.userError "signature row absent")
  let shape ← checked (sigRow.getObjVal? "shape")
  let sig ← checked (shape.getObjVal? "signature")
  let abi := Json.mkObj [("kind", toJson "rust"), ("unwind", Json.null)]
  let changed := sigRow.setObjVal! "shape" (shape.setObjVal! "signature" (sig.setObjVal! "abi" abi))
  let broken := { document with types := document.types.set! signatureId changed }
  rejected (selectClosureTemplate broken definition #[.type (.tuple #[])])
  IO.println "foundation std closure: genuine1:188 inherited/synthetic arguments, RustCall signature and MIR spine match; missing/duplicate/ABI controls reject"
