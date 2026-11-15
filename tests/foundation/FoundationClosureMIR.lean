import Miri.Frontend.FoundationClosureMIR

set_option maxHeartbeats 2000000
open Lean Miri Miri.Frontend.Foundation
private def checked (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error e => throw (IO.userError e)
private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def reject (result : Except String α) : IO Unit :=
  match result with | .error _ => pure () | .ok _ => throw (IO.userError "invalid closure source accepted")

def main (paths : List String) : IO Unit := do
  let [sourcePath, referencePath] := paths | throw (IO.userError "usage: source schema12")
  let document ← checked (Json.parse (← IO.FS.readFile sourcePath) >>= decode)
  let some definition := document.definitions.findIdx? (fun row =>
    (row.getObjValAs? String "path").toOption == some "std::rt::lang_start::{closure#0}")
    | throw (IO.userError "genuine selected std closure absent")
  let (physical,prepared) ← checked (prepareClosureMIRTypes (PhysicalTypeRegistry.start document)
    definition #[.type (.tuple #[])])
  require (prepared.item.localTypes.size == 5 && prepared.item.argumentCount == 1)
    "std closure source local/argument count differs"
  let selected ← checked (selectClosureTemplate document definition #[.type (.tuple #[])])
  let joins := closureMIRJoins physical selected
  let blocks ← checked (selected.body.getObjValAs? (Array Json) "blocks")
  require (blocks.size == 5) "genuine std closure control spine differs"
  let some entry := blocks[0]? | throw (IO.userError "closure entry block absent")
  let statements ← checked (entry.getObjValAs? (Array Json) "statements")
  let some statement := statements[3]? | throw (IO.userError "genuine capture assignment absent")
  let value ← checked (statement.getObjVal? "value")
  let lowered ← checked (lowerJoinedRvalue prepared joins (fun _ => .error "unexpected constant") value)
  let .Use (.Copy place) .Yes := lowered.value | throw (IO.userError "copy/retag preservation failed")
  let some fact := lowered.places[0]? | throw (IO.userError "projected place fact absent")
  require (place.localId == 1 && place.projection.size == 2 && fact.projectionTypes.size == 2)
    "closure capture intermediate projection types absent"
  let some (MIR.ProjectionElem.Field 0 fieldId) := place.projection[1]? | throw (IO.userError "closure upvar field projection absent")
  let (field,_) ← checked (physical.lookup fieldId)
  let .functionPointer signature _ := field.shape | throw (IO.userError "captured fnptr physical identity absent")
  require (signature.inputs.isEmpty && signature.abi == .Rust) "captured Rust function signature differs"
  let metadata ← checked (selected.body.getObjVal? "source_metadata")
  let callSpans ← checked (metadata.getObjValAs? (Array Json) "call_spans")
  let some firstCallSpans := callSpans[0]? | throw (IO.userError "closure source call spans absent")
  let terminal ← checked (entry.getObjVal? "terminator")
  reject (checkClosureCallSyntax prepared joins (fun _ => .error "constant unavailable")
    ⟨.direct, none, none, none, .normal 0⟩ terminal firstCallSpans .Return)
  let templates ← checked (document.source.getObjValAs? (Array Json) "closure_templates")
  let some templateIndex := templates.findIdx? (· == selected.body) | throw (IO.userError "template source absent")
  let invalid := selected.body.setObjVal! "required_consts" (toJson #[Json.mkObj []])
  let alteredSource := document.source.setObjVal! "closure_templates" (toJson (templates.set! templateIndex invalid))
  let altered := { document with source := alteredSource }
  reject (prepareClosureMIRTypes (PhysicalTypeRegistry.start altered) definition #[.type (.tuple #[])])
  let reference ← checked (Json.parse (← IO.FS.readFile referencePath))
  let definitions ← checked (reference.getObjValAs? (Array Json) "definitions")
  let some sourceDefinition := document.definitions[definition]? | throw (IO.userError "source definition absent")
  let crateIndex ← checked (sourceDefinition.getObjValAs? Nat "crate_index")
  let index ← checked (sourceDefinition.getObjValAs? Nat "index")
  let some compilerDefinition := definitions.findIdx? (fun d =>
    (d.getObjValAs? Nat "crate").toOption == some crateIndex &&
    (d.getObjValAs? Nat "index").toOption == some index) | throw (IO.userError "compiler closure definition absent")
  let bodies ← checked (reference.getObjValAs? (Array Json) "bodies")
  let some body := bodies.find? (fun b =>
    (b.getObjValAs? Nat "source_def_id").toOption == some compilerDefinition)
    | throw (IO.userError "compiler closure body absent")
  let compilerBlocks ← checked (body.getObjValAs? (Array Json) "basic_blocks")
  require (compilerBlocks.size == blocks.size) "closure control block count differs"
  let some compilerEntry := compilerBlocks[0]? | throw (IO.userError "compiler closure entry absent")
  let compilerStatements ← checked (compilerEntry.getObjValAs? (Array Json) "statements")
  let some compilerStatement := compilerStatements[3]? | throw (IO.userError "compiler capture statement absent")
  let kindId ← checked (compilerStatement.getObjValAs? Nat "kind")
  let kinds ← checked (reference.getObjValAs? (Array Json) "statement_kinds")
  let some kind := kinds[kindId]? | throw (IO.userError "compiler assignment kind absent")
  -- Raw compiler spine is compared separately from Lean-local physical IDs.
  let compilerValue ← checked (kind.getObjVal? "rvalue")
  require ((← checked (compilerValue.getObjValAs? String "kind")) == "Use") "compiler captured value differs"
  let compilerOperand ← checked (compilerValue.getObjVal? "operand")
  require ((← checked (compilerOperand.getObjValAs? String "kind")) == "Copy" &&
    (← checked ((← checked (compilerValue.getObjVal? "retag")).getObjValAs? Bool "performs_retag")))
    "compiler Copy/WithRetag differs"
  let compilerPlace ← checked (compilerOperand.getObjVal? "place")
  let projections ← checked (compilerPlace.getObjValAs? (Array Json) "projection")
  require ((← checked (compilerPlace.getObjValAs? Nat "local")) == place.localId && projections.size == 2)
    "compiler capture projection spine differs"
  let some compilerDeref := projections[0]? | throw (IO.userError "compiler deref absent")
  let some compilerField := projections[1]? | throw (IO.userError "compiler field absent")
  require ((← checked (compilerDeref.getObjValAs? String "kind")) == "Deref" &&
    (← checked (compilerField.getObjValAs? String "kind")) == "Field" &&
    (← checked (compilerField.getObjValAs? Nat "index")) == 0) "compiler capture projection differs"
  let withoutRetag ← checked (lowerJoinedRvalue prepared joins (fun _ => .error "unexpected constant")
    (value.setObjVal! "retag" (toJson false)))
  let .Use (.Copy _) .No := withoutRetag.value | throw (IO.userError "No retag was lost")
  let sourcePlace ← checked ((← checked (value.getObjVal? "operand")).getObjVal? "place")
  reject (lowerSourcePlace prepared.item.localTypes
    (sourcePlace.setObjVal! "projection" (toJson #[Json.mkObj [("kind",toJson "deref")],
      Json.mkObj [("kind",toJson "field"),("index",toJson (1:Nat)),("type",toJson (0:Nat))]])) joins)
  let badJoins := { joins with sourceType := fun _ => .ok (.primitive "uint" "u8") }
  reject (lowerJoinedRvalue prepared badJoins (fun _ => .error "constant unavailable") value)
  reject (lowerSourcePlace prepared.item.localTypes sourcePlace)
  match lowerPreparedMIR prepared (rvalueJoins := joins) with
  | .error "foundation call query is unavailable" => pure ()
  | .error error => throw (IO.userError s!"unexpected pre-call lowering blocker: {error}")
  | .ok _ => throw (IO.userError "missing closure call query accepted")
  IO.println "closure MIR: genuine five-block source locals and projected Copy/Retag prepare; missing call queries/field joins reject"
