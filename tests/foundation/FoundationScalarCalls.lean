import Miri.Frontend.FoundationCallExecute
import Miri.Input.Decoder

set_option maxHeartbeats 2000000

open Lean Miri Miri.Frontend.Foundation

private def checked {α : Type} : Except String α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def run (sourcePath referencePath name : String) (value width : Nat) : IO Unit := do
  let document ← checked (Json.parse (← IO.FS.readFile sourcePath) >>= decode)
  let some definition := document.definitions.findIdx? (fun row =>
      (row.getObjValAs? String "path").toOption == some name) | throw (IO.userError "scalar caller source absent")
  let program ← checked (restrictedDirectCallProgram document definition)
  let some root := program.input.bodies[0]? | throw (IO.userError "root body absent")
  let some block := root.mir.basicBlocks[0]? | throw (IO.userError "root block absent")
  match block.terminator.kind with
  | .Call (.Constant _) args _ _ _ _ _ =>
    let some argument := args[0]? | throw (IO.userError "call argument absent")
    match argument.operand with
    | .Move p => unless p.projection.isEmpty do throw (IO.userError "unexpected Move projection")
    | _ => throw (IO.userError "genuine call Move operand was lost")
  | _ => throw (IO.userError "genuine source Call operand was lost")
  let some leaf := program.input.bodies[1]? | throw (IO.userError "leaf body absent")
  let some leafBlock := leaf.mir.basicBlocks[0]? | throw (IO.userError "leaf block absent")
  let some assignment := leafBlock.statements[0]? | throw (IO.userError "leaf assignment absent")
  let some sourceLeaf := document.bodies.find? (fun b =>
      (b.getObjValAs? Nat "definition").toOption == leaf.definitionId) | throw (IO.userError "leaf source absent")
  let sourceBlocks ← checked (sourceLeaf.getObjValAs? (Array Json) "blocks")
  let some sourceBlock := sourceBlocks[0]? | throw (IO.userError "leaf source block absent")
  let statements ← checked (sourceBlock.getObjValAs? (Array Json) "statements")
  let some statement := statements[0]? | throw (IO.userError "leaf source assignment absent")
  let rvalue ← checked (statement.getObjVal? "value")
  let sourceRetag ← checked (rvalue.getObjValAs? Bool "retag")
  match assignment.kind with
  | .Assign _ (.Use (.Copy _) retag) =>
    unless retag == (if sourceRetag then .Yes else .No) do throw (IO.userError "Use retag flag changed")
  | _ => throw (IO.userError "genuine identity Copy/Use was lost")
  let prepared ← checked (Input.CompilerProviders.prepare program)
  IO.println (← checked (FixedDirectCallRun.runPrepared prepared value))
  match FixedDirectCallRun.runPrepared prepared (2^(width*8)) with
  | .error "bounded call input exceeds scalar width" => pure ()
  | .error error => throw (IO.userError s!"unexpected oversized-input error: {error}")
  | .ok _ => throw (IO.userError "oversized scalar input was silently truncated")
  let reference ← checked (Input.decodeJson (← IO.FS.readFile referencePath))
  let reference ← checked (Input.lowerProgram reference.document)
  let reference ← checked (Input.CompilerProviders.prepare reference)
  IO.println (← checked (FixedDirectCallRun.runPrepared reference value))
  let some sourceRoot := document.bodies.find? (fun b =>
      (b.getObjValAs? Nat "definition").toOption == some definition) | throw (IO.userError "root source absent")
  let brokenRoot := sourceRoot.setObjVal! "required_consts" (toJson #[Json.null])
  let broken := { document with bodies := document.bodies.map fun body =>
    if body == sourceRoot then brokenRoot else body }
  match restrictedDirectCallProgram broken definition with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "unresolved required constant ignored")
  let broken := { document with source := document.source.setObjVal! "entry_selection" Json.null }
  match restrictedDirectCallProgram broken definition with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "missing compiler entry selection was treated as a library")
  IO.println s!"{name}: {width}-byte scalar, source Move/Copy/retag and fail-closed width/required-const/entry-selection controls passed"

def main (paths : List String) : IO Unit := do
  let [u16Source, u16Reference, usizeSource, usizeReference] := paths
    | throw (IO.userError "expected finite/schema12 u16 and usize call exports")
  run u16Source u16Reference "call_u16" 0xBEEF 2
  run usizeSource usizeReference "call_usize" 0x123456789ABCDEF0 8
