import Miri.Frontend.FoundationCallGraphProgram
import Miri.Frontend.FoundationCallExecute
import Miri.Input.Decoder

set_option maxHeartbeats 2000000
open Lean Miri Miri.Frontend.Foundation

private def checked {α : Type} : Except String α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def load (path : String) : IO Document := do
  checked (Json.parse (← IO.FS.readFile path) >>= decode)

private def definition (d : Document) (name : String) : IO Nat := do
  let some id := d.definitions.findIdx? (fun row =>
      (row.getObjValAs? String "path").toOption == some name) | throw (IO.userError s!"source {name} absent")
  pure id

private def rejected {α : Type} (result : Except String α) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "unsupported/missing call graph material accepted")

private def run (path referencePath name : String) (nodes sites : Nat)
    (frames : FixedDirectCallRun.FrameObservation) : IO Unit := do
  let document ← load path
  let root ← definition document name
  let graph ← checked (scalarCallGraph document root)
  unless graph.items.size == nodes && graph.sites.size == sites &&
      graph.pool.registry.instances.size == nodes && graph.pool.abis.size == 1 do
    throw (IO.userError "demand closure instance/site/ABI identity mismatch")
  if name == "twice" then
    let some first := graph.sites[0]? | throw (IO.userError "first site absent")
    let some second := graph.sites[1]? | throw (IO.userError "second site absent")
    unless first.demand.node.id == second.demand.node.id &&
        first.demand.node.genericArgs == second.demand.node.genericArgs &&
        first.demand.functionOrdinal == second.demand.functionOrdinal do
      throw (IO.userError "repeated complete instance demand was not deduplicated")
  let program ← checked (scalarCallGraphProgram document root)
  let prepared ← checked (Input.CompilerProviders.prepare program)
  IO.println (← checked (FixedDirectCallRun.runPrepared prepared 0xBEEF frames))
  let reference ← checked (Input.decodeJson (← IO.FS.readFile referencePath))
  let reference ← checked (Input.lowerProgram reference.document)
  let reference ← checked (Input.CompilerProviders.prepare reference)
  IO.println (← checked (FixedDirectCallRun.runPrepared reference 0xBEEF frames))
  let leafId ← definition document "identity"
  let missing := { document with bodies := document.bodies.filter fun body =>
    (body.getObjValAs? Nat "definition").toOption != some leafId }
  rejected (scalarCallGraphProgram missing root)
  let some leaf := document.bodies.find? (fun body =>
      (body.getObjValAs? Nat "definition").toOption == some leafId) | throw (IO.userError "leaf absent")
  rejected (scalarCallGraphProgram { document with bodies := document.bodies.push leaf } root)
  let missingSites := { program.input with bodies := program.input.bodies.map fun body =>
    { body with callEvidence := body.callEvidence.map fun _ => none } }
  match Input.lowerProgram missingSites >>= Input.CompilerProviders.prepare with
  | .error _ => pure ()
  | .ok prepared => rejected (FixedDirectCallRun.runPrepared prepared 0xBEEF frames)
  IO.println s!"{name}: complete-key dedup and missing/duplicate template/site controls passed"

def main (paths : List String) : IO Unit := do
  let [chain, chainReference, twice, twiceReference, recursive, mutualPath] := paths
    | throw (IO.userError "expected finite/schema12 chain and twice, plus finite self/mutual-recursive exports")
  run chain chainReference "chain" 3 2 ⟨3, 2, 2⟩
  run twice twiceReference "twice" 2 2 ⟨2, 2, 1⟩
  let document ← load recursive
  let root ← definition document "recursive"
  match scalarCallGraph document root with
  | .error "recursive source-definition call graph unsupported" => pure ()
  | .error error => throw (IO.userError s!"unexpected recursion rejection: {error}")
  | .ok _ => throw (IO.userError "recursive demand closure accepted")
  IO.println "recursive source graph rejected before execution"
  let document ← load mutualPath
  let root ← definition document "mutual_a"
  match scalarCallGraph document root with
  | .error "recursive source-definition call graph unsupported" => pure ()
  | .error error => throw (IO.userError s!"unexpected mutual-recursion rejection: {error}")
  | .ok _ => throw (IO.userError "mutual recursive demand closure accepted")
  IO.println "mutually recursive source graph rejected before execution"
