import Miri.Frontend.FoundationStdSource
import Miri.Frontend.FoundationMIR
open Lean Miri Miri.Frontend.Foundation
private def checked {α : Type} (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def failure {α : Type} (value : Except String α) : IO Unit :=
  match value with | .error _ => pure () | .ok _ => throw (IO.userError "missing/invalid std source accepted")
def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected combined std startup source")
  let document ← checked (Json.parse (← IO.FS.readFile path) >>= decode)
  let spine ← checked (stdStartupSource document)
  unless spine.main != spine.start && spine.start != spine.internal &&
      spine.closure.parentDefinition == spine.start do throw (IO.userError "source identities not distinct/joined")
  let blocks ← checked (spine.internalBody.getObjValAs? (Array Json) "blocks")
  let mut resumes := 0
  for block in blocks do
    let terminal ← checked (block.getObjVal? "terminator")
    if (← checked (terminal.getObjValAs? String "kind")) == "unwind_resume" then
      let cleanup ← checked (block.getObjValAs? Bool "cleanup")
      unless (← checked (lowerSourceControlTerminator terminal blocks.size cleanup)) == .UnwindResume do
        throw (IO.userError "source resume changed fixed constructor")
      failure (lowerSourceControlTerminator terminal blocks.size false)
      resumes := resumes + 1
  unless resumes == 1 do throw (IO.userError "genuine std cleanup resume absent")
  for definition in #[spine.main,spine.start,spine.internal] do
    let bodies ← checked (document.bodies.filterM fun body => return (← body.getObjValAs? Nat "definition") != definition)
    failure (stdStartupSource { document with bodies })
  failure (stdStartupSource { document with source := document.source.setObjVal! "closure_templates" (toJson (#[] : Array Json)) })
  failure (lowerSourceControlTerminator (Json.mkObj [("kind",toJson "goto"),("target",toJson blocks.size)]) blocks.size false)
  failure (lowerSourceControlTerminator (Json.mkObj [("kind",toJson "return")]) blocks.size true)
  IO.println "std startup source: compiler main/start, actual internal Call and Closure/parent identities join; genuine cleanup Resume retained; missing source/invalid control reject; no runnable program claimed"
