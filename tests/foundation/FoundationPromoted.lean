import Miri.Frontend.FoundationPromoted

open Lean Miri.Frontend.Foundation

private def checked {α : Type} : Except String α → IO α
  | .ok value => pure value
  | .error e => throw (IO.userError e)
private def rejected {α : Type} : Except String α → IO Unit
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "missing/distorted promoted material accepted")

private def check (materialPath referencePath : String) : IO Document := do
  let document ← checked (Json.parse (← IO.FS.readFile materialPath) >>= decode)
  let reference ← checked (Json.parse (← IO.FS.readFile referencePath))
  let path ← checked (reference.getObjValAs? String "owner_path")
  let some owner := document.definitions.findIdx? (fun row =>
      (row.getObjValAs? String "path").toOption == some path) | throw (IO.userError "source promoted owner absent")
  let some definition := document.definitions[owner]? | throw (IO.userError "source owner DefId absent")
  unless (← checked (definition.getObjValAs? Nat "crate_index")) == (← checked (reference.getObjValAs? Nat "owner_crate")) &&
      (← checked (definition.getObjValAs? Nat "index")) == (← checked (reference.getObjValAs? Nat "owner_index")) do
    throw (IO.userError "direct compiler source owner DefId mismatch")
  let table ← checked (promotedSourceTable document owner)
  unless table.templates.size == (← checked (reference.getObjValAs? Nat "count")) do
    throw (IO.userError "complete compiler promoted table count mismatch")
  let entries ← checked (reference.getObjValAs? (Array Json) "entries")
  unless entries.size == table.templates.size do throw (IO.userError "probe complete entry count mismatch")
  for (body, expected) in table.templates.zip entries do
    unless body.index == (← checked (expected.getObjValAs? Nat "index")) &&
        body.requiredConstants.size == (← checked (expected.getObjValAs? Nat "required_count")) &&
        body.localTypes.size == (← checked (expected.getObjValAs? (Array String) "locals")).size do
      throw (IO.userError "promoted source index/required constants/locals disagree")
    unless (← checked (body.source.getObjValAs? Nat "argument_count")) == (← checked (expected.getObjValAs? Nat "argument_count")) &&
        (← checked (body.source.getObjVal? "spread_argument")) == (← checked (expected.getObjVal? "spread_argument")) do
      throw (IO.userError "promoted source argument/spread mismatch")
    let phase ← checked ((← checked (body.source.getObjVal? "source_metadata")).getObjVal? "phase")
    unless (← checked (phase.getObjValAs? String "kind")) == "runtime" &&
        (← checked (phase.getObjValAs? String "phase")) == "post_cleanup" &&
        (← checked (expected.getObjValAs? String "phase")) == "Runtime(PostCleanup)" do
      throw (IO.userError "promoted source phase mismatch")
    let blocks ← checked (body.source.getObjValAs? (Array Json) "blocks")
    let statements ← checked (expected.getObjValAs? (Array (Array String)) "statements")
    let terminals ← checked (expected.getObjValAs? (Array String) "terminators")
    unless blocks.size == statements.size && blocks.size == terminals.size do
      throw (IO.userError "promoted source block count mismatch")
    for h : i in [:blocks.size] do
      let actual ← checked (blocks[i].getObjValAs? (Array Json) "statements")
      let some statementNames := statements[i]? | throw (IO.userError "probe statement row absent")
      unless actual.size == statementNames.size do throw (IO.userError "promoted statement count mismatch")
      unless (← checked ((← checked (blocks[i].getObjVal? "terminator")).getObjValAs? String "kind")) == "return" &&
          terminals[i]? == some "return" do throw (IO.userError "promoted terminator mismatch")
  let tables ← checked (document.source.getObjValAs? (Array Json) "promoted_tables")
  let some raw := tables[0]? | throw (IO.userError "raw source table absent")
  rejected (promotedSourceTable {document with source := document.source.setObjVal! "promoted_tables" (toJson (#[] : Array Json))} owner)
  rejected (promotedSourceTable {document with source := document.source.setObjVal! "promoted_tables" (toJson (tables ++ tables))} owner)
  let broken := raw.setObjVal! "promoted_count" (toJson (table.templates.size + 1))
  rejected (promotedSourceTable {document with source := document.source.setObjVal! "promoted_tables" (toJson #[broken])} owner)
  if let some body := table.templates[0]? then
    let bodyWrongIndex := body.source.setObjVal! "source_promoted" (toJson (1 : Nat))
    let broken := raw.setObjVal! "templates" (toJson #[bodyWrongIndex])
    rejected (promotedSourceTable {document with source := document.source.setObjVal! "promoted_tables" (toJson #[broken])} owner)
    let missingRequired := body.source.setObjVal! "required_consts" Json.null
    let broken := raw.setObjVal! "templates" (toJson #[missingRequired])
    rejected (promotedSourceTable {document with source := document.source.setObjVal! "promoted_tables" (toJson #[broken])} owner)
    let blocks ← checked (body.source.getObjValAs? (Array Json) "blocks")
    let some block := blocks[0]? | throw (IO.userError "positive promoted entry absent")
    let statements ← checked (block.getObjValAs? (Array Json) "statements")
    let some cast := statements[0]? | throw (IO.userError "promoted reification absent")
    let rvalue ← checked (cast.getObjVal? "value")
    unless (← checked (rvalue.getObjValAs? String "kind")) == "cast_reify_function_pointer" &&
        (← checked (rvalue.getObjValAs? String "safety")) == "safe" &&
        (← checked (rvalue.getObjValAs? String "source")) == "as_cast" do
      throw (IO.userError "genuine reification source operands lost")
  else
    rejected (selectPromotedTemplate document owner 0)
  IO.println s!"{path}: complete source table count={table.templates.size}; compiler identity/phase/required-const/spine and corruption controls passed"
  pure document

def main (paths : List String) : IO Unit := do
  let [positive, positiveReference, empty, emptyReference] := paths
    | throw (IO.userError "expected material/probe pairs for local positive and std internal zero")
  let _ ← check positive positiveReference
  let _ ← check empty emptyReference
