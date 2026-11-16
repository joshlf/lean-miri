import Miri.Input.Decoder
import Miri.Input.RuntimeMetadata

open Miri.Input

private def oracleRows : JsonReader.Parser (Array (Nat × Layout)) := do
  let rows ← JsonReader.object (none : Option (Array (Nat × Layout))) fun rows key => do
    if key != "types" then JsonReader.skipValue; return rows
    let values ← JsonReader.array do
      let (id,layout) ← JsonReader.object (none,none) fun fields key => do
        match key with
        | "type_id" => return (some (← JsonReader.natural),fields.2)
        | "layout" => return (fields.1,some (← DecoderValues.parseLayout))
        | _ => JsonReader.skipValue; pure fields
      pure (← JsonReader.required id "type_id",← JsonReader.required layout "layout")
    pure (some values)
  JsonReader.required rows "types"

def main (args : List String) : IO UInt32 := do
  let [inputPath,oraclePath] := args
    | throw (IO.userError "usage: CheckSourceLayouts <fresh-source-input.json> <same-producer-oracle.json>")
  let input ← match ← decodeFile inputPath with
    | .ok input => pure input
    | .error message => throw (IO.userError message)
  let runtime ← match RuntimeMetadata.ofDocument input.document with
    | .ok runtime => pure runtime
    | .error message => throw (IO.userError (toString message))
  let rows ← match JsonReader.run oracleRows (← IO.FS.readFile oraclePath) with
    | .ok rows => pure rows
    | .error message => throw (IO.userError message)
  let mut seen : Std.HashSet Nat := {}
  let mut failures := 0
  for (id,source) in rows do
    unless id < input.document.types.size && !seen.contains id do
      throw (IO.userError "layout oracle contains a dangling or duplicate type ID")
    seen := seen.insert id
    let expected ← match RuntimeMetadata.layout runtime.target source with
      | .ok expected => pure expected
      | .error message => throw (IO.userError (toString message))
    match runtime.lookup id with
    | .ok actual =>
      unless actual.layout == expected do
        failures := failures+1
        IO.println s!"type={id} rustc={reprStr expected} Lean={reprStr actual.layout}"
    | .error message =>
      failures := failures+1
      IO.println s!"type={id} Lean={message}"
  unless seen.size == input.document.types.size do
    throw (IO.userError "layout oracle does not cover the exported concrete type table")
  IO.println s!"source layouts: compared={rows.size}, failures={failures}; finite compiler comparison only"
  return if !rows.isEmpty && failures == 0 then 0 else 1
