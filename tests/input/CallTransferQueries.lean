import Miri.Input.Decoder
import Miri.Input.ConcreteCovariance

open Miri.Input

private structure Check where
  source : TypeId
  target : TypeId
  expected : Bool
  label : String

private def checks : JsonReader.Parser (Array Check) := do
  let result ← JsonReader.object none fun result key => do
    if key != "checks" then JsonReader.skipValue; return result
    let rows ← JsonReader.array do
      let (source, target, expected, label) ← JsonReader.object (none, none, none, none)
        fun (source, target, expected, label) key => do
          match key with
          | "source_type" => return (some (← JsonReader.natural), target, expected, label)
          | "target_type" => return (source, some (← JsonReader.natural), expected, label)
          | "expected" => return (source, target, some (← JsonReader.boolean), label)
          | "label" => return (source, target, expected, some (← JsonReader.string))
          | _ => JsonReader.skipValue; return (source, target, expected, label)
      pure ⟨← JsonReader.required source "source_type", ← JsonReader.required target "target_type",
        ← JsonReader.required expected "expected", ← JsonReader.required label "label"⟩
    return some rows
  JsonReader.required result "checks"

private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error reason => throw (IO.userError reason)

def main (args : List String) : IO Unit := do
  let [path, expectations] := args | throw (IO.userError "expected current call-transfer input and exact source-edge checks")
  let decoded ← must (decodeJson (← IO.FS.readFile path))
  let runtime ← must (RuntimeMetadata.ofDocument decoded.document |>.mapError toString)
  let rows ← must (JsonReader.run checks (← IO.FS.readFile expectations))
  unless !rows.isEmpty do throw (IO.userError "no call-transfer semantic controls")
  for row in rows do
    unless row.source < decoded.document.types.size && row.target < decoded.document.types.size do
      throw (IO.userError s!"{row.label}: source-edge control references an absent type")
    let actual ← must (ConcreteCovariance.relation runtime row.source row.target)
    unless actual == row.expected do
      throw (IO.userError s!"{row.label}: covariance {row.source} → {row.target}: expected {row.expected}, got {actual}")
    for endpoint in #[row.source, row.target] do
      unless (← must (ConcreteCovariance.relation runtime endpoint endpoint)) do
        throw (IO.userError s!"{row.label}: reflexive control failed for {endpoint}")
  IO.println s!"call-transfer covariance: {rows.size} exact source-edge expectations and reflexive controls passed"
