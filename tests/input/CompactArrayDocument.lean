import Miri.Input.Decoder
import Miri.Input.RuntimeMetadata

open Lean Miri.Input

private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)

def main (args : List String) : IO Unit := do
  unless !args.isEmpty do throw (IO.userError "expected concrete array exporter input(s)")
  for path in args do
    let text ← IO.FS.readFile path
    let decoded ← must (decodeJson text)
    let runtime ← must ((RuntimeMetadata.ofDocument decoded.document).mapError toString)
    let mut arrays := 0
    for node in decoded.document.types do
      match node.shape with
      | .array element _ constructor =>
        let element ← must ((runtime.lookup element).mapError toString)
        let layout ← must ((runtime.lookup node.id).mapError toString)
        match layout.layout.fields with
        | .Array stride count =>
          unless stride == element.layout.size && count.toNat == constructor.count do
            throw (IO.userError "source array constructor disagrees with computed compact fields")
          arrays := arrays + 1
        | _ => throw (IO.userError "array layout expanded fields instead of a formula")
      | _ => pure ()
    unless arrays > 0 do throw (IO.userError "fixture has no concrete arrays")
    let json ← must (Json.parse text)
    for version in #[8, 9, 10, 11, 12] do
      match decodeJson (json.setObjVal! "schema_version" (toJson version)).compress with
      | .error error =>
        unless error.contains "unsupported schema version" do throw (IO.userError error)
      | .ok _ => throw (IO.userError s!"obsolete schema {version} accepted")
  IO.println "PASS concrete array source constructors compute compact field formulas; old schemas rejected"
