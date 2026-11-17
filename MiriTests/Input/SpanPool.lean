import Miri.Input.LowerMIR
import Miri.Input.TableCore

open Miri Miri.Input

private def span : SourceSpanData := {
  lo := 3, hi := 8,
  start := ⟨1, 2⟩, «end» := ⟨1, 7⟩, context := 0, file := 0, runtimeFile := 0, expansionLocation := ⟨0,1,3⟩ }

private def check (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

def main : IO Unit := do
  let fields := "\"is_dummy\":false,\"lo\":3,\"hi\":8,\"start\":{\"line\":1,\"column\":2}," ++
    "\"end\":{\"line\":1,\"column\":7},\"file\":0,\"runtime_file\":0,\"expansion_location\":{\"file\":0,\"line\":1,\"column\":3},\"ctxt\":"
  let text := "{ " ++ fields ++ "7}"
  let .ok decoded := JsonReader.run DecoderValues.parseSourceSpan text
    | throw (IO.userError "typed source context rejected")
  check (decoded.context == 7) "source context identity changed"
  for invalid in #["\"#7\"", "{}", "true", "null"] do
    check (!(JsonReader.run DecoderValues.parseSourceSpan ("{" ++ fields ++ invalid ++ "}")).isOk)
      "non-numeric source context accepted"
  let tables : CompilerTables := {spans := #[span, span], definitions := #[], typeConstants := #[]}
  for id in #[0, 1] do
    let .ok (reference, after) := lowerCompilerSpan tables ⟨id⟩
      | throw (IO.userError "valid span ID rejected")
    check (reference.id == id) "equal span payloads collapsed distinct IDs"
    check (after.spans == tables.spans) "span lookup changed definitions"
    check (after.definitions == tables.definitions && after.typeConstants == tables.typeConstants)
      "span lookup changed another pool"
  for id in #[2, 999999] do
    check (!(lowerCompilerSpan tables ⟨id⟩).isOk) "out of bounds span accepted"
  IO.println "span IDs preserve definitions and reject out of bounds references"
