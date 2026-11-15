import Miri.Frontend.FoundationSource

open Lean Miri.Frontend.Foundation

private def fixture (scope : Nat := 0) (parent : String := "null")
    (localCount : String := "[0]") : Except String Json := do
  let span := "{\"is_dummy\":false,\"lo\":10,\"hi\":20,\"ctxt\":\"#0\",\"file\":\"fixture.rs\",\"start\":{\"line\":1,\"column\":0},\"end\":{\"line\":1,\"column\":10}}"
  let info := "{\"span\":" ++ span ++ ",\"scope\":" ++ toString scope ++ "}"
  Json.parse ("{\"locals\":" ++ localCount ++ ",\"blocks\":[{\"statements\":[]}],\"source_metadata\":{\"span\":" ++ span ++
    ",\"definition_span\":" ++ span ++ ",\"phase\":{\"kind\":\"runtime\",\"phase\":\"optimized\"},\"injection_phase\":null,\"locals\":[{\"mutable\":true,\"source_info\":" ++ info ++
    "}],\"scopes\":[{\"span\":" ++ span ++ ",\"parent\":" ++ parent ++ ",\"inlined_parent\":null}],\"blocks\":[{\"statements\":[],\"terminator\":" ++ info ++ "}]}}")

def main : IO Unit := do
  match fixture >>= validateSourceMetadata with
  | .ok () => pure ()
  | .error e => throw (IO.userError e)
  for input in [fixture 1, fixture 0 "0", fixture 0 "null" "[]"] do
    match input >>= validateSourceMetadata with
    | .error _ => pure ()
    | .ok () => throw (IO.userError "malformed source metadata accepted")
  let markers ← match Json.parse "{\"locals\":[0,0,0],\"blocks\":[{\"statements\":[{\"kind\":\"storage_live\",\"local\":1},{\"kind\":\"storage_dead\",\"local\":2}]}]}" >>= alwaysStorageLive with
    | .ok value => pure value
    | .error e => throw (IO.userError e)
  unless markers == #[true, false, false] do throw (IO.userError "storage marker derivation mismatch")
  IO.println "foundation source metadata: valid capture and 3 rejection controls passed"
