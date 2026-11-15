import Lean

/-! Minimal live provider client. stdout is reserved for newline-delimited JSON. -/
open Lean

private def query (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) (name : String) : IO (Nat × Nat) := do
  let start ← IO.monoNanosNow
  stdout.putStrLn ((Json.mkObj [("op", toJson "layout_of"), ("type", toJson name)]).compress)
  stdout.flush
  let response ← match Json.parse (← stdin.getLine) with
    | .ok value => pure value
    | .error error => throw (IO.userError error)
  let size ← match response.getObjValAs? Nat "size" with
    | .ok value => pure value
    | .error error => throw (IO.userError error)
  let align ← match response.getObjValAs? Nat "align" with
    | .ok value => pure value
    | .error error => throw (IO.userError error)
  if align != (if name == "u64" then 8 else 1) then
    throw (IO.userError s!"wrong alignment for Foo<{name}>")
  return (size, (← IO.monoNanosNow) - start)

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  stdout.putStrLn "{\"op\":\"ready\"}"
  stdout.flush
  let mut roundtrips := #[]
  for _ in [:10] do
    let (size8, roundtrip8) ← query stdin stdout "u8"
    unless size8 == 2 do
      throw (IO.userError "Foo<u8> must be two bytes")
    roundtrips := roundtrips.push roundtrip8
    let (size64, roundtrip64) ← query stdin stdout "u64"
    unless size64 == 16 do
      throw (IO.userError "Foo<u64> must be sixteen bytes")
    roundtrips := roundtrips.push roundtrip64
  -- The rustc callback and TyCtxt must remain alive through this delayed request.
  IO.sleep 100
  let (size, delayedNs) ← query stdin stdout "u64"
  unless size == 16 do throw (IO.userError "delayed Foo<u64> query failed")
  roundtrips := roundtrips.push delayedNs
  stdout.putStrLn ((Json.mkObj [("op", toJson "done"),
    ("lean_roundtrip_ns", toJson roundtrips)]).compress)
  stdout.flush
