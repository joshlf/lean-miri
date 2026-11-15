import Miri.Frontend.FoundationConst

open Lean Miri.Frontend.Foundation

private def types : Except String (Array Json) := do
  let j ← Json.parse "[{\"shape\":{\"kind\":\"uint\",\"name\":\"u8\"}},{\"shape\":{\"kind\":\"bool\"}},{\"shape\":{\"kind\":\"tuple\",\"elements\":[]}}]"
  j.getArr?

private def scalar (type : Nat) (bits : String) (size : Nat := 1) : Json :=
  Json.mkObj [("kind", toJson "constant"), ("type", toJson type),
    ("value", Json.mkObj [("kind", toJson "scalar"), ("bits", toJson bits),
      ("size_bytes", toJson size)])]

private def body (operands : Array Json) : Json :=
  Json.mkObj [("required_consts", toJson operands)]

def main : IO Unit := do
  let ts ← match types with
    | .ok value => pure value
    | .error e => throw (IO.userError e)
  for operands in [#[], #[scalar 0 "255"], #[scalar 1 "1"]] do
    match evaluateRequiredConstants ts 64 (body operands) with
    | .ok () => pure ()
    | .error e => throw (IO.userError e)
  let param := Json.mkObj [("kind", toJson "constant"), ("type", toJson (0 : Nat)),
    ("value", Json.mkObj [("kind", toJson "param"), ("index", toJson (1 : Nat))])]
  match evaluateRequiredConstants ts 64 (body #[param]) #[none, some ⟨0, 42, 1⟩] with
  | .ok () => pure ()
  | .error e => throw (IO.userError e)
  -- The second obligation is mandatory even when no MIR instruction uses it.
  for operands in [#[scalar 0 "0", scalar 0 "256"], #[scalar 0 "1" 2],
      #[scalar 1 "2"], #[scalar 3 "0"], #[scalar 0 "bad"], #[param],
      #[Json.mkObj [("kind", toJson "copy")]]] do
    match evaluateRequiredConstants ts 64 (body operands) with
    | .error _ => pure ()
    | .ok () => throw (IO.userError "malformed or unresolved required const accepted")
  match evaluateRequiredConstants ts 64 (body #[param]) #[none, some ⟨1, 1, 1⟩] with
  | .error _ => pure ()
  | .ok () => throw (IO.userError "mismatched parameter type accepted")
  IO.println "foundation required constants: 4 successes and 8 rejection controls passed"
