import Miri.Frontend.FoundationExecution
import Miri.Frontend.FoundationObligations

open Lean Miri.Frontend.Foundation

private def fixture (operand := "copy") (source := 1) (retag := true)
    (returnKind := "return") (dest := 0) : Except String Document := do
  let template := "{\"definition\":0,\"argument_count\":1,\"environment\":{\"parameters\":[],\"clauses\":[]},\"required_consts\":[],\"locals\":[0,0,0],\"blocks\":[{\"cleanup\":false,\"statements\":[{\"kind\":\"assign\",\"place\":{\"local\":DEST,\"projection\":[]},\"value\":{\"kind\":\"use\",\"retag\":RETAG,\"operand\":{\"kind\":\"OPERAND\",\"place\":{\"local\":SOURCE,\"projection\":[]}}}}],\"terminator\":{\"kind\":\"RETURN\"}}]}"
  let body ← Json.parse (template.replace "DEST" (toString dest) |>.replace "SOURCE" (toString source) |>.replace "RETAG" (toString retag) |>.replace "OPERAND" operand |>.replace "RETURN" returnKind)
  let declaration := Json.mkObj [("parent",Json.null),("parent_count",toJson (0 : Nat)),
    ("own_parameter_count",toJson (0 : Nat)),("self_type",Json.null)]
  let owner := Json.mkObj [("definition_id",toJson (0 : Nat)),("kind",toJson "fn"),("generic_declaration",declaration)]
  let layer := Json.mkObj [("owner",toJson (0 : Nat)),("parent",Json.null),("parent_count",toJson (0 : Nat)),
    ("self_type",Json.null),("parameters",toJson (#[] : Array Json)),("clauses",toJson (#[] : Array Json))]
  let body := body.setObjVal! "environment" (Json.mkObj [("owner",toJson (0 : Nat)),("layers",toJson #[layer])])
  let row ← Json.parse "{\"type_id\":0,\"shape\":{\"kind\":\"param\",\"index\":0}}"
  let target : Target := { triple := "x86_64-unknown-linux-gnu", dataLayout := "", pointerSizeBits := 64, endian := "little" }
  return { source := Json.null, target, definitions := #[owner], types := #[row], bodies := #[body] }

private def noObligations (document : Document) (source : Json) : Except String Unit := do
  let env ← flattenEnvironment document source
  let clauses ← env.getObjValAs? (Array Json) "clauses"
  unless clauses.isEmpty do throw "unvalidated obligations"

private def run (doc : Except String Document) (ty := ConcreteType.primitive "uint" "u8")
    (value := ExecutionValue.scalar 42) : Except String ExecutionValue := do
  let doc ← doc
  evaluateRestrictedBody doc 0 #[some ty] #[] (noObligations doc) #[value]

private def expectError (r : Except String ExecutionValue) : IO Unit :=
  match r with
  | .error _ => pure ()
  | .ok v => throw (IO.userError s!"unexpected success {repr v}")

private def synthetic : IO Unit := do
  match run (fixture) with
  | .ok (.scalar 42) => pure ()
  | other => throw (IO.userError s!"identity failed {repr other}")
  match run (fixture "move") with
  | .ok (.scalar 42) => pure ()
  | other => throw (IO.userError s!"move failed {repr other}")
  let values := ExecutionValue.aggregate #[.scalar 1, .scalar 255]
  match run (fixture) (.array (.primitive "uint" "u8") 2) values with
  | .ok v => unless v == values do throw (IO.userError "array changed")
  | .error e => throw (IO.userError e)
  expectError (run (fixture "copy" 2)) -- uninitialized read
  expectError (run (fixture "copy" 1 true "goto"))
  expectError (run (fixture "copy" 1 true "return" 2)) -- no return assignment
  expectError (run (fixture) (.primitive "uint" "u8") (.scalar 256))
  expectError (run (fixture) (.pointer "reference" (.primitive "uint" "u8")))
  expectError (run (fixture) (.primitive "bool" "") (.scalar 2))
  expectError (run (fixture) (.array (.primitive "uint" "u8") 3) values)
  IO.println "restricted structural evaluator: 10 checks passed"

private def load (path : String) : IO Document := do
  let text ← IO.FS.readFile path
  match Json.parse text >>= decode with
  | .ok d => pure d
  | .error e => throw (IO.userError e)

/-- Requires fresh `--foundation` exports, rather than committed synthetic query answers. -/
private def integration (identityPath arrayPath : String) : IO Unit := do
  let types := #[some (ConcreteType.primitive "uint" "u8")]
  let identity ← load identityPath
  let result := evaluateRestrictedBody identity 2 types #[]
    (checkEnvironment identity types #[]) #[.scalar 73]
  match result with
  | .ok (.scalar 73) => pure ()
  | other => throw (IO.userError s!"fresh identity failed: {repr other}")
  let d ← load arrayPath
  let constants := #[none, some 3]
  let value := ExecutionValue.aggregate #[.scalar 2, .scalar 3, .scalar 5]
  let result := evaluateRestrictedBody d 2 types constants
    (checkEnvironment d types constants) #[value]
  match result with
  | .ok v => unless v == value do throw (IO.userError "fresh array changed")
  | .error e => throw (IO.userError e)
  expectError (evaluateRestrictedBody d 2 types #[] (checkEnvironment d types #[]) #[value])
  let unknown ← match Json.parse "{\"path\":\"unknown::Trait\"}" with
    | .ok j => pure j
    | .error e => throw (IO.userError e)
  let invalid := { identity with definitions := identity.definitions.set! 0 unknown }
  expectError (evaluateRestrictedBody invalid 2 types #[]
    (checkEnvironment invalid types #[]) #[.scalar 73])
  IO.println "fresh foundation exports: 4 checks passed"

/-- With no arguments, run self-contained synthetic assertions. Supply fresh
identity and array_identity foundation JSON paths to additionally check exports. -/
def main (args : List String) : IO Unit := do
  synthetic
  match args with
  | [] => pure ()
  | [identityPath, arrayPath] => integration identityPath arrayPath
  | _ => throw (IO.userError "usage: RestrictedExecution.lean [IDENTITY_JSON ARRAY_JSON]")
