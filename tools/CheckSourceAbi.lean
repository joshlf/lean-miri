import Miri.Input.Decoder
import Miri.Input.CallResolution
import MiriTests.Input.OracleAbi
import Miri.Input.SourceAbiRuntime

open Miri.Input

private structure OracleRow where
  key : Nat
  extra : Array TypeId
  abi : OracleAbi.FunctionAbi

private structure Oracle where
  layouts : Array Layout
  instances : Array OracleRow
  pointers : Array OracleRow

private def parseRow (key : String) : JsonReader.Parser OracleRow := do
  let (subject, extra, abi) ← JsonReader.object (none, none, none) fun (subject, extra, abi) field => do
    if field == key then return (some (← JsonReader.natural), extra, abi)
    match field with
    | "extra_argument_types" => return (subject, some (← JsonReader.array JsonReader.natural), abi)
    | "abi" => return (subject, extra, some (← OracleAbi.parseFunctionAbi "$oracle.abi"))
    | _ => JsonReader.skipValue; return (subject, extra, abi)
  return ⟨← JsonReader.required subject key, ← JsonReader.required extra "extra_argument_types",
    ← JsonReader.required abi "abi"⟩

private def parseOracle : JsonReader.Parser Oracle := do
  let value ← JsonReader.object (none : Option Oracle) fun value key => do
    if key != "abi" then JsonReader.skipValue; return value
    let (layouts, instances, pointers) ← JsonReader.object (none, none, none) fun (layouts, instances, pointers) key => do
      match key with
      | "abi_layouts" => return (some (← JsonReader.array (DecoderValues.parseLayout "$oracle.abi_layouts")), instances, pointers)
      | "instances" => return (layouts, some (← JsonReader.array (parseRow "instance_id")), pointers)
      | "pointers" => return (layouts, instances, some (← JsonReader.array (parseRow "type_id")))
      | _ => JsonReader.skipValue; return (layouts, instances, pointers)
    return some ⟨← JsonReader.required layouts "abi_layouts", ← JsonReader.required instances "instances",
      ← JsonReader.required pointers "pointers"⟩
  JsonReader.required value "abi"

def main (args : List String) : IO UInt32 := do
  let [path, oraclePath] := args | throw (IO.userError "usage: CheckSourceAbi <fresh-export.json> <oracle.json>")
  let input ← match ← decodeFile path with
    | .ok input => pure input
    | .error reason => throw (IO.userError s!"input decode failed: {reason}")
  let document := input.document
  let oracle ← IO.FS.readFile oraclePath
  let oracle ← match JsonReader.run parseOracle oracle with
    | .ok oracle => pure oracle
    | .error reason => throw (IO.userError s!"oracle decode failed: {reason}")
  let runtime ← match RuntimeMetadata.ofDocument document with
    | .ok runtime => pure runtime
    | .error reason => throw (IO.userError s!"target decode failed: {reason}")
  let program ← match lowerProgram document with
    | .ok program => pure program
    | .error reason => throw (IO.userError s!"MIR lowering failed: {reason}")
  let context : CompilerFacts.Context := ⟨runtime, program, none⟩
  let mut checked := 0
  let mut errors := 0
  for row in oracle.instances do
    let actual := SourceAbiRuntime.ofInstance context row.key row.extra
    let expected := OracleAbi.functionAbi runtime oracle.layouts row.abi
    match actual, expected with
    | .ok actual, .ok expected =>
      checked := checked + 1
      unless actual == expected do
        errors := errors + 1
        IO.println s!"instance {row.key} extra={reprStr row.extra}: ABI differs\ncomputed={reprStr actual}\nrustc={reprStr expected}"
    | .error reason, _ =>
      errors := errors + 1
      IO.println s!"instance {row.key}: calculation failed: {reason}"
    | _, .error reason =>
      errors := errors + 1
      IO.println s!"instance {row.key}: compiler oracle decode failed: {reason}"
  for row in oracle.pointers do
    let actual := do
      let node ← runtime.node row.key |>.mapError toString
      let .functionPointer signature _ := node.shape | throw "oracle pointer type is not FnPtr"
      SourceAbiRuntime.ofSignature context signature row.extra
    let expected := OracleAbi.functionAbi runtime oracle.layouts row.abi
    match actual, expected with
    | .ok actual, .ok expected =>
      checked := checked + 1
      unless actual == expected do
        errors := errors + 1
        IO.println s!"pointer {row.key} extra={reprStr row.extra}: ABI differs\ncomputed={reprStr actual}\nrustc={reprStr expected}"
    | .error reason, _ | _, .error reason =>
      errors := errors + 1
      IO.println s!"pointer {row.key}: {reason}"
  IO.println s!"source ABI: compared={checked}, failures={errors}; finite compiler comparison only"
  if checked == 0 && errors == 0 && document.bodies.isEmpty && !document.rootDeclarations.isEmpty then
    IO.println "source ABI: not applicable: declaration-only input"
    return 0
  return if errors == 0 && checked > 0 then 0 else 1
