import Miri.Frontend.FoundationCompilerEntryProgram
import Miri.Input.Decoder

open Lean Miri Miri.Frontend.Foundation

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

/-- Compare the computed dummy Rust start signature ABI against its independent
fresh schema12 compiler request, including every mode attribute and complete
physical layout. Shared primitive/argument roles translate compilation-local IDs. -/
def main (paths : List String) : IO Unit := do
  let [foundationPath, compilerPath] := paths | throw (IO.userError "expected finite and ordinary compiler-entry exports")
  let document ← checked (Json.parse (← IO.FS.readFile foundationPath) >>= decode)
  let computed ← checked (restrictedCompilerEntryProgram document)
  let compiler ← checked (Input.decodeJson (← IO.FS.readFile compilerPath))
  let actual := compiler.document
  let some computedHelper := computed.input.queries.functionFacts.helperSignatures[0]?
    | throw (IO.userError "computed helper signature absent")
  unless computed.input.queries.functionFacts.helperSignatures.size == 1 do
    throw (IO.userError "computed helper signature domain broadened")
  let some entry := actual.queries.main.entries[0]? | throw (IO.userError "compiler main entry absent")
  let some start := entry.signature.startResolution | throw (IO.userError "compiler start resolution absent")
  let some startRow := actual.queries.instanceAbis.find? (fun row =>
      row.instanceId == start.instanceId && row.extraArgumentTypes.isEmpty)
    | throw (IO.userError "compiler start ABI query absent")
  let some startAbi := actual.functionAbis[startRow.abiId]? | throw (IO.userError "compiler start ABI absent")
  let selected := actual.queries.functionFacts.helperSignatures.filter fun row =>
    row.signature.inputs == startAbi.arguments.map (·.typeId) &&
    row.signature.output == startAbi.returnValue.typeId && row.signature.safety == .Safe &&
    row.signature.abi == .Rust && !row.signature.cVariadic && !row.splatted
  let some actualHelper := selected[0]? | throw (IO.userError "compiler exact dummy start signature absent")
  unless selected.size == 1 && computedHelper.signature.safety == .Safe &&
      computedHelper.signature.abi == .Rust && !computedHelper.signature.cVariadic && !computedHelper.splatted do
    throw (IO.userError "dummy start signature key differs")
  let some computedAbi := computed.input.functionAbis[computedHelper.abiId]? | throw (IO.userError "computed helper ABI absent")
  let some actualAbi := actual.functionAbis[actualHelper.abiId]? | throw (IO.userError "compiler helper ABI absent")
  unless computedAbi.arguments.size == actualAbi.arguments.size &&
      computedAbi.callingConvention == actualAbi.callingConvention &&
      computedAbi.canUnwind == actualAbi.canUnwind && computedAbi.cVariadic == actualAbi.cVariadic &&
      computedAbi.fixedCount == actualAbi.fixedCount do
    throw (IO.userError "helper ABI header differs")
  let target ← checked (runtimeTargetOfTarget document.target)
  for (left, right) in (computedAbi.arguments.push computedAbi.returnValue).zip
      (actualAbi.arguments.push actualAbi.returnValue) do
    unless left.mode == right.mode do throw (IO.userError "helper ABI mode/attributes differ")
    let some leftNode := computed.input.types[left.typeId]? | throw (IO.userError "computed helper type absent")
    let some rightNode := actual.types[right.typeId]? | throw (IO.userError "compiler helper type absent")
    unless leftNode.shapeKind == rightNode.shapeKind do throw (IO.userError "helper argument type role differs")
    let some leftLayout := computed.input.layouts[left.layoutId]? | throw (IO.userError "computed helper layout absent")
    let some rightLayout := actual.layouts[right.layoutId]? | throw (IO.userError "compiler helper layout absent")
    let left ← checked ((Input.RuntimeMetadata.layout target leftLayout).mapError toString)
    let right ← checked ((Input.RuntimeMetadata.layout target rightLayout).mapError toString)
    unless left == right do throw (IO.userError "helper complete physical layout differs")
  IO.println "foundation compiler-entry helper: exact signature domain, FnAbi header/modes/attributes/full layouts match fresh compiler query"
