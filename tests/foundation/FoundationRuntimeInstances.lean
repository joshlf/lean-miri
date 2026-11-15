import Miri.Frontend.FoundationRuntimeInstances

open Lean Miri.Frontend.Foundation

private def checked {α : Type} : Except String α → IO α
  | .ok value => pure value
  | .error e => throw (IO.userError e)

private def reject (r : Except String RuntimeItemComponents) : IO Unit :=
  match r with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "unsupported runtime instance accepted")

/-- Fresh identity material: runtime attribute/identity joins only, not a guest
execution or a compiler-correspondence/safety proof. -/
def main (paths : List String) : IO Unit := do
  let path :: rest := paths | throw (IO.userError "expected fresh identity foundation JSON path")
  let source ← IO.FS.readFile path
  let document ← checked (Json.parse source >>= decode)
  let some body := document.bodies[0]? | throw (IO.userError "missing body")
  let definition ← checked (body.getObjValAs? Nat "definition")
  let arguments := #[ItemArgument.type (.primitive "uint" "u8")]
  let value ← checked (buildRuntimeItem document definition arguments)
  unless value.runtime.instanceId == 0 && value.instanceAbi.instanceId == 0 &&
      value.instanceAbi.abiId == 0 && value.instanceAbi.extraArgumentTypes.isEmpty do
    throw (IO.userError "runtime instance ABI identity mismatch")
  unless value.runtime.display == "identity::<u8>" && value.runtime.itemName == some "identity" do
    throw (IO.userError "runtime instance display mismatch")
  unless !value.runtime.requiresCallerLocation && !value.runtime.isForeignItem &&
      !value.runtime.isClosureLike && value.runtime.intrinsicMetadata == some none &&
      value.runtime.symbolName == none do
    throw (IO.userError "runtime instance source attributes mismatch")
  unless value.frames.crates.any (·.1 == value.frames.localCrate) do
    throw (IO.userError "local frame crate missing")
  let facts ← checked (body.getObjVal? "runtime_source")
  let invalidBody := body.setObjVal! "runtime_source" (facts.setObjVal! "rustc_intrinsic" (toJson true))
  reject (buildRuntimeItem { document with bodies := #[invalidBody] } definition arguments)
  let invalidBody := body.setObjVal! "runtime_source" (facts.setObjVal! "is_local_root" (toJson false))
  reject (buildRuntimeItem { document with bodies := #[invalidBody] } definition arguments)
  let brokenSource := document.source.setObjVal! "frame_metadata" Json.null
  reject (buildRuntimeItem { document with source := brokenSource } definition arguments)
  reject (buildRuntimeItem document definition #[.type (.array (.primitive "uint" "u8") 2)])
  IO.println "foundation runtime instances: 8 checks passed"
  match rest with
  | [] => pure ()
  | [referencePath] =>
    let referenceText ← IO.FS.readFile referencePath
    let reference ← checked (Json.parse referenceText)
    let runtime ← checked (reference.getObjVal? "compiler_runtime_queries")
    let instances ← checked (runtime.getObjValAs? (Array Json) "instances")
    let rows := instances.filter fun row =>
      (row.getObjValAs? String "display").toOption == some value.runtime.display
    unless rows.size == 1 do throw (IO.userError "missing exact compiler identity display control")
    let some row := rows[0]? | throw (IO.userError "missing compiler identity control")
    for (key, expected) in #[
        ("requires_caller_location", value.runtime.requiresCallerLocation),
        ("inline_never", value.runtime.inlineNever),
        ("is_foreign_item", value.runtime.isForeignItem),
        ("is_closure_like", value.runtime.isClosureLike)] do
      unless (← checked (row.getObjValAs? Bool key)) == expected do
        throw (IO.userError s!"compiler runtime source mismatch: {key}")
    unless (← checked (row.getObjValAs? (Option String) "item_name")) == value.runtime.itemName do
      throw (IO.userError "compiler runtime item name mismatch")
    unless (← checked (row.getObjValAs? (Array Json) "target_features")).isEmpty do
      throw (IO.userError "compiler target-feature mismatch")
    IO.println "foundation runtime instances: genuine monomorphic compiler control passed"
  | _ => throw (IO.userError "expected identity and optional ordinary export paths")
