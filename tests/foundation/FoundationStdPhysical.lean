import Miri.Frontend.FoundationBridge
import Miri.Frontend.FoundationFnAbiRegistry
import Miri.Input.TableTail
open Lean Miri Miri.Frontend.Foundation
private def expect (r : Except String α) : IO α := match r with
| .ok a => pure a | .error e => throw (IO.userError e)
private def check (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)
private def rejects (r : Except String α) : IO Unit := match r with
| .error _ => pure () | .ok _ => throw (IO.userError "unsupported aggregate accepted")
def main (paths : List String) : IO Unit := do
  let [sourcePath, oraclePath, closureSourcePath] := paths | throw (IO.userError "usage: source projected-oracle")
  let d ← expect (Json.parse (← IO.FS.readFile sourcePath) >>= decode)
  let oracle ← expect (Json.parse (← IO.FS.readFile oraclePath))
  check ((← expect (oracle.getObjValAs? String "rustc_commit")) == "8144389c895da997dbdecaa635e41d6a50be6ffd") "oracle compiler revision"
  let expected ← expect (oracle.getObjValAs? (Array Json) "local_layouts")
  let some body := d.bodies[0]? | throw (IO.userError "std body absent")
  let definition ← expect (body.getObjValAs? Nat "definition")
  let prepared ← expect (prepareItem d definition #[])
  check (prepared.item.localTypes.size == expected.size && expected.size == 7) "std local coverage"
  let target ← expect (runtimeTargetOfTarget d.target)
  let mut registry := PhysicalTypeRegistry.start d
  for (ty,i) in prepared.item.localTypes.zipIdx do
    let (r,id) ← expect (registry.intern ty)
    registry := r
    let actual ← expect (r.runtimeLayout id)
    let some row := expected[i]? | throw (IO.userError "compiler local layout absent")
    let layout ← expect (Input.JsonReader.run Input.DecoderValues.decodeCompilerLayout row.compress)
    let compiler ← expect ((Input.RuntimeMetadata.layout target layout).mapError toString)
    check (actual.layout == compiler) s!"complete real std local{i} layout differs"
  let _ ← expect (rustFunctionAbiOfItem d definition #[])
  -- The same tuple's MaybeUnsized tail must not use the closure's AlwaysSized
  -- ordering or seed. Inspect its exact independently emitted compiler row in
  -- the closure source test separately; here check the pinned distinction.
  let some (ConcreteType.closure closureDefinition args) := prepared.item.localTypes[6]? | throw (IO.userError "std capture closure absent")
  let some (ConcreteType.tuple fields) := args.back? | throw (IO.userError "capture tuple absent")
  let tuple ← expect (physicalLayoutOfDocument d (.tuple fields))
  let closure ← expect (physicalLayoutOfDocument d (.closure closureDefinition args))
  let tupleOracle ← expect (oracle.getObjVal? "capture_tuple_layout")
  let tupleExpected ← expect (Input.JsonReader.run Input.DecoderValues.decodeCompilerLayout tupleOracle.compress)
  let tupleActual ← expect ((Input.RuntimeMetadata.layout target tuple).mapError toString)
  let tupleExpected ← expect ((Input.RuntimeMetadata.layout target tupleExpected).mapError toString)
  check (tupleActual == tupleExpected) "complete MaybeUnsized capture tuple layout differs"
  check (tuple.randomizationSeed != closure.randomizationSeed) "tuple tail seed accidentally included"
  rejects (physicalLayoutOfDocument d (.tuple (fields.extract 0 2)))
  rejects (physicalLayoutOfDocument d (.tuple #[.tuple #[], .primitive "uint" "u8", .primitive "uint" "u8"]))
  let closureSource ← expect (Json.parse (← IO.FS.readFile closureSourcePath) >>= decode)
  let wrappers ← expect (oracle.getObjValAs? (Array Json) "scalar_wrappers")
  check (wrappers.size == 2) "compiler scalar wrapper coverage"
  for wrapper in wrappers do
    let defn ← expect (wrapper.getObjVal? "definition")
    let crate ← expect (defn.getObjValAs? Nat "crate")
    let index ← expect (defn.getObjValAs? Nat "index")
    let some sourceDef := closureSource.definitions.findIdx? (fun row =>
      (row.getObjValAs? Nat "crate_index").toOption == some crate &&
      (row.getObjValAs? Nat "index").toOption == some index)
      | throw (IO.userError "source scalar wrapper declaration absent")
    let (r,id) ← expect ((PhysicalTypeRegistry.start closureSource).intern (.nominal sourceDef #[]))
    let actual ← expect (r.runtimeLayout id)
    let expected ← expect (wrapper.getObjVal? "layout")
    let expected ← expect (Input.JsonReader.run Input.DecoderValues.decodeCompilerLayout expected.compress)
    let expected ← expect ((Input.RuntimeMetadata.layout target expected).mapError toString)
    check (actual.layout == expected) "complete source scalar wrapper differs"
  IO.println "PASS actual std prepareItem, all7 complete local layouts, direct root FnAbi, both source ExitCode wrappers; unsupported aggregate controls"
