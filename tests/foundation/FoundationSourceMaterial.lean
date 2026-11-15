import Miri.Frontend.FoundationSourceMaterial

open Lean Miri Miri.Frontend.Foundation
private def checked (value : Except String α) : IO α :=
  match value with | .ok v => pure v | .error e => throw (IO.userError e)
private def check (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)
private def rejects (value : Except String α) : IO Unit :=
  match value with | .error _ => pure () | .ok _ => throw (IO.userError "invalid typed source accepted")

def main (paths : List String) : IO Unit := do
  for path in paths do
    let source ← checked (Json.parse (← IO.FS.readFile path))
    let document ← checked (decode source)
    let material ← checked (typedSourceMaterial document)
    checked material.validate
    check (material.target.triple == document.target.triple &&
      material.target.pointerSizeBits == document.target.pointerSizeBits &&
      material.target.runtimeDataLayout.isSome) "typed source target projection differs"
    let expected ← checked (sourceItemDeclarations document)
    check (material.declarations == expected && !expected.isEmpty) "typed source declaration projection differs"
    for declaration in material.declarations do
      let slots ← checked (Input.SourceDeclarations.fullParameters material.genericLayers declaration.definition)
      check (slots == declaration.parameters) "typed source full generic slots differ"
    check (material.genericMir == .unsupported && material.physical.isNone &&
      material.constraints == .unsupported) "unrepresented typed source material claimed available"
    rejects ({material with target := {material.target with triple := ""}}.validate)
    rejects ({material with genericLayers := #[]}.validate)
    let some declaration := material.declarations[0]? | throw (IO.userError "declaration absent")
    rejects ({material with declarations := material.declarations.push declaration}.validate)
    let mismatch := {declaration with parameters := declaration.parameters.push .region}
    rejects ({material with declarations := #[mismatch]}.validate)
    let some layer := material.genericLayers[0]? | throw (IO.userError "layer absent")
    let cycle := {layer with parent := some layer.owner}
    rejects ({material with genericLayers := #[cycle]}.validate)
    let some evidence := material.target.runtimeDataLayout | throw (IO.userError "target evidence absent")
    let bad := {material.target with runtimeDataLayout := some {evidence with pointerWidthBits := evidence.pointerWidthBits + 8}}
    rejects ({material with target := bad}.validate)
    IO.println s!"typed source {path}: {material.declarations.size} Item declarations, {material.genericLayers.size} lexical layers; MIR/type/constraint availability remains Unsupported"
