import Miri.Frontend.FoundationNominalLayout
import Miri.Input.Decoder
open Lean Miri Miri.Frontend.Foundation
private def expect (r : Except String α) : IO α :=
  match r with | .ok a => pure a | .error e => throw (IO.userError e)
private def check (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)
private def rejects (r : Except String α) : IO Unit :=
  match r with | .error _ => pure () | .ok _ => throw (IO.userError "unsupported nominal source accepted")

def main (paths : List String) : IO Unit := do
  let [sourcePath, referencePath] := paths | throw (IO.userError "usage: source reference")
  let d ← expect (Json.parse (← IO.FS.readFile sourcePath) >>= decode)
  let reference := (← expect (Input.decodeJson (← IO.FS.readFile referencePath))).document
  let runtime := Input.RuntimeMetadata.ofDocument reference
  let runtime ← expect (runtime.mapError toString)
  let names := #["std::result::Result", "std::boxed::Box", "std::boxed::BoxRaw", "std::alloc::Global", "std::ptr::NonNull"]
  let some dynamicId := d.types.findIdx? (fun t =>
    ((t.getObjVal? "shape" >>= fun s => s.getObjValAs? String "kind").toOption == some "dynamic"))
    | throw (IO.userError "dynamic source absent")
  let mut count := 0
  for (t, i) in d.types.zipIdx do
    let shape ← expect (t.getObjVal? "shape")
    if (shape.getObjValAs? String "kind").toOption == some "adt" then
      let defId ← expect (shape.getObjValAs? Nat "definition")
      let some defn := d.definitions[defId]? | throw (IO.userError "source definition missing")
      let path ← expect (defn.getObjValAs? String "path")
      if names.contains path then
        let actual ← expect (sourceNominalPhysicalLayout d i #[dynamicId])
        -- Source ids are never compared with compiler ids. Join the fixture's
        -- erased concrete nominal displays, then compare all converted fields.
        let some compiler := reference.types.find? (fun t =>
          t.display.startsWith path && !t.display.contains '\'' &&
          (if path == "std::alloc::Global" then t.display == path
           else (t.display.splitOn "dyn std::any::Any").length > 1))
          | throw (IO.userError s!"compiler nominal missing {path}")
        let doc := { reference with layouts := reference.layouts.set! compiler.layoutId actual }
        let modified ← expect ((Input.RuntimeMetadata.ofDocument doc).mapError toString)
        let expected ← expect ((runtime.lookup compiler.id).mapError toString)
        let got ← expect ((modified.lookup compiler.id).mapError toString)
        check (got.layout == expected.layout) s!"full nominal layout differs: {path}"
        count := count + 1
  check (count ≥ 5) "nominal chain comparison incomplete"
  rejects (sourceNominalPhysicalLayout { d with definitions := #[] } 0)
  rejects (sourceNominalPhysicalLayout d d.types.size)
  rejects (sourceNominalPhysicalLayout { d with source := Json.mkObj [] } 0)
  let root ← expect (d.types[0]!.getObjVal? "shape")
  let defId ← expect (root.getObjValAs? Nat "definition")
  let defn := d.definitions[defId]!
  let adt ← expect (defn.getObjVal? "adt")
  let repr ← expect (adt.getObjVal? "representation")
  for badRepr in #[repr.setObjVal! "flags_bits" (toJson (1 : Nat)),
      repr.setObjVal! "pack_bytes" (toJson (1 : Nat))] do
    let altered := defn.setObjVal! "adt" (adt.setObjVal! "representation" badRepr)
    rejects (sourceNominalPhysicalLayout { d with definitions := d.definitions.set! defId altered } 0)
  let variants ← expect (adt.getObjValAs? (Array Json) "variants")
  let badVariant := variants[0]!.setObjVal! "discriminant"
    (Json.mkObj [("kind", toJson "explicit"), ("definition", toJson defId)])
  let altered := defn.setObjVal! "adt" (adt.setObjVal! "variants" (toJson (variants.set! 0 badVariant)))
  rejects (sourceNominalPhysicalLayout { d with definitions := d.definitions.set! defId altered } 0)
  let seed ← expect (repr.getObjValAs? Nat "field_shuffle_seed")
  let changed := defn.setObjVal! "adt" (adt.setObjVal! "representation"
    (repr.setObjVal! "field_shuffle_seed" (toJson (seed+1))))
  let base ← expect (sourceNominalPhysicalLayout d 0)
  let altered ← expect (sourceNominalPhysicalLayout { d with definitions := d.definitions.set! defId changed } 0)
  check (altered.randomizationSeed == (UInt64.ofNat base.randomizationSeed + 3).toNat)
    "enum declaration seed not composed with both variant seeds"
  IO.println s!"PASS: {count} complete nominal layouts; seed derivation and 6 fail-closed controls"
