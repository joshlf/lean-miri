import Miri.Frontend.FoundationNominalLayout
import Miri.Input.Decoder
import Miri.Frontend.FoundationPhysicalRegistry
import Miri.Frontend.FoundationBridge
import Miri.Frontend.FoundationPrimitiveFacts
open Lean Miri Miri.Frontend.Foundation
private def expect (r : Except String α) : IO α :=
  match r with | .ok a => pure a | .error e => throw (IO.userError e)
private def check (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)
private def rejects (r : Except String α) : IO Unit :=
  match r with | .error _ => pure () | .ok _ => throw (IO.userError "unsupported nominal source accepted")

private def compareTree (fuel : Nat) (r : PhysicalTypeRegistry) (expected : Input.RuntimeMetadata)
    (a b : Nat) : IO Unit := do
  let .succ fuel := fuel | throw (IO.userError "shape comparison fuel")
  let (left, _) ← expect (r.lookup a)
  let right ← expect ((expected.node b).mapError toString)
  let l ← expect (r.runtimeLayout a)
  let e ← expect ((expected.lookup b).mapError toString)
  check (l.layout == e.layout) "canonical child layout differs"
  match left.shape, right.shape with
  | .adt a, .adt b =>
    check (a.kind == b.kind && a.representation == b.representation &&
      a.args.size == b.args.size && a.variants.size == b.variants.size) "nominal source representation differs"
    for (a,b) in a.args.zip b.args do
      let .Type a := a | throw (IO.userError "nominal arg")
      let .Type b := b | throw (IO.userError "compiler nominal arg")
      compareTree fuel r expected a b
    for (a,b) in a.variants.zip b.variants do
      check (a.index == b.index && a.name == b.name && a.fields.size == b.fields.size) "variant identity differs"
      for (a,b) in a.fields.zip b.fields do
        check (a.index == b.index && a.name == b.name) "field identity differs"
        compareTree fuel r expected a.typeId b.typeId
  | .patternType a .notNull, .patternType b .notNull
  | .rawPointer a .Not, .rawPointer b .Not => compareTree fuel r expected a b
  | .dynamicTraitObject a _ ar, .dynamicTraitObject b _ br =>
    check (a.size == b.size && ar == br) "dynamic identity shape differs"
  | .int a, .int b => check (a == b) "primitive identity differs"
  | _, _ => throw (IO.userError "canonical shape differs")

def main (paths : List String) : IO Unit := do
  let [sourcePath, referencePath, stdPath] := paths | throw (IO.userError "usage: source reference std-source")
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
  let some sourceBody := d.bodies[0]? | throw (IO.userError "source body missing")
  let definition ← expect (sourceBody.getObjValAs? Nat "definition")
  let prepared ← expect (prepareItem d definition #[])
  let some demanded := prepared.item.localTypes[0]? | throw (IO.userError "return local missing")
  let (registry, rootId) ← expect ((PhysicalTypeRegistry.start d).intern demanded)
  let some body := reference.bodies[0]? | throw (IO.userError "compiler body missing")
  let some expectedId := body.mir.locals[0]? | throw (IO.userError "compiler return missing")
  compareTree 128 registry runtime rootId expectedId
  let (again, againId) ← expect (registry.intern demanded)
  check (againId == rootId && again.types.size == registry.types.size) "nominal canonical dedup failed"
  rejects (primitiveFactsDomain demanded) -- nominal trait/drop facts remain unavailable
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
  let std ← expect (Json.parse (← IO.FS.readFile stdPath) >>= decode)
  let some stdBody := std.bodies[0]? | throw (IO.userError "std body absent")
  let locals ← expect (stdBody.getObjValAs? (Array Nat) "locals")
  let some resultId := locals[5]? | throw (IO.userError "std local5 absent")
  let concrete ← expect (typeExpr std resultId >>= instantiate #[] #[] >>= eraseRegions)
  let (stdRegistry, stdId) ← expect ((PhysicalTypeRegistry.start std).intern concrete)
  compareTree 128 stdRegistry runtime stdId expectedId
  rejects (primitiveFactsDomain concrete)
  IO.println s!"PASS: {count} complete nominal layouts, canonical recursive identities, actual std local5; seed derivation and 7 fail-closed controls"
