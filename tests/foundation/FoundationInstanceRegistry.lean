import Miri.Frontend.FoundationInstanceRegistry

open Lean Miri.Frontend.Foundation

private def load (path : String) : IO Document := do
  let text ← IO.FS.readFile path
  match Json.parse text >>= decode with
  | .ok document => pure document
  | .error e => throw (IO.userError e)

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error e => throw (IO.userError e)

/-- Supply a fresh ordinary generic identity export. These are finite pool/join
checks, not fixed-interpreter execution or compiler-correspondence proofs. -/
def main (paths : List String) : IO Unit := do
  let path :: rest := paths | throw (IO.userError "expected fresh identity foundation JSON path")
  let document ← load path
  let some body := document.bodies[0]? | throw (IO.userError "missing body")
  let definition ← checked (body.getObjValAs? Nat "definition")
  let registry ← checked (InstanceRegistry.start (PhysicalTypeRegistry.start document))
  let u8 := #[ItemArgument.type (.primitive "uint" "u8")]
  let (registry, first) ← checked (registry.intern definition u8)
  unless first.id == 0 && first.bodyId == some 0 && first.definitionId == some definition &&
      first.instanceKind == .Item definition do
    throw (IO.userError "incorrect instance identity")
  let (registry, duplicate) ← checked (registry.intern definition u8)
  unless duplicate.id == first.id && registry.instances.size == 1 && registry.bodyDefinitions.size == 1 do
    throw (IO.userError "identical request was not deduplicated")
  let (registry, second) ← checked (registry.intern definition #[.type (.primitive "uint" "u16")])
  unless second.id == 1 && second.bodyId == some 1 && second.genericArgs != first.genericArgs do
    throw (IO.userError "distinct substitution lost instance identity")
  let row ← checked (document.definitions[definition]!.getObjValAs? Nat "crate_index")
  unless registry.definitions[definition]?.map (·.crateIndex) == some row do
    throw (IO.userError "source DefId changed")
  match registry.intern definition #[.constant 2] with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "wrong-kind argument accepted")
  let sourceDefinition := document.definitions[definition]!
  let changed := sourceDefinition.setObjVal! "kind" (toJson "assoc_fn")
  let broken := { document with definitions := document.definitions.set! definition changed }
  let bad ← checked (InstanceRegistry.start (PhysicalTypeRegistry.start broken))
  match bad.intern definition u8 with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "unresolved associated method accepted")
  let promoted := { document with bodies := #[body.setObjVal! "promoted_count" (toJson (1 : Nat))] }
  let promotedRegistry ← checked (InstanceRegistry.start (PhysicalTypeRegistry.start promoted))
  match promotedRegistry.intern definition u8 with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "unconstructed promoted bodies accepted")
  let duplicateRow := sourceDefinition.setObjVal! "definition_id" (toJson document.definitions.size)
  let duplicateDefinitions := { document with definitions := document.definitions.push duplicateRow }
  match InstanceRegistry.start (PhysicalTypeRegistry.start duplicateDefinitions) with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "duplicate source DefId accepted")
  IO.println "foundation instance registry: 8 checks passed"
  match rest with
  | [] => pure ()
  | [arrayPath] =>
    let document ← load arrayPath
    let some body := document.bodies[0]? | throw (IO.userError "missing array body")
    let definition ← checked (body.getObjValAs? Nat "definition")
    let registry ← checked (InstanceRegistry.start (PhysicalTypeRegistry.start document))
    let args := #[ItemArgument.type (.primitive "uint" "u16"), .constant 3]
    let (registry, first) ← checked (registry.intern definition args)
    let some (Miri.MIR.GenericArg.Const constantId) := first.genericArgs[1]?
      | throw (IO.userError "const generic identity was lost")
    let target ← checked (runtimeTargetOfTarget document.target)
    let width := target.base.pointerWidth.bits.toNat / 8
    let some (Miri.MIR.TypeConst.Value typeId tree) := registry.physical.typeConstants[constantId]?
      | throw (IO.userError "missing typed const generic")
    unless tree.nodes == #[.Leaf 3 width] && tree.root == 0 do
      throw (IO.userError "const generic bits/width changed")
    let (node, _) ← checked (registry.physical.lookup typeId)
    unless node.id == typeId do throw (IO.userError "missing const generic physical type")
    let (registry, duplicate) ← checked (registry.intern definition args)
    unless duplicate.id == first.id && registry.instances.size == 1 do
      throw (IO.userError "const generic request not deduplicated")
    let (_, second) ← checked (registry.intern definition #[.type (.primitive "uint" "u16"), .constant 4])
    unless second.id != first.id && second.genericArgs != first.genericArgs do
      throw (IO.userError "distinct const generic request aliased")
    IO.println "foundation const instance registry: 3 checks passed"
  | _ => throw (IO.userError "expected identity and optional array export paths")
