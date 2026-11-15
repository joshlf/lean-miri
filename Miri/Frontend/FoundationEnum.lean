import Miri.Frontend.Foundation

/-! Enum declaration source, not physical tag/niche layout. Explicit embedded
constant identities are retained, but their values are not guessed. -/
namespace Miri.Frontend.Foundation
open Lean

inductive EnumDiscriminantSource where
  | relative (distance : Nat)
  | explicit (definition : Nat)
  deriving BEq, Repr

structure EnumFieldSource where
  definition : Nat
  name : String
  type : Nat
  deriving Repr

structure EnumVariantSource where
  definition : Nat
  name : String
  constructor : Option (Nat × String)
  fieldsNonExhaustive : Bool
  discriminant : EnumDiscriminantSource
  fields : Array EnumFieldSource
  deriving Repr

structure EnumDeclarationSource where
  definition : Nat
  environment : Json
  representation : Json
  variantsNonExhaustive : Bool
  variants : Array EnumVariantSource

private def checkedDefinition (document : Document) (id : Nat) (kind : String) : Except String Unit := do
  let some row := document.definitions[id]? | throw "enum source definition absent"
  unless (← row.getObjValAs? Nat "definition_id") == id do throw "enum definition identity mismatch"
  unless (← row.getObjValAs? String "kind") == kind do throw "enum source definition kind mismatch"

/-- Validate the complete ordered declaration while retaining source expressions.
This does not authorize a physical ADT type or provide enum layout metadata. -/
def enumDeclarationSource (document : Document) (definition : Nat) : Except String EnumDeclarationSource := do
  checkedDefinition document definition "Enum"
  let some row := document.definitions[definition]? | throw "enum declaration absent"
  let adt ← row.getObjVal? "adt"
  unless (← adt.getObjValAs? String "kind") == "enum" do throw "enum declaration material absent"
  let rows ← adt.getObjValAs? (Array Json) "variants"
  let mut variants : Array EnumVariantSource := #[]
  let mut lastExplicit : Option Nat := none
  for index in [:rows.size] do
    let some source := rows[index]? | throw "enum variant missing"
    unless (← source.getObjValAs? Nat "index") == index do throw "enum variant order mismatch"
    let variantDefinition ← source.getObjValAs? Nat "definition"
    checkedDefinition document variantDefinition "Variant"
    let discriminantSource ← source.getObjVal? "discriminant"
    let discriminant : EnumDiscriminantSource ← match ← discriminantSource.getObjValAs? String "kind" with
      | "relative" => do
        let distance ← discriminantSource.getObjValAs? Nat "distance"
        let expected := match lastExplicit with | some prior => index - prior | none => index
        unless distance == expected do throw "enum relative discriminant source distance mismatch"
        pure (.relative distance)
      | "explicit" => do
        let embedded ← discriminantSource.getObjValAs? Nat "definition"
        checkedDefinition document embedded "AnonConst"
        lastExplicit := some index
        pure (.explicit embedded)
      | _ => throw "enum discriminant source unsupported"
    let constructorSource ← source.getObjVal? "constructor"
    let constructor ← if constructorSource == Json.null then pure none else do
      let id ← constructorSource.getObjValAs? Nat "definition"
      let some ctor := document.definitions[id]? | throw "enum constructor absent"
      unless (← ctor.getObjValAs? Nat "definition_id") == id do throw "enum constructor identity mismatch"
      let kind ← constructorSource.getObjValAs? String "kind"
      let expected ← match kind with
        | "function" => pure "Ctor(Variant, Fn)"
        | "constant" => pure "Ctor(Variant, Const)"
        | _ => throw "enum constructor kind unsupported"
      unless (← ctor.getObjValAs? String "kind") == expected do throw "enum constructor definition kind mismatch"
      pure (some (id,kind))
    let fieldsSource ← source.getObjValAs? (Array Json) "fields"
    let fields ← fieldsSource.mapIdxM fun fieldIndex field => do
      unless (← field.getObjValAs? Nat "index") == fieldIndex do throw "enum field order mismatch"
      let id ← field.getObjValAs? Nat "definition"
      checkedDefinition document id "Field"
      let type ← field.getObjValAs? Nat "type"
      unless type < document.types.size do throw "enum field type absent"
      pure { definition := id, name := ← field.getObjValAs? String "name", type := type : EnumFieldSource }
    variants := variants.push {
      definition := variantDefinition, name := ← source.getObjValAs? String "name", constructor
      fieldsNonExhaustive := ← source.getObjValAs? Bool "fields_non_exhaustive", discriminant, fields }
  let environment ← adt.getObjVal? "environment"
  let representation ← adt.getObjVal? "representation"
  let variantsNonExhaustive ← adt.getObjValAs? Bool "variants_non_exhaustive"
  return { definition, environment, representation, variantsNonExhaustive, variants }


/-- The logical ordinal of all-implicit variants only. These naturals are not
physical tag values, niche encodings, or evaluated explicit discriminants. -/
def implicitEnumOrdinals (declaration : EnumDeclarationSource) : Except String (Array Nat) := do
  declaration.variants.mapIdxM fun index variant => do
    match variant.discriminant with
    | .relative distance =>
      unless distance == index do throw "enum implicit source distance mismatch"
      pure index
    | .explicit _ => throw "explicit enum discriminant evaluation unsupported"

end Miri.Frontend.Foundation
