import Miri.Frontend.FoundationEnum

open Lean Miri.Frontend.Foundation

private def checked {α : Type} (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)

private def requireFailure {α : Type} (value : Except String α) : IO Unit :=
  match value with | .error _ => pure () | .ok _ => throw (IO.userError "malformed enum source accepted")

/-- Source declaration and logical ordinals compared with a fresh independent
compiler export. No physical enum layout is constructed or executed. -/
def main (paths : List String) : IO Unit := do
  let [finitePath,compilerPath] := paths | throw (IO.userError "expected finite and compiler enum exports")
  let document ← checked (Json.parse (← IO.FS.readFile finitePath) >>= decode)
  let some choice := document.definitions.find? (fun row => (row.getObjValAs? String "path").toOption == some "Choice")
    | throw (IO.userError "Choice declaration missing")
  let id ← checked (choice.getObjValAs? Nat "definition_id")
  let declaration ← checked (enumDeclarationSource document id)
  let ordinals ← checked (implicitEnumOrdinals declaration)
  unless ordinals == #[0,1] do throw (IO.userError "wrong implicit ordinals")
  let some value := declaration.variants[1]? | throw (IO.userError "Value variant absent")
  unless value.fields.size == 1 do throw (IO.userError "generic field absent")
  let some field := value.fields[0]? | throw (IO.userError "generic field absent")
  let fieldType ← checked (typeExpr document field.type)
  match fieldType with
  | .parameter 0 => pure ()
  | _ => throw (IO.userError "enum field template lost generic parameter")
  let ordinary ← checked (Json.parse (← IO.FS.readFile compilerPath))
  let types ← checked (ordinary.getObjValAs? (Array Json) "types")
  let some concrete := types.find? (fun row => (row.getObjValAs? String "display").toOption == some "Choice<u8>")
    | throw (IO.userError "compiler concrete Choice absent")
  let shape ← checked (concrete.getObjVal? "shape")
  unless (← checked (shape.getObjVal? "representation")) == declaration.representation do
    throw (IO.userError "source representation differs from compiler")
  let rawDefinitions ← checked (ordinary.getObjValAs? (Array Json) "definitions")
  let compilerId ← checked (shape.getObjValAs? Nat "def_id")
  let some raw := rawDefinitions[compilerId]? | throw (IO.userError "compiler definition absent")
  unless (← checked (raw.getObjValAs? Nat "crate")) == (← checked (choice.getObjValAs? Nat "crate_index")) &&
      (← checked (raw.getObjValAs? Nat "index")) == (← checked (choice.getObjValAs? Nat "index")) do
    throw (IO.userError "source/compiler enum identity mismatch")
  let facts ← checked (concrete.getObjVal? "compiler_facts")
  let discrId ← checked (facts.getObjValAs? Nat "discriminants")
  let discriminants ← checked (ordinary.getObjValAs? (Array Json) "discriminants")
  let some discr := discriminants[discrId]? | throw (IO.userError "compiler discriminants absent")
  let values ← checked (discr.getObjValAs? (Array Json) "values")
  unless values.size == ordinals.size do throw (IO.userError "compiler variant count differs")
  for index in [:values.size] do
    let some actual := values[index]? | throw (IO.userError "compiler discriminant absent")
    let some ordinal := ordinals[index]? | throw (IO.userError "source ordinal absent")
    unless (← checked (actual.getObjValAs? Nat "variant")) == index &&
        (← checked (actual.getObjValAs? String "bits")) == toString ordinal do
      throw (IO.userError "logical source ordinal differs from compiler")
    let ty ← checked (actual.getObjValAs? Nat "type")
    let some node := types[ty]? | throw (IO.userError "compiler discriminant type absent")
    unless (← checked (node.getObjValAs? String "display")) == "isize" do
      throw (IO.userError "default logical discriminant type differs")
  let some explicit := document.definitions.find? (fun row => (row.getObjValAs? String "path").toOption == some "Explicit")
    | throw (IO.userError "explicit declaration missing")
  let explicitDeclaration ← checked (enumDeclarationSource document (← checked (explicit.getObjValAs? Nat "definition_id")))
  requireFailure (implicitEnumOrdinals explicitDeclaration)
  let some first := declaration.variants[0]? | throw (IO.userError "first variant absent")
  let bad := { declaration with variants := declaration.variants.mapIdx (fun index entry => if index == 0 then { first with discriminant := .relative 1 } else entry) }
  requireFailure (implicitEnumOrdinals bad)
  let adt ← checked (choice.getObjVal? "adt")
  let sourceVariants ← checked (adt.getObjValAs? (Array Json) "variants")
  let badVariants := sourceVariants.mapIdx fun index entry =>
    if index == 1 then entry.setObjVal! "index" (toJson (0 : Nat)) else entry
  let badChoice := choice.setObjVal! "adt" (adt.setObjVal! "variants" (toJson badVariants))
  let badDocument := { document with definitions := document.definitions.mapIdx fun index entry =>
    if index == id then badChoice else entry }
  requireFailure (enumDeclarationSource badDocument id)
  let badDistances := sourceVariants.mapIdx fun index entry =>
    if index == 1 then entry.setObjVal! "discriminant"
      (Json.mkObj [("kind",toJson "relative"),("distance",toJson (0 : Nat))]) else entry
  let wrongDistance := choice.setObjVal! "adt" (adt.setObjVal! "variants" (toJson badDistances))
  requireFailure (enumDeclarationSource { document with definitions := document.definitions.mapIdx fun index entry =>
    if index == id then wrongDistance else entry } id)
  -- A missing referenced source definition cannot become an empty declaration.
  requireFailure (enumDeclarationSource { document with definitions := #[] } id)
  IO.println "foundation enum: generic fields/repr/raw identity and implicit logical isize ordinals match compiler; explicit evaluation and malformed source reject; physical layout unprovided"
