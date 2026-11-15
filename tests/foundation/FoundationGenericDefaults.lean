import Miri.Frontend.FoundationGenericDefaults
import Miri.Frontend.FoundationObligations

open Lean Miri.Frontend.Foundation
private def checked {α : Type} (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def failure {α : Type} (value : Except String α) : IO Unit :=
  match value with | .error _ => pure () | .ok _ => throw (IO.userError "invalid/missing generic source accepted")

def main (paths : List String) : IO Unit := do
  let [finitePath,compilerPath] := paths | throw (IO.userError "expected finite and compiler generic-default exports")
  let document ← checked (Json.parse (← IO.FS.readFile finitePath) >>= decode)
  let some packet := document.definitions.find? (fun row =>
      (row.getObjValAs? String "path").toOption == some "Packet")
    | throw (IO.userError "Packet definition absent")
  let adt ← checked (packet.getObjVal? "adt")
  let environment ← checked (adt.getObjVal? "environment")
  let flatEnvironment ← checked (flattenEnvironment document environment)
  let parameters ← checked (flatEnvironment.getObjValAs? (Array Json) "parameters")
  let [parameter] := parameters.toList | throw (IO.userError "expected one Packet parameter")
  let some source ← checked (typeParameterDefaultSource document parameter)
    | throw (IO.userError "captured default absent")
  let defaultType ← checked (instantiate #[] #[] source)
  unless sameConcrete 1024 defaultType (.primitive "uint" "u8") do throw (IO.userError "wrong captured default template")
  -- The actual root uses u16; a declaration default cannot replace that argument
  -- or make the missing-argument environment check succeed.
  failure (checkEnvironment document #[] #[] environment)
  let _ ← checked (checkEnvironment document #[some (.primitive "uint" "u16")] #[none] environment)
  let compiler ← checked (Json.parse (← IO.FS.readFile compilerPath))
  let types ← checked (compiler.getObjValAs? (Array Json) "types")
  let some actual := types.find? (fun row =>
      (row.getObjValAs? String "display").toOption == some "Packet<u16>")
    | throw (IO.userError "compiler explicit specialization absent")
  let shape ← checked (actual.getObjVal? "shape")
  let variants ← checked (shape.getObjValAs? (Array Json) "variants")
  let [variant] := variants.toList | throw (IO.userError "compiler Packet variant absent")
  let fields ← checked (variant.getObjValAs? (Array Json) "fields")
  let [field] := fields.toList | throw (IO.userError "compiler Packet field absent")
  let fieldType ← checked (field.getObjValAs? Nat "type")
  let some node := types[fieldType]? | throw (IO.userError "compiler field type absent")
  unless (← checked (node.getObjValAs? String "display")) == "u16" do throw (IO.userError "compiler explicit argument replaced by default")
  let some defaultNode := types.find? (fun row =>
      let display := (row.getObjValAs? String "display").toOption
      display == some "Packet" || display == some "Packet<u8>")
    | throw (IO.userError "compiler default specialization absent")
  let defaultShape ← checked (defaultNode.getObjVal? "shape")
  let defaultVariants ← checked (defaultShape.getObjValAs? (Array Json) "variants")
  let [defaultVariant] := defaultVariants.toList | throw (IO.userError "compiler default variant absent")
  let defaultFields ← checked (defaultVariant.getObjValAs? (Array Json) "fields")
  let [defaultField] := defaultFields.toList | throw (IO.userError "compiler default field absent")
  let defaultFieldType ← checked (defaultField.getObjValAs? Nat "type")
  let some defaultFieldNode := types[defaultFieldType]? | throw (IO.userError "compiler default field type absent")
  unless (← checked (defaultFieldNode.getObjValAs? String "display")) == "u8" do
    throw (IO.userError "source declared default differs from compiler specialization")
  failure (typeParameterDefaultSource document (parameter.setObjVal! "default" Json.null))
  failure (typeParameterDefaultSource document (parameter.setObjVal! "has_default" (toJson false)))
  failure (typeParameterDefaultSource { document with definitions := #[] } parameter)
  IO.println "foundation generic default: retained u8 template; explicit u16 compiler field agrees; absent args/default source and inconsistent flags reject"
