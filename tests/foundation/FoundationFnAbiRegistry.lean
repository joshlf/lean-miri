import Miri.Frontend.FoundationFnAbiRegistry

open Lean Miri.Frontend.Foundation

private def rejects (result : Except String (PhysicalTypeRegistry × Miri.Input.FunctionAbi)) : IO Unit := do
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "unsupported registry FnAbi accepted")

/-- Uses an identity<T> export. Checks fixed-interpreter layout conversion and
registry joins; does not run a MIR body or claim semantic correspondence. -/
def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected fresh identity foundation JSON")
  let document ← IO.ofExcept (decode (← IO.ofExcept (Json.parse (← IO.FS.readFile path))))
  let some body := document.bodies[0]? | throw (IO.userError "missing body")
  let definition ← IO.ofExcept (body.getObjValAs? Nat "definition")
  for ty in [ConcreteType.primitive "bool" "", .primitive "int" "i128",
      .tuple #[], .array (.primitive "uint" "u8") 3,
      .array (.primitive "uint" "u8") 8] do
    let (registry, abi) ← IO.ofExcept (rustFunctionAbiOfItem document definition #[.type ty])
    let some arg := abi.arguments[0]? | throw (IO.userError "missing argument")
    unless arg.typeId == abi.returnValue.typeId && arg.layoutId == abi.returnValue.layoutId do
      throw (IO.userError "identity type/layout join mismatch")
    let (node, _) ← IO.ofExcept (registry.lookup arg.typeId)
    unless node.layoutId == arg.layoutId do throw (IO.userError "physical layout join mismatch")
    let _ ← IO.ofExcept (registry.runtimeLayout arg.typeId)
    unless abi.fixedCount == 1 && !abi.cVariadic && abi.callingConvention.kind == .rust do
      throw (IO.userError "signature ABI mismatch")
  let args := #[ItemArgument.type (.primitive "uint" "u8")]
  let attrs ← IO.ofExcept (body.getObjVal? "function_attributes")
  for key in ["track_caller", "is_foreign", "is_drop_glue"] do
    let changed := body.setObjVal! "function_attributes" (attrs.setObjVal! key (toJson true))
    rejects (rustFunctionAbiOfItem {document with bodies := #[changed]} definition args)
  let signature ← IO.ofExcept (body.getObjVal? "signature")
  let changed := body.setObjVal! "signature" (signature.setObjVal! "c_variadic" (toJson true))
  rejects (rustFunctionAbiOfItem {document with bodies := #[changed]} definition args)
  let changed := body.setObjVal! "signature" (signature.setObjVal! "abi"
    (Json.mkObj [("kind", toJson "c"), ("unwind", Json.null)]))
  rejects (rustFunctionAbiOfItem {document with bodies := #[changed]} definition args)
  rejects (rustFunctionAbiOfItem {document with target := {document.target with architecture := "aarch64"}}
    definition args)
  rejects (rustFunctionAbiOfItem document definition #[.type (.array (.primitive "uint" "u8") 9)])
  rejects (rustFunctionAbiOfItem document definition #[.type (.pointer "raw_pointer" (.primitive "uint" "u8"))])
  IO.println "foundation registry FnAbi: 5 physical joins and 8 fail-closed checks passed"
