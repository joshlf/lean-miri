import Miri.Frontend.FoundationClosurePhysical
import Miri.Input.Decoder

set_option maxHeartbeats 4000000
open Lean Miri Miri.Frontend.Foundation
private def checked (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error e => throw (IO.userError e)
private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def reject (result : Except String α) : IO Unit :=
  match result with | .error _ => pure () | .ok _ => throw (IO.userError "unsupported closure physical material accepted")

private def compareTypes (fuel : Nat) (registry : PhysicalTypeRegistry)
    (reference : Input.ImportDocument) (runtime : Input.RuntimeMetadata) (left right : Nat) : IO Unit := do
  let .succ fuel := fuel | throw (IO.userError "closure comparison depth exhausted")
  let (actual, _) ← checked (registry.lookup left)
  let some expected := reference.types[right]? | throw (IO.userError "compiler closure type absent")
  let layout ← checked (registry.runtimeLayout left)
  let compilerLayout ← checked ((runtime.lookup right).mapError toString)
  require (layout.layout == compilerLayout.layout) s!"complete closure/argument physical layout differs at source {left}/compiler {right}: {reprStr layout.layout} vs {reprStr compilerLayout.layout}"
  match actual.shape, expected.shape with
  | .closure definition args count, .closure compilerDefinition compilerArgs compilerCount =>
    let some sourceDef := registry.registry.document.definitions[definition]? | throw (IO.userError "source closure def absent")
    let some compilerDef := reference.definitions[compilerDefinition]? | throw (IO.userError "compiler closure def absent")
    require ((← checked (sourceDef.getObjValAs? Nat "crate_index")) == compilerDef.crateIndex &&
      (← checked (sourceDef.getObjValAs? Nat "index")) == compilerDef.index &&
      count == compilerCount && args.size == compilerArgs.size) "closure complete identity differs"
    for (a,b) in args.zip compilerArgs do
      let .Type a := a | throw (IO.userError "closure arg type absent")
      let .Type b := b | throw (IO.userError "compiler closure arg type absent")
      compareTypes fuel registry reference runtime a b
  | .tuple args, .tuple compilerArgs =>
    require (args.size == compilerArgs.size) "tuple arity differs"
    for (a,b) in args.zip compilerArgs do compareTypes fuel registry reference runtime a b
  | .functionPointer a av, .functionPointer b bv =>
    require (a.safety == b.safety && a.abi == b.abi && a.cVariadic == b.cVariadic &&
      a.inputs.size == b.inputs.size && av.isEmpty && bv.isEmpty) "source FnPtr signature differs"
    for (a,b) in a.inputs.zip b.inputs do compareTypes fuel registry reference runtime a b
    compareTypes fuel registry reference runtime a.output b.output
  | .int a, .int b => require (a == b) "closure kind integer differs"
  | _, _ => throw (IO.userError "unexpected closure argument shape")

def main (paths : List String) : IO Unit := do
  let [sourcePath, referencePath] := paths | throw (IO.userError "usage: source schema12")
  let document ← checked (Json.parse (← IO.FS.readFile sourcePath) >>= decode)
  let reference := (← checked (Input.decodeJson (← IO.FS.readFile referencePath))).document
  let runtime ← checked ((Input.RuntimeMetadata.ofDocument reference).mapError toString)
  let some definition := document.definitions.findIdx? (fun row =>
    (row.getObjValAs? String "path").toOption == some "std::rt::lang_start::{closure#0}")
      | throw (IO.userError "std closure source absent")
  let (physical, binding) ← checked (internSourceClosure (PhysicalTypeRegistry.start document)
    definition #[.type (.tuple #[])])
  let some sourceDef := document.definitions[definition]? | throw (IO.userError "source definition absent")
  let crateIndex ← checked (sourceDef.getObjValAs? Nat "crate_index")
  let index ← checked (sourceDef.getObjValAs? Nat "index")
  let some compilerClosure := reference.types.find? (fun row => match row.shape with
    | .closure defn _ _ => reference.definitions[defn]? == some ⟨crateIndex, index⟩
    | _ => false) | throw (IO.userError "compiler closure type absent")
  compareTypes 128 physical reference runtime binding.typeId compilerClosure.id
  let (same, again) ← checked (internSourceClosure physical definition #[.type (.tuple #[])])
  require (again.typeId == binding.typeId && same.types.size == physical.types.size) "closure canonical dedup failed"
  let target ← checked (runtimeTargetOfTarget document.target)
  let pointerSize ← checked ((target.pointerSizeIn ABI.AddressSpace.ZERO).mapError toString)
  let mut physical := physical
  for kind in #["raw_pointer_mut", "reference_erased_mut", "reference_erased_const"] do
    let (next, id) ← checked (physical.intern (.pointer kind binding.closureTy))
    let layout ← checked (next.runtimeLayout id)
    require (layout.layout.size.bytes.toNat == pointerSize.bytes.toNat) "closure thin pointer layout differs"
    physical := next
  reject (internSourceClosure physical definition #[])
  reject (internSourceClosure physical document.definitions.size #[.type (.tuple #[])])
  reject (physical.intern (.tuple #[.primitive "uint" "u8", .primitive "uint" "u16"]))
  reject (physical.intern (.closure definition #[.primitive "int" "i64",
    .functionPointer #[.tuple #[]] (.primitive "int" "i32") "safe" "rust_call" false, .tuple #[]]))
  reject (physical.intern (.closure definition #[.primitive "int" "i8",
    .functionPointer #[.tuple #[]] (.primitive "int" "i32") "safe" "rust" false, .tuple #[]]))
  IO.println "closure physical: complete genuine std closure/arguments/RustCall layouts match; dedup and references pass; absent/generic/multifield controls reject"
