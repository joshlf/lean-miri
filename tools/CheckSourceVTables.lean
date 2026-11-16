import Miri.Input.Decoder
import Miri.Input.ConcreteVTable
import Miri.Input.ConcreteTypeQueries
import Miri.Input.CompilerRuntimeQueries

open Lean Miri.Input Miri.Interpreter

deriving instance Repr, BEq for VTableEntry

def main (args : List String) : IO UInt32 := do
  let [inputPath,oraclePath] := args
    | throw (IO.userError "usage: CheckSourceVTables <source-input.json> <same-producer-oracle.json>")
  let input ← match ← decodeFile inputPath with
    | .ok input => pure input
    | .error reason => throw (IO.userError reason)
  let document := input.document
  let .ok runtime := RuntimeMetadata.ofDocument document | throw (IO.userError "target decode failed")
  let .ok program := lowerProgram document | throw (IO.userError "MIR lowering failed")
  let .ok queries := CompilerRuntimeQueries.prepare program | throw (IO.userError "runtime queries preparation failed")
  let .ok oracle := Json.parse (← IO.FS.readFile oraclePath) | throw (IO.userError "oracle JSON is invalid")
  let .ok rows := (oracle.getObjVal? "vtables").bind Json.getArr? | throw (IO.userError "oracle vtables are absent")
  let mut seen : Std.HashSet (Nat × Option Nat) := {}
  let mut failures := 0
  let mut slots := 0
  for row in rows do
    let .ok ty := (row.getObjVal? "type_id").bind Json.getNat? | throw (IO.userError "oracle vtable type is absent")
    let .ok rawPrincipal := row.getObjVal? "principal" | throw (IO.userError "oracle principal is absent")
    let principal ← match rawPrincipal with
      | .null => pure none
      | value =>
        let .ok id := value.getNat? | throw (IO.userError "oracle principal is invalid")
        pure (some id)
    if seen.contains (ty,principal) then throw (IO.userError "duplicate oracle vtable key")
    seen := seen.insert (ty,principal)
    let .ok rawEntries := (row.getObjVal? "entries").bind Json.getArr? | throw (IO.userError "oracle entries are absent")
    let mut expected : Array (VTableEntry Nat) := #[]
    let .ok layout := runtime.lookup ty | throw (IO.userError "vtable concrete layout calculation failed")
    let .ok alignBytes := layout.layout.align.abi.bytes | throw (IO.userError "vtable concrete alignment is invalid")
    for entry in rawEntries do
      let .ok kind := (entry.getObjVal? "kind").bind Json.getStr? | throw (IO.userError "oracle entry kind is absent")
      match kind with
      | "drop_in_place" =>
        let .ok value := entry.getObjVal? "instance_id" | throw (IO.userError "oracle drop identity is absent")
        let .ok needs := ConcreteTypeQueries.needsDrop runtime ty | throw (IO.userError "drop analysis failed")
        match value with
        | .null => unless !needs do failures := failures+1; IO.println s!"type={ty}: drop should be null"
        | value =>
          let .ok id := value.getNat? | throw (IO.userError "oracle drop identity is invalid")
          unless needs && CompilerRuntimeQueries.resolveDropGlue queries ty == .ok id do
            failures := failures+1
            IO.println s!"type={ty}: drop executable binding differs"
        expected := expected.push .dropInPlace
      | "size_bytes" | "align_bytes" =>
        let .ok value := (entry.getObjVal? "value").bind Json.getNat? | throw (IO.userError "oracle size or alignment is absent")
        let actual := if kind == "size_bytes" then layout.layout.size.bytes.toNat else alignBytes.toNat
        unless actual == value do failures := failures+1; IO.println s!"type={ty}: {kind} differs"
        expected := expected.push (if kind == "size_bytes" then .size else .align)
      | "vacant" => expected := expected.push .vacant
      | "method" =>
        let .ok id := (entry.getObjVal? "instance_id").bind Json.getNat? | throw (IO.userError "oracle method identity is absent")
        expected := expected.push (.method id)
      | "supertrait_vtable_pointer" =>
        let .ok id := (entry.getObjVal? "principal").bind Json.getNat? | throw (IO.userError "oracle supertrait is absent")
        expected := expected.push (.traitVPtr id)
      | _ => throw (IO.userError s!"unknown oracle vtable entry {kind}")
    let actual := ConcreteVTable.entries document principal ty
    let matching := match actual with | .ok entries => entries == expected | .error _ => false
    unless matching do
      failures := failures+1
      IO.println s!"type={ty} principal={reprStr principal}: rustc={reprStr expected} Lean={reprStr actual}"
    if let some principal := principal then
      let source := document.types.find? fun node => match node.shape with
        | .dynamicTraitObject _ (some id) _ => ConcreteVTable.normalizedPredicate document id == .ok principal
        | _ => false
      if let some source := source then
        let .ok segments := ConcreteVTable.segments document.sourceVtables principal
          | throw (IO.userError "source vtable segment calculation failed")
        for segment in segments do
          let target := document.types.find? fun node => match node.shape with
            | .dynamicTraitObject _ (some id) _ => ConcreteVTable.normalizedPredicate document id == .ok segment.principal
            | _ => false
          if let some target := target then
            let slot := (expected.toList.zipIdx.find? fun (entry,_) => entry == .traitVPtr segment.principal).map (·.2)
            let actual := ConcreteVTable.supertraitSlot document source.id target.id
            slots := slots+1
            unless actual == .ok slot do
              failures := failures+1
              IO.println s!"upcast {source.id}->{target.id}: rustc={reprStr slot} Lean={reprStr actual}"
  unless seen.size == document.sourceVtables.bindings.size do
    throw (IO.userError "vtable oracle does not cover all concrete executable bindings")
  IO.println s!"source vtables: compared={rows.size}, upcast_slots={slots}, failures={failures}; finite compiler comparison only"
  return if failures == 0 then 0 else 1
