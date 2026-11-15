import Miri.Frontend.FoundationBodyCore
import Miri.Frontend.FoundationInstanceRegistry
import Miri.Input.Decoder

open Lean Miri Miri.Frontend.Foundation

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

/-- Source shared reborrows lower to the same fixed MIR constructors and typed
Deref facts as an independent genuine ordinary export. This is a component
comparison, not execution of the reference function or a safety theorem. -/
def main (paths : List String) : IO Unit := do
  let [foundationPath, compilerPath] := paths | throw (IO.userError "expected finite and ordinary reference-rvalue exports")
  let document ← checked (Json.parse (← IO.FS.readFile foundationPath) >>= decode)
  let some source := document.bodies[0]? | throw (IO.userError "source body absent")
  let definition ← checked (source.getObjValAs? Nat "definition")
  let prepared ← checked (prepareItem document definition #[])
  let mut physical := PhysicalTypeRegistry.start document
  for type in prepared.item.localTypes do
    let (next, _) ← checked (physical.intern type)
    physical := next
  let (withByte, u8) ← checked (physical.intern (.primitive "uint" "u8"))
  physical := withByte
  let registry ← checked (InstanceRegistry.start physical)
  let (_, instanceNode) ← checked (registry.intern definition #[])
  let spans ← checked (buildSpanRegistry source)
  let some sourceDefinition := document.definitions[definition]? | throw (IO.userError "source definition absent")
  let defPath ← checked (sourceDefinition.getObjValAs? String "path")
  unless (← checked (source.getObjValAs? (Array Json) "required_consts")).isEmpty do
    throw (IO.userError "component fixture acquired required constants")
  let bindings : BodyBindings := {
    types := physical.registry.entries.mapIdx fun id item => ⟨item.type,id⟩
    physicalTypeIds := physical.types.map (·.id)
    spans := spans.spans, compilerSpans := spans.compilerSpans, files := spans.files
    definitionId := definition, instanceNode, defPath, sourcePath := "$.bodies[0]"
    backtraceSpans := spans.backtraces, requiredConsts := #[] }
  let computed ← checked (lowerPreparedBodyCore prepared bindings)
  let compiler ← checked (Input.decodeJson (← IO.FS.readFile compilerPath))
  let doc := compiler.document
  let some root := doc.bodyRoots[0]? | throw (IO.userError "compiler root absent")
  let some actual := doc.bodies[root.bodyId]? | throw (IO.userError "compiler body absent")
  unless computed.mir.basicBlocks.size == actual.mir.basicBlocks.size do
    throw (IO.userError "rvalue block count changed")
  let mut reborrows := 0
  for (left, right) in computed.mir.basicBlocks.zip actual.mir.basicBlocks do
    unless left.statements.map (·.kind) == right.statements.map (·.kind) &&
        left.terminator.kind == right.terminator.kind do
      throw (IO.userError "reference/rvalue MIR constructors differ from compiler")
    for statement in left.statements do
      if let .Assign _ (.Ref .Erased .Shared place) := statement.kind then
        reborrows := reborrows + 1
        unless place.projection == #[.Deref] do throw (IO.userError "fixture reborrow projection changed")
        let some blockFacts := computed.nodeFacts[0]? | throw (IO.userError "computed node facts absent")
        let some facts := blockFacts[0]? | throw (IO.userError "computed node fact absent")
        let some typing := facts.places.find? (·.place == place)
          | throw (IO.userError "computed projected place fact absent")
        unless typing.typeId == u8 && typing.projectionTypes == #[u8] do
          throw (IO.userError "computed Deref fact lost exact pointee identity")
  unless reborrows == 2 do throw (IO.userError "genuine two-reborrow fixture changed")
  let invalid := Json.mkObj [("local", toJson (1 : Nat)), ("projection", toJson #[Json.mkObj [("kind", toJson "field")]])]
  match lowerSourcePlace prepared.item.localTypes invalid with
  | .error "rvalue source projection unsupported" => pure ()
  | _ => throw (IO.userError "unjoined field projection accepted")
  let missingPointee := { bindings with types := bindings.types.filter fun binding =>
    !(sameConcrete 1024 binding.concrete (.primitive "uint" "u8")) }
  match lowerPreparedBodyCore prepared missingPointee with
  | .error "foundation body missing or duplicate physical type binding" => pure ()
  | .error error => throw (IO.userError s!"unexpected missing projection type diagnostic: {error}")
  | .ok _ => throw (IO.userError "projected pointee type invented from whole-local bindings")
  IO.println "foundation shared Ref/Deref: constructors and exact projected pointee facts match fresh compiler MIR; unjoined projections reject"
