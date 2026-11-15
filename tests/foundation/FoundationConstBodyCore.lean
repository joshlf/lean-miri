import Miri.Frontend.FoundationBodyCore
import Miri.Frontend.FoundationConstOperand
import Miri.Frontend.FoundationInstanceRegistry
import Miri.Frontend.FoundationFnAbiRegistry

open Lean Miri Miri.Frontend.Foundation
private def checked (value : Except String α) : IO α :=
  match value with | .ok result => pure result | .error e => throw (IO.userError e)

def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected fresh scalar const source")
  let document ← checked (Json.parse (← IO.FS.readFile path) >>= decode)
  let some source := document.bodies[0]? | throw (IO.userError "missing body")
  let definition ← checked (source.getObjValAs? Nat "definition")
  let prepared ← checked (prepareItem document definition #[])
  let (physical, _) ← checked (rustFunctionAbiOfItem document definition #[])
  let registry ← checked (InstanceRegistry.start physical)
  let (registry, instanceNode) ← checked (registry.intern definition #[])
  let physical := registry.physical
  let spans ← checked (buildSpanRegistry source)
  let callback (operand : Json) : Except String (MIR.ConstOperand × ConcreteType) := do
    let (next, constant) ← lowerScalarConstantOperand physical spans operand
    unless next.types.size == physical.types.size && next.layouts.size == physical.layouts.size do
      throw "constant extended closed physical types"
    let id ← operand.getObjValAs? Nat "type"
    return (constant, ← instantiate #[] #[] (← typeExpr document id))
  let sources ← checked (source.getObjValAs? (Array Json) "required_consts")
  unless !sources.isEmpty do throw (IO.userError "fixture must retain actual required constants")
  let required ← checked (sources.mapM fun operand => do return (← callback operand).1)
  let some row := document.definitions[definition]? | throw (IO.userError "missing definition")
  let bindings : BodyBindings := {
    types := physical.registry.entries.mapIdx (fun id entry => ⟨entry.type,id⟩)
    physicalTypeIds := physical.types.map (·.id)
    spans := spans.spans, compilerSpans := spans.compilerSpans, files := spans.files
    definitionId := definition, instanceNode := instanceNode
    defPath := ← checked (row.getObjValAs? String "path"), sourcePath := "$.bodies[0]"
    backtraceSpans := spans.backtraces, requiredConsts := required }
  let body ← checked (lowerPreparedBodyCore prepared bindings callback)
  unless body.requiredConsts == required do throw (IO.userError "required source order lost")
  let wrong := required.map fun constant =>
    match constant.value with
    | .Val _ typeId => {constant with value := .Val (.Scalar (.Int 38 1)) typeId}
  for supplied in [#[], required ++ required, wrong] do
    match lowerPreparedBodyCore prepared {bindings with requiredConsts := supplied} callback with
    | .error "foundation required constant source-order join mismatch" => pure ()
    | .error e => throw (IO.userError s!"unexpected required join failure: {e}")
    | .ok _ => throw (IO.userError "missing or extra required constant accepted")
  match lowerPreparedBodyCore prepared bindings with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "required constant accepted without source evaluator")
  IO.println "fresh required const BodyCore exact source-order join passed"
