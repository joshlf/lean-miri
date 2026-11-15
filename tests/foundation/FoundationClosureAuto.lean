import Miri.Frontend.FoundationClosureAuto
open Lean Miri.Frontend.Foundation

private def checked (value : Except String α) : IO α := do
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def rejected (value : Except String α) : IO Unit := do
  match value with | .error _ => pure () | .ok _ => throw (IO.userError "unsupported closure auto source accepted")
private def withDeclaration (document : Document) (id : Nat) (replacement : Json) : Except String Document := do
  let material ← document.source.getObjVal? "closure_auto_source"
  let rows ← material.getObjValAs? (Array Json) "declarations"
  let rows ← rows.mapM fun row => do
    return if (← row.getObjValAs? Nat "definition") == id then replacement else row
  return {document with source := document.source.setObjVal! "closure_auto_source" (material.setObjVal! "declarations" (toJson rows))}

def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected genuine std closure source")
  let document ← checked (Json.parse (← IO.FS.readFile path) >>= decode)
  let templates ← checked (document.source.getObjValAs? (Array Json) "closure_templates")
  unless templates.size == 1 do throw (IO.userError "expected one genuine std closure template")
  let some template := templates[0]? | throw (IO.userError "std closure source absent")
  let closureId ← checked (template.getObjValAs? Nat "definition")
  let arguments := #[ItemArgument.type (.tuple #[])]
  let closure ← checked (selectClosureTemplate document closureId arguments)
  let .tuple captures := closure.tupledUpvars | throw (IO.userError "closure upvar tuple absent")
  unless captures.size == 1 do throw (IO.userError "std closure does not capture exactly one fn pointer")
  let some capture := captures[0]? | throw (IO.userError "std closure capture absent")
  let ConcreteType.functionPointer inputs output _ abi _ := capture
    | throw (IO.userError "std closure capture is not FnPtr")
  unless inputs.isEmpty && abi == "rust" && sameConcrete 1024 output (.tuple #[]) do
    throw (IO.userError "std captured fn()->T source substitution mismatch")
  let material ← checked (document.source.getObjVal? "closure_auto_source")
  let declarations ← checked (material.getObjValAs? (Array Json) "declarations")
  unless declarations.size == 2 do throw (IO.userError "expected Sync and RefUnwindSafe declarations")
  let traitIds ← checked (declarations.mapM fun row => row.getObjValAs? Nat "definition")
  let _ ← checked (checkClosureTargetAutos document closureId arguments traitIds)
  for declaration in declarations do
    let traitId ← checked (declaration.getObjValAs? Nat "definition")
    let headers ← checked (declaration.getObjValAs? (Array Json) "manual_impl_headers")
    let some original := headers[0]? | throw (IO.userError "complete manual source inventory absent")
    let pointerRoot := Json.mkObj [("kind",toJson "fn_pointer")]
    let positive := original.setObjVal! "self_constructor" pointerRoot |>.setObjVal! "polarity" (toJson "Positive")
    let negative := positive.setObjVal! "polarity" (toJson "Negative")
    let identity ← checked (original.getObjVal? "definition")
    let index ← checked (identity.getObjValAs? Nat "index")
    let another := positive.setObjVal! "definition" (identity.setObjVal! "index" (toJson (index + 100000)))
    let unknown := original.setObjVal! "self_constructor" (Json.mkObj [("kind",toJson "unknown")])
    for changed in #[
        declaration.setObjVal! "complete_manual_headers" (toJson false),
        declaration.setObjVal! "manual_impl_headers" (toJson #[positive]),
        declaration.setObjVal! "manual_impl_headers" (toJson #[negative]),
        declaration.setObjVal! "manual_impl_headers" (toJson #[positive,another]),
        declaration.setObjVal! "manual_impl_headers" (toJson #[original,original]),
        declaration.setObjVal! "manual_impl_headers" (toJson #[unknown]),
        declaration.setObjVal! "is_auto" (toJson false),
        declaration.setObjVal! "clauses" (toJson #[Json.mkObj [("kind",toJson "unsupported")]])] do
      rejected (checkClosureCaptureAuto (← checked (withDeclaration document traitId changed)) closureId arguments traitId)
  let upvarType ← checked (template.getObjValAs? Nat "tupled_upvars_type")
  let some pointerType := document.types.findIdx? (fun row =>
      ((row.getObjVal? "shape").bind (fun shape => shape.getObjValAs? String "kind")).toOption == some "raw_pointer")
    | throw (IO.userError "genuine std argv raw pointer source absent")
  let some tupleRow := document.types[upvarType]? | throw (IO.userError "upvar source type absent")
  let shape ← checked (tupleRow.getObjVal? "shape")
  let changed := tupleRow.setObjVal! "shape" (shape.setObjVal! "elements" (toJson #[pointerType]))
  let unknownCapture ← if h : upvarType < document.types.size then
    pure {document with types := document.types.set upvarType changed h}
    else throw (IO.userError "upvar source out of bounds")
  rejected (checkClosureTargetAutos unknownCapture closureId arguments traitIds)
  rejected (checkClosureCaptureAuto document closureId arguments document.definitions.size)
  IO.println "genuine std closure Sync/RefUnwindSafe: fn-pointer capture decomposition and unknown/manual/negative/ambiguous controls passed"
