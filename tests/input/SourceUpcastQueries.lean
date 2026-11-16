import Miri.Input.Decoder
import Miri.Input.ConcreteCastQueries
import Miri.Input.ConcreteVTable

open Miri.Input

private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error reason => throw (IO.userError reason)

def main (args : List String) : IO Unit := do
  let (path, required) ← match args with
    | [path] => pure (path, true)
    | [path, "no-upcast"] => pure (path, false)
    | _ => throw (IO.userError "expected fresh input and optional no-upcast control")
  let decoded ← must (decodeJson (← IO.FS.readFile path))
  let document := decoded.document
  let runtime ← must (RuntimeMetadata.ofDocument document |>.mapError toString)
  let mut checked := 0
  for binding in document.sourceVtables.bindings do
    let some principal := binding.principal | continue
    for target in document.types do
      let .dynamicTraitObject _ (some targetPrincipal) _ := target.shape | continue
      let targetPrincipal ← must (ConcreteVTable.normalizedPredicate document targetPrincipal)
      if principal != targetPrincipal then continue
      let tails ← must (ConcreteCastQueries.lockstepTails runtime binding.typeId target.id)
      unless tails == (binding.typeId, target.id) do
        throw (IO.userError "concrete-to-dynamic lockstep tails changed their exact type identities")
      checked := checked + 1
  for source in document.types do
    let .dynamicTraitObject _ (some sourcePrincipal) _ := source.shape | continue
    for target in document.types do
      let .dynamicTraitObject _ (some targetPrincipal) _ := target.shape | continue
      if sourcePrincipal == targetPrincipal then continue
      match ConcreteVTable.supertraitSlot document source.id target.id with
      | .error _ => pure ()
      | .ok _ =>
        let tails ← must (ConcreteCastQueries.lockstepTails runtime source.id target.id)
        unless tails == (source.id, target.id) do
          throw (IO.userError "dynamic-object lockstep tails changed their exact type identities")
        checked := checked + 1
  if required && checked == 0 then throw (IO.userError "control has no source vtable coercion or distinct supertrait pair")
  IO.println s!"source upcast queries: {checked} source coercion/supertrait pairs; no precomputed cast answers"
