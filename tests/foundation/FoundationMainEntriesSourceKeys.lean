import Miri.Frontend.FoundationMainEntries
open Lean Miri.Frontend.Foundation
private def checked {α : Type} (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected compiler-entry source")
  let document ← checked (Json.parse (← IO.FS.readFile path) >>= decode)
  let initial ← checked (DirectCallPool.start (PhysicalTypeRegistry.start document))
  let (pool,_) ← checked (prepareMainEntries initial)
  unless pool.functionSourceDefinitions.size == pool.functionInstances.size &&
      pool.functionSourceArguments.size == pool.functionInstances.size do
    throw (IO.userError "start source function identity vectors incomplete")
  let _ ← checked pool.finishFunctionTypes
  let (same,_) ← checked (prepareMainEntries pool)
  unless same.functionInstances == pool.functionInstances do throw (IO.userError "repeated entry demand duplicated FnDef")
  let _ ← checked same.finishFunctionTypes
  for broken in #[{ pool with functionSourceDefinitions := #[] },{ pool with functionSourceArguments := #[] }] do
    match broken.finishFunctionTypes with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError "missing original FnDef source identity accepted")
  IO.println "main entry: start FnDef source identities preserved on first/repeated demands; missing source vectors reject"
