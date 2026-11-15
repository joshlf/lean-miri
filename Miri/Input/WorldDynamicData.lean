import Miri.Input.RuntimeArrayTypes
import Miri.Input.WorldDynamicSource

namespace Miri.Input.WorldDynamicData
open Miri.Interpreter
private def lift (result : Except String α) : RuntimeArrayTypes.CompilerM α :=
  match result with | .ok value => pure value | .error error => throw error

def runtimeData (fuel : Nat) (owner : Miri.MIR.TyId) :
    RuntimeArrayTypes.CompilerM (Option VirtualCalls.DynamicData) := do
  RuntimeArrayTypes.liftType (WorldDynamicSource.runtimeData (← get).metadata fuel owner)

/-- Unported result-catalog leaves may consume only their real immutable
prefix. A valid suffix handle must never be dropped or reinterpreted as a row. -/
def requireMaterialPredicates (values : PredicateList) : RuntimeArrayTypes.CompilerM Unit := do
  let world ← get
  for id in values do
    let _ ← lift (world.arena.existential id)
    unless id < world.arena.materialPredicates.size do
      throw "constructed runtime predicate requires source vtable comparison/normalization/allocation"

def requireMaterialPrincipal (principal : Option Nat) : RuntimeArrayTypes.CompilerM Unit := do
  let some id := principal | return ()
  requireMaterialPredicates #[id]
  let predicate ← lift ((← get).arena.existential id)
  let .trait .. := predicate.body | throw "vtable principal predicate is not a trait"

def requireMaterialType (id : Miri.MIR.TyId) : RuntimeArrayTypes.CompilerM Unit := do
  let .material _ ← lift ((← get).arena.lookupType id)
    | throw "constructed type requires source vtable query"
  pure ()

end Miri.Input.WorldDynamicData
