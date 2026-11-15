import Miri.Input.RuntimeMetadata
import Miri.Interpreter.VirtualCalls

namespace Miri.Input.WorldDynamicSource
private def lift (result : Except String α) : TypeArena.WorldM α :=
  match result with | .ok value => pure value | .error error => throw error

def runtimeData (_metadata : RuntimeMetadata) (_fuel : Nat) (owner : Miri.MIR.TyId) :
    TypeArena.WorldM (Option Miri.Interpreter.VirtualCalls.DynamicData) := do
  match ← lift ((← get).lookupType owner) with
  | .material node =>
    match node.shape with
    | .dynamicTraitObject predicates principal _ => return some ⟨predicates,principal⟩
    | _ => return none
  | .constructed (.dynamic _) =>
    throw "constructed dynamic type has no exact rustc predicate result"
  | .constructed _ => return none

end Miri.Input.WorldDynamicSource
