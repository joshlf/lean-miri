import Miri.Input.TypeArenaWorld

namespace Miri.Input.WorldTypeHash

def query (world : TypeArena.World) (_fuel : Nat) (id : TypeId) : Except String Miri.ABI.U128 := do
  let .material node ← world.lookupType id
    | throw "constructed type has no exact rustc TypeId hash"
  let some facts := node.compilerFacts | throw "rustc TypeId hash absent"
  let some value := facts.typeIdHash | throw "rustc TypeId hash absent"
  unless value < 2^128 do throw "rustc TypeId hash exceeds u128"
  pure (BitVec.ofNat 128 value)

end Miri.Input.WorldTypeHash
