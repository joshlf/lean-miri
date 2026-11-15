import Miri.Frontend.FoundationDirectCalls

open Lean Miri.Frontend.Foundation

private def checked {α : Type} : Except String α → IO α
  | .ok value => pure value
  | .error e => throw (IO.userError e)

/-- Supply fresh --foundation --root calls --root identity material, and an
ordinary schema12 --root calls export of the same Rust source/compiler. -/
def main (paths : List String) : IO Unit := do
  let [path, referencePath] := paths | throw (IO.userError "expected finite and ordinary call exports")
  let text ← IO.FS.readFile path
  let document ← checked (Json.parse text >>= decode)
  let some definition := document.definitions.findIdx? (fun d =>
      (d.getObjValAs? String "path").toOption == some "calls") | throw (IO.userError "missing calls source")
  let caller ← checked (instantiateItem document definition #[])
  let (physical, preservedId) ← checked ((PhysicalTypeRegistry.start document).intern (.primitive "uint" "u16"))
  let (preserved, _) ← checked (physical.lookup preservedId)
  let pool ← checked (DirectCallPool.start physical)
  let (pool, root, rootAbi) ← checked (pool.internItem definition #[])
  let (after, _) ← checked (pool.registry.physical.lookup preservedId)
  unless preservedId == 0 && after.id == preserved.id && after.display == preserved.display do
    throw (IO.userError "ABI demand changed existing physical type identity")
  let blocks ← checked (caller.source.getObjValAs? (Array Json) "blocks")
  let some block := blocks[0]? | throw (IO.userError "missing source call block")
  let terminator ← checked (block.getObjVal? "terminator")
  let operand ← checked (terminator.getObjVal? "function")
  let (pool, demand) ← checked (pool.demand #[] operand)
  unless root.id == 0 && demand.node.id == 1 && demand.abiId == rootAbi do
    throw (IO.userError "incorrect callee instance or shared ABI identity")
  let (again, duplicate) ← checked (pool.demand #[] operand)
  unless duplicate.node.id == demand.node.id && again.registry.instances.size == 2 &&
      again.functionInstances.size == 1 && again.abis.size == pool.abis.size do
    throw (IO.userError "call request not deduplicated")
  let frozen ← checked pool.finishFunctionTypes
  let evidence ← checked (DirectCallPool.evidence frozen demand)
  let some typeId := evidence.functionType | throw (IO.userError "call function type absent")
  let some node := frozen.types[typeId]? | throw (IO.userError "FnDef node absent")
  unless node.display == "fn(u8) -> u8 {identity::<u8>}" do
    throw (IO.userError "FnDef display mismatch")
  let some layout := frozen.layouts[node.layoutId]? | throw (IO.userError "FnDef layout absent")
  unless layout.sizeBytes == some 0 && layout.abiAlignBytes == some 1 &&
      layout.randomizationSeed == 0 do throw (IO.userError "FnDef ZST layout mismatch")
  match pool.demand #[] (operand.setObjVal! "kind" (toJson "move")) with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "non-FnDef call accepted")
  let referenceText ← IO.FS.readFile referencePath
  let reference ← checked (Json.parse referenceText)
  let types ← checked (reference.getObjValAs? (Array Json) "types")
  let exact := types.filter fun t => (t.getObjValAs? String "display").toOption == some node.display
  unless exact.size == 1 do throw (IO.userError "missing genuine FnDef display comparison")
  let some compilerType := exact[0]? | throw (IO.userError "missing genuine FnDef type")
  let compilerLayoutId ← checked (compilerType.getObjValAs? Nat "layout")
  let layouts ← checked (reference.getObjValAs? (Array Nat) "layouts")
  let some compilerLayoutValueId := layouts[compilerLayoutId]? | throw (IO.userError "missing layout pool reference")
  let layoutValues ← checked (reference.getObjValAs? (Array Json) "layout_values")
  let some compilerLayout := layoutValues[compilerLayoutValueId]? | throw (IO.userError "missing compiler layout")
  for (key, expected) in #[("size_bytes", 0), ("abi_align_bytes", 1),
      ("unadjusted_abi_align_bytes", 1), ("randomization_seed", 0)] do
    unless (← checked (compilerLayout.getObjValAs? Nat key)) == expected do
      throw (IO.userError s!"genuine FnDef layout mismatch: {key}")
  let fields ← checked (compilerLayout.getObjVal? "fields")
  unless (← checked (fields.getObjValAs? String "kind")) == "arbitrary" &&
      (← checked (fields.getObjValAs? Nat "field_count")) == 0 do
    throw (IO.userError "genuine FnDef field shape mismatch")
  let backend ← checked (compilerLayout.getObjVal? "backend_repr")
  unless (← checked (backend.getObjValAs? String "kind")) == "memory" &&
      (← checked (backend.getObjValAs? Bool "sized")) do
    throw (IO.userError "genuine FnDef backend mismatch")
  IO.println "foundation direct call demands: 8 checks passed"
