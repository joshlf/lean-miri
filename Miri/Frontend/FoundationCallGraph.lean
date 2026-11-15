import Miri.Frontend.FoundationCallProgram

/-! Finite worklist demand closure for an acyclic same-scalar ordinary item call
 graph. No compiler resolver process or persistent answer cache is consulted. -/
namespace Miri.Frontend.Foundation
open Lean

structure ScalarGraphItem where
  prepared : PreparedItem
  node : Input.InstanceNode

structure ScalarGraphSite where
  caller : Nat
  block : Nat
  demand : DirectCallPool.Demand

structure ScalarCallGraph where
  pool : DirectCallPool
  items : Array ScalarGraphItem
  sites : Array ScalarGraphSite
  root : Input.InstanceNode
  scalar : ConcreteType

private def itemArguments (physical : PhysicalTypeRegistry) (node : Input.InstanceNode) :
    Except String (Array ItemArgument) := node.genericArgs.mapM fun arg => do
  match arg with
  | .Type id =>
    let some entry := physical.registry.entries[id]? | throw "graph generic type absent"
    pure (.type entry.type)
  | _ => throw "scalar graph const/lifetime arguments unsupported"

private def reachable (fuel : Nat) (edges : Array (Nat × Nat)) (sourceId target : Nat) : Bool :=
  if sourceId == target then true else match fuel with
  | 0 => false
  | f+1 => edges.any fun (a,b) => a == sourceId && reachable f edges b target

/-- Explore at most one complete Instance key per source definition. Every
supported argument is either absent or exactly the common scalar type; a second
substitution for one source definition is rejected, rather than enumerated.
The work bound is the finite source definition count plus one. Cycles are checked
on source definition edges, which also rejects polymorphic recursion. -/
def scalarCallGraph (document : Document) (definition : Nat) : Except String ScalarCallGraph := do
  let pool ← DirectCallPool.start (PhysicalTypeRegistry.start document)
  let (pool, root, _) ← pool.internItem definition #[]
  let prepared ← prepareItem document definition #[]
  let some scalar := prepared.item.localTypes[0]? | throw "graph root return type absent"
  let .primitive "uint" name := scalar | throw "graph requires unsigned scalar"
  unless name ∈ ["u8", "u16", "usize"] do throw "graph scalar type unsupported"
  let (pool, items, sites) ← go (document.definitions.size + 1) pool
    #[⟨prepared, root⟩] 0 #[] #[] scalar
  return ⟨pool, items, sites, root, scalar⟩
where
  go (fuel : Nat) (pool : DirectCallPool) (items : Array ScalarGraphItem) (cursor : Nat)
      (sites : Array ScalarGraphSite) (edges : Array (Nat × Nat)) (scalar : ConcreteType) :
      Except String (DirectCallPool × Array ScalarGraphItem × Array ScalarGraphSite) := do
    if cursor == items.size then return (pool, items, sites)
    let .succ fuel := fuel | throw "finite scalar graph worklist bound exhausted"
    let some current := items[cursor]? | throw "graph worklist cursor absent"
    let item := current.prepared.item
    unless item.argumentCount == 1 && item.localTypes.all (sameConcrete 1024 scalar) do
      throw "graph requires identical scalar arguments/returns/locals"
    unless (← item.source.getObjValAs? (Array Json) "required_consts").isEmpty do
      throw "graph required-constant operands unsupported"
    let mut pool := pool
    for ty in item.localTypes do
      let (physical, _) ← pool.registry.physical.intern ty
      pool := { pool with registry := { pool.registry with physical } }
    let mut items := items
    let mut sites := sites
    let mut edges := edges
    let blocks ← item.source.getObjValAs? (Array Json) "blocks"
    for h : block in [:blocks.size] do
      let terminal ← blocks[block].getObjVal? "terminator"
      if (← terminal.getObjValAs? String "kind") != "call" then continue
      let (next, demand) ← pool.demand item.arguments (← terminal.getObjVal? "function")
      pool := next
      let .Item callee := demand.node.instanceKind | throw "graph callee is not ordinary Item"
      if reachable (edges.size + 1) edges callee item.definition then
        throw "recursive source-definition call graph unsupported"
      edges := edges.push (item.definition, callee)
      sites := sites.push ⟨current.node.id, block, demand⟩
      if let some previous := items.find? (·.node.id == demand.node.id) then
        unless previous.node.instanceKind == demand.node.instanceKind &&
            previous.node.genericArgs == demand.node.genericArgs do
          throw "graph duplicate instance identity conflicts with complete key"
      else
        unless !(items.any (·.prepared.item.definition == callee)) do
          throw "graph multiple substitutions for one source definition unsupported"
        let arguments ← itemArguments pool.registry.physical demand.node
        unless arguments.isEmpty || (arguments.size == 1 && arguments.all (fun arg =>
            match arg with | .type ty => sameConcrete 1024 ty scalar | _ => false)) do
          throw "graph callee argument tuple leaves same-scalar domain"
        let prepared ← prepareItem document callee arguments
        items := items.push ⟨prepared, demand.node⟩
    go fuel pool items (cursor + 1) sites edges scalar

end Miri.Frontend.Foundation
