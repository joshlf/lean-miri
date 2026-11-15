import Miri.Input.SourceCompilerWorld

/-! machine.rs::find_mir_or_eval_fn asks tcx.is_foreign_item(instance.def_id()).
Pinned rustc_middle/hir/mod.rs defines that property by the definition's immediate
ForeignMod parent. Finite generic declaration attributes retain that source
property; ABI convention and diagnostic names do not decide foreignness. -/
namespace Miri.Input.SourceCallFacts
open Miri.Interpreter

def isForeignItem (world : SourceCompilerWorld.World) (callee : CallInstance) : Except String Bool := do
  let node ← SourceCompilerWorld.node world callee
  let definition := node.instanceKind.defId
  let some raw := world.canonical.definitions[definition]? | throw "foreign-item definition absent"
  let some material := world.canonical.sourceMaterial | throw "foreign-item source material unavailable"
  let some abi := material.abi | throw "foreign-item declaration attributes unavailable"
  let [header] := (abi.functions.filter (·.definition == raw)).toList
    | throw "foreign-item declaration attributes absent/ambiguous"
  return header.attributes.foreignItem

/-- The source declaration currently carries no complete symbol mangling/link
contract. An actual foreign call must reject this missing capability, rather
than read a saved instance answer or use a DefPath as its symbol. -/
def symbolName (_world : SourceCompilerWorld.World) (_callee : CallInstance) : Except String String :=
  throw "source foreign symbol naming unavailable"
end Miri.Input.SourceCallFacts
