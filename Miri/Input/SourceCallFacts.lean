import Miri.Input.SourceCompilerSymbolNames

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

/-- Declaration attributes determine fixed names through the same current
World; unsupported mangling and missing source remain explicit failures. -/
def symbolName (world : SourceCompilerWorld.World) (callee : CallInstance) : Except String String :=
  SourceCompilerSymbolNames.symbolName world callee

end Miri.Input.SourceCallFacts
