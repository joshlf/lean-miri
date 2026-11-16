import Miri.Input.Model
import Miri.Interpreter.VTable

namespace Miri.Input.ConcreteVTable

structure Segment where
  principal : PredicateId
  methods : Array DefinitionRef
  emitVptr : Bool
  deriving Repr, DecidableEq

def normalizedPredicate (document : ImportDocument) (id : PredicateId) : Except String PredicateId := do
  let some record := document.compilerPredicates[id]? | throw "predicate normalization material is absent"
  let some id := record.normalizedId | throw "predicate normalization result is absent"
  return id

private def declaration (material : SourceVTableMaterial) (principal : PredicateId) : Except String SourceObjectTrait := do
  let some value := material.objectTraits.find? (·.principal == principal)
    | throw "instantiated object trait declaration is absent"
  return value

private def hasEntries (material : SourceVTableMaterial) (principal : PredicateId) : Except String Bool :=
  go (material.objectTraits.size + 1) #[] principal
where
  go (fuel : Nat) (active : Array PredicateId) (principal : PredicateId) : Except String Bool := do
    if active.contains principal then throw "object supertrait cycle"
    let .succ fuel := fuel | throw "object supertrait traversal limit"
    let value ← declaration material principal
    unless value.ownMethods.isEmpty do return true
    for parent in value.superTraits do
      if ← go fuel (active.push principal) parent then return true
    return false

def segments (material : SourceVTableMaterial) (principal : PredicateId) : Except String (Array Segment) := do
  let (_,_,result) ← visit (material.objectTraits.size + 1) #[] false false principal
  return result
where
  visit (fuel : Nat) (seen : Array PredicateId) (newVptr emitVptr : Bool) (principal : PredicateId) :
      Except String (Array PredicateId × Bool × Array Segment) := do
    let .succ fuel := fuel | throw "vtable segment traversal limit"
    let value ← declaration material principal
    let mut seen := seen.push principal
    let mut newVptr := newVptr
    let mut output := #[]
    for parent in value.superTraits do
      unless seen.contains parent do
        let (next,nextVptr,children) ← visit fuel seen newVptr newVptr parent
        seen := next
        newVptr := nextVptr
        output := output ++ children
    let has := ← hasEntries material principal
    output := output.push ⟨principal,value.ownMethods,emitVptr && has && !material.noTraitVptr⟩
    return (seen,newVptr || has,output)

def supertraitSlot (document : ImportDocument) (source target : TypeId) : Except String (Option Nat) := do
  let some target := document.types[target]? | throw "upcast target type is absent"
  let .dynamicTraitObject _ target _ := target.shape | throw "upcast target is not dynamic"
  let some target := target | return none
  let target ← normalizedPredicate document target
  let some source := document.types[source]? | throw "upcast source type is absent"
  let .dynamicTraitObject _ source _ := source.shape | throw "upcast source is not dynamic"
  let some source := source | throw "upcast source has no principal"
  let source ← normalizedPredicate document source
  let mut offset := 3
  for segment in ← segments document.sourceVtables source do
    offset := offset + segment.methods.size
    if segment.principal == target then return if segment.emitVptr then some offset else none
    if segment.emitVptr then offset := offset + 1
  throw "upcast target principal is not a source supertrait"

def entries (document : ImportDocument) (principal : Option PredicateId) (typeId : TypeId) :
    Except String (Array (Miri.Interpreter.VTableEntry InstanceId)) := do
  let principal ← principal.mapM (normalizedPredicate document)
  let some node := document.types[typeId]? | throw "vtable concrete type is absent"
  let normalizedType := node.sourceLayout.normalizedType
  let some _ := document.sourceVtables.bindings.find? fun binding =>
      binding.typeId == normalizedType && binding.principal == principal
    | throw "concrete vtable executable bindings are absent"
  let mut output := #[.dropInPlace,.size,.align]
  let some principal := principal | return output
  for segment in ← segments document.sourceVtables principal do
    let some ownerBinding := document.sourceVtables.bindings.find? fun binding =>
        binding.typeId == normalizedType && binding.principal == some segment.principal
      | throw "supertrait vtable executable bindings are absent"
    for method in segment.methods do
      let some binding := ownerBinding.methods.find? fun binding =>
          binding.owner == segment.principal && binding.definition == method
        | throw "vtable method executable binding is absent"
      output := output.push (match binding.instanceId with | some id => .method id | none => .vacant)
    if segment.emitVptr then output := output.push (.traitVPtr segment.principal)
  return output

end Miri.Input.ConcreteVTable
