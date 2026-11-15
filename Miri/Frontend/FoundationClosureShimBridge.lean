import Miri.Frontend.FoundationClosurePhysical
import Miri.Frontend.FoundationClosureShimSpans
import Miri.Frontend.FoundationInstanceRegistry
import Miri.Frontend.FoundationDirectCalls
import Miri.Input.LowerMIR
import Miri.Frontend.FoundationSignatureBinder

/-! Checked source-to-input call-shim bridge. All type/layout references come
from the source physical registry. Only dense Lean-local instance/body/ABI/FnDef
pool indices are interned here; no rustc allocation or TCX dedup identity exists
in this result. The ordinary closure body is explicitly pending. The result is
an importer fragment, never a complete executable Program. -/
namespace Miri.Frontend.Foundation
open Lean

structure ClosureShimImportedBody where
  bodyId : Nat
  body : Input.Body

structure ClosureShimImport where
  registry : InstanceRegistry
  /-- Frozen physical types plus the two demanded method FnDef ZST types. -/
  types : Array Input.TypeNode
  layouts : Array Input.Layout
  spans : SpanRegistry
  abis : Array Input.FunctionAbi
  instanceAbis : Array Input.Catalog.InstanceAbi
  functionTypes : Array Input.Catalog.FunctionType
  bodies : Array ClosureShimImportedBody
  pendingBodyIds : Array Nat
  entryInstance : Nat

private def internNode (registry : InstanceRegistry) (kind : Interpreter.CallInstanceKind)
    (arguments : Array MIR.GenericArg) (definition : Nat) :
    Except String (InstanceRegistry × Input.InstanceNode) := do
  let document := registry.physical.registry.document
  let some source := document.definitions[definition]? | throw "closure shim definition absent"
  let some _ := registry.definitions[definition]? | throw "closure shim preserved DefId absent"
  unless kind.defId == definition do throw "closure shim instance source definition mismatch"
  for node in registry.instances do
    if node.instanceKind == kind && node.genericArgs == arguments then
      unless node.kind == .instanceMir && node.definitionId == some definition &&
          node.promotedBodies.isEmpty && node.dispatchSlot.isNone && node.virtualIdentity.isNone &&
          node.defPath == some (← source.getObjValAs? String "path") do
        throw "closure shim existing instance conflicts with source identity"
      let some body := node.bodyId | throw "closure shim existing instance lacks body"
      unless registry.bodyDefinitions[body]? == some definition do
        throw "closure shim existing body reservation conflicts"
      return (registry,node)
  let node : Input.InstanceNode := {
    id := registry.instances.size, instanceKind := kind, genericArgs := arguments,
    kind := .instanceMir, definitionId := some definition,
    defPath := some (← source.getObjValAs? String "path"),
    bodyId := some registry.bodyDefinitions.size, promotedBodies := #[] }
  return ({registry with
    instances := registry.instances.push node
    bodyDefinitions := registry.bodyDefinitions.push definition},node)

private def checkedLayout (physical : PhysicalTypeRegistry) (id : Nat)
    (expected : FoundationLayout) : Except String Input.TypeNode := do
  let (node,layout) ← physical.lookup id
  unless layout.sizeBytes == some expected.size && layout.abiAlignBytes == some expected.align do
    throw "closure shim physical layout disagrees with source derivation"
  let _ ← physical.runtimeLayout id
  return node

private def abiFor (physical : PhysicalTypeRegistry) (receiver output : Nat)
    (component : ClosureShimAbi) : Except String Input.FunctionAbi := do
  let receiver ← checkedLayout physical receiver component.receiverLayout
  let output ← checkedLayout physical output component.outputLayout
  return {
    arguments := #[⟨receiver.id,receiver.layoutId,component.receiverMode⟩],
    returnValue := ⟨output.id,output.layoutId,component.outputMode⟩,
    callingConvention := component.callingConvention, cVariadic := component.cVariadic,
    canUnwind := component.canUnwind, fixedCount := component.fixedCount }

private def reserveAbi (abis : Array Input.FunctionAbi) (abi : Input.FunctionAbi) : Array Input.FunctionAbi × Nat :=
  match abis.findIdx? (· == abi) with
  | some id => (abis,id)
  | none => (abis.push abi,abis.size)

private def wholePlace (id : Nat) : MIR.Place := ⟨id,#[]⟩
private def placeFact (p : MIR.Place) (ty : Nat) (projections : Array Nat := #[]) : Input.PlaceFact :=
  ⟨p,ty,projections⟩

/-- Generate actual fixed MIR and call-resolution evidence from a checked
symbolic rule. All local ordinals are MIR locals; physical references are joined
here, and source spans are the compiler declaration identity/DUMMY_SP. -/
private def lowerBody (source : ClosureShimBody) (spans : ClosureShimSpans)
    (node : Input.InstanceNode) (sourcePath defPath : String)
    (locals : Array Nat) (closureType calleeType calleeInstance calleeAbi : Nat) :
    Except String Input.Body := do
  let some definition := node.definitionId | throw "closure shim instance definition missing"
  unless source.argumentCount == 2 && source.spreadArgument == 2 && locals.size == source.locals.size do
    throw "closure shim local/source arity mismatch"
  let some output := locals[0]? | throw "closure shim output local absent"
  let some receiverType := locals[1]? | throw "closure shim receiver local absent"
  let some tuple := locals[2]? | throw "closure shim tuple local absent"
  let info : MIR.SourceInfo := ⟨⟨spans.methodSpan⟩,0⟩
  let mut blocks := #[]
  let mut facts := #[]
  let mut evidence := #[]
  for block in source.blocks do
    let mut statements := #[]
    let mut blockFacts := #[]
    if block.borrowReceiverIntoThree then
      let some borrowed := locals[3]? | throw "closure shim borrowed local absent"
      statements := #[⟨info,.Assign (wholePlace 3) (.Ref .Erased (.Mut .Default) (wholePlace 1))⟩]
      blockFacts := #[{places := #[placeFact (wholePlace 3) borrowed,placeFact (wholePlace 1) receiverType]}]
    let (terminator,call,nodeFacts) ← match block.terminator with
      | .call _ _ receiver target cleanup => do
        let (arg,argumentType,projectionTypes) ← match receiver with
          | .dereferenceLocalOne => do
            let some .rawMutClosure := source.locals[1]?
              | throw "closure shim deref receiver source type mismatch"
            pure (⟨1,#[.Deref]⟩,closureType,#[closureType])
          | .mutableBorrowLocalThree => do
            let some ty := locals[3]? | throw "closure shim borrowed argument absent"
            pure (wholePlace 3,ty,#[])
        let unwind := match cleanup with | none => MIR.UnwindAction.Continue | some b => .Cleanup b
        let function : MIR.Operand := .Constant ⟨⟨spans.methodSpan⟩,none,.Val .ZeroSized calleeType⟩
        let args : Array MIR.SpannedOperand := #[⟨⟨spans.argumentSpan⟩,.Move arg⟩,
          ⟨⟨spans.argumentSpan⟩,.Move (wholePlace 2)⟩]
        let term := MIR.TerminatorKind.Call function args (wholePlace 0) (some target) unwind .Misc ⟨spans.methodSpan⟩
        let call : Input.CallResolutionEvidence := ⟨.direct,some calleeInstance,some calleeType,none,.normal calleeAbi⟩
        pure (term,some call,{places := #[placeFact arg argumentType projectionTypes,
          placeFact (wholePlace 2) tuple,placeFact (wholePlace 0) output]})
      | .dropReceiver target terminate =>
        pure (.Drop (wholePlace 1) target (if terminate then .Terminate .InCleanup else .Continue) false none,
          none,{places := #[placeFact (wholePlace 1) receiverType]})
      | .returnValue => pure (.Return,none,{})
      | .resumeUnwind => pure (.UnwindResume,none,{})
    blocks := blocks.push ⟨statements,⟨info,terminator⟩,block.cleanup⟩
    facts := facts.push (blockFacts.push nodeFacts)
    evidence := evidence.push call
  return {
    mir := ⟨.Runtime .Optimized,source.argumentCount,some source.spreadArgument,locals,blocks⟩,
    definitionId := some definition, defPath, sourcePath,
    spanId := spans.methodSpan, preambleDefSpanId := spans.methodSpan,
    injectionPhase := none, instanceId := node.id,
    localSources := Array.replicate locals.size ⟨spans.methodSpan,0⟩,
    sourceScopes := #[⟨0,none,spans.methodSpan,none,none⟩],
    backtraceSpans := spans.registry.backtraces, callEvidence := evidence,
    nodeFacts := facts, requiredConsts := #[], promotedBodies := #[] }



/-- Restricted pinned type printer for this bridge's newly demanded closure
nodes. Component pool labels are not executable Rust type names. -/
private def sourceTypeDisplay (document : Document) (fuel : Nat) (type : ConcreteType) : Except String String := do
  let .succ fuel := fuel | throw "closure type diagnostic depth exhausted"
  let recurse := sourceTypeDisplay document fuel
  match type with
  | .primitive "int" name | .primitive "uint" name => return name
  | .primitive "bool" "" => return "bool"
  | .primitive "char" "" => return "char"
  | .tuple fields =>
    let fields ← fields.mapM recurse
    return "(" ++ String.intercalate ", " fields.toList ++ (if fields.size == 1 then "," else "") ++ ")"
  | .functionPointer inputs output safety abi variadic =>
    unless !variadic && (safety == "safe" || safety == "unsafe") && (abi == "rust" || abi == "rust_call") do
      throw "closure function diagnostic ABI unsupported"
    let inputs ← inputs.mapM recurse
    let output ← recurse output
    return (if safety == "unsafe" then "unsafe " else "") ++
      (if abi == "rust_call" then "extern \"rust-call\" " else "") ++
      "fn(" ++ String.intercalate ", " inputs.toList ++ ")" ++ (if output == "()" then "" else " -> " ++ output)
  | .pointer kind pointee =>
    let pointerPrefix ← match kind with
      | "raw_pointer_const" => pure "*const "
      | "raw_pointer_mut" => pure "*mut "
      | "reference_erased_const" => pure "&"
      | "reference_erased_mut" => pure "&mut "
      | _ => throw "closure pointer diagnostic region unsupported"
    return pointerPrefix ++ (← recurse pointee)
  | .closure definition arguments =>
    let templates ← document.source.getObjValAs? (Array Json) "closure_templates"
    let rows ← templates.filterM fun row => return (← row.getObjValAs? Nat "definition") == definition
    let some row := rows[0]? | throw "closure diagnostic source absent"
    unless rows.size == 1 do throw "closure diagnostic source duplicated"
    let parent ← row.getObjValAs? Nat "parent_definition"
    let count ← row.getObjValAs? Nat "parent_count"
    let some parentRow := document.definitions[parent]? | throw "closure diagnostic parent absent"
    let some ownRow := document.definitions[definition]? | throw "closure diagnostic definition absent"
    let parentPath ← parentRow.getObjValAs? String "path"
    let ownPath ← ownRow.getObjValAs? String "path"
    unless ownPath.startsWith (parentPath ++ "::{closure#") && arguments.size == count + 3 do
      throw "closure diagnostic lexical source shape unsupported"
    let inherited ← (arguments.extract 0 count).mapM recurse
    let generic := if inherited.isEmpty then "" else "<" ++ String.intercalate ", " inherited.toList ++ ">"
    return "{closure@" ++ parentPath ++ generic ++ (ownPath.drop parentPath.length).toString ++ "}"
  | _ => throw "closure type diagnostic structure unsupported"

private def callMethod (body : ClosureShimBody) : Except String Nat := do
  let some block := body.blocks[0]? | throw "generated closure shim entry absent"
  let .call method .. := block.terminator | throw "generated closure shim entry not a call"
  return method

private def declarationMethod (document : Document) (kind : String) : Except String Json := do
  let source ← readFnVtableDeclarations document.source
  let row ← fnSourceDeclaration source (← fnSourceRoot source kind)
  let methods ← (← row.getObjValAs? (Array Json) "associated_items").filterM fun row =>
    return (← row.getObjValAs? String "kind") == "method"
  let some method := methods[0]? | throw "closure shim trait method absent"
  unless methods.size == 1 do throw "closure shim trait method ambiguous"
  method.getObjVal? "method"

/-- Check every original parent predicate before creating an executable instance.
There is no std::Termination special case or empty-environment fallback. -/
private def checkParents (document : Document) (selected : SelectedClosureTemplate) : Except String Unit := do
  let types := selected.parentArguments.map fun arg => match arg with | .type ty => some ty | _ => none
  let constants := selected.parentArguments.map fun arg => match arg with | .constant n => some n | _ => none
  checkEnvironment document types constants selected.parentEnvironment

/-- Fresh, deterministically interned fragment. `pendingBodyIds` is nonempty:
ordinary closure MIR must be lowered independently before complete importer
readiness. Construction of this fragment never supplies a function address. -/
def buildClosureShimImportInRegistry (initial : InstanceRegistry) (initialAbis : Array Input.FunctionAbi)
    (definition : Nat) (parentArguments : Array ItemArgument) (tupledInputs outputType : ConcreteType) :
    Except String ClosureShimImport := do
  let document := initial.physical.registry.document
  let selected ← selectClosureTemplate document definition parentArguments
  checkParents document selected
  let (physical,binding) ← internSourceClosure initial.physical definition parentArguments
  let onceSource ← closureShimBody document definition parentArguments tupledInputs outputType false
  let vtableSource ← closureShimBody document definition parentArguments tupledInputs outputType true
  let spans ← closureShimSpans document vtableSource
  let onceSpan ← closureShimSpans document onceSource
  unless spans.registry.spans == onceSpan.registry.spans do throw "closure shim source span discrepancy"
  let (physical,output) ← physical.intern outputType
  let (physical,tuple) ← physical.intern tupledInputs
  let (physical,raw) ← physical.intern (.pointer "raw_pointer_mut" binding.closureTy)
  let (physical,borrowed) ← physical.intern (.pointer "reference_erased_mut" binding.closureTy)
  let (physical,shared) ← physical.intern (.pointer "reference_erased_const" binding.closureTy)
  let mut checkedTypes := physical.types.extract 0 initial.physical.types.size
  for id in [initial.physical.types.size:physical.types.size] do
    let some entry := physical.registry.entries[id]? | throw "closure diagnostic physical entry absent"
    let some node := physical.types[id]? | throw "closure diagnostic physical node absent"
    let display ← sourceTypeDisplay document 128 entry.type
    unless checkedTypes.size == id do throw "closure diagnostic physical pool gap"
    checkedTypes := checkedTypes.push {node with display}
  let physical := {physical with types := checkedTypes}
  let closureNode ← checkedLayout physical binding.typeId
    (← closureVtableImageCandidate document definition parentArguments .fn tupledInputs outputType).selfLayout
  let .closure actual args upvars := closureNode.shape | throw "closure shim physical Self is not closure"
  unless actual == definition && args == binding.fullArguments && upvars == 1 do
    throw "closure shim physical Self source identity mismatch"
  for (source,arg) in selected.fullArguments.zip args do
    let .type expected := source | throw "closure shim non-type source argument unsupported"
    let .Type id := arg | throw "closure shim physical argument kind mismatch"
    let some entry := physical.registry.entries[id]? | throw "closure shim physical argument absent"
    unless sameConcrete 1024 entry.type (← eraseRegions expected) do
      throw "closure shim full generic argument source mismatch"
  let onceAbi ← abiFor physical binding.typeId output
    (← closureShimAbi document definition parentArguments tupledInputs outputType false)
  let vtableAbi ← abiFor physical raw output
    (← closureShimAbi document definition parentArguments tupledInputs outputType true)
  let (sharedNode,_) ← physical.lookup shared
  let image ← closureVtableImageCandidate document definition parentArguments .fn tupledInputs outputType
  let attrs ← selected.body.getObjVal? "function_attributes"
  unless !(← attrs.getObjValAs? Bool "track_caller") &&
      !(← attrs.getObjValAs? Bool "is_foreign") && !(← attrs.getObjValAs? Bool "is_drop_glue") do
    throw "closure item ABI requires unadjusted source attributes"
  let itemUnwind ← rustUnwindFactsOfSource document.source selected.body
  let itemMode : Input.AbiPassMode := ⟨.direct,
    #[⟨144,0,if image.selfLayout.align > 1 then some image.selfLayout.align else none,.none⟩],
    none,none,none,none⟩
  let itemAbi : Input.FunctionAbi := {onceAbi with
    arguments := #[⟨shared,sharedNode.layoutId,itemMode⟩], canUnwind := rustCanUnwind itemUnwind}
  let mut registry := {initial with physical}
  let onceMethod ← callMethod vtableSource
  let mutMethod ← callMethod onceSource
  let (next,item) ← internNode registry (.Item definition) binding.fullArguments definition
  registry := next
  let methodArgs := #[MIR.GenericArg.Type binding.typeId,.Type tuple]
  let (next,once) ← internNode registry (.Shim (.ClosureOnce onceMethod definition false)) methodArgs onceMethod
  registry := next
  let (next,vtable) ← internNode registry (.Shim (.VTable onceMethod)) methodArgs onceMethod
  registry := next
  let (abis,itemAbiId) := reserveAbi initialAbis itemAbi
  let (abis,onceAbiId) := reserveAbi abis onceAbi
  let (abis,vtableAbiId) := reserveAbi abis vtableAbi
  -- Freeze structural types. Preserve the declared projection and lifetime
  -- binder in FnDef signatures rather than replacing them with ABI erasures.
  let source ← readFnVtableDeclarations document.source
  let onceDecl ← fnSourceDeclaration source (← fnSourceRoot source "fn_once")
  let outputs ← (← onceDecl.getObjValAs? (Array Json) "associated_items").filterM fun row =>
    return (← row.getObjValAs? String "kind") == "type" && (← row.getObjValAs? String "name") == "Output"
  let some projection := outputs[0]? | throw "closure FnOnce Output source absent"
  unless outputs.size == 1 do throw "closure FnOnce Output source ambiguous"
  let projectionDef ← projection.getObjValAs? Nat "definition"
  let onceTrait ← fnSourceRoot source "fn_once"
  let mutTrait ← fnSourceRoot source "fn_mut"
  let some onceTraitRow := document.definitions[onceTrait]? | throw "FnOnce diagnostic path absent"
  let some mutTraitRow := document.definitions[mutTrait]? | throw "FnMut diagnostic path absent"
  let onceTraitPath ← onceTraitRow.getObjValAs? String "path"
  let mutTraitPath ← mutTraitRow.getObjValAs? String "path"
  let aliasDisplay := "<" ++ closureNode.display ++ " as " ++ onceTraitPath ++ "<()>>::Output"
  let (outputNode,_) ← physical.lookup output
  let mut types := physical.types
  let alias := types.size
  types := types.push {
    id := alias,layoutId := outputNode.layoutId,
    display := aliasDisplay,
    shape := .alias .projection projectionDef methodArgs,
    compilerFacts := some {
      typingEnvironment := "fully_monomorphized", booleanQueries := #[],
      typeQueries := #[("normalized",some output),("metadata_tail",some output)]}}
  let onceMethodSource ← declarationMethod document "fn_once"
  unless (← onceMethodSource.getObjValAs? (Array Json) "signature_bound_variables").isEmpty do
    throw "closure FnOnce declaration binder unsupported"
  let method ← declarationMethod document "fn_mut"
  let binderSource ← method.getObjValAs? (Array Json) "signature_bound_variables"
  let some binder := binderSource[0]? | throw "closure FnMut structural binder source absent"
  let inputSource ← method.getObjValAs? (Array Json) "inputs"
  let some receiverSource := inputSource[0]? | throw "closure FnMut source receiver absent"
  let sourceRegion ← receiverSource.getObjVal? "source_region"
  unless (← sourceRegion.getObjValAs? String "kind") == "bound" &&
      (← sourceRegion.getObjValAs? Nat "debruijn") == 0 &&
      (← sourceRegion.getObjValAs? Nat "variable") == 0 &&
      (← sourceRegion.getObjVal? "region_kind") == (← binder.getObjVal? "region_kind") do
    throw "closure FnMut receiver source binder identity mismatch"
  let variables : Array MIR.BoundVariableKind ← signatureBoundVariables document
    (Json.mkObj [("bound_variables",← method.getObjVal? "signature_bound_variables")])
  let some (MIR.BoundVariableKind.Region region) := variables[0]? | throw "closure FnMut receiver binder absent"
  unless variables.size == 1 do throw "closure FnMut receiver binder arity unsupported"
  let (borrowedNode,_) ← physical.lookup borrowed
  let boundReference := types.size
  types := types.push {
    id := boundReference,layoutId := borrowedNode.layoutId,
    display := borrowedNode.display,
    shape := .reference binding.typeId .Mut (.Bound (.Bound 0) 0 region)}
  let target ← runtimeTargetOfTarget document.target
  let fnLayout ← DirectCallPool.fnDefinitionLayout target
  let fnLayoutId := physical.layouts.size
  let onceFunction := types.size
  types := types.push {
    id := onceFunction,layoutId := fnLayoutId,
    display := "extern \"rust-call\" fn(" ++ closureNode.display ++ ", ()) -> " ++ aliasDisplay ++
      " {<" ++ closureNode.display ++ " as " ++ onceTraitPath ++ "<()>>::call_once}",shape := .functionDefinition onceMethod methodArgs
      ⟨#[binding.typeId,tuple],alias,.Safe,.RustCall,false⟩ #[]}
  let mutFunction := types.size
  types := types.push {
    id := mutFunction,layoutId := fnLayoutId,
    display := "for<'a> extern \"rust-call\" fn(&'a mut " ++ closureNode.display ++ ", ()) -> " ++ aliasDisplay ++
      " {<" ++ closureNode.display ++ " as " ++ mutTraitPath ++ "<()>>::call_mut}",shape := .functionDefinition mutMethod methodArgs
      ⟨#[boundReference,tuple],alias,.Safe,.RustCall,false⟩ variables}
  let some definitionRow := document.definitions[onceMethod]? | throw "closure method source definition absent"
  let path ← definitionRow.getObjValAs? String "path"
  let onceBody ← lowerBody onceSource spans once "$foundation.generated.closure_once" path
    #[output,binding.typeId,tuple,borrowed] binding.typeId mutFunction item.id itemAbiId
  let vtableBody ← lowerBody vtableSource spans vtable "$foundation.generated.vtable" path
    #[output,raw,tuple] binding.typeId onceFunction once.id onceAbiId
  let some onceBodyId := once.bodyId | throw "closure-once body reservation absent"
  let some vtableBodyId := vtable.bodyId | throw "vtable body reservation absent"
  let some itemBodyId := item.bodyId | throw "closure Item body reservation absent"
  return {
    registry, types, layouts := physical.layouts.push fnLayout, spans := spans.registry,
    abis, functionTypes := #[⟨onceFunction,some once.id,⟨#[binding.typeId,tuple],output,.Safe,.RustCall,false⟩⟩,
      ⟨mutFunction,some item.id,⟨#[borrowed,tuple],output,.Safe,.RustCall,false⟩⟩],
    instanceAbis := #[⟨item.id,#[],itemAbiId⟩,⟨once.id,#[],onceAbiId⟩,⟨vtable.id,#[],vtableAbiId⟩],
    bodies := #[⟨onceBodyId,onceBody⟩,⟨vtableBodyId,vtableBody⟩], pendingBodyIds := #[itemBodyId],
    entryInstance := vtable.id}

/-- Fresh-registry convenience entry. The InRegistry variant preserves caller
physical/instance/body/ABI identities and is the program-assembly demand API. -/
def buildClosureShimImport (document : Document) (definition : Nat)
    (parentArguments : Array ItemArgument) (tupledInputs outputType : ConcreteType) :
    Except String ClosureShimImport := do
  let initial ← InstanceRegistry.start (PhysicalTypeRegistry.start document)
  buildClosureShimImportInRegistry initial #[] definition parentArguments tupledInputs outputType

end Miri.Frontend.Foundation
