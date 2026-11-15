import Miri.Input.Model.SourceMir
import Miri.Input.SourceAbi
import Miri.Input.SourceCompilerWorldAbi
import Miri.Input.LowerMIR

/-! Demand-time typed source MIR lowering. IDs are allocated only in the current
World. Unsupported syntax is rejected, never erased or changed to a no-op. -/
namespace Miri.Input.SourceMirLowering
open Miri.Interpreter
abbrev World := SourceCompilerWorld.World

private def known (value : SourceMir.Operator α) : Except String α :=
  match value with | .known value => pure value | .unsupported tag => throw s!"Unsupported source MIR operator {tag}"
private def phase : SourceMir.Phase → Except String MIR.MirPhase
  | .known value => pure value | .unsupported tag => throw s!"Unsupported source MIR phase {tag}"

private structure Context where
  source : SourceMir.Body
  types : Array (Option Nat)
  spans : Array Nat

private def span (c : Context) (id : Nat) : Except String Nat := do
  let some id := c.spans[id]? | throw "Invalid source MIR span reference"
  return id
private def info (c : Context) (source : SourceMir.SourceInfo) : Except String MIR.SourceInfo := do
  return ⟨⟨← span c source.span⟩,source.scope⟩
private def place (c : Context) (p : SourceMir.Place) : Except String MIR.Place := do
  unless p.localId < c.source.locals.size do throw "Invalid source MIR local reference"
  -- Projected-place facts need an independently derived type path. The initial
  -- common lowering domain deliberately rejects them rather than omit facts.
  unless p.projection.isEmpty do throw "Unsupported typed source projected place facts"
  return ⟨p.localId,#[]⟩
private def constant (c : Context) (value : SourceMir.Constant) : Except String MIR.ConstOperand := do
  unless value.userType.isNone do throw "Unsupported source MIR user type annotation"
  let some type := c.types[value.type]?.join | throw "Unsupported source MIR constant type not yet instantiated"
  let matching :=  c.source.spans.filter (·.key == value.span)
  let [sourceSpan] := matching.toList | throw "Invalid source MIR constant span identity absent/ambiguous"
  let value' ← match value.value with
    | .zeroSized => pure MIR.ConstValue.ZeroSized
    | .scalar bits bytes => pure (.Scalar (.Int bits bytes))
    | _ => throw "Unsupported typed source constant evaluation"
  return ⟨⟨← span c sourceSpan.identity⟩,value.userType,.Val value' type⟩
private def operand (c : Context) : SourceMir.Operand → Except String MIR.Operand
  | .copy p => return .Copy (← place c p)
  | .move p => return .Move (← place c p)
  | .constant value => return .Constant (← constant c value)
  | .unsupported tag => throw s!"Unsupported source MIR operand {tag}"
private def rvalue (c : Context) : SourceMir.Rvalue → Except String MIR.Rvalue
  | .use op retag => return .Use (← operand c op) (if retag then .Yes else .No)
  | .binary op left right => return .BinaryOp (← known op) (← operand c left) (← operand c right)
  | .unary op value => return .UnaryOp (← known op) (← operand c value)
  | .aggregateTuple values => return .Aggregate .Tuple (← values.mapM (operand c))
  | _ => throw "Unsupported typed source MIR rvalue"
private def statement (c : Context) (s : SourceMir.Statement) : Except String MIR.Statement := do
  let kind : MIR.StatementKind ← match s.kind with
    | .assign p value => pure (MIR.StatementKind.Assign (← place c p) (← rvalue c value))
    | .storageLive id => pure (.StorageLive id)
    | .storageDead id => pure (.StorageDead id)
    | .nop => pure .Nop
    | .unsupported tag => throw s!"Unsupported source MIR statement {tag}"
  return ⟨← info c s.source,kind⟩
private def terminator (c : Context) (t : SourceMir.Terminator) : Except String MIR.Terminator := do
  let kind : MIR.TerminatorKind ← match t.kind with
    | .returnValue => pure MIR.TerminatorKind.Return
    | .goto target => pure (.Goto target #[])
    | .resumeUnwind => pure .UnwindResume
    | .terminateUnwind reason => pure (MIR.TerminatorKind.UnwindTerminate (← known reason))
    | .unreachable => pure .Unreachable
    | .switchInt op values otherwise => do
      pure (MIR.TerminatorKind.SwitchInt (← operand c op) ⟨values.map (fun (v,b) => .Case v b),otherwise⟩)
    | _ => throw "Unsupported typed source MIR terminator"
  return ⟨← info c t.source,kind⟩

/-- Install one genuine typed body. Existing canonical rows retain their IDs.
No compiler function/allocation identity is inferred from these local handles. -/
def derive (initial : World) (callee : CallInstance) : Except String World := do
  let node ← SourceCompilerWorld.node initial callee
  if node.kind == .instanceMir then
    let _ ← SourceCompilerWorld.bodyId initial callee
    return initial
  let key ← SourceCompilerWorld.keyOf initial callee
  let some material := initial.canonical.sourceMaterial | throw "Unsupported source MIR material absent"
  let some mir := material.genericMir | throw "Unsupported typed source MIR unavailable"
  let [body] := (mir.bodies.filter fun b => b.definition == key.definition && b.promoted.isNone).toList
    | throw "Unsupported source MIR body absent/ambiguous"
  unless body.promotedCount == 0 do throw "Unsupported source MIR promoted body installation"
  let some physical := material.physical | throw "Unsupported typed source MIR type expressions unavailable"
  let parameters ← SourceDeclarations.fullParameters material.genericLayers key.definition
  unless parameters.size == key.arguments.size do throw "Invalid source MIR substitution count"
  let mut typeArguments := #[]
  let mut constArguments := #[]
  for (parameter,arg) in parameters.zip key.arguments do
    match parameter,arg with
    | .typeParameter,.Type id =>
      typeArguments := typeArguments.push (some (← SourceConcreteTypes.concreteType initial material.target.pointerSizeBits id))
      constArguments := constArguments.push none
    | .region,.Lifetime _ =>
      typeArguments := typeArguments.push none; constArguments := constArguments.push none
    | _,_ => throw "Unsupported typed source MIR generic constant substitution"
  -- Derivation also checks the source signature and its inherited obligations.
  let (initial,abi) ← SourceAbi.derive initial callee #[]
  let (initial,_) ← SourceCompilerWorld.attachInstanceAbi initial callee #[] abi
  let mut world := initial
  let root := mir.rootSpan
  let rootId := world.canonical.queries.session.rootSpan
  let some rootData := world.canonical.spans[rootId]? | throw "Invalid canonical source session root span"
  unless world.canonical.files[rootData.file]? == some root.file &&
      rootData == ⟨root.isDummy,root.key.lo,root.key.hi,⟨root.startLine,root.startColumn⟩,
        ⟨root.endLine,root.endColumn⟩,root.key.context,rootData.file⟩ do
    throw "Invalid typed MIR/canonical session root span mismatch"
  if let some (_,existing) := world.derivedSourceSpans.find? (·.1 == root.key) then
    unless existing == rootId do throw "Invalid source session root identity conflict"
  else world := {world with derivedSourceSpans := world.derivedSourceSpans.push (root.key,rootId)}
  let mut types := #[]
  -- Only referenced types are instantiated, not all source type rows.
  let mut typeMap : Array (Option Nat) := Array.replicate physical.types.size none
  let mut seen := #[]
  let needed := body.locals.map (·.type) ++ body.requiredConstants.map (·.type)
  for ref in needed do
    unless seen.contains ref do
      let concrete ← SourceTypes.instantiate physical typeArguments constArguments ref
      let concrete ← SourceTypes.eraseRegions concrete
      let (updated,id) ← SourcePhysical.intern world concrete
      unless ref < typeMap.size do throw "Invalid source MIR local type reference"
      typeMap := typeMap.setIfInBounds ref (some id)
      seen := seen.push ref
      world := updated
  for source in body.locals do
    let some id := typeMap[source.type]?.join | throw "Invalid source MIR local type absent"
    types := types.push id
  unless body.spreadArgument.isNone && body.argumentCount == abi.arguments.size &&
      types[0]? == some abi.returnValue.typeId do throw "Invalid source MIR signature/return local mismatch"
  for (argument,index) in abi.arguments.zipIdx do
    unless types[index+1]? == some argument.typeId do throw "Invalid source MIR argument local/signature mismatch"
  let mut spanIds := #[]
  for source in body.spans do
    unless source.identity == spanIds.size do throw "Invalid source MIR span identity order"
    let file := (world.canonical.files.findIdx? (· == source.file)).getD world.canonical.files.size
    let files := if file == world.canonical.files.size then world.canonical.files.push source.file else world.canonical.files
    let row : SourceSpanData := ⟨source.isDummy,source.key.lo,source.key.hi,
      ⟨source.startLine,source.startColumn⟩,⟨source.endLine,source.endColumn⟩,source.key.context,file⟩
    let id ← if let some (_,id) := world.derivedSourceSpans.find? (·.1 == source.key) then do
      unless world.canonical.spans[id]? == some row do throw "Invalid source span identity/payload conflict"
      pure id
    else do
      let id := world.canonical.spans.size
      world := {world with
        derivedSourceSpans := world.derivedSourceSpans.push (source.key,id)
        canonical := {world.canonical with files,spans := world.canonical.spans.push row}}
      pure id
    spanIds := spanIds.push id
  let c : Context := ⟨body,typeMap,spanIds⟩
  let blocks ← body.blocks.mapM fun b => do
    return MIR.BasicBlock.mk (← b.statements.mapM (statement c)) (← terminator c b.terminator) b.cleanup
  let sourceScopes ← body.scopes.mapIdxM fun id s => do
    return SourceScope.mk id s.parent (← span c s.span) none s.inlinedParent
  let mut backtraceSpans := #[]
  for b in body.backtraces do
    let file := (world.canonical.files.findIdx? (· == b.filename)).getD world.canonical.files.size
    if file == world.canonical.files.size then
      world := {world with canonical := {world.canonical with files := world.canonical.files.push b.filename}}
    backtraceSpans := backtraceSpans.push ⟨← span c b.span,⟨b.bytePosition,b.line,b.column,file⟩⟩
  let localSources ← body.locals.mapM fun l => do
    return SourceInfo.mk (← span c l.source.span) l.source.scope
  let bodyId := world.canonical.bodies.size
  let actual : Input.Body := {
    mir := ⟨← phase body.phase,body.argumentCount,body.spreadArgument,types,blocks⟩,
    definitionId := node.definitionId, defPath := node.defPath.getD "", sourcePath := s!"source.mir[{bodyId}]",
    spanId := ← span c body.bodySpan,preambleDefSpanId := ← span c body.definitionSpan,
    injectionPhase := ← body.injectionPhase.mapM phase,instanceId := callee,
    localSources,sourceScopes,backtraceSpans,callEvidence := Array.replicate blocks.size none,
    nodeFacts := blocks.map (fun b => Array.replicate (b.statements.size+1) {}),
    requiredConsts := ← body.requiredConstants.mapM (constant c),promotedBodies := #[] }
  LocalValidation.validateBody actual s!"source.bodies[{bodyId}]"
  let lowered ← lowerBody (LowerContext.ofDocument world.canonical) actual.toBodyCore
  unless lowered.obligations.isEmpty do throw "Unsupported source MIR lowering obligations"
  let some _ := world.canonical.instances[callee]? | throw "Invalid source MIR instance disappeared"
  let updated := {node with kind := .instanceMir,bodyId := some bodyId}
  return {world with canonical := {world.canonical with
    bodies := world.canonical.bodies.push actual
    instances := world.canonical.instances.setIfInBounds callee updated}}
end Miri.Input.SourceMirLowering
