import Miri.Frontend.FoundationClosureShimBridge
import Miri.Input.Decoder
open Lean Miri Miri.Frontend.Foundation
set_option maxHeartbeats 8000000
private def checked (value : Except String α) : IO α :=
  match value with | .ok v => pure v | .error e => throw (IO.userError e)
private def check (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)
private def sameDefinition (left : Array Input.DefinitionId) (a : Nat)
    (right : Array Input.DefinitionId) (b : Nat) : Bool :=
  left[a]? == right[b]? && left[a]?.isSome
private def sameRegion (defs : Array Input.DefinitionId) (refs : Array Input.DefinitionId) : MIR.Region → MIR.Region → Bool
  | .Erased,.Erased => true
  | .Bound a x (.Named d),.Bound b y (.Named e) => a == b && x == y && sameDefinition defs d refs e
  | _,_ => false
private def shape (fuel : Nat) (source : ClosureShimImport) (reference : Input.ImportDocument)
    (a b : Nat) : Bool := Id.run do
  let .succ fuel := fuel | return false
  let some left := source.types[a]? | return false
  let some right := reference.types[b]? | return false
  let child := shape fuel source reference
  let defeq := fun x y => sameDefinition source.registry.definitions x reference.definitions y
  let args (a b : Array MIR.GenericArg) := a.size == b.size && (a.zip b).all fun (x,y) =>
    match x,y with | .Type x,.Type y => child x y | _,_ => false
  match left.shape,right.shape with
  | .int a,.int b => return a == b
  | .tuple a,.tuple b => return a.size == b.size && (a.zip b).all fun (x,y) => child x y
  | .closure d a n,.closure e b m => return defeq d e && n == m && args a b
  | .rawPointer a m,.rawPointer b n => return m == n && child a b
  | .reference a m r,.reference b n s => return m == n && sameRegion source.registry.definitions reference.definitions r s && child a b
  | .alias k d a,.alias l e b => return k == l && defeq d e && args a b
  | .functionPointer a av,.functionPointer b bv =>
    return av.isEmpty && bv.isEmpty && a.safety == b.safety && a.abi == b.abi && a.cVariadic == b.cVariadic &&
      a.inputs.size == b.inputs.size && (a.inputs.zip b.inputs).all (fun (x,y) => child x y) && child a.output b.output
  | .functionDefinition d a s v,.functionDefinition e b t w =>
    let binders := v.size == w.size && (v.zip w).all fun (x,y) => match x,y with
      | .Region (.Named d),.Region (.Named e) => defeq d e
      | _,_ => false
    return defeq d e && args a b && binders && s.safety == t.safety && s.abi == t.abi && s.cVariadic == t.cVariadic &&
      s.inputs.size == t.inputs.size && (s.inputs.zip t.inputs).all (fun (x,y) => child x y) && child s.output t.output
  | _,_ => return false

private def rebaseBody (body : MIR.Body) (types : Array Nat) (methodSpan dummySpan : Nat) : Except String MIR.Body := do
  let typeId (id : Nat) := match types[id]? with | some id => Except.ok id | none => .error "type rebase absent"
  let source (_ : MIR.SourceInfo) : MIR.SourceInfo := ⟨⟨methodSpan⟩,0⟩
  let blocks ← body.basicBlocks.mapM fun block => do
    let statements := block.statements.map fun s => {s with sourceInfo := source s.sourceInfo}
    let kind ← match block.terminator.kind with
      | .Call (.Constant constant) args dest target unwind callSource _ => do
        let .Val .ZeroSized ty := constant.value | throw "generated shim callee not ZST"
        let constant := {constant with span := ⟨methodSpan⟩,value := .Val .ZeroSized (← typeId ty)}
        pure (.Call (.Constant constant) (args.map fun a => {a with span := ⟨dummySpan⟩}) dest target unwind callSource ⟨methodSpan⟩)
      | other => pure other
    return {block with statements,terminator := ⟨source block.terminator.sourceInfo,kind⟩}
  return {body with locals := ← body.locals.mapM typeId,basicBlocks := blocks}

def main (paths : List String) : IO Unit := do
  let [sourcePath,referencePath] := paths | throw (IO.userError "expected genuine closure source/schema12")
  let document ← checked (Json.parse (← IO.FS.readFile sourcePath) >>= decode)
  let templates ← checked (document.source.getObjValAs? (Array Json) "closure_templates")
  let some template := templates[0]? | throw (IO.userError "closure source absent")
  let definition ← checked (template.getObjValAs? Nat "definition")
  let fragment ← checked (buildClosureShimImport document definition #[] (.tuple #[]) (.primitive "int" "i32"))
  let reference := (← checked (Input.decodeJson (← IO.FS.readFile referencePath))).document
  let runtime ← checked ((Input.RuntimeMetadata.ofDocument reference).mapError toString)
  let target ← checked (runtimeTargetOfTarget document.target)
  let mut rebasing := #[]
  for row in fragment.types do
    let matching := reference.types.filter fun rhs => shape 128 fragment reference row.id rhs.id
    let some compiler := matching[0]? | throw (IO.userError s!"generated physical type unmatched: {row.id} {row.display}")
    check (matching.size == 1) "ambiguous source physical type join"
    rebasing := rebasing.push compiler.id
    let some layout := fragment.layouts[row.layoutId]? | throw (IO.userError "source layout absent")
    let layout ← checked ((Input.RuntimeMetadata.layout target layout).mapError toString)
    let expected ← checked ((runtime.lookup compiler.id).mapError toString)
    check (layout == expected.layout) s!"complete physical layout differs for {row.display}"
    -- Diagnostic spelling is source-driven; it is not type identity.
  check (fragment.pendingBodyIds.size == 1 && fragment.bodies.size == 2) "pending ordinary closure body silently filled"
  let again ← checked (buildClosureShimImportInRegistry fragment.registry fragment.abis definition #[]
    (.tuple #[]) (.primitive "int" "i32"))
  check (again.registry.instances.size == fragment.registry.instances.size &&
    again.registry.bodyDefinitions.size == fragment.registry.bodyDefinitions.size &&
    again.types.size == fragment.types.size && again.abis.size == fragment.abis.size &&
    again.entryInstance == fragment.entryInstance) "repeated shim demand changed local identities"
  for generated in fragment.bodies do
    let some node := fragment.registry.instances[generated.body.instanceId]? | throw (IO.userError "source shim instance absent")
    let matching := reference.instances.filter fun rhs =>
      match node.instanceKind,rhs.instanceKind with
      | .Shim (.VTable d),.Shim (.VTable e) => sameDefinition fragment.registry.definitions d reference.definitions e
      | .Shim (.ClosureOnce a b c),.Shim (.ClosureOnce d e f) => c == f &&
          sameDefinition fragment.registry.definitions a reference.definitions d && sameDefinition fragment.registry.definitions b reference.definitions e
      | _,_ => false
    let some compiler := matching[0]? | throw (IO.userError "compiler shim absent")
    check (matching.size == 1) "compiler shim ambiguous"
    let some compilerBodyId := compiler.bodyId | throw (IO.userError "compiler shim body absent")
    let some compilerBody := reference.bodies[compilerBodyId]? | throw (IO.userError "compiler body ID absent")
    let some entry := compilerBody.mir.basicBlocks[0]? | throw (IO.userError "compiler entry absent")
    let .Call _ arguments .. := entry.terminator.kind | throw (IO.userError "compiler shim not call")
    let some argument := arguments[0]? | throw (IO.userError "compiler argument absent")
    let rebased ← checked (rebaseBody generated.body.mir rebasing compilerBody.spanId argument.span.id)
    check (rebased == compilerBody.mir) "complete generated fixed MIR differs from compiler shim"
    let context : Input.LowerContext := {
      spans := fragment.spans.spans, layouts := fragment.layouts,
      definitions := fragment.registry.definitions,instances := fragment.registry.instances,
      typeConstants := fragment.registry.physical.typeConstants,typeIds := fragment.types.map (·.id)}
    let lowered ← checked (Input.lowerBody context generated.body.toBodyCore)
    check (lowered.obligations.isEmpty && lowered.body == generated.body.mir) "fixed importer changed or rejected generated shim"
    let some query := fragment.instanceAbis.find? (·.instanceId == node.id) | throw (IO.userError "source ABI mapping absent")
    let some abi := fragment.abis[query.abiId]? | throw (IO.userError "source ABI absent")
    let some expectedQuery := reference.queries.instanceAbis.find? (·.instanceId == compiler.id) | throw (IO.userError "compiler ABI mapping absent")
    let some expected := reference.functionAbis[expectedQuery.abiId]? | throw (IO.userError "compiler ABI absent")
    let rebaseArgument (arg : Input.AbiArgument) : Except String Input.AbiArgument := do
      let some id := rebasing[arg.typeId]? | throw "ABI type rebase absent"
      let some ty := reference.types[id]? | throw "ABI compiler type absent"
      return {arg with typeId := id,layoutId := ty.layoutId}
    let actual := {abi with
      arguments := ← checked (abi.arguments.mapM rebaseArgument)
      returnValue := ← checked (rebaseArgument abi.returnValue)}
    check (actual == expected) "complete generated FunctionAbi differs from compiler"
  -- A missing original source attribute or predicate cannot be replaced by a
  -- successful bridge. std parent predicates are checked by the same entry.
  match buildClosureShimImport document definition #[.type (.tuple #[])] (.tuple #[]) (.primitive "int" "i32") with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "wrong source parent arguments accepted")
  match buildClosureShimImport document definition #[] (.tuple #[]) (.primitive "int" "i64") with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "mismatching closure signature accepted")
  let brokenInstances := fragment.registry.instances.map fun node =>
    if node.instanceKind == .Item definition then {node with kind := .identityOnly} else node
  let broken := {fragment.registry with instances := brokenInstances}
  match buildClosureShimImportInRegistry broken fragment.abis definition #[] (.tuple #[]) (.primitive "int" "i32") with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "conflicting existing instance accepted")
  let missing := template.setObjVal! "function_attributes" Json.null
  let missingSource := document.source.setObjVal! "closure_templates" (toJson (#[missing] : Array Json))
  let missingDoc := {document with source := missingSource}
  match buildClosureShimImport missingDoc definition #[] (.tuple #[]) (.primitive "int" "i32") with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "missing source closure attributes accepted")
  IO.println "closure shim bridge: real Input.Body+FunctionAbi+local instance pools match compiler and lower through fixed importer; ordinary closure body remains explicit pending"
