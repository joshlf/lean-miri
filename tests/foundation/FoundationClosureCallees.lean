import Miri.Frontend.FoundationClosureMIR
import Miri.Frontend.FoundationDirectCalls
import Miri.Input.Decoder

set_option maxHeartbeats 4000000
open Lean Miri Miri.Frontend.Foundation
private def checked (r : Except String α) : IO α :=
  match r with | .ok a => pure a | .error e => throw (IO.userError e)
private def require (b : Bool) (e : String) : IO Unit := unless b do throw (IO.userError e)
private def reject (r : Except String α) : IO Unit :=
  match r with | .error _ => pure () | .ok _ => throw (IO.userError "unsupported callee source accepted")
private def unitType (d : Input.ImportDocument) (id : Nat) : Bool :=
  match d.types[id]?.map (·.shape) with | some (Input.TypeShape.tuple fields) => fields.isEmpty | _ => false
private def unitFn (d : Input.ImportDocument) (id : Nat) : Bool :=
  match d.types[id]?.map (·.shape) with
  | some (Input.TypeShape.functionPointer signature bound) => signature.inputs.isEmpty && unitType d signature.output &&
      signature.abi == .Rust && signature.safety == .Safe && !signature.cVariadic && bound.isEmpty
  | _ => false

def main (paths : List String) : IO Unit := do
  let [sourcePath,referencePath] := paths | throw (IO.userError "usage: source schema12")
  let document ← checked (Json.parse (← IO.FS.readFile sourcePath) >>= decode)
  let some owner := document.definitions.findIdx? (fun row =>
    (row.getObjValAs? String "kind").toOption == some "closure") | throw (IO.userError "closure source absent")
  let selected ← checked (selectClosureTemplate document owner #[.type (.tuple #[])])
  let (physical,_) ← checked (prepareClosureMIRTypes (PhysicalTypeRegistry.start document) owner #[.type (.tuple #[])])
  let blocks ← checked (selected.body.getObjValAs? (Array Json) "blocks")
  let some entry := blocks[0]? | throw (IO.userError "closure source entry absent")
  let function ← checked ((← checked (entry.getObjVal? "terminator")).getObjVal? "function")
  let (pool,demand) ← checked ((← checked (DirectCallPool.start physical)).demand selected.fullArguments function)
  let (same,again) ← checked (pool.demand selected.fullArguments function)
  require (again.node.id == demand.node.id && same.registry.instances.size == pool.registry.instances.size &&
    same.abis.size == pool.abis.size) "same source callee demand did not deduplicate"
  let prepared ← checked (prepareItem document demand.resolvedDefinition
    #[.type (.functionPointer #[] (.tuple #[]) "safe" "rust" false),.type (.tuple #[])])
  let sourceBlocks ← checked (prepared.item.source.getObjValAs? (Array Json) "blocks")
  require (sourceBlocks.size == 5) "genuine callee source spine differs"
  let some entry := sourceBlocks[0]? | throw (IO.userError "callee entry absent")
  let statements ← checked (entry.getObjValAs? (Array Json) "statements")
  let some tupleStatement := statements[4]? | throw (IO.userError "callee tuple assignment absent")
  let tupleSource ← checked (tupleStatement.getObjVal? "value")
  let nestedFunction ← checked ((← checked (entry.getObjVal? "terminator")).getObjVal? "function")
  let calleeArguments := #[ItemArgument.type (.functionPointer #[] (.tuple #[]) "safe" "rust" false),.type (.tuple #[])]
  match pool.demand calleeArguments nestedFunction with
  | .error message => IO.println s!"next source query remains unsupported: {message}"
  | .ok _ => throw (IO.userError "control nested query unexpectedly became available; expand its regression")
  let tuple ← checked (lowerJoinedRvalue prepared {} (fun _ => .error "unexpected constant") tupleSource)
  require (tuple.value == .Aggregate .Tuple #[]) "actual unit tuple aggregate was not preserved"
  let some cleanup := sourceBlocks[3]? | throw (IO.userError "callee cleanup absent")
  let dropSource ← checked (cleanup.getObjVal? "terminator")
  let (drop,fact) ← checked (lowerSourceDrop prepared {} dropSource)
  require (fact.place == ⟨2,#[]⟩ && sameConcrete 1024 fact.type (.tuple #[])) "callee dropped source type differs"
  let reference := (← checked (Input.decodeJson (← IO.FS.readFile referencePath))).document
  let some sourceDef := document.definitions[demand.resolvedDefinition]? | throw (IO.userError "source callee definition absent")
  let definition : Input.DefinitionId := ⟨← checked (sourceDef.getObjValAs? Nat "crate_index"),
    ← checked (sourceDef.getObjValAs? Nat "index")⟩
  let some compilerDefinition := reference.definitions.findIdx? (· == definition)
    | throw (IO.userError "compiler callee definition absent")
  let candidates := reference.instances.filter fun node => node.instanceKind == .Item compilerDefinition &&
    match node.genericArgs.toList with
    | [.Type f,.Type t] => unitFn reference f && unitType reference t
    | _ => false
  require (candidates.size == 1) "compiler unit function callee instance ambiguous/absent"
  let some compiler := candidates[0]? | throw (IO.userError "compiler callee absent")
  let some bodyId := compiler.bodyId | throw (IO.userError "compiler callee body absent")
  let some body := reference.bodies[bodyId]? | throw (IO.userError "compiler callee body slot absent")
  let some compilerEntry := body.mir.basicBlocks[0]? | throw (IO.userError "compiler callee entry absent")
  let some compilerTuple := compilerEntry.statements[4]? | throw (IO.userError "compiler tuple assignment absent")
  let .Assign _ compilerTupleValue := compilerTuple.kind | throw (IO.userError "compiler tuple assignment differs")
  require (compilerTupleValue == tuple.value) "unit Aggregate.Tuple differs from genuine compiler"
  let some block := body.mir.basicBlocks[3]? | throw (IO.userError "compiler callee cleanup absent")
  require (block.terminator.kind == drop && body.mir.basicBlocks.size == sourceBlocks.size)
    "synchronous Drop/unwind/replace/async fields differ from genuine compiler"
  let some abiMap := reference.queries.instanceAbis.find? (·.instanceId == compiler.id)
    | throw (IO.userError "compiler callee ABI mapping absent")
  let some expected := reference.functionAbis[abiMap.abiId]? | throw (IO.userError "compiler callee ABI absent")
  let some actual := pool.abis[demand.abiId]? | throw (IO.userError "pure callee ABI absent")
  require (actual.callingConvention == expected.callingConvention && actual.canUnwind == expected.canUnwind &&
    actual.fixedCount == expected.fixedCount && actual.cVariadic == expected.cVariadic &&
    actual.returnValue.mode == expected.returnValue.mode && actual.arguments.map (·.mode) == expected.arguments.map (·.mode))
    "pure FnDef callee full pass modes/ABI differ"
  reject (lowerSourceDrop prepared {} (dropSource.setObjVal! "async_drop" (toJson (some (0:Nat)))))
  reject (lowerSourceDrop prepared {} (dropSource.setObjVal! "target" (toJson sourceBlocks.size)))
  reject (lowerJoinedRvalue prepared {} (fun _ => .error "constant unavailable") (Json.mkObj [("kind",toJson "aggregate_tuple")]))
  reject ((← checked (DirectCallPool.start (PhysicalTypeRegistry.start {document with bodies := #[]}))).demand selected.fullArguments function)
  IO.println "closure callee: genuine source FnDef instance/ABI, unit aggregate and synchronous Drop match; missing body/async/target controls reject; nested calls still require source queries"
