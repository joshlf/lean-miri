import Miri.Input.SourceCompilerWorld
import Miri.Input.CompilerIntrinsicFacts
import Miri.Interpreter.ExecutionCallLeaves

/-! machine.rs::check_fn_target_features exact compiler attributes/session.
Feature order and all Enabled/Forced/Implied kinds are retained in input. The
source driver performs the initial guard, diagnostic filtering and wasm abort.
-/
namespace Miri.Input.CompilerTargetFeatures
open Lean Miri.Interpreter
private def facts (p : CompilerIntrinsicFacts.Prepared) (callee : CallInstance) : Except String Catalog.RuntimeInstance := do
  let some entry := p.entries.find? (·.callee == callee) | throw "missing exact full-instance target features"
  pure entry.facts

def required (p : CompilerIntrinsicFacts.Prepared) (callee : CallInstance) :
    Except String (Array ExecutionCallLeaves.TargetFeature) := do
  (← facts p callee).targetFeatures.mapM fun feature => do
    let implied ← match feature.kind with
      | "implied" => pure true | "enabled" | "forced" => pure false
      | _ => throw "unknown compiler target-feature kind"
    pure ⟨feature.name, implied⟩

def available (p : CompilerIntrinsicFacts.Prepared) (name : String) : Except String Bool :=
  pure (p.program.input.queries.session.internalTargetFeatures.contains name)

def isLikeWasm (p : CompilerIntrinsicFacts.Prepared) : Except String Bool :=
  pure p.program.input.queries.session.isLikeWasm
/-- The pinned codegen_instance_attrs adjustments never alter target_features:
all three source kinds retain order; only Implied is omitted from diagnostics. -/
def requiredOfDefinition (material : SourceAbi.Material) (definition : DefinitionId) :
    Except String (Array ExecutionCallLeaves.TargetFeature) := do
  let [header] := (material.targetFeatureDeclarations.filter (·.definition == definition)).toList
    | throw "source target-feature declaration absent/ambiguous"
  header.features.mapM fun feature => do
    let implied ← match feature.kind with
      | .implied => pure true | .enabled | .forced => pure false
      | .unsupported tag => throw s!"Unsupported source target-feature kind {tag}"
    return ⟨feature.name,implied⟩

def requiredSource (world : SourceCompilerWorld.World) (callee : CallInstance) :
    Except String (Array ExecutionCallLeaves.TargetFeature) := do
  let node ← SourceCompilerWorld.node world callee
  let some raw := world.canonical.definitions[node.instanceKind.defId]?
    | throw "source target-feature definition absent"
  let some source := world.canonical.sourceMaterial | throw "source target-feature material unavailable"
  let some abi := source.abi | throw "source target-feature attributes unavailable"
  requiredOfDefinition abi raw

private def lift (query : Except String A) : EStateM StepError S A :=
  match query with | .ok value => pure value | .error error => throw (.unsupported error)

private def source (access : SourceCompilerWorld.Access S)
    (query : SourceCompilerWorld.World → Except String A) : EStateM StepError S A := do
  let some world := access.get (← get) | throw (.unsupported "source target-feature World unavailable")
  unless world.canonical.sourceMaterial.isSome do throw (.unsupported "source target-feature material unavailable")
  lift (query world)

def dictionary (p : CompilerIntrinsicFacts.Prepared) (access : SourceCompilerWorld.Access S) : ExecutionCallLeaves.TargetFeatures S :=
  if p.program.input.sourceMaterial.isSome then
    {required := fun callee => source access (requiredSource · callee)
     available := fun name => source access fun world => pure (world.canonical.queries.session.internalTargetFeatures.contains name)
     isLikeWasm := source access fun world => pure world.canonical.queries.session.isLikeWasm}
  else
    {required := fun callee => lift (required p callee)
     available := fun name => lift (available p name)
     isLikeWasm := lift (isLikeWasm p)}
end Miri.Input.CompilerTargetFeatures
