import Miri.Input.CompilerCallPipeline
import Miri.Input.SourceCallerLocation

/-! Complete compiler dictionary for source virtual/drop/caller-location
drivers. All identities refer to the pipeline's final shared tables. -/
namespace Miri.Input.CompilerVirtualLeaves
open Miri.Interpreter
private def lift (value : Except String A) : EStateM StepError S A :=
  match value with
  | .ok value => pure value
  | .error reason => throw (.unsupported s!"compiler virtual query: {reason}")

private def source (access : SourceCompilerWorld.Access S) (operation : SourceCompilerWorld.World → Except String A) :
    EStateM StepError S A := do
  let some world := access.get (← get) | throw (.unsupported "compiler virtual World unavailable")
  lift (operation world)

def make (p : CompilerCallPipeline.Prepared) (access : SourceCompilerWorld.Access S) : VirtualCalls.CompilerHooks S C :=
  let facts := p.symbols.facts
  let sourceMode := p.calls.program.input.sourceMaterial.isSome
  let hooks : VirtualCalls.CompilerHooks S C := {
    instanceArgs := fun inst => lift (CompilerInstance.argsOf facts.context.loweringContext.instances inst)
    classifyReceiver := fun ty => lift (CompilerVirtualFacts.receiverKind facts.context ty)
    fieldLayout := fun layout index => lift ((facts.context.runtime.field layout index).mapError toString)
    structTailForCodegen := fun ty => lift (CompilerFacts.requiredType facts.context ty "metadata_tail")
    dynamicData := fun ty => lift (CompilerVirtualFacts.dynamicData facts ty)
    mutPointerType := fun ty => lift (CompilerRuntimeQueries.mutPointerType p.runtime ty)
    mutReferenceType := fun ty => lift (CompilerRuntimeQueries.mutReferenceType p.runtime ty)
    builtinDeref := fun ty => lift (CompilerFacts.builtinDeref facts.context ty true)
    layoutOf := fun ty => lift (CompilerFacts.layoutOf facts.context ty)
    parentTrait := fun method => lift (CompilerRuntimeQueries.parentTrait p.runtime method)
    rebaseVirtualArgs := fun args parent concrete => lift (CompilerRuntimeQueries.rebaseVirtualArgs p.runtime args parent concrete)
    expectResolveForVTable := fun _ method args => lift (CompilerRuntimeQueries.expectResolveForVTable p.runtime method args)
    resolveDropGlue := fun ty => lift (CompilerRuntimeQueries.resolveDropGlue p.runtime ty)
    requiresCallerLocation := fun callee => if sourceMode then
      source access (SourceCallerLocation.requiresCallerLocation · callee)
      else lift (CompilerRuntimeQueries.requiresCallerLocation p.runtime callee)
    sourceScope := fun identity callee body index => do
      if sourceMode then return ← source access (SourceCallerLocation.sourceScope · identity callee body index)
      let some actual := p.scopes.program.bundle.bodies[identity.index]?
        | throw (.unsupported "canonical frame body identity is absent")
      unless actual.body == body do throw (.invalidProgram "frame body identity/content mismatch")
      lift (CompilerScopes.sourceScope p.scopes identity.index index)
    unitLayout := lift (CompilerFacts.unitLayout facts.context) }
  if sourceMode then hooks else CompilerVirtualFacts.scopeHooks p.scopes hooks
end Miri.Input.CompilerVirtualLeaves
