import Miri.Input.CompilerGlobals
import Miri.Input.CompilerPrimitiveFacts
import Miri.Input.StructuralDeref
import Miri.Interpreter.TypedRetag
import Miri.Interpreter.LayoutCompat
import Miri.Interpreter.ValidityVisitor

/-! Required compiler facts for the fixed interpreter. Query evidence is keyed
by exact compilation-local TyId and explicit fully_monomorphized typing_env.
Sources: rustc_middle ty/{util,sty,inhabitedness}; interpret/{call,visitor,validity}
and Miri helpers.rs UnsafeCellVisitor/tree_borrows/mod.rs NewPermission.
No diagnostic type spelling establishes a semantic property. -/
namespace Miri.Input.CompilerFacts
open Lean Miri.ABI Miri.Memory Miri.Interpreter
abbrev Result := Except String

private def computeUnitLayout (runtime : RuntimeMetadata) :
    Result (TyAndLayout TypeId) := do
  let some source := runtime.source.types.find? (fun ty =>
    match ty.shape with | .tuple elements => elements.isEmpty | _ => false)
    | throw "compiler unit type identity missing"
  runtime.lookup source.id |>.mapError toString

structure Context where
  runtime : RuntimeMetadata
  program : LoweredProgram
  lowering : Option LowerContext := none

def Context.loweringContext (context : Context) : LowerContext :=
  let ctx := match context.lowering with
    | some prepared => prepared
    | none => LowerContext.ofDocument context.program.input
  ctx

/-- Type-bearing lowering reads the current execution universe at the call
site; instance-identity-only users can keep the material lowering context. -/
def Context.loweringContextM (context : Context) : TypeArena.WorldM LowerContext := do
  pure (context.loweringContext.withWorld (← get))

def Context.primitiveLayout (context : Context) (key : String) :
    Except String (TyAndLayout TypeId) :=
  CompilerPrimitiveFacts.primitiveLayout context.runtime key

def Context.orderingLayout (context : Context) : Except String (TyAndLayout TypeId) :=
  CompilerPrimitiveFacts.orderingLayout context.runtime

/-- Prepare lowering metadata for the current program. -/
def Context.withProgram (context : Context) (program : LoweredProgram) : Context :=
  { context with program, lowering := some (LowerContext.ofDocument program.input) }

def ofProgram (runtime : RuntimeMetadata) (program : LoweredProgram) : Result Context := do
  let program := CompilerGlobals.prepareProgram program
  return {
    runtime
    program
    lowering := some (LowerContext.ofDocument program.input)
  }
private def node (context : Context) (id : TypeId) : Result TypeNode :=
  (context.runtime.node id).mapError toString
private def facts (context : Context) (id : TypeId) : Result TypeCompilerFacts := do
  let source ← (context.runtime.node id).mapError toString
  let some facts := source.compilerFacts | throw s!"missing compiler_facts for type {id}"
  unless facts.typingEnvironment == "fully_monomorphized" do
    throw "compiler query typing-environment mismatch"
  pure facts

def boolean (context : Context) (id : TypeId) (query : String) : Result Bool := do
  let source ← (context.runtime.node id).mapError toString
  if query == "is_dynamic" then return source.shapeKind == .dynamicTraitObject
  if query == "is_too_generic" then return source.shapeKind == .alias
  let value ← facts context id
  let some (_,result) := value.booleanQueries.find? (·.1 == query)
    | throw s!"missing exact rustc boolean result {query}"
  pure result

def optionalType (context : Context) (id : TypeId) (query : String) : Result (Option TypeId) := do
  let source ← node context id
  let entry ← if query == "builtin_deref_explicit" || query == "builtin_deref_implicit" || query == "boxed_type" then do
      -- Signature-bound source material keeps its Binder graph while facts
      -- use the explicitly instantiated query view recorded by the exporter.
      let source ← node context (source.layoutQueryInputTypeId.getD id)
      let isBox ← if source.shapeKind == .adt then do
        let f ← facts context id
        let some (_, isBox) := f.booleanQueries.find? (·.1 == "is_box")
          | throw "missing Box definition identity"
        pure isBox
      else pure false
      if query == "boxed_type" then StructuralDeref.boxedType source.shape isBox
      else StructuralDeref.builtinDeref source.shape isBox (query == "builtin_deref_explicit")
    else if id >= context.program.input.types.size && query == "unsafe_binder_erased" then
      pure none
    else do
      let f ← facts context id
      let some (_, entry) := f.typeQueries.find? (·.1 == query)
        | throw s!"missing compiler type query {query}"
      pure entry
  if let some ty := entry then let _ ← node context ty
  pure entry

def requiredType (context : Context) (id : TypeId) (query : String) : Result TypeId := do
  let some ty ← optionalType context id query | throw s!"compiler query {query} returned None"
  pure ty
def layoutOf (context : Context) (id : TypeId) : Result (TyAndLayout TypeId) :=
  (context.runtime.lookup id).mapError toString

def unitLayout (context : Context) : Result (TyAndLayout TypeId) :=
  computeUnitLayout context.runtime

def builtinDeref (context : Context) (id : TypeId) (explicit : Bool) : Result (Option TypeId) :=
  optionalType context id (if explicit then "builtin_deref_explicit" else "builtin_deref_implicit")

def referencePointee (context : Context) (id : TypeId) : Result (TypeId × MIR.Mutability) := do
  let source ← node context id
  let .reference pointee mutability _ := source.shape
    | throw "reference_pointee requested for a non-reference"
  let _ ← node context pointee
  pure (pointee,mutability)

def retagTypeShape (context : Context) (id : TypeId) : Result Miri.TreeBorrows.RetagPipeline.RetagTypeShape := do
  let source ← node context id
  pure ⟨← boolean context id "is_global_box",source.shapeKind == .reference,
    source.shapeKind == .rawPointer,← boolean context id "is_box"⟩

private def adtShape (context : Context) (id : TypeId) : Result AdtShape := do
  let .adt value := (← node context id).shape | throw "ADT layout query on non-ADT"
  pure value

def adtInfo (context : Context) (id : TypeId) : Result (LayoutCompat.AdtInfo TypeId) := do
  let data ← adtShape context id
  let kind := match data.kind with
    | .structKind => LayoutCompat.AdtKind.Struct | .unionKind => .Union | .enumKind => .Enum
  let variants := data.variants.map fun variant => variant.fields.map fun field =>
    ({ name := field.name, ty := field.typeId } : LayoutCompat.Field TypeId)
  pure ⟨kind,data.representation.transparent,data.representation.c,data.representation.rust,variants⟩

private def lift (value : Result A) : EStateM StepError S A :=
  match value with | .ok value => pure value | .error error => throw (.invalidProgram error)

/-- Replace only compiler leaves; all actual memory/projection/dyn operations
retain their source implementation and stateful failure behavior. -/
def typedRetagHooks (context : Context) (machine : TypedRetag.Hooks K U) : TypedRetag.Hooks K U :=
  { machine with
    typeShape := fun ty => lift (retagTypeShape context ty)
    builtinDeref := fun ty => lift (requiredType context ty "builtin_deref_explicit")
    referencePointee := fun ty => lift (referencePointee context ty)
    isUnpin := fun ty => lift (boolean context ty "is_unpin")
    isUnsafeUnpin := fun ty => lift (boolean context ty "is_unsafe_unpin")
    typeIsFreeze := fun ty => lift (boolean context ty "is_freeze")
    freeze := { machine.freeze with
      isUnsafeCell := fun ty => lift (boolean context ty "is_unsafe_cell")
      typeIsFreeze := fun ty => lift (boolean context ty "is_freeze")
      isDynamic := fun ty => lift (boolean context ty "is_dynamic")
      isBox := fun ty => lift (boolean context ty "is_box")
      isTooGeneric := fun ty => lift (boolean context ty "is_too_generic") } }

end Miri.Input.CompilerFacts
