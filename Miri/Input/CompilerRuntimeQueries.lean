import Miri.Input.CompilerScopes

/-! Type constructors preserve source identity: equal physical layouts cannot
substitute for the requested pointer, reference, or concrete shim. -/
namespace Miri.Input.CompilerRuntimeQueries
open Lean Miri.Interpreter
structure Prepared where
  program : LoweredProgram
  callerLocation : Array (CallInstance × Bool)
def prepare (program : LoweredProgram) : Except String Prepared := do
  let some abi := program.input.sourceAbi | throw "source ABI definitions are absent"
  let callers := abi.definitions.filterMap fun definition => definition.map fun definition =>
    (definition.instanceId,definition.callerLocation.isSome)
  pure ⟨program,callers⟩

def mutPointerType (prepared : Prepared) (id : Nat) : Except String Nat := do
  let candidates := prepared.program.input.types.filter fun node => match node.shape with
    | .rawPointer pointee .Mut => pointee == id
    | _ => false
  unless candidates.size == 1 do throw "canonical mutable pointer type is absent or ambiguous"
  let some result := candidates[0]? | throw "mutable pointer type index invariant"
  pure result.id

def mutReferenceType (prepared : Prepared) (id : Nat) : Except String Nat := do
  let candidates := prepared.program.input.types.filter fun node => match node.shape with
    | .reference pointee .Mut .Erased => pointee == id
    | _ => false
  unless candidates.size == 1 do throw "canonical erased mutable reference type is absent or ambiguous"
  let some result := candidates[0]? | throw "mutable reference type index invariant"
  pure result.id

def resolveDropGlue (prepared : Prepared) (id : Nat) : Except String CallInstance := do
  let some node := prepared.program.input.types[id]? | throw "drop type is absent"
  let normalized := node.sourceLayout.normalizedType
  let candidates := prepared.program.input.instances.filter fun candidate => match candidate.instanceKind with
    | .Shim (.DropGlue _ ty) =>
      (candidate.genericArgs[0]? == some (.Type normalized)) && (ty.isNone || ty == some normalized)
    | _ => false
  unless candidates.size == 1 do throw "collected concrete drop glue is absent or ambiguous"
  let some callee := candidates[0]? | throw "drop glue index invariant"
  pure callee.id

def requiresCallerLocation (prepared : Prepared) (callee : CallInstance) : Except String Bool := do
  let node ← CompilerInstance.source prepared.program.input.instances callee
  match node.instanceKind with
  | .Item _ | .Virtual .. | .Shim (.VTable _) =>
    let some (_,track) := prepared.callerLocation.find? (·.1 == callee)
      | throw "source caller-location attributes are absent"
    pure track
  | .Shim (.ClosureOnce _ _ track) => pure track
  | _ => pure false
def parentTrait (prepared : Prepared) (method : MIR.DefId) : Except String MIR.DefId := do
  let candidates := prepared.program.input.sourceTraits.declarations.filter (·.ownVtableMethods.contains method)
  unless candidates.size == 1 do throw "method owner trait declaration is absent or ambiguous"
  let some declaration := candidates[0]? | throw "method owner index invariant"
  pure declaration.definition

def rebaseVirtualArgs (prepared : Prepared) (args : Array MIR.GenericArg)
    (parent : MIR.DefId) (concrete : Nat) : Except String (Array MIR.GenericArg) := do
  let some declaration := prepared.program.input.sourceTraits.declarations.find? (·.definition == parent)
    | throw "virtual method parent declaration is absent"
  unless !declaration.parameters.isEmpty && declaration.parameters.size ≤ args.size do
    throw "virtual method arguments do not contain the parent trait prefix"
  if bound : 0 < args.size then
    pure (args.set 0 (.Type concrete) bound)
  else throw "virtual method Self argument invariant"

def expectResolveForVTable (prepared : Prepared) (method : MIR.DefId)
    (args : Array MIR.GenericArg) : Except String CallInstance := do
  let some self := args[0]? | throw "vtable method has no Self argument"
  let MIR.GenericArg.Type concrete := self | throw "vtable method has no concrete Self type"
  let document := prepared.program.input
  let mut result := none
  for binding in document.sourceVtables.bindings do
    if binding.typeId != concrete then continue
    for methodBinding in binding.methods do
      if methodBinding.definition != method then continue
      let some owner := document.predicates[methodBinding.owner]? | throw "vtable owner predicate is absent"
      let prefixSize := owner.genericArgs.size+1
      if args.size < prefixSize || args.extract 1 prefixSize != owner.genericArgs then continue
      unless (args.extract prefixSize args.size).all (fun arg => match arg with | .Lifetime .Erased => true | _ => false) do
        throw "object method has non-erased generic arguments"
      let some callee := methodBinding.instanceId | throw "selected vtable method is vacant"
      if let some previous := result then
        unless previous == callee do throw "conflicting concrete vtable method bindings"
      result := some callee
  let some callee := result | throw "concrete vtable method binding is absent"
  pure callee
private def lift (result : Except String A) : EStateM StepError S A :=
  match result with
  | .ok result => pure result
  | .error error => throw (.invalidProgram error)

def hooks (prepared : Prepared) (base : VirtualCalls.CompilerHooks S C) :
    VirtualCalls.CompilerHooks S C :=
  { base with
    instanceArgs := fun inst => lift (CompilerInstance.argsOf
      prepared.program.input.instances inst)
    mutPointerType := fun ty => lift (mutPointerType prepared ty)
    mutReferenceType := fun ty => lift (mutReferenceType prepared ty)
    resolveDropGlue := fun ty => lift (resolveDropGlue prepared ty)
    requiresCallerLocation := fun callee => lift (requiresCallerLocation prepared callee)
    parentTrait := fun method => lift (parentTrait prepared method)
    rebaseVirtualArgs := fun args parent concrete => lift (rebaseVirtualArgs prepared args parent concrete)
    expectResolveForVTable := fun _ method args => lift (expectResolveForVTable prepared method args) }
end Miri.Input.CompilerRuntimeQueries
