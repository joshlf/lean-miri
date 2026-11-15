import Miri.Frontend.FoundationClosure
import Miri.Frontend.FoundationFnVtable
import Miri.Frontend.FoundationRegionErasure

/-! Builtin callable recipes from finite closure/function-pointer source.
Pinned select/candidate_assembly.rs requires closure_kind.extends(requested),
confirmation.rs unifies the tuple signature, and ty/instance.rs selects the
Item/ClosureOnce/FnPtr/VTable constructors below. These are source recipes, not
executable InstanceNodes: parent predicates, shim MIR/ABI and allocation identity
remain explicit missing joins. No compiler selection answer is consumed. -/
namespace Miri.Frontend.Foundation
open Lean

structure ClosureSourceKey where
  definition : Nat
  arguments : Array ItemArgument
  deriving Repr

inductive CallableSourceKey where
  | closure (key : ClosureSourceKey)
  | functionPointer (type : ConcreteType)
  deriving Repr

inductive BuiltinCallableRecipe where
  | closureItem (key : ClosureSourceKey)
  | closureOnce (callOnce : Nat) (key : ClosureSourceKey) (trackCaller : Bool) (tupledInputs : ConcreteType)
  | fnPointer (method : Nat) (pointerType tupledInputs : ConcreteType)
  | vtable (method : Nat) (self : CallableSourceKey) (tupledInputs : ConcreteType)
  deriving Repr

structure BuiltinClosureCandidate where
  recipe : BuiltinCallableRecipe
  closure : SelectedClosureTemplate
  /-- Retained premises are not silently treated as discharged. -/
  parentEnvironment : Json
  parentArguments : Array ItemArgument

/-- The compiler's known-kind branch. Unknown/inferred kinds are not represented
by SourceClosureKind and cannot turn into successful candidates here. -/
def sourceClosureSupports (actual requested : SourceClosureKind) : Bool :=
  match actual, requested with
  | .fn, _ | .fnMut, .fnMut | .fnMut, .fnOnce | .fnOnce, .fnOnce => true
  | _, _ => false

private def goalMethod (document : Document) (requested : SourceClosureKind) : Except String Nat := do
  let source ← readFnVtableDeclarations document.source
  let name := match requested with | .fn => "fn" | .fnMut => "fn_mut" | .fnOnce => "fn_once"
  let principal ← fnSourceRoot source name
  let plan ← fnVtableCandidates source principal
  let methods := plan.slots.filterMap fun slot => match slot with
    | .methodOrVacant traitId method _ => if traitId == principal then some method else none
    | _ => none
  unless methods.size == 1 do throw "callable source method identity absent or duplicate"
  let some method := methods[0]? | throw "callable source method absent"
  return method

private def signatureMatches (actualTuple actualOutput requestedTuple requestedOutput : ConcreteType) : Except String Unit := do
  let .tuple _ := requestedTuple | throw "builtin Fn arguments are not a tuple"
  unless sameConcrete 1024 (← eraseRegions actualTuple) (← eraseRegions requestedTuple) &&
      sameConcrete 1024 (← eraseRegions actualOutput) (← eraseRegions requestedOutput) do
    throw "builtin Fn tuple or Output source mismatch"

/-- Ordinary closure selection and the vtable adjustment are separate source
branches. In particular, a by-value Self method becomes VTableShim before
ordinary FnOnce adapter resolution in rustc. Track-caller reification for
reference slots remains unsupported rather than returning a wrong Item. -/
def builtinClosureCandidate (document : Document) (definition : Nat)
    (parentArguments : Array ItemArgument) (requested : SourceClosureKind)
    (tupledInputs output : ConcreteType) (forVtable : Bool := false) : Except String BuiltinClosureCandidate := do
  let selected ← selectClosureTemplate document definition parentArguments
  unless sourceClosureSupports selected.kind requested do throw "closure kind does not implement requested Fn source family"
  unless selected.signature.safety == "safe" && !selected.signature.cVariadic &&
      (← selected.signature.abi.getObjValAs? String "kind") == "rust_call" do
    throw "closure builtin signature is not safe nonvariadic RustCall"
  unless selected.signature.inputs.size == 1 do throw "closure RustCall source signature must have one tuple"
  let some actualTuple := selected.signature.inputs[0]? | throw "closure source tuple absent"
  signatureMatches actualTuple selected.signature.output tupledInputs output
  let trackCaller ← selected.body.getObjValAs? Bool "track_caller"
  let method ← goalMethod document requested
  let arguments ← selected.fullArguments.mapM fun argument => do
    match argument with
    | .type value => return ItemArgument.type (← eraseRegions value)
    | .constant _ => throw "const closure source argument normalization unsupported"
  let tupledInputs ← eraseRegions tupledInputs
  let key : ClosureSourceKey := ⟨definition,arguments⟩
  let recipe ← if forVtable && requested == .fnOnce then
    pure (.vtable method (.closure key) tupledInputs)
  else if forVtable && trackCaller then
    throw "track-caller closure vtable reification source is unsupported"
  else if requested == .fnOnce && selected.kind != .fnOnce then
    pure (.closureOnce method key trackCaller tupledInputs)
  else pure (.closureItem key)
  return ⟨recipe,selected,selected.parentEnvironment,parentArguments⟩

/-- FnSig::is_fn_trait_compatible requires Rust ABI, safe and nonvariadic. The
function-pointer builtin is not a blanket implementation for foreign/unsafe
functions; no empty impl catalog is presumed. -/
def builtinFnPointerRecipe (document : Document) (pointerType : ConcreteType)
    (requested : SourceClosureKind) (tupledInputs output : ConcreteType)
    (forVtable : Bool := false) : Except String BuiltinCallableRecipe := do
  let pointerType ← eraseRegions pointerType
  let tupledInputs ← eraseRegions tupledInputs
  let .functionPointer inputs actualOutput safety abi variadic := pointerType
    | throw "builtin Fn pointer source is not a function pointer"
  unless safety == "safe" && abi == "rust" && !variadic do
    throw "function pointer does not satisfy builtin Fn signature source rule"
  signatureMatches (.tuple inputs) actualOutput tupledInputs output
  let method ← goalMethod document requested
  if forVtable && requested == .fnOnce then
    return .vtable method (.functionPointer pointerType) tupledInputs
  return .fnPointer method pointerType tupledInputs

structure BuiltinClosureVtableCandidates where
  shape : FnVtableCandidatePlan
  methods : Array BuiltinClosureCandidate

/-- Connect each declaration slot candidate to the builtin callable constructor
recipe for one requested concrete closure. Metadata/drop values, vacant-slot
proofs, auto traits, shim MIR/ABI and allocation identities are still absent. -/
def builtinClosureVtableCandidates (document : Document) (definition : Nat)
    (parentArguments : Array ItemArgument) (principal : SourceClosureKind)
    (tupledInputs output : ConcreteType) : Except String BuiltinClosureVtableCandidates := do
  let source ← readFnVtableDeclarations document.source
  let name := match principal with | .fn => "fn" | .fnMut => "fn_mut" | .fnOnce => "fn_once"
  let root ← fnSourceRoot source name
  let shape ← fnVtableCandidates source root
  let mut methods := #[]
  for slot in shape.slots do
    if let .methodOrVacant traitId _ _ := slot then
      let requested ← if traitId == (← fnSourceRoot source "fn") then pure SourceClosureKind.fn
        else if traitId == (← fnSourceRoot source "fn_mut") then pure .fnMut
        else if traitId == (← fnSourceRoot source "fn_once") then pure .fnOnce
        else throw "unknown callable source trait slot"
      methods := methods.push (← builtinClosureCandidate document definition parentArguments requested tupledInputs output true)
  return ⟨shape,methods⟩

end Miri.Frontend.Foundation
