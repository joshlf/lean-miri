import Miri.Frontend.FoundationClosureVtableImage
import Miri.Frontend.FoundationFnAbi

/-! Pinned Fn-family method fulfillment and call-shim generation. This narrow
slice admits a Fn closure with one fn-pointer upvar, unit tupled input and supported scalar
output at optNo on x86_64. Identities remain symbolic: no MIR/instance/type/
layout/AllocId table indices are synthesized. The retained parent environment
is not a claim that the closure's ordinary Rust body can already execute.

Rules: traits/mod.rs::instantiate_and_check_impossible_clauses,
mir_transform/shim.rs::build_call_shim, ty_utils/abi.rs::fn_sig_for_fn_abi.
ClosureOnce's two Drop blocks are preserved even for a non-dropping concrete
capture: its MIR is generic, unlike the monomorphized ABI query. -/
namespace Miri.Frontend.Foundation
open Lean

private def paramArgument (index : Nat) : Json :=
  Json.mkObj [("kind",toJson "type"),("type",Json.mkObj [("kind",toJson "param"),("index",toJson index)])]

private def methodRow (source : FnVtableDeclarations) (traitId method : Nat) : Except String Json := do
  let row ← fnSourceDeclaration source traitId
  let rows ← (← row.getObjValAs? (Array Json) "associated_items").filterM fun item =>
    return (← item.getObjValAs? Nat "definition") == method
  let some row := rows[0]? | throw "Fn shim method declaration absent"
  unless rows.size == 1 do throw "Fn shim method declaration duplicated"
  row.getObjVal? "method"

/-- Exact complete inherited predicate shapes for this pinned Fn family.
Unknown/bound/negative clauses cannot be counted as merely ambiguous success.
Each admitted predicate has a positive builtin witness: sized unit Args, tuple
Args, sized closure Self, or the selected compatible builtin closure signature. -/
private def checkMethodClauses (source : FnVtableDeclarations) (traitId method : Nat)
    (kind : SourceClosureKind) : Except String Unit := do
  let row ← methodRow source traitId method
  let owners ← row.getObjValAs? (Array Json) "clause_source"
  unless owners.size == 2 do throw "Fn method predicate parent chain unsupported"
  let some own := owners[0]? | throw "Fn method own predicate source missing"
  let some parent := owners[1]? | throw "Fn method parent predicate source missing"
  unless (← own.getObjValAs? Nat "definition") == method &&
      (← own.getObjValAs? (Option Nat) "parent") == some traitId &&
      (← own.getObjValAs? (Array Json) "clauses").isEmpty &&
      (← parent.getObjValAs? Nat "definition") == traitId &&
      (← parent.getObjValAs? (Option Nat) "parent").isNone do
    throw "Fn method predicate source chain mismatch"
  let inherited := match kind with
    | .fnOnce => #[]
    | .fnMut => #[("fn_once",#[paramArgument 0,paramArgument 1])]
    | .fn => #[("fn_mut",#[paramArgument 0,paramArgument 1])]
  let ownKind := match kind with | .fn => "fn" | .fnMut => "fn_mut" | .fnOnce => "fn_once"
  let expected := #[("meta_sized",#[paramArgument 0])] ++ inherited ++
    #[("sized",#[paramArgument 1]),("tuple",#[paramArgument 1]),
      (ownKind,#[paramArgument 0,paramArgument 1])]
  let clauses ← parent.getObjValAs? (Array Json) "clauses"
  unless clauses.size == expected.size do throw "Fn method complete predicate count mismatch"
  for (clause,(name,arguments)) in clauses.zip expected do
    unless (← clause.getObjValAs? String "kind") == "trait" &&
        (← clause.getObjValAs? String "polarity") == "Positive" &&
        (← clause.getObjValAs? Bool "core_source") &&
        (← clause.getObjValAs? (Array Json) "bound_variables").isEmpty &&
        (← clause.getObjValAs? String "lang_item") == name &&
        (← clause.getObjValAs? (Array Json) "arguments") == arguments do
      throw "Fn method predicate source unsupported"
    let id ← clause.getObjValAs? Nat "definition"
    unless id < source.definitions.size do throw "Fn predicate source identity out of bounds"
    if #["fn","fn_mut","fn_once"].contains name then
      unless id == (← fnSourceRoot source name) do throw "Fn predicate language identity mismatch"
    if name == "meta_sized" then
      let marker ← fnSourceDeclaration source id
      unless (← marker.getObjValAs? String "lang_item") == "meta_sized" do
        throw "Fn metadata marker language identity mismatch"

inductive ResolvedClosureVtableCell where
  | nullDrop
  | unsigned (value : Nat)
  | method (target : BuiltinClosureCandidate)

structure ResolvedClosureVtableMethods where
  image : ClosureVtableImageCandidate
  /-- All source clauses succeeded; no Vacant branch remains in this domain. -/
  methods : Array BuiltinClosureCandidate
  cells : Array ResolvedClosureVtableCell

/-- The supported Self is sized, unit is a sized Tuple, and compatible builtin
Fn signatures discharge every captured method predicate plus associated-trait
fulfillment. This discharges slot presence, not unrelated closure-parent bounds. -/
def resolveClosureVtableMethods (document : Document) (definition : Nat)
    (parentArguments : Array ItemArgument) (tupledInputs output : ConcreteType) : Except String ResolvedClosureVtableMethods := do
  let .tuple inputs := tupledInputs | throw "closure shim Args are not a tuple"
  unless inputs.isEmpty do throw "closure shim nonempty Args layout unsupported"
  let tuple := tupledInputs
  let image ← closureVtableImageCandidate document definition parentArguments .fn tuple output
  let source ← readFnVtableDeclarations document.source
  let plan ← builtinClosureVtableCandidates document definition parentArguments .fn tuple output
  let some first := plan.methods[0]? | throw "closure method source absent"
  unless first.closure.kind == .fn do throw "resolved Fn closure requires Fn kind"
  let mut methods := #[]
  for (kind,name) in #[(SourceClosureKind.fnOnce,"fn_once"),(.fnMut,"fn_mut"),(.fn,"fn")] do
    let traitId ← fnSourceRoot source name
    let item ← builtinClosureCandidate document definition parentArguments kind tuple output true
    let method ← match item.recipe with
      | .vtable method _ _ => pure method
      | .closureItem _ => do
        let declaration ← fnSourceDeclaration source traitId
        let members ← (← declaration.getObjValAs? (Array Json) "associated_items").filterM fun member =>
          return (← member.getObjValAs? String "kind") == "method"
        let some member := members[0]? | throw "Fn source method absent"
        member.getObjValAs? Nat "definition"
      | _ => throw "resolved Fn vtable constructor unsupported"
    checkMethodClauses source traitId method kind
    methods := methods.push item
  let cells := image.cells.map fun cell => match cell with
    | .nullDrop => ResolvedClosureVtableCell.nullDrop
    | .unsigned value => .unsigned value
    | .methodOrVacant target => .method target
  return ⟨image,methods,cells⟩

inductive ClosureShimType where
  | output | unit | closure | rawMutClosure | mutRefClosure
  deriving Repr, DecidableEq
inductive ClosureShimReceiver where
  | dereferenceLocalOne | mutableBorrowLocalThree
  deriving Repr, DecidableEq
inductive ClosureShimTerminator where
  | call (method : Nat) (callee : BuiltinCallableRecipe) (receiver : ClosureShimReceiver)
      (target : Nat) (unwindCleanup : Option Nat)
  | dropReceiver (target : Nat) (terminateOnUnwind : Bool)
  | returnValue | resumeUnwind
structure ClosureShimBlock where
  cleanup : Bool
  borrowReceiverIntoThree : Bool
  terminator : ClosureShimTerminator
structure ClosureShimBody where
  locals : Array ClosureShimType
  argumentCount : Nat
  spreadArgument : Nat
  blocks : Array ClosureShimBlock
  outputType : ConcreteType
  sourceSpan : Json
  sourceSpanKey : Json

/-- Finite call-shim construction with symbolic closure/type/function identity.
The direct call always passes the receiver and local2 unit tuple to local0.
No physical MIR Body can be returned before a checked closure registry exists. -/
def closureShimBody (document : Document) (definition : Nat)
    (parentArguments : Array ItemArgument) (tupledInputs output : ConcreteType)
    (vtable : Bool) : Except String ClosureShimBody := do
  let resolved ← resolveClosureVtableMethods document definition parentArguments tupledInputs output
  let some method := resolved.methods[0]? | throw "closure shim method source absent"
  let .vtable methodId _ _ := method.recipe | throw "closure shim method recipe mismatch"
  let source ← readFnVtableDeclarations document.source
  let row ← methodRow source (← fnSourceRoot source "fn_once") methodId
  let span ← row.getObjVal? "source_span"
  let spanKey ← row.getObjVal? "source_span_key"
  let _ ← spanKey.getObjValAs? Nat "lo"
  let _ ← spanKey.getObjValAs? Nat "hi"
  let _ ← spanKey.getObjValAs? String "ctxt"
  let _ ← spanKey.getObjValAs? (Option Nat) "parent_local_definition"
  let tuple := tupledInputs
  let calleeKind := if vtable then "fn_once" else "fn_mut"
  let calleeDeclaration ← fnSourceDeclaration source (← fnSourceRoot source calleeKind)
  let calleeMembers ← (← calleeDeclaration.getObjValAs? (Array Json) "associated_items").filterM fun member =>
    return (← member.getObjValAs? String "kind") == "method"
  let some calleeMember := calleeMembers[0]? | throw "shim callee declaration absent"
  unless calleeMembers.size == 1 do throw "shim callee declaration ambiguous"
  let calleeMethod ← calleeMember.getObjValAs? Nat "definition"
  let target ← builtinClosureCandidate document definition parentArguments
    (if vtable then .fnOnce else .fnMut) tuple output
  if vtable then
    return ⟨#[.output,.rawMutClosure,.unit],2,2,
      #[⟨false,false,.call calleeMethod target.recipe .dereferenceLocalOne 1 none⟩,
        ⟨false,false,.returnValue⟩],output,span,spanKey⟩
  return ⟨#[.output,.closure,.unit,.mutRefClosure],2,2,
    #[⟨false,true,.call calleeMethod target.recipe .mutableBorrowLocalThree 1 (some 3)⟩,
      ⟨false,false,.dropReceiver 2 false⟩,⟨false,false,.returnValue⟩,
      ⟨true,false,.dropReceiver 4 true⟩,⟨true,false,.resumeUnwind⟩],output,span,spanKey⟩

structure ClosureShimAbi where
  receiver : ClosureShimType
  receiverLayout : FoundationLayout
  receiverMode : Miri.Input.AbiPassMode
  outputLayout : FoundationLayout
  outputMode : Miri.Input.AbiPassMode
  canUnwind : Bool
  fixedCount : Nat
  cVariadic : Bool
  callingConvention : Miri.Input.CanonicalAbi

/-- RustCall untuples the empty tuple: fixedCount is one, not the MIR argCount
of two. Sole fn-pointer capture scalar ABI retains NonNull; VTable's raw pointer
receiver does not. Reject optimizer-dependent or non-x86_64 cases. -/
def closureShimAbi (document : Document) (definition : Nat)
    (parentArguments : Array ItemArgument) (tupledInputs output : ConcreteType)
    (vtable : Bool) : Except String ClosureShimAbi := do
  let methods ← resolveClosureVtableMethods document definition parentArguments tupledInputs output
  let compilation ← document.source.getObjVal? "compilation"
  unless (← compilation.getObjValAs? String "opt_level") == "No" &&
      document.target.pointerSizeBits == 64 &&
      document.target.architecture == "x86_64" do
    throw "closure shim ABI requires optNo x86_64 source"
  let declarations ← readFnVtableDeclarations document.source
  let fnOnce ← fnSourceRoot declarations "fn_once"
  let some first := methods.methods[0]? | throw "closure shim method missing"
  let .vtable method _ _ := first.recipe | throw "closure shim constructor mismatch"
  let row ← methodRow declarations fnOnce method
  let never ← row.getObjValAs? Bool "never_unwind"
  let foreign ← row.getObjValAs? Bool "is_foreign"
  let panic ← compilation.getObjValAs? String "panic_strategy"
  unless panic == "unwind" || panic == "abort" do throw "closure shim panic strategy unsupported"
  let mode : Miri.Input.AbiPassMode := ⟨.direct,
    #[⟨if vtable then 128 else 144,0,none,.none⟩],none,none,none,none⟩
  let layout ← if vtable then
      layoutOfDocument document (.functionPointer #[] (.tuple #[]) "safe" "rust" false)
    else pure methods.image.selfLayout
  return ⟨if vtable then .rawMutClosure else .closure,layout,mode,
    ← layoutOfDocument document output,← rustPassModeOfDocument document true output,
    rustCanUnwind ⟨true,never,panic == "unwind",foreign,true,false⟩,1,false,⟨.rust,none,none,none⟩⟩

end Miri.Frontend.Foundation
