import Miri.Input.SourceCompilerWorld

/-! Source-backed auto-trait queries for retag. Pinned util.rs trivial fastpaths
are independent of impl selection. A closure is not trivial: selection requires
an auto declaration and complete exclusion of every relevant manual impl, then
recurses through tupled_upvars (select/mod.rs::constituent_types_for_auto_trait).
Unknown or potentially matching headers never become negative evidence. -/
namespace Miri.Input.SourceCompilerAutoTraits
open SourceAbi
abbrev Role := AutoTraitRole
abbrev World := SourceCompilerWorld.World

private def typeNode (world : World) (id : Nat) : Except String TypeNode := do
  let some node := world.canonical.types[id]? | throw "auto trait canonical type absent"
  return node

/-- The exact same trivial fastpath covers Unpin and UnsafeUnpin. Freeze has
this same constructor domain in the pinned compiler. Failure is unknown. -/
private def trivial (world : World) (id : Nat) : Except String Bool := go (world.canonical.types.size+1) id
where
  go (fuel : Nat) (id : Nat) : Except String Bool := do
    let .succ fuel := fuel | throw "auto trait trivial traversal exhausted"
    match (← typeNode world id).shape with
    | .bool | .char | .int _ | .uint _ | .float _ | .str | .never | .reference .. |
      .rawPointer .. | .functionDefinition .. | .functionPointer .. => pure true
    | .array child .. | .slice child | .patternType child _ => go fuel child
    | .tuple fields =>
      for field in fields do unless (← go fuel field) do return false
      pure true
    | _ => pure false

private def declaration (world : World) (role : Role) : Except String AutoDeclaration := do
  let some source := world.canonical.sourceMaterial | throw "auto trait typed source absent"
  let some abi := source.abi | throw "auto trait declaration source unavailable"
  let some material := abi.autoTraits | throw "auto trait language item/header source unavailable"
  let some (_,some definition) := material.langItems.find? (·.1 == role)
    | throw "auto trait language item absent"
  let matching := material.declarations.filter (·.definition == definition)
  let [declaration] := matching.toList | throw "auto trait declaration absent/ambiguous"
  unless declaration.isAuto && declaration.hasSelf && declaration.parameters == #[(0,false)] &&
      declaration.associatedItems == 0 && declaration.complete do
    throw "auto trait source declaration domain unsupported/incomplete"
  unless declaration.langItem == some role do throw "auto trait language identity mismatch"
  for clause in declaration.clauses do
    match clause with
    | .ok _ => pure ()
    | .error reason => throw reason
  return declaration

/-- Exclusion uses only rigid outer constructor identity. A candidate of the
same closure/tuple root or any unknown/alias root needs further selection
material and is Unsupported, including negative and reservation impls. -/
private def outer : AutoSelfHead → AutoSelfHead
  | .pattern base _ => outer base
  | head => head

private def exclude (declaration : AutoDeclaration) (head : AutoSelfHead) : Except String Unit := do
  for implementation in declaration.implementations do
    let disjoint := match outer implementation.selfHead,outer head with
      | .unknown,_ => false
      | .closure a,.closure b => a != b
      | .tuple a,.tuple b => a != b
      | .adt a,.adt b => a != b
      | .functionDefinition a,.functionDefinition b => a != b
      | .coroutineClosure a,.coroutineClosure b => a != b
      | .rigid a,.rigid b => a != b
      | _,_ => true
    unless disjoint do throw "auto trait manual impl may apply; selection source unsupported"

def check (world : World) (role : Role) (id : Nat) : Except String Bool :=
  go (world.canonical.types.size+1) #[] id
where
  go (fuel : Nat) (active : Array Nat) (id : Nat) : Except String Bool := do
    if ← trivial world id then return true
    let .succ fuel := fuel | throw "auto trait constituent traversal exhausted"
    unless !active.contains id do throw "auto trait cyclic constituent proof unsupported"
    let source ← declaration world role
    let node ← typeNode world id
    let (head,children) ← match node.shape with
      | .closure definition args count => do
        let some raw := world.canonical.definitions[definition]? | throw "auto trait closure identity absent"
        let some (.Type tuple) := args.back? | throw "auto trait closure upvar tuple absent"
        let .tuple fields := (← typeNode world tuple).shape | throw "auto trait closure upvars are not tuple"
        unless fields.size == count do throw "auto trait closure capture count mismatch"
        pure (AutoSelfHead.closure raw,#[tuple])
      | .tuple fields => pure (AutoSelfHead.tuple fields.size,fields)
      | .array child .. => pure (.rigid "array",#[child])
      | .slice child => pure (.rigid "slice",#[child])
      | _ => throw "auto trait nontrivial source type domain unsupported"
    exclude source head
    for child in children do
      unless (← go fuel (active.push id) child) do return false
    return true
end Miri.Input.SourceCompilerAutoTraits
