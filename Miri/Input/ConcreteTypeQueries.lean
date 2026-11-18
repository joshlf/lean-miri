import Miri.Input.ConcreteTraitQueries

namespace Miri.Input.ConcreteTypeQueries
open Miri.MIR

private def node (runtime : RuntimeMetadata) (id : TypeId) : Except String TypeNode :=
  runtime.node id |>.mapError toString

private def unique (runtime : RuntimeMetadata) (predicate : TypeNode → Bool) : Except String TypeId := do
  let values := runtime.source.types.filter predicate
  let some value := values[0]? | throw "required concrete type is absent"
  unless values.size == 1 do throw "concrete type identity is ambiguous"
  return value.id

def integerType (runtime : RuntimeMetadata) (kind : IntegerKind) : Except String TypeId :=
  unique runtime fun node => node.shapeMetadata.signedKind == some (.known kind) ||
    node.shapeMetadata.unsignedKind == some (.known kind)

def boxedType (runtime : RuntimeMetadata) (id : TypeId) : Except String (Option TypeId) := do
  let value ← node runtime id
  unless value.sourceLayout.isBox do return none
  let .adt data := value.shape | throw "Box declaration is attached to a non-ADT"
  let some argument := data.args[0]? | throw "Box pointee type argument is absent"
  let GenericArg.Type id := argument | throw "Box pointee argument is not a type"
  return some id

def metadataTail (runtime : RuntimeMetadata) (id : TypeId) : Except String TypeId := do
  go (runtime.source.types.size + 1) (← node runtime id).sourceLayout.normalizedType
where
  go (fuel id : Nat) : Except String TypeId := do
    let .succ fuel := fuel | throw "recursive unsized type tail"
    let value ← node runtime id
    match value.shape with
    | .adt data =>
      if data.kind == .structKind then
        if let some variant := data.variants[0]? then
          if let some field := variant.fields.back? then return ← go fuel field.typeId
      return id
    | .tuple fields =>
      if let some field := fields.back? then return ← go fuel field
      return id
    | .patternType base _ => go fuel base
    | _ => return id

def pointerMetadataType (runtime : RuntimeMetadata) (id : TypeId) : Except String TypeId := do
  let tail ← metadataTail runtime id
  let value ← node runtime tail
  match value.shape with
  | .str | .slice _ => integerType runtime .usize
  | .dynamicTraitObject .. =>
    unique runtime fun candidate =>
      candidate.sourceLayout.isDynMetadata && match candidate.shape with
        | .adt data => data.args[0]? == some (.Type tail)
        | _ => false
  | .unsafeBinder .. => throw "pointer metadata of an unsafe binder is unsupported by pinned rustc"
  | .alias .. => throw "unnormalized alias in pointer metadata query"
  | _ => unique runtime fun candidate => match candidate.shape with
      | .tuple fields => fields.isEmpty | _ => false

def discriminantType (runtime : RuntimeMetadata) (id : TypeId) : Except String TypeId := do
  go (runtime.source.types.size + 1) (← node runtime id).sourceLayout.normalizedType
where
  go (fuel id : Nat) : Except String TypeId := do
    let .succ fuel := fuel | throw "recursive discriminant type"
    let value ← node runtime id
    match value.shape with
    | .adt data =>
      if data.kind != .enumKind then return ← integerType runtime .u8
      let kind := match data.representation.integer with
        | none => IntegerKind.isize
        | some repr => match repr with
          | .pointerSized signed => if signed then .isize else .usize
          | .fixed (.known kind) _ _ => kind
      integerType runtime kind
    | .patternType base _ | .unsafeBinder base _ => go fuel base
    | .coroutine .. => integerType runtime .u32
    | _ => integerType runtime .u8

private def arrayLength (runtime : RuntimeMetadata) (id : TypeConstantId) : Except String Nat := do
  let some (.Value _ tree) := runtime.source.typeConstants[id]? | throw "array length is not concrete"
  let some (.Leaf value _) := tree.nodes[tree.root]? | throw "array length is not a scalar"
  return value

def opsemInhabited (runtime : RuntimeMetadata) (id : TypeId) : Except String Bool := do
  go (2 * (runtime.source.types.size + 1)) #[] false (← node runtime id).sourceLayout.normalizedType
where
  go (fuel : Nat) (seen : Array DefinitionRef) (stopAtRef : Bool) (id : TypeId) : Except String Bool := do
    let .succ fuel := fuel | throw "opsem inhabitedness recursion limit"
    let value ← node runtime id
    match value.shape with
    | .never => return false
    | .reference pointee .. => if stopAtRef then return true else go fuel seen stopAtRef pointee
    | .tuple fields =>
      for field in fields do unless (← go fuel seen stopAtRef field) do return false
      return true
    | .array element length _ =>
      if (← arrayLength runtime length) == 0 then return true
      go fuel seen stopAtRef element
    | .patternType base _ | .unsafeBinder base _ => go fuel seen stopAtRef base
    | .closure .. | .coroutine .. | .coroutineClosure .. =>
      for field in value.sourceLayout.closureUpvars do
        unless (← go fuel seen stopAtRef field) do return false
      return true
    | .adt data =>
      if data.kind == .unionKind then return true
      let stopAtRef := stopAtRef || seen.contains data.definition
      let seen := seen.push data.definition
      for variant in data.variants do
        let mut all := true
        for field in variant.fields do
          unless (← go fuel seen stopAtRef field.typeId) do all := false; break
        if all then return true
      return false
    | .alias .. => throw "unnormalized alias in opsem inhabitedness"
    | _ => return true

def needsDrop (runtime : RuntimeMetadata) (id : TypeId) : Except String Bool := do
  go (runtime.source.types.size + 1) #[] (← node runtime id).sourceLayout.normalizedType
where
  go (fuel : Nat) (active : Array TypeId) (id : TypeId) : Except String Bool := do
    let .succ fuel := fuel | throw "needs_drop recursion limit"
    if active.contains id then return false
    let active := active.push id
    let value ← node runtime id
    let fields ← match value.shape with
      | .dynamicTraitObject .. => return true
      | .adt data =>
        if value.sourceLayout.hasDestructor then return true
        if value.sourceLayout.isManuallyDrop || data.kind == .unionKind then return false
        pure (data.variants.flatMap (·.fields.map (·.typeId)))
      | .tuple fields => pure fields
      | .array element length _ =>
        if (← arrayLength runtime length) == 0 then return false
        pure #[element]
      | .slice element | .patternType element _ | .unsafeBinder element _ => pure #[element]
      | .closure .. | .coroutineClosure .. => pure value.sourceLayout.closureUpvars
      -- The ordinary query is non-exhaustive: rustc conservatively requires
      -- coroutine drop glue even when every stored field is drop-free.
      | .coroutine .. => return true
      | .alias .. => throw "unnormalized alias in needs_drop"
      | _ => pure #[]
    for field in fields do if ← go fuel active field then return true
    return false

private inductive SyntaxNode where
  | type (id : TypeId)
  | constant (id : TypeConstantId)
  | predicate (id : PredicateId)
  deriving DecidableEq

private inductive SyntaxFlag where
  | erasableRegions | parameters | nonRegionParameters | escapingBoundVariables
  | inference | placeholders | errors
  deriving DecidableEq

private def syntaxHasFlag (runtime : RuntimeMetadata) (flag : SyntaxFlag) (id : TypeId) : Except String Bool :=
  let count := runtime.source.types.size + runtime.source.typeConstants.size + runtime.source.predicates.size + 1
  visit (count * count) #[] #[(.type id,0)]
where
  bound (depth : Nat) : BoundVarIndexKind → Bool
    | .Bound index => index >= depth
    | .Canonical => true
  region (depth : Nat) (value : Region) : Bool :=
    match flag,value with
    | .erasableRegions,.Erased | .erasableRegions,.Bound .. => false
    | .erasableRegions,_ => true
    | .parameters,.EarlyParameter .. => true
    | .escapingBoundVariables,.Bound index .. => bound depth index
    | .inference,.InferenceVariable .. | .placeholders,.Placeholder .. | .errors,.Error => true
    | _,_ => false
  arguments (depth : Nat) (values : Array GenericArg) : Bool × Array (SyntaxNode × Nat) := Id.run do
    let mut found := false
    let mut children := #[]
    for value in values do
      match value with
      | .Type id => children := children.push (.type id,depth)
      | .Const id => children := children.push (.constant id,depth)
      | .Lifetime value => found := found || region depth value
    return (found,children)
  pattern (depth : Nat) : CompilerPattern → Array (SyntaxNode × Nat)
    | .range start finish => #[(.constant start,depth),(.constant finish,depth)]
    | .or children => children.flatMap (pattern depth)
    | .notNull => #[]
  visit (fuel : Nat) (seen pending : Array (SyntaxNode × Nat)) : Except String Bool := do
    let some current := pending.back? | return false
    let .succ fuel := fuel | throw "type syntax traversal exceeds the input universe"
    let pending := pending.pop
    let depth := current.2
    let (found,children) ← match current.1 with
      | .type id =>
        let value ← node runtime id
        match value.shape with
        | .adt data => pure (arguments depth data.args)
        | .closure _ args _ | .coroutine _ args | .coroutineClosure _ args | .alias _ _ args => pure (arguments depth args)
        | .reference pointee _ lifetime => pure (region depth lifetime,#[(.type pointee,depth)])
        | .rawPointer pointee _ | .slice pointee => pure (false,#[(.type pointee,depth)])
        | .unsafeBinder inner _ => pure (false,#[(.type inner,depth+1)])
        | .array element length _ => pure (false,#[(.type element,depth),(.constant length,depth)])
        | .tuple fields => pure (false,fields.map fun id => (.type id,depth))
        | .functionDefinition _ args _ _ => pure (arguments (depth+1) args)
        | .functionPointer signature _ =>
          pure (false,(signature.inputs.push signature.output).map fun id => (.type id,depth+1))
        | .dynamicTraitObject predicates _ lifetime =>
          pure (region depth lifetime,predicates.map fun id => (.predicate id,depth+1))
        | .patternType base value => pure (false,(pattern depth value).push (.type base,depth))
        | _ => pure (false,#[])
      | .constant id =>
        let some value := runtime.source.typeConstants[id]? | throw "type syntax constant is absent"
        match value with
        | .Value ty _ => pure (false,#[(.type ty,depth)])
        | .Alias _ _ _ args | .Expr _ args => pure (arguments depth args)
        | .Param .. => pure (flag == .parameters || flag == .nonRegionParameters,#[])
        | .Bound index _ => pure (flag == .escapingBoundVariables && bound depth index,#[])
        | .InferVar .. | .InferFresh .. => pure (flag == .inference,#[])
        | .Placeholder .. => pure (flag == .placeholders,#[])
        | .Error => pure (flag == .errors,#[])
      | .predicate id =>
        let some value := runtime.source.predicates[id]? | throw "type syntax predicate is absent"
        let (found,children) := arguments depth value.genericArgs
        pure (found,children ++ value.projectionTerm.toArray.map fun id => (.type id,depth))
    if found then return true
    let seen := seen.push current
    let mut pending := pending
    for child in children do
      unless seen.contains child || pending.contains child do pending := pending.push child
    visit fuel seen pending

def boolean (runtime : RuntimeMetadata) (id : TypeId) (query : String) : Except String Bool := do
  let value ← node runtime id
  let source := value.sourceLayout
  match query with
  | "is_unsafe_cell" => return source.isUnsafeCell
  | "is_c_void" => return source.isCVoid
  | "is_x87_f80_raw" => return source.specialFloat == some .x87f80
  | "is_simd" => return match value.shape with | .adt data => data.representation.simd | _ => false
  | "is_box" => return source.isBox
  | "is_global_box" =>
    unless source.isBox do return false
    let .adt data := value.shape | throw "Box declaration on a non-ADT"
    match data.args[1]? with
    | none => return true
    | some (GenericArg.Type allocator) => return (← node runtime allocator).sourceLayout.isGlobalAllocator
    | _ => throw "Box allocator argument is not a type"
  | "is_dynamic" => return value.shapeKind == .dynamicTraitObject
  | "is_too_generic" => return value.shapeKind == .alias
  | "is_monomorphic" =>
    if ← syntaxHasFlag runtime .nonRegionParameters id then return false
    if ← syntaxHasFlag runtime .escapingBoundVariables id then return false
    if ← syntaxHasFlag runtime .inference id then return false
    if ← syntaxHasFlag runtime .placeholders id then return false
    return !(← syntaxHasFlag runtime .errors id)
  | "is_monomorphic_enough" => return !(← syntaxHasFlag runtime .parameters id)
  | "is_like_maybe_dangling" => return source.isMaybeDangling || source.isManuallyDrop || value.shapeKind == .coroutine
  | "is_freeze" => ConcreteTraitQueries.check runtime .freeze id
  | "is_unpin" => ConcreteTraitQueries.check runtime .unpin id
  | "is_unsafe_unpin" => ConcreteTraitQueries.check runtime .unsafeUnpin id
  | "needs_drop" => needsDrop runtime id
  | "opsem_inhabited" => opsemInhabited runtime id
  | "is_sized" =>
    -- rustc's has_trivial_sizedness classifies arrays before querying layout.
    -- This lets validity check a thin raw pointer even if its array is too large.
    if value.shapeKind == .array then return true
    return (← runtime.lookup id |>.mapError toString).layout.isSized
  | "pass_indirectly_in_non_rustic_abis" => return match value.shape with
      | .adt data => data.representation.flagsBits &&& 32 != 0
      | _ => false
  | "has_erasable_regions" => syntaxHasFlag runtime .erasableRegions id
  | _ => throw s!"unknown concrete boolean query {query}"

def optionalType (runtime : RuntimeMetadata) (id : TypeId) (query : String) : Except String (Option TypeId) := do
  let value ← node runtime id
  match query with
  | "normalized" => return some (value.sourceLayout.normalizedType)
  | "discriminant_type" => some <$> discriminantType runtime id
  | "boxed_type" => boxedType runtime id
  | "unsafe_binder_erased" => return match value.shape with | .unsafeBinder inner _ => some inner | _ => none
  | "builtin_deref_explicit" | "builtin_deref_implicit" =>
    if let some id ← boxedType runtime id then return some id
    return match value.shape with
      | .reference inner .. => some inner
      | .rawPointer inner _ => if query == "builtin_deref_explicit" then some inner else none
      | _ => none
  | "metadata_tail" => some <$> metadataTail runtime id
  | "pointer_metadata_type" => some <$> pointerMetadataType runtime id
  | _ => throw s!"unknown concrete type query {query}"

end Miri.Input.ConcreteTypeQueries
