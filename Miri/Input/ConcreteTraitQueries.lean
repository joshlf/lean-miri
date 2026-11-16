import Miri.Input.RuntimeMetadata
import Miri.Input.Model.SourceTraits

namespace Miri.Input.ConcreteTraitQueries
open Miri.MIR
abbrev Bindings := Array (Option GenericArg)

private def typeNode (runtime : RuntimeMetadata) (id : TypeId) : Except String TypeNode :=
  runtime.node id |>.mapError toString

private def bind (bindings : Bindings) (index : Nat) (value : GenericArg) : Except String (Option Bindings) := do
  if bound : index < bindings.size then
    let slot := bindings[index]
    match slot with
    | none => return some (bindings.set index (some value))
    | some prior => return if prior == value then some bindings else none
  else throw "trait parameter slot is out of bounds"

mutual
private def matchType (runtime : RuntimeMetadata) (material : SourceTraitMaterial) (fuel : Nat)
    (pattern goal : Nat) (bindings : Bindings) : Except String (Option Bindings) := do
  let .succ fuel := fuel | throw "trait type matching recursion limit"
  let some pattern := material.types[pattern]? | throw "trait source expression absent"
  let node ← typeNode runtime goal
  match pattern,node.shape with
  | .parameter index,_ => bind bindings index (.Type goal)
  | .primitive kind integer float,_ =>
    if node.shapeKind != kind then return none
    let matching := match node.shape with
      | .int (.known actual) | .uint (.known actual) => integer == some actual
      | .float actual => float == some actual
      | _ => true
    return if matching then some bindings else none
  | .adt definition arguments,.adt actual =>
    if definition != actual.definition then return none
    matchArguments runtime material fuel arguments actual.args bindings
  | .tuple fields,.tuple actual =>
    if fields.size != actual.size then return none
    let mut bindings := bindings
    for (field,actual) in fields.zip actual do
      let some next ← matchType runtime material fuel field actual bindings | return none
      bindings := next
    return some bindings
  | .array element length,.array actual actualLength _ =>
    let some bindings ← matchType runtime material fuel element actual bindings | return none
    matchArgument runtime material fuel length (.Const actualLength) bindings
  | .slice element,.slice actual => matchType runtime material fuel element actual bindings
  | .reference pointee mutability,.reference actual actualMutability _
  | .rawPointer pointee mutability,.rawPointer actual actualMutability =>
    if mutability != actualMutability then return none
    matchType runtime material fuel pointee actual bindings
  | .functionDefinition definition arguments,.functionDefinition actual actualArguments ..
  | .closure definition arguments,.closure actual actualArguments _ =>
    if definition != actual then return none
    matchArguments runtime material fuel arguments actualArguments bindings
  | .patternType base pattern,.patternType actualBase actualPattern =>
    let some bindings ← matchType runtime material fuel base actualBase bindings | return none
    matchPattern runtime material fuel pattern actualPattern bindings
  | .projectionAlias definition arguments,.alias .projection actual actualArguments =>
    if definition != actual then return none
    matchArguments runtime material fuel arguments actualArguments bindings
  | .projectionAlias ..,_ => throw "generic associated type normalization is required by this trait candidate"
  | .unsupported reason kind,_ =>
    if let some kind := kind then
      if kind != node.shapeKind then return none
    throw s!"unsupported relevant trait type pattern: {reason}"
  | _,_ => return none

private def matchArgument (runtime : RuntimeMetadata) (material : SourceTraitMaterial) (fuel : Nat)
    (pattern : SourceTraitArgument) (goal : GenericArg) (bindings : Bindings) : Except String (Option Bindings) := do
  let .succ fuel := fuel | throw "trait argument matching recursion limit"
  match pattern,goal with
  | .type expression,.Type actual => matchType runtime material fuel expression actual bindings
  | .constant value,.Const actual =>
    return if runtime.source.typeConstants[value]? == runtime.source.typeConstants[actual]? then some bindings else none
  | .constantParameter index,.Const actual => bind bindings index (.Const actual)
  | .lifetime,.Lifetime _ => return some bindings
  | .unsupported reason,_ => throw s!"unsupported relevant trait argument: {reason}"
  | _,_ => return none

private def matchArguments (runtime : RuntimeMetadata) (material : SourceTraitMaterial) (fuel : Nat)
    (patterns : Array SourceTraitArgument) (goals : Array GenericArg) (bindings : Bindings) :
    Except String (Option Bindings) := do
  let .succ fuel := fuel | throw "trait arguments matching recursion limit"
  if patterns.size != goals.size then return none
  let mut current := bindings
  for (pattern,goal) in patterns.zip goals do
    let some next ← matchArgument runtime material fuel pattern goal current | return none
    current := next
  return some current

private def matchPattern (runtime : RuntimeMetadata) (material : SourceTraitMaterial) (fuel : Nat)
    (pattern : SourceTraitPattern) (goal : CompilerPattern) (bindings : Bindings) : Except String (Option Bindings) := do
  let .succ fuel := fuel | throw "trait pattern matching recursion limit"
  match pattern,goal with
  | .notNull,.notNull => return some bindings
  | .range start finish,.range actualStart actualFinish =>
    let some bindings ← matchArgument runtime material fuel start (.Const actualStart) bindings | return none
    matchArgument runtime material fuel finish (.Const actualFinish) bindings
  | .or patterns,.or actual =>
    if patterns.size != actual.size then return none
    let mut bindings := bindings
    for (pattern,actual) in patterns.zip actual do
      let some next ← matchPattern runtime material fuel pattern actual bindings | return none
      bindings := next
    return some bindings
  | _,_ => return none
end

private def instantiateArgument (runtime : RuntimeMetadata) (material : SourceTraitMaterial)
    (bindings : Bindings) (argument : SourceTraitArgument) : Except String GenericArg := do
  match argument with
  | .lifetime => return .Lifetime .Erased
  | .unsupported reason => throw s!"unsupported relevant trait argument: {reason}"
  | .constant value => return .Const value
  | .constantParameter index =>
    let some (some (.Const value)) := bindings[index]? | throw "unbound trait constant parameter"
    return .Const value
  | .type expression =>
    if let some (.parameter index) := material.types[expression]? then
      let some (some (.Type value)) := bindings[index]? | throw "unbound trait type parameter"
      return .Type value
    let mut result := none
    for node in runtime.source.types do
      if let some matched ← matchType runtime material (3 * (material.types.size + 1)) expression node.id bindings then
        if matched == bindings then
          if let some prior := result then
            if prior != node.id then throw "ambiguous concrete trait expression identity"
          result := some node.id
    let some id := result | throw "concrete trait clause type is absent from the source type graph"
    return .Type id

private def isSized (runtime : RuntimeMetadata) (id : TypeId) : Except String Bool := do
  let layout ← runtime.lookup id |>.mapError toString
  return layout.layout.backendRepr.isSized

private def isMetaSized (runtime : RuntimeMetadata) (id : TypeId) : Except String Bool :=
  go (runtime.source.types.size + 1) id
where
  go (fuel id : Nat) : Except String Bool := do
    let .succ fuel := fuel | throw "MetaSized structural tail recursion limit"
    let node ← typeNode runtime id
    match node.shape with
    | .foreign _ => return false
    | .adt data =>
      if data.kind == .structKind then
        if let some field := data.variants[0]?.bind (·.fields.back?) then return ← go fuel field.typeId
      return true
    | .tuple fields =>
      if let some field := fields.back? then return ← go fuel field
      return true
    | .alias .. => throw "unnormalized alias in MetaSized query"
    | _ => return true

def check (runtime : RuntimeMetadata) (role : SourceTraitRole) (id : TypeId) : Except String Bool := do
  let id := (← typeNode runtime id).sourceLayout.normalizedType
  if role == .freeze || role == .unpin || role == .unsafeUnpin then
    if ← trivial (runtime.source.types.size+1) id then return true
  let declarations := runtime.source.sourceTraits.declarations.filter (·.role == role)
  let some declaration := declarations[0]? | throw s!"trait language item declaration is absent ({reprStr role})"
  if declarations.size != 1 then throw "ambiguous trait language item declarations"
  select (runtime.source.sourceTraits.types.size + runtime.source.types.size + 1)
    #[] declaration.definition #[.Type id]
where
  trivial (fuel id : Nat) : Except String Bool := do
    let .succ fuel := fuel | throw "trivial auto-trait source recursion limit"
    match (← typeNode runtime id).shape with
    | .bool | .char | .int _ | .uint _ | .float _ | .str | .never
    | .rawPointer .. | .reference .. | .functionDefinition .. | .functionPointer .. => return true
    | .tuple fields =>
      for field in fields do unless (← trivial fuel field) do return false
      return true
    | .array child .. | .slice child | .patternType child _ => trivial fuel child
    | _ => return false
  select (fuel : Nat) (active : Array (DefinitionRef × Array GenericArg))
      (definition : DefinitionRef) (arguments : Array GenericArg) : Except String Bool := do
    let .succ fuel := fuel | throw "trait obligation recursion limit"
    let material := runtime.source.sourceTraits
    let some declaration := material.declarations.find? (·.definition == definition)
      | throw "referenced trait declaration is absent"
    let some selfArgument := arguments[0]? | throw "trait obligation has no Self argument"
    let GenericArg.Type self := selfArgument | throw "trait obligation Self is not a type"
    let node ← typeNode runtime self
    if declaration.role == .sized then return ← isSized runtime self
    if declaration.role == .metaSized then return ← isMetaSized runtime self
    if declaration.role != .other then
      match node.shape with
      | .bool | .char | .int _ | .uint _ | .float _ | .str | .never
      | .rawPointer .. | .reference .. | .functionDefinition .. | .functionPointer .. => return true
      | _ => pure ()
    if active.contains (definition,arguments) then
      if declaration.isAuto then return true
      throw "non-auto trait obligation cycle"
    let active := active.push (definition,arguments)
    let mut relevant := false
    let mut selected : Option Bool := none
    for implementation in declaration.implementations do
      let bindings := Array.replicate implementation.parameters.size none
      let some bindings ← matchArguments runtime material (3 * (material.types.size + 1))
          implementation.arguments arguments bindings | continue
      relevant := true
      unless implementation.isFinal do
        throw "trait specialization is unsupported"
      if ← clauses fuel active bindings implementation.clauses then
        let answer ← match implementation.polarity with
          | .positive => pure true
          | .negative => pure false
          | .reservation => throw "trait reservation implementation is unsupported"
        if selected.isSome then throw "multiple applicable trait implementations"
        selected := some answer
    if let some answer := selected then return answer
    if relevant then return false
    if let .dynamicTraitObject predicates _ _ := node.shape then
      let expectedArguments := arguments.extract 1 arguments.size
      for id in predicates do
        let some predicate := runtime.source.predicates[id]? | throw "dynamic trait predicate is absent"
        if predicate.kind == .autoTrait && predicate.definitionId == definition && expectedArguments.isEmpty then
          return true
        if predicate.kind == .trait then
          let some evidence := runtime.source.compilerPredicates[id]? | throw "dynamic principal normalization is absent"
          let some principal := evidence.normalizedId | throw "dynamic principal normalization result is absent"
          if ← objectContains (runtime.source.sourceVtables.objectTraits.size+1) #[] principal definition expectedArguments then
            return true
      return false
    unless declaration.isAuto do return false
    unless (← clauses fuel active (arguments.map some) declaration.superClauses) do return false
    let children ← match node.shape with
      | .adt data =>
        if node.sourceLayout.isPhantomData then
          let some argument := data.args[0]? | throw "PhantomData type argument is absent"
          let GenericArg.Type child := argument | throw "PhantomData argument is not a type"
          pure #[child]
        else pure (data.variants.flatMap (·.fields.map (·.typeId)))
      | .tuple fields => pure fields
      | .array child .. | .slice child | .patternType child _ => pure #[child]
      | .closure .. | .coroutineClosure .. => pure node.sourceLayout.closureUpvars
      | .unsafeBinder child _ => pure #[child]
      | .foreign _ => return false
      | .coroutine .. => throw "coroutine auto-trait source constituents are unavailable"
      | .alias .. => throw "unnormalized alias in concrete trait query"
      | _ => pure #[]
    for child in children do
      unless (← select fuel active definition #[.Type child]) do return false
    return true
  objectContains (fuel : Nat) (active : Array PredicateId) (source : PredicateId)
      (target : DefinitionRef) (arguments : Array GenericArg) : Except String Bool := do
    if active.contains source then return false
    let .succ fuel := fuel | throw "dynamic supertrait bound traversal limit"
    let some predicate := runtime.source.predicates[source]? | throw "dynamic source predicate is absent"
    if predicate.definitionId == target && predicate.genericArgs == arguments then return true
    let some declaration := runtime.source.sourceVtables.objectTraits.find? (·.principal == source)
      | throw "instantiated dynamic source trait declaration is absent"
    for parent in declaration.superTraits do
      if ← objectContains fuel (active.push source) parent target arguments then return true
    return false
  clauses (fuel : Nat) (active : Array (DefinitionRef × Array GenericArg)) (bindings : Bindings)
      (values : Array SourceTraitClause) : Except String Bool := do
    let .succ fuel := fuel | throw "trait clause recursion limit"
    for clause in values do
      match clause with
      | .regionOutlives | .typeOutlives _ => pure ()
      | .unsupported reason => throw s!"unsupported relevant trait clause: {reason}"
      | .trait definition arguments =>
        let arguments ← arguments.mapM (instantiateArgument runtime runtime.source.sourceTraits bindings)
        unless (← select fuel active definition arguments) do return false
    return true

end Miri.Input.ConcreteTraitQueries
