import Miri.Input.Model.SourceTraits
import Miri.Input.TableCore

namespace Miri.Input.SourceTraitsDecoder
open JsonReader

private structure Fields where
  kind : Option String := none
  index : Option Nat := none
  expression : Option Nat := none
  value : Option Nat := none
  definition : Option Nat := none
  arguments : Array SourceTraitArgument := #[]
  fields : Array Nat := #[]
  element : Option Nat := none
  length : Option SourceTraitArgument := none
  pointee : Option Nat := none
  mutability : Option MIR.Mutability := none
  shapeKind : Option TypeShapeKind := none
  integer : Option MIR.IntegerKind := none
  float : Option FloatTypeTag := none
  reason : Option String := none
  base : Option Nat := none
  pattern : Option SourceTraitPattern := none

def argument : Parser SourceTraitArgument := do
  let p ← object ({} : Fields) fun p key => do
    match key with
    | "kind" => return {p with kind := some (← string)}
    | "expression" => return {p with expression := some (← natural)}
    | "value" => return {p with value := some (← natural)}
    | "index" => return {p with index := some (← natural)}
    | "reason" => return {p with reason := some (← string)}
    | _ => skipValue; return p
  match ← required p.kind "kind" with
  | "type" => return .type (← required p.expression "expression")
  | "constant" => return .constant (← required p.value "value")
  | "constant_parameter" => return .constantParameter (← required p.index "index")
  | "lifetime" => return .lifetime
  | "unsupported" => return .unsupported (← required p.reason "reason")
  | tag => fail s!"unknown trait argument kind {tag}"

private structure PatternFields where
  kind : Option String := none
  start : Option SourceTraitArgument := none
  finish : Option SourceTraitArgument := none
  children : Option (Array SourceTraitPattern) := none

partial def pattern : Parser SourceTraitPattern := do
  let p ← object ({} : PatternFields) fun p key => do
    match key with
    | "kind" => return {p with kind := some (← string)}
    | "start" => return {p with start := some (← argument)}
    | "end" => return {p with finish := some (← argument)}
    | "patterns" => return {p with children := some (← array pattern)}
    | _ => skipValue; return p
  match ← required p.kind "kind" with
  | "not_null" => return .notNull
  | "range" => return .range (← required p.start "start") (← required p.finish "end")
  | "or" => return .or (← required p.children "patterns")
  | tag => fail s!"unknown trait type pattern {tag}"

def typeExpression : Parser SourceTraitType := do
  let p ← object ({} : Fields) fun p key => do
    match key with
    | "kind" => return {p with kind := some (← string)}
    | "index" => return {p with index := some (← natural)}
    | "definition" => return {p with definition := some (← natural)}
    | "arguments" => return {p with arguments := ← array argument}
    | "fields" => return {p with fields := ← array natural}
    | "element" => return {p with element := some (← natural)}
    | "length" => return {p with length := some (← argument)}
    | "pointee" => return {p with pointee := some (← natural)}
    | "mutability" =>
      let tag ← object (none : Option String) fun value key => do
        if key == "kind" then return some (← string)
        skipValue
        return value
      let mutability ← match ← required tag "kind" with
        | "mutable" => pure MIR.Mutability.Mut
        | "immutable" => pure .Not
        | tag => fail s!"unknown trait pointer mutability {tag}"
      return {p with mutability := some mutability}
    | "shape_kind" => return {p with shapeKind := ← nullable (do liftExcept (DecoderValues.typeShapeKind (← string)))}
    | "integer_kind" =>
      let kind ← nullable do
        let .known kind ← liftExcept (DecoderValues.integerTypeTag (← string))
        pure kind
      return {p with integer := kind}
    | "float_kind" => return {p with float := ← nullable (do liftExcept (DecoderValues.floatTypeTag (← string)))}
    | "reason" => return {p with reason := some (← string)}
    | "base" => return {p with base := some (← natural)}
    | "pattern" => return {p with pattern := some (← pattern)}
    | _ => skipValue; return p
  match ← required p.kind "kind" with
  | "parameter" => return .parameter (← required p.index "index")
  | "primitive" => return .primitive (← required p.shapeKind "shape_kind") p.integer p.float
  | "adt" => return .adt (← required p.definition "definition") p.arguments
  | "tuple" => return .tuple p.fields
  | "array" => return .array (← required p.element "element") (← required p.length "length")
  | "slice" => return .slice (← required p.element "element")
  | "reference" => return .reference (← required p.pointee "pointee") (← required p.mutability "mutability")
  | "raw_pointer" => return .rawPointer (← required p.pointee "pointee") (← required p.mutability "mutability")
  | "function_definition" => return .functionDefinition (← required p.definition "definition") p.arguments
  | "closure" => return .closure (← required p.definition "definition") p.arguments
  | "projection_alias" => return .projectionAlias (← required p.definition "definition") p.arguments
  | "pattern_type" => return .patternType (← required p.base "base") (← required p.pattern "pattern")
  | "unsupported" => return .unsupported (← required p.reason "reason") p.shapeKind
  | tag => fail s!"unknown trait type expression {tag}"

def clause : Parser SourceTraitClause := do
  let p ← object ({} : Fields) fun p key => do
    match key with
    | "kind" => return {p with kind := some (← string)}
    | "definition" => return {p with definition := some (← natural)}
    | "arguments" => return {p with arguments := ← array argument}
    | "type" => return {p with expression := some (← natural)}
    | "reason" => return {p with reason := some (← string)}
    | _ => skipValue; return p
  match ← required p.kind "kind" with
  | "trait" => return .trait (← required p.definition "definition") p.arguments
  | "region_outlives" => return .regionOutlives
  | "type_outlives" => return .typeOutlives (← required p.expression "type")
  | "unsupported" => return .unsupported (← required p.reason "reason")
  | tag => fail s!"unknown trait clause {tag}"

def parameterKind : Parser SourceParameterKind := do
  match ← string with
  | "type" => pure .type
  | "lifetime" => pure .lifetime
  | "constant" => pure .constant
  | tag => fail s!"unknown trait parameter kind {tag}"

private structure ImplementationFields where
  definition : Option Nat := none
  parameters : Array SourceParameterKind := #[]
  selfType : Option Nat := none
  arguments : Array SourceTraitArgument := #[]
  clauses : Array SourceTraitClause := #[]
  polarity : Option SourceTraitPolarity := none
  isFinal : Option Bool := none

def implementation : Parser SourceTraitImplementation := do
  let p ← object ({} : ImplementationFields) fun p key => do
    match key with
    | "definition" => return {p with definition := some (← natural)}
    | "parameters" => return {p with parameters := ← array parameterKind}
    | "self_type" => return {p with selfType := some (← natural)}
    | "arguments" => return {p with arguments := ← array argument}
    | "clauses" => return {p with clauses := ← array clause}
    | "polarity" =>
      let polarity ← match ← string with
        | "positive" => pure SourceTraitPolarity.positive
        | "negative" => pure .negative
        | "reservation" => pure .reservation
        | tag => fail s!"unknown trait impl polarity {tag}"
      return {p with polarity := some polarity}
    | "is_final" => return {p with isFinal := some (← boolean)}
    | _ => skipValue; return p
  return ⟨← required p.definition "definition", p.parameters, ← required p.selfType "self_type",
    p.arguments,p.clauses,← required p.polarity "polarity",← required p.isFinal "is_final"⟩

private structure DeclarationFields where
  definition : Option Nat := none
  role : Option SourceTraitRole := none
  isAuto : Option Bool := none
  parameters : Array SourceParameterKind := #[]
  superClauses : Array SourceTraitClause := #[]
  ownVtableMethods : Array Nat := #[]
  superTraits : Array Nat := #[]
  implementations : Array SourceTraitImplementation := #[]

def declaration : Parser SourceTraitDeclaration := do
  let p ← object ({} : DeclarationFields) fun p key => do
    match key with
    | "definition" => return {p with definition := some (← natural)}
    | "role" =>
      let role ← match ← string with
        | "freeze" => pure SourceTraitRole.freeze
        | "unpin" => pure .unpin
        | "unsafe_unpin" => pure .unsafeUnpin
        | "sized" => pure .sized
        | "meta_sized" => pure .metaSized
        | "other" => pure .other
        | tag => fail s!"unknown source trait role {tag}"
      return {p with role := some role}
    | "is_auto" => return {p with isAuto := some (← boolean)}
    | "parameters" => return {p with parameters := ← array parameterKind}
    | "super_clauses" => return {p with superClauses := ← array clause}
    | "own_vtable_methods" => return {p with ownVtableMethods := ← array natural}
    | "super_traits" => return {p with superTraits := ← array natural}
    | "implementations" => return {p with implementations := ← array implementation}
    | _ => skipValue; return p
  return ⟨← required p.definition "definition",← required p.role "role",← required p.isAuto "is_auto",
    p.parameters,p.superClauses,p.ownVtableMethods,p.superTraits,p.implementations⟩

private structure AdtFields where
  definition : Option Nat := none
  parameters : Array SourceParameterKind := #[]
  isStruct : Option Bool := none
  tailType : Option Nat := none
  clauses : Array SourceTraitClause := #[]

def adtDeclaration : Parser SourceAdtDeclaration := do
  let p ← object ({} : AdtFields) fun p key => do
    match key with
    | "definition" => return {p with definition := some (← natural)}
    | "parameters" => return {p with parameters := ← array parameterKind}
    | "is_struct" => return {p with isStruct := some (← boolean)}
    | "tail_type" => return {p with tailType := ← nullable natural}
    | "clauses" => return {p with clauses := ← array clause}
    | _ => skipValue; return p
  return ⟨← required p.definition "definition",p.parameters,← required p.isStruct "is_struct",p.tailType,p.clauses⟩

private structure AssociatedTypeFields where
  definition : Option Nat := none
  parameters : Array SourceParameterKind := #[]
  bounds : Array SourceTraitClause := #[]

def associatedType : Parser SourceAssociatedTypeDeclaration := do
  let value ← object ({} : AssociatedTypeFields) fun value key => do
    match key with
    | "definition" => return {value with definition := some (← natural)}
    | "parameters" => return {value with parameters := ← array parameterKind}
    | "bounds" => return {value with bounds := ← array clause}
    | _ => skipValue; return value
  return ⟨← required value.definition "definition",value.parameters,value.bounds⟩

private structure MaterialFields where
  types : Option (Array SourceTraitType) := none
  declarations : Option (Array SourceTraitDeclaration) := none
  adtDeclarations : Option (Array SourceAdtDeclaration) := none
  associatedTypes : Option (Array SourceAssociatedTypeDeclaration) := none

def material : Parser SourceTraitMaterial := do
  let p ← object ({} : MaterialFields) fun p key => do
    match key with
    | "types" => return {p with types := some (← array typeExpression)}
    | "declarations" => return {p with declarations := some (← array declaration)}
    | "adt_declarations" => return {p with adtDeclarations := some (← array adtDeclaration)}
    | "associated_type_declarations" => return {p with associatedTypes := some (← array associatedType)}
    | _ => skipValue; return p
  return ⟨← required p.types "types",← required p.declarations "declarations",
    ← required p.adtDeclarations "adt_declarations",← required p.associatedTypes "associated_type_declarations"⟩

def validate (definitions : Array DefinitionId) (constants : Array MIR.TypeConst)
    (material : SourceTraitMaterial) : Except String Unit := do
  let definition (id : Nat) : Except String Unit :=
    unless id < definitions.size do throw "trait declaration definition is out of bounds"
  let expressionUses (uses : Array (Array (Nat × SourceParameterKind))) (expression : Nat) :
      Except String (Array (Nat × SourceParameterKind)) := do
    let some value := uses[expression]? | throw "trait type expression is absent or refers forward in its source graph"
    return value
  let argumentUses (uses : Array (Array (Nat × SourceParameterKind)))
      (argument : SourceTraitArgument) : Except String (Array (Nat × SourceParameterKind)) := do
    match argument with
    | .type expression => expressionUses uses expression
    | .constant id =>
      let some (MIR.TypeConst.Value ..) := constants[id]? | throw "trait constant is not a concrete value"
      return #[]
    | .constantParameter index => return #[(index,.constant)]
    | .lifetime | .unsupported _ => return #[]
  let argumentsUses (uses : Array (Array (Nat × SourceParameterKind)))
      (arguments : Array SourceTraitArgument) : Except String (Array (Nat × SourceParameterKind)) := do
    let mut result := #[]
    for argument in arguments do result := result ++ (← argumentUses uses argument)
    return result
  let rec patternUses (uses : Array (Array (Nat × SourceParameterKind)))
      (value : SourceTraitPattern) : Except String (Array (Nat × SourceParameterKind)) := do
    match value with
    | .notNull => return #[]
    | .range start finish => return (← argumentUses uses start) ++ (← argumentUses uses finish)
    | .or children =>
      let mut result := #[]
      for child in children do result := result ++ (← patternUses uses child)
      return result
  let mut uses : Array (Array (Nat × SourceParameterKind)) := #[]
  for expression in material.types do
    let parameters ← match expression with
      | .parameter index => pure #[(index,.type)]
      | .adt id arguments | .functionDefinition id arguments | .closure id arguments | .projectionAlias id arguments =>
        definition id
        argumentsUses uses arguments
      | .tuple fields => do
        let mut result := #[]
        for field in fields do result := result ++ (← expressionUses uses field)
        pure result
      | .array child length => do
        let childUses ← expressionUses uses child
        let lengthUses ← argumentUses uses length
        pure (childUses ++ lengthUses)
      | .slice child | .reference child _ | .rawPointer child _ => expressionUses uses child
      | .patternType base value => do
        let baseUses ← expressionUses uses base
        let valueUses ← patternUses uses value
        pure (baseUses ++ valueUses)
      | .primitive kind integer float => do
        match kind with
        | .int | .uint => unless integer.isSome && float.isNone do throw "invalid trait integer pattern"
        | .float => unless float.isSome && integer.isNone do throw "invalid trait float pattern"
        | .bool | .char | .str | .never =>
          unless integer.isNone && float.isNone do throw "invalid trait primitive pattern"
        | _ => throw "invalid primitive trait pattern kind"
        pure #[]
      | .unsupported .. => pure #[]
    uses := uses.push parameters
  let checkParameters (parameters : Array SourceParameterKind) (uses : Array (Nat × SourceParameterKind)) : Except String Unit := do
    for (index,kind) in uses do
      unless parameters[index]? == some kind do throw "trait source parameter has an invalid slot or kind"
  let clauseUses (value : SourceTraitClause) : Except String (Array (Nat × SourceParameterKind)) := do
    match value with
    | .trait id arguments =>
      definition id
      let some target := material.declarations.find? (·.definition == id) | throw "trait clause declaration is absent"
      unless arguments.size == target.parameters.size do throw "trait clause argument count mismatch"
      argumentsUses uses arguments
    | .typeOutlives expression => expressionUses uses expression
    | .regionOutlives | .unsupported _ => pure #[]
  let mut seen : Std.HashSet Nat := {}
  for declaration in material.declarations do
    definition declaration.definition
    if seen.contains declaration.definition then throw "duplicate source trait declaration"
    seen := seen.insert declaration.definition
    unless declaration.parameters[0]? == some .type do throw "trait declaration has no Self type parameter"
    for method in declaration.ownVtableMethods do definition method
    for parent in declaration.superTraits do
      unless material.declarations.any (·.definition == parent) do throw "source supertrait declaration is absent"
    for value in declaration.superClauses do
      checkParameters declaration.parameters (← clauseUses value)
    for implementation in declaration.implementations do
      definition implementation.definition
      unless implementation.arguments.size == declaration.parameters.size do throw "trait implementation argument count mismatch"
      unless implementation.arguments[0]? == some (SourceTraitArgument.type implementation.selfType) do
        throw "trait implementation Self header mismatch"
      checkParameters implementation.parameters (← argumentsUses uses implementation.arguments)
      for value in implementation.clauses do
        checkParameters implementation.parameters (← clauseUses value)
  let mut seenAdts : Std.HashSet Nat := {}
  for declaration in material.adtDeclarations do
    definition declaration.definition
    if seenAdts.contains declaration.definition then throw "duplicate source ADT declaration"
    seenAdts := seenAdts.insert declaration.definition
    if let some tail := declaration.tailType then
      checkParameters declaration.parameters (← expressionUses uses tail)
    for value in declaration.clauses do
      checkParameters declaration.parameters (← clauseUses value)
  let mut seenAssociated : Std.HashSet Nat := {}
  for declaration in material.associatedTypes do
    definition declaration.definition
    if seenAssociated.contains declaration.definition then throw "duplicate associated type declaration"
    seenAssociated := seenAssociated.insert declaration.definition
    for value in declaration.bounds do
      checkParameters declaration.parameters (← clauseUses value)

end Miri.Input.SourceTraitsDecoder
