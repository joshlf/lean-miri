import Miri.Input.Model.SourceDeclarations
import Miri.Input.Model.SourceTypes

/-! Finite ABI declaration syntax. This records original generic clauses and
signatures, not monomorphic ABI/selection answers. Unknown semantics are explicit
constructors and cannot be confused with an empty supported clause list. -/
namespace Miri.Input.SourceAbi

inductive BuiltinTrait where
  | sized | copy | metaSized
  deriving Repr, DecidableEq

structure BuiltinDeclaration where
  definition : DefinitionId
  role : BuiltinTrait
  pinnedCore : Bool := false
  deriving Repr, DecidableEq

inductive Clause where
  | trait (definition : DefinitionId) (role : Option BuiltinTrait) (arguments : Array SourceTypes.TypeRef)
  | constHasType (parameter : Nat) (type : SourceTypes.TypeRef)
  | typeOutlives (type : SourceTypes.TypeRef) (region : SourceTypes.Region)
  | unsupported (kind : String)
  deriving Repr, DecidableEq

structure OwnerClauses where
  owner : DefinitionId
  parent : Option DefinitionId
  clauses : Array Clause
  deriving Repr, DecidableEq

structure ConstParameterType where
  definition : DefinitionId
  type : SourceTypes.TypeRef
  deriving Repr, DecidableEq

structure Attributes where
  neverUnwind : Bool
  trackCaller : Bool
  foreignItem : Bool
  dropGlue : Bool
  deriving Repr, DecidableEq

structure Function where
  definition : DefinitionId
  signature : SourceTypes.Signature
  attributes : Attributes
  constParameterTypes : Array ConstParameterType := #[]
  deriving Repr, DecidableEq

inductive SelfHead where
  | tuple (arity : Nat)
  | adt (definition : DefinitionId)
  | never
  | unsupported (tag : String)
  deriving Repr, DecidableEq

structure ImplHeader where
  definition : DefinitionId
  traitDefinition : DefinitionId
  argumentCount : Nat
  selfHead : SelfHead
  parameterCount : Nat
  genericParent : Option DefinitionId
  clauseCount : Nat
  clauseParent : Option DefinitionId
  positive : Bool
  nonConst : Bool
  final : Bool
  deriving Repr, DecidableEq

structure SuperTrait where
  definition : DefinitionId
  argumentCount : Nat
  selfParameter : Option Nat
  positive : Bool
  boundVariableCount : Nat
  deriving Repr, DecidableEq

/-- A complete finite ordinary-trait header domain, independent of a goal. -/
structure TraitDeclaration where
  definition : DefinitionId
  isAuto : Bool
  isMarker : Bool
  isCoinductive : Bool
  isSafe : Bool
  nonConst : Bool
  parameterCount : Nat
  hasSelf : Bool
  genericParent : Option DefinitionId
  complete : Bool
  superTraits : Array SuperTrait
  implementations : Array ImplHeader
  deriving Repr, DecidableEq

structure Material where
  functions : Array Function
  owners : Array OwnerClauses
  builtins : Array BuiltinDeclaration
  panicUnwinds : Bool
  panicInDropUnwinds : Bool
  traits : Array TraitDeclaration := #[]
  deriving Repr, DecidableEq

end Miri.Input.SourceAbi
