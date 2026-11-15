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
  deriving Repr, DecidableEq

inductive Clause where
  | trait (definition : DefinitionId) (role : Option BuiltinTrait) (arguments : Array SourceTypes.TypeRef)
  | constHasType (parameter : Nat) (type : SourceTypes.TypeRef)
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

structure Material where
  functions : Array Function
  owners : Array OwnerClauses
  builtins : Array BuiltinDeclaration
  panicUnwinds : Bool
  panicInDropUnwinds : Bool
  deriving Repr, DecidableEq

end Miri.Input.SourceAbi
