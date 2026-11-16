import Miri.Input.Model.Types

namespace Miri.Input

inductive SourceTraitRole where
  | freeze | unpin | unsafeUnpin | sized | metaSized | other
  deriving Repr, DecidableEq

inductive SourceParameterKind where
  | type | lifetime | constant
  deriving Repr, DecidableEq

inductive SourceTraitArgument where
  | type (expression : Nat)
  | constant (value : TypeConstantId)
  | constantParameter (index : Nat)
  | lifetime
  | unsupported (reason : String)
  deriving Repr, DecidableEq

inductive SourceTraitPattern where
  | notNull
  | range (start finish : SourceTraitArgument)
  | or (patterns : Array SourceTraitPattern)
  deriving Repr

inductive SourceTraitType where
  | parameter (index : Nat)
  | primitive (kind : TypeShapeKind) (integer : Option MIR.IntegerKind := none)
      (float : Option FloatTypeTag := none)
  | adt (definition : DefinitionRef) (arguments : Array SourceTraitArgument)
  | tuple (fields : Array Nat)
  | array (element : Nat) (length : SourceTraitArgument)
  | slice (element : Nat)
  | reference (pointee : Nat) (mutability : MIR.Mutability)
  | rawPointer (pointee : Nat) (mutability : MIR.Mutability)
  | functionDefinition (definition : DefinitionRef) (arguments : Array SourceTraitArgument)
  | closure (definition : DefinitionRef) (arguments : Array SourceTraitArgument)
  | projectionAlias (definition : DefinitionRef) (arguments : Array SourceTraitArgument)
  | patternType (base : Nat) (pattern : SourceTraitPattern)
  | unsupported (reason : String) (shapeKind : Option TypeShapeKind := none)
  deriving Repr

inductive SourceTraitClause where
  | trait (definition : DefinitionRef) (arguments : Array SourceTraitArgument)
  | regionOutlives
  | typeOutlives (type : Nat)
  | unsupported (reason : String)
  deriving Repr, DecidableEq

inductive SourceTraitPolarity where
  | positive | negative | reservation
  deriving Repr, DecidableEq

structure SourceTraitImplementation where
  definition : DefinitionRef
  parameters : Array SourceParameterKind
  selfType : Nat
  arguments : Array SourceTraitArgument
  clauses : Array SourceTraitClause
  polarity : SourceTraitPolarity
  isFinal : Bool
  deriving Repr, DecidableEq

structure SourceTraitDeclaration where
  definition : DefinitionRef
  role : SourceTraitRole
  isAuto : Bool
  parameters : Array SourceParameterKind
  superClauses : Array SourceTraitClause
  ownVtableMethods : Array DefinitionRef := #[]
  superTraits : Array DefinitionRef := #[]
  implementations : Array SourceTraitImplementation
  deriving Repr, DecidableEq

structure SourceAdtDeclaration where
  definition : DefinitionRef
  parameters : Array SourceParameterKind
  isStruct : Bool
  tailType : Option Nat
  clauses : Array SourceTraitClause
  deriving Repr, DecidableEq

structure SourceAssociatedTypeDeclaration where
  definition : DefinitionRef
  parameters : Array SourceParameterKind
  bounds : Array SourceTraitClause
  deriving Repr, DecidableEq

structure SourceTraitMaterial where
  types : Array SourceTraitType := #[]
  declarations : Array SourceTraitDeclaration := #[]
  adtDeclarations : Array SourceAdtDeclaration := #[]
  associatedTypes : Array SourceAssociatedTypeDeclaration := #[]
  deriving Repr

def SourceTraitMaterial.vtableMinEntries (material : SourceTraitMaterial)
    (principal : Option DefinitionRef) : Except String Nat := do
  let some principal := principal | return 3
  let (_,count) ← visit (material.declarations.size + 1) #[] principal
  return 3 + count
where
  visit (fuel : Nat) (seen : Array DefinitionRef) (definition : DefinitionRef) :
      Except String (Array DefinitionRef × Nat) := do
    if seen.contains definition then return (seen,0)
    let .succ fuel := fuel | throw "source supertrait graph exceeds its declaration universe"
    let some declaration := material.declarations.find? (·.definition == definition)
      | throw "vtable principal or supertrait declaration is absent"
    let mut seen := seen.push definition
    let mut count := declaration.ownVtableMethods.size
    for parent in declaration.superTraits do
      let (next,added) ← visit fuel seen parent
      seen := next
      count := count + added
    return (seen,count)

end Miri.Input
