import Miri.Input.Model.Types
import Miri.Input.Model.Catalogs
import Miri.Input.Model.Coroutine
import Miri.Input.Model.SourceTraits
import Miri.Input.Model.SourceVTables
import Miri.Input.Model.SourceAbi

namespace Miri.Input

structure RootDeclaration where
  definition : DefinitionRef
  defPath : String
  genericParameters : Array SourceParameterKind
  deriving Repr, DecidableEq

structure ImportDocument where
  sourceCastTargets : Array SourceCastTarget := #[]
  rootDeclarations : Array RootDeclaration := #[]
  sourceVtables : SourceVTableMaterial := {}
  sourceTraits : SourceTraitMaterial := {}
  sourceAbi : Option SourceAbiMaterial := none
  compilerPredicates : Array CompilerPredicateEvidence := #[]
  producer : Producer
  runtimeTargetDataLayout : Option TargetDataLayoutEvidence := none
  predicates : Array VtablePredicate := #[]
  definitions : Array DefinitionId := #[]
  typeConstants : Array Miri.MIR.TypeConst := #[]
  /-- Exact diagnostic and remapped filenames, shared across all source records. -/
  files : Array String := #[]
  spans : Array SourceSpanData := #[]
  syntaxContexts : Array SyntaxContext := #[]
  expansions : Array SourceExpansion := #[]
  types : Array TypeNode
  allocations : Array AllocationNode
  compilerAllocIdWorld : Option CompilerAllocIdWorld := none
  instances : Array InstanceNode
  selectedScope : Option SelectedScope
  bodyRoots : Array BodyRoot := #[]
  bodies : Array Body
  coroutineCoverage : Option CoroutineCoverage := none
  queries : Catalog.Queries
  producerSettings : Catalog.ProducerSettings

structure ExecutionInput where
  document : ImportDocument

end Miri.Input
