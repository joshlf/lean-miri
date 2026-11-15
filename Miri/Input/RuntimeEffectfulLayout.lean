import Miri.Input.RuntimeMetadata
import Miri.Input.RuntimeArrayQueries
import Miri.Input.CompilerTypingEnv

namespace Miri.Input.RuntimeEffectfulLayout
open Miri.Interpreter GenericSubstitution
set_option autoImplicit false
variable {S A : Type}

/-- Type-level constant evaluation is resolved through an exact rustc result. -/
abbrev Provider (S : Type) := CompilerTypingEnv.Env → TypeId → Option MIR.SpanRef → Term → RvalueM S Term

/-- Missing engine capability remains a failure at the actual constant demand. -/
def unavailable : Provider S := fun _ _ _ term =>
  throw (.unsupported s!"runtime type-level constant has no rustc evaluation result: {repr term}")

private def argumentArray : Terms → Array Term
  | .nil => #[]
  | .cons head tail => #[head] ++ argumentArray tail

/-- Rebuild the source key in the current World to avoid matching unrelated IDs. -/
def compilerResults (types : RuntimeArrayQueries.Access S)
    (metadata : RuntimeMetadata) : Provider S := fun _ expected _ source => do
  let current ← getThe S
  let arena := (types.get current).arena
  let fuel := metadata.materialLayoutFuel + 3 * (arena.constructedTypes.size + arena.constructedConstants.size)
  let mut found : Option TypeConstantId := none
  for row in metadata.source.compilerTypeConstResults do
    let sourceKind := if row.aliasKind == "inherent_impl" || row.aliasKind == "inherent_self"
      then "inherent" else row.aliasKind
    let tag := s!"alias_{sourceKind}_{if row.rigid then "rigid" else "not_rigid"}"
    if let .definition .constant sourceTag definition children := source then
      if sourceTag == tag then
        let identity ← match arena.identity row.definition with
          | .ok value => pure value
          | .error error => throw (.unsupported s!"rustc type constant definition: {error}")
        if identity == definition then
          let arguments ← match GenericInstantiationWorld.ofArguments arena fuel row.genericArgs with
            | .ok value => pure value
            | .error error => throw (.unsupported s!"rustc type constant arguments: {error}")
          if children == GenericSubstitution.Terms.ofArray arguments then
            found := some row.valueConstId
  let some resultId := found
    | throw (.unsupported s!"missing exact rustc type-level constant result for {repr source}")
  let result ← match arena.lookupConstant resultId with
    | .ok value => pure value
    | .error error => throw (.unsupported s!"rustc type constant result: {error}")
  match result with
  | .Value ty _ =>
    unless ty == expected do
      throw (.unsupported "rustc type constant result type disagrees with instantiated source")
  | _ => throw (.unsupported "rustc type constant result is not a value")
  match GenericInstantiationWorld.ofConstant arena fuel resultId with
  | .ok term => pure term
  | .error error => throw (.unsupported s!"rustc type constant value reification: {error}")

def layout (types : RuntimeArrayQueries.Access S) (_provider : Provider S)
    (_environment : CompilerTypingEnv.Env) (_usage : Option MIR.SpanRef)
    (metadata : RuntimeMetadata) (id : TypeId) : RvalueM S (Miri.ABI.TyAndLayout TypeId) :=
  RuntimeArrayQueries.perform types (RuntimeMetadata.layoutInWorld metadata id)

def fieldType (types : RuntimeArrayQueries.Access S) (_provider : Provider S)
    (_environment : CompilerTypingEnv.Env) (_usage : Option MIR.SpanRef)
    (metadata : RuntimeMetadata) (id variant index : Nat) : RvalueM S TypeId :=
  RuntimeArrayQueries.perform types (RuntimeMetadata.fieldTypeInWorld metadata id variant index)

def fieldLayout (types : RuntimeArrayQueries.Access S) (_provider : Provider S)
    (_environment : CompilerTypingEnv.Env) (_usage : Option MIR.SpanRef)
    (metadata : RuntimeMetadata) (parent : Miri.ABI.TyAndLayout TypeId) (index : Nat) :
    RvalueM S (Miri.ABI.TyAndLayout TypeId) :=
  RuntimeArrayQueries.perform types (RuntimeMetadata.fieldLayoutForInWorld metadata parent index)
def normalizeType (types : RuntimeArrayQueries.Access S) (_provider : Provider S)
    (_environment : CompilerTypingEnv.Env) (_usage : Option MIR.SpanRef)
    (metadata : RuntimeMetadata) (id : TypeId) : RvalueM S TypeId :=
  RuntimeArrayQueries.perform types
    (WorldNormalization.normalizeType () 10000 metadata.materialLayoutFuel id)

def pointerMetadataType (types : RuntimeArrayQueries.Access S) (_provider : Provider S)
    (_environment : CompilerTypingEnv.Env) (_usage : Option MIR.SpanRef)
    (metadata : RuntimeMetadata) (id : TypeId) : RvalueM S TypeId :=
  RuntimeArrayQueries.perform types (RuntimeMetadata.pointerMetadataTypeInWorld metadata id)
end Miri.Input.RuntimeEffectfulLayout
