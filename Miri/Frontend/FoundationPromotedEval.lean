import Miri.Frontend.FoundationPromoted
import Miri.Frontend.FoundationSignatureFnAbi

/-! Pure symbolic interpretation of the supported promoted function-pointer
construction. Values are recipes, never guest pointers or allocation IDs.
CTFE uses salt zero (pinned interpret/machine.rs and mir/interpret/mod.rs),
unlike Miri's runtime function-salt choice. Allocation interning/provenance must
be supplied before materialization; successful recipe construction is not a
successful fixed-interpreter execution or a Rust safety statement. -/
namespace Miri.Frontend.Foundation
open Lean

structure PromotedFunctionKey where
  definition : Nat
  compilerDefinition : Input.DefinitionId
  /-- This restricted interpreter accepts no generic function arguments. -/
  arguments : Array MIR.GenericArg
  ctfeSalt : Fin 32

structure PromotedFunctionRecipe where
  key : PromotedFunctionKey
  pointerType : ConcreteType
  abi : Input.FunctionAbi

structure SharedPromotedRecipe where
  owner : Nat
  index : Nat
  /-- Local cell identity within this source promoted frame, not an AllocId. -/
  cellLocal : Nat
  outputType : ConcreteType
  cellType : ConcreteType
  function : PromotedFunctionRecipe
  physical : PhysicalTypeRegistry
  source : PromotedTemplate

inductive PromotedIdentityRequirement where
  | functionAllocation (key : PromotedFunctionKey)
  | internedSharedCell (owner index cellLocal : Nat)

/-- Explicit outstanding compiler/global identities; none is a chosen numeric
ID. The shared cell also needs initialized bytes, relocation provenance, borrow
root and immutable promotion interning before a concrete pointer can exist. -/
def SharedPromotedRecipe.requirements (recipe : SharedPromotedRecipe) : Array PromotedIdentityRequirement :=
  #[.functionAllocation recipe.function.key, .internedSharedCell recipe.owner recipe.index recipe.cellLocal]

inductive PromotedMaterializationError where
  | unsupported (requirement : PromotedIdentityRequirement)

/-- No CTFE allocation/key/salt or promoted-memory identity has been proved or
captured by this source-only path. Never manufacture an address/AllocId. -/
def materializeSharedPromoted (recipe : SharedPromotedRecipe) :
    Except PromotedMaterializationError MIR.ConstValue :=
  .error (.unsupported (.functionAllocation recipe.function.key))

private def whole (locals : Nat) (p : Json) : Except String Nat := do
  unless (← p.getObjValAs? (Array Json) "projection").isEmpty do throw "symbolic promoted projection unsupported"
  let id ← p.getObjValAs? Nat "local"
  unless id < locals do throw "symbolic promoted local absent"
  return id

private def functionRecipe (document : Document) (table : Json) (value : Json)
    (target : ConcreteType) (physical : PhysicalTypeRegistry) :
    Except String (PhysicalTypeRegistry × PromotedFunctionRecipe) := do
  let operand ← value.getObjVal? "operand"
  unless (← operand.getObjValAs? String "kind") == "constant" &&
      (← (← operand.getObjVal? "value").getObjValAs? String "kind") == "zero_sized" do
    throw "symbolic reification requires FnDef ZST"
  let sourceType ← operand.getObjValAs? Nat "type"
  let some row := document.types[sourceType]? | throw "symbolic FnDef type absent"
  let shape ← row.getObjVal? "shape"
  unless (← shape.getObjValAs? String "kind") == "function_definition" &&
      (← shape.getObjValAs? (Array Json) "arguments").isEmpty do
    throw "symbolic reification supports nongeneric FnDef only"
  let definition ← shape.getObjValAs? Nat "definition"
  let some sourceDefinition := document.definitions[definition]? | throw "symbolic function definition absent"
  unless (← sourceDefinition.getObjValAs? String "kind") == "fn" do throw "symbolic function is not ordinary free Fn"
  let compilerDefinition : Input.DefinitionId := {
    crateIndex := ← sourceDefinition.getObjValAs? Nat "crate_index"
    index := ← sourceDefinition.getObjValAs? Nat "index" }
  unless compilerDefinition.crateIndex < 2^32 && compilerDefinition.index < 2^32 do
    throw "symbolic compiler DefId exceeds rustc width"
  let identities ← document.definitions.filterM fun row => do
    return (← row.getObjValAs? Nat "crate_index") == compilerDefinition.crateIndex &&
      (← row.getObjValAs? Nat "index") == compilerDefinition.index
  unless identities.size == 1 do throw "symbolic compiler DefId identity is ambiguous"
  let headers ← table.getObjValAs? (Array Json) "function_headers"
  let candidates ← headers.filterM fun header => return (← header.getObjValAs? Nat "definition") == definition
  unless candidates.size == 1 do throw "symbolic original function declaration missing/duplicate"
  let some header := candidates[0]? | throw "symbolic declaration absent"
  let runtime ← header.getObjVal? "runtime_source"
  unless !(← runtime.getObjValAs? Bool "rustc_intrinsic") do throw "symbolic intrinsic reification unsupported"
  let environment ← header.getObjVal? "environment"
  let flat ← flattenEnvironment document environment
  unless (← flat.getObjValAs? (Array Json) "parameters").isEmpty do throw "symbolic generic declaration unsupported"
  checkEnvironment document #[] #[] environment
  let signature ← header.getObjVal? "signature"
  unless (← signatureBoundVariables document signature).isEmpty do throw "symbolic bound function declaration unsupported"
  let sourceAbi ← signature.getObjVal? "abi"
  unless (← sourceAbi.getObjValAs? String "kind") == "rust" &&
      (← sourceAbi.getObjVal? "unwind") == Json.null &&
      !(← signature.getObjValAs? Bool "c_variadic") do throw "symbolic declaration ABI unsupported"
  let safety ← signature.getObjValAs? String "safety"
  unless safety == (← value.getObjValAs? String "safety") do throw "symbolic reification safety differs from declaration"
  let mut inputs := #[]
  for id in (← signature.getObjValAs? (Array Nat) "inputs") do
    inputs := inputs.push (← instantiate #[] #[] (← typeExpr document id))
  let output ← instantiate #[] #[] (← typeExpr document (← signature.getObjValAs? Nat "output"))
  let declared := ConcreteType.functionPointer inputs output safety "rust" false
  unless sameConcrete 1024 target declared do throw "symbolic cast target differs from original declaration signature"
  let allHeaders ← document.source.getObjValAs? (Array Json) "source_function_signatures"
  unless allHeaders.contains header do throw "symbolic declaration is absent from source signature domain"
  let (physical, abi) ← rustFunctionAbiOfSourceSignatureInRegistry physical definition #[]
  return (physical, ⟨⟨definition, compilerDefinition, #[], ⟨0, by decide⟩⟩, declared, abi⟩)

/-- Interpret the exact straight-line reify/shared-borrow promoted constructor
symbolically, after checking all required constants and original declaration
facts. An unresolved required constant stops before the first instruction.
No vtable resolution, host callback or memory/allocation operation occurs here. -/
def evaluateSharedPromotedRecipe (document : Document) (owner index : Nat) :
    Except String SharedPromotedRecipe := do
  let body ← selectPromotedTemplate document owner index
  let tables ← document.source.getObjValAs? (Array Json) "promoted_tables"
  let some table := tables.find? (fun row => (row.getObjValAs? Nat "definition").toOption == some owner)
    | throw "symbolic promoted owner table absent"
  checkEnvironment document #[] #[] (← table.getObjVal? "environment")
  unless body.requiredConstants.isEmpty do throw "symbolic promoted required-constant evaluation unavailable"
  let blocks ← body.source.getObjValAs? (Array Json) "blocks"
  unless blocks.size == 1 do throw "symbolic promoted control flow unsupported"
  let some block := blocks[0]? | throw "symbolic promoted entry block absent"
  unless !(← block.getObjValAs? Bool "cleanup") &&
      (← (← block.getObjVal? "terminator").getObjValAs? String "kind") == "return" do
    throw "symbolic promoted constructor requires normal Return"
  let statements ← block.getObjValAs? (Array Json) "statements"
  unless statements.size == 2 && body.localTypes.size == 2 do throw "symbolic promoted constructor spine unsupported"
  let mut types := #[]
  let mut physical := PhysicalTypeRegistry.start document
  for source in body.localTypes do
    let ty ← instantiate #[] #[] (← typeExpr document source)
    types := types.push ty
    let (next, _) ← physical.intern ty
    physical := next
  let some first := statements[0]? | throw "symbolic reify assignment absent"
  let some second := statements[1]? | throw "symbolic shared borrow absent"
  unless (← first.getObjValAs? String "kind") == "assign" &&
      (← second.getObjValAs? String "kind") == "assign" do throw "symbolic promoted statement unsupported"
  let cellLocal ← whole types.size (← first.getObjVal? "place")
  unless cellLocal != 0 do throw "symbolic reification overwrites return reference"
  let reify ← first.getObjVal? "value"
  unless (← reify.getObjValAs? String "kind") == "cast_reify_function_pointer" do throw "symbolic first instruction is not reify"
  let target ← instantiate #[] #[] (← typeExpr document (← reify.getObjValAs? Nat "target"))
  let some cellType := types[cellLocal]? | throw "symbolic promoted cell type absent"
  unless sameConcrete 1024 cellType target do throw "symbolic reification destination type mismatch"
  let (next, function) ← functionRecipe document table reify target physical
  physical := next
  unless (← whole types.size (← second.getObjVal? "place")) == 0 do throw "symbolic borrow does not initialize return local"
  let borrow ← second.getObjVal? "value"
  unless (← borrow.getObjValAs? String "kind") == "ref" &&
      (← borrow.getObjValAs? String "borrow_kind") == "shared" &&
      (← whole types.size (← borrow.getObjVal? "place")) == cellLocal do throw "symbolic borrow target/kind mismatch"
  let some outputType := types[0]? | throw "symbolic promoted return type absent"
  let .pointer kind pointee := outputType | throw "symbolic promoted return type is not reference"
  let region ← borrow.getObjValAs? String "region"
  unless kind == s!"reference_{region}_const" && sameConcrete 1024 pointee cellType do
    throw "symbolic promoted return reference/pointee mismatch"
  return ⟨owner, index, cellLocal, outputType, cellType, function, physical, body⟩

end Miri.Frontend.Foundation
