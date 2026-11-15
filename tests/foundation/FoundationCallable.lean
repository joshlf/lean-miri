import Miri.Frontend.FoundationCallable

open Lean Miri.Frontend.Foundation
private def checked (value : Except String α) : IO α :=
  match value with | .ok result => pure result | .error e => throw (IO.userError e)
private def rejects (value : Except String α) : IO Unit :=
  match value with | .error _ => pure () | .ok _ => throw (IO.userError "unsupported callable source accepted")

private def sameDefinition (source : Document) (sourceId : Nat) (oracle : Array Json) (id : Nat) : Except String Bool := do
  let some a := source.definitions[sourceId]? | throw "source callable definition absent"
  let some b := oracle[id]? | throw "compiler callable definition absent"
  return (← a.getObjValAs? Nat "crate_index") == (← b.getObjValAs? Nat "crate") &&
    (← a.getObjValAs? Nat "index") == (← b.getObjValAs? Nat "index")

private def referenceType (fuel : Nat) (types : Array Json) (id : Nat) (value : ConcreteType) : Except String Bool := do
  let .succ fuel := fuel | throw "compiler callable type comparison exhausted"
  let some row := types[id]? | throw "compiler callable type absent"
  let shape ← row.getObjVal? "shape"
  match value with
  | .primitive "int" name => return (← shape.getObjValAs? String "kind") == "int" && (← shape.getObjValAs? String "signed_kind") == name
  | .tuple fields =>
    unless (← shape.getObjValAs? String "kind") == "tuple" do return false
    let ids ← shape.getObjValAs? (Array Nat) "elements"
    unless ids.size == fields.size do return false
    for (id, field) in ids.zip fields do
      unless ← referenceType fuel types id field do return false
    return true
  | .functionPointer inputs output safety abi variadic =>
    unless (← shape.getObjValAs? String "kind") == "function_pointer" do return false
    let sig ← shape.getObjVal? "signature"
    unless (← (← sig.getObjVal? "safety").getObjValAs? String "kind") == safety &&
        (← (← sig.getObjVal? "abi").getObjValAs? String "kind") == abi &&
        (← sig.getObjValAs? Bool "c_variadic") == variadic do return false
    let ids ← sig.getObjValAs? (Array Nat) "inputs"
    unless ids.size == inputs.size do return false
    for (id, input) in ids.zip inputs do
      unless ← referenceType fuel types id input do return false
    referenceType fuel types (← sig.getObjValAs? Nat "output") output
  | _ => throw "unsupported callable comparison type"

private def compareKey (document : Document) (key : ClosureSourceKey) (row : Json)
    (definitions types : Array Json) : Except String Unit := do
  unless ← sameDefinition document key.definition definitions (← row.getObjValAs? Nat "def_id") do
    throw "compiler closure Item definition differs"
  let arguments ← row.getObjValAs? (Array Json) "generic_args"
  unless arguments.size == key.arguments.size do throw "compiler closure full argument count differs"
  for (arg, expected) in arguments.zip key.arguments do
    let .type expected := expected | throw "non-type closure argument unsupported"
    unless (← arg.getObjValAs? String "kind") == "type" &&
        (← referenceType 64 types (← arg.getObjValAs? Nat "value") expected) do
      throw "compiler closure full argument differs"

private def compareTraitArguments (document : Document) (self : CallableSourceKey) (tuple : ConcreteType)
    (row : Json) (definitions types : Array Json) : Except String Unit := do
  let arguments ← row.getObjValAs? (Array Json) "generic_args"
  unless arguments.size == 2 do throw "compiler callable trait argument count differs"
  let some receiver := arguments[0]? | throw "compiler callable Self absent"
  let some inputs := arguments[1]? | throw "compiler callable Args absent"
  unless (← receiver.getObjValAs? String "kind") == "type" &&
      (← inputs.getObjValAs? String "kind") == "type" do throw "compiler callable trait argument kinds differ"
  let id ← receiver.getObjValAs? Nat "value"
  match self with
  | .closure key =>
    let some type := types[id]? | throw "compiler callable Self type absent"
    let shape ← type.getObjVal? "shape"
    unless (← shape.getObjValAs? String "kind") == "closure" do throw "compiler callable Self is not closure"
    compareKey document key shape definitions types
  | .functionPointer pointer =>
    unless ← referenceType 64 types id pointer do throw "compiler callable FnPtr Self differs"
  unless ← referenceType 64 types (← inputs.getObjValAs? Nat "value") tuple do
    throw "compiler callable tupled Args differ"

private def compilerInstance (rows : Array Json) (id : Nat) : Except String Json := do
  let values ← rows.filterM fun row => return (← row.getObjValAs? Nat "instance_id") == id
  unless values.size == 1 do throw "compiler callable instance absent/duplicate"
  let some value := values[0]? | throw "compiler callable instance absent"
  return value

def main (paths : List String) : IO Unit := do
  let [sourcePath, oraclePath, pointerPath] := paths | throw (IO.userError "expected closure source, projected std oracle, FnPtr oracle")
  let document ← checked (Json.parse (← IO.FS.readFile sourcePath) >>= decode)
  let oracle ← checked (Json.parse (← IO.FS.readFile oraclePath))
  unless (← checked (oracle.getObjValAs? String "oracle_schema")) == "lean-miri-rustc-mir" &&
      (← checked (oracle.getObjValAs? Nat "oracle_schema_version")) == 12 do
    throw (IO.userError "callable oracle is not projected schema12")
  unless (← checked (oracle.getObjValAs? String "rustc_commit")) == "8144389c895da997dbdecaa635e41d6a50be6ffd" do
    throw (IO.userError "callable oracle compiler pin differs")
  let definitions ← checked (oracle.getObjValAs? (Array Json) "definitions")
  let types ← checked (oracle.getObjValAs? (Array Json) "types")
  let instances ← checked (oracle.getObjValAs? (Array Json) "instances")
  let some closure := document.definitions.findIdx? (fun row =>
      (row.getObjValAs? String "path").toOption == some "std::rt::lang_start::{closure#0}")
    | throw (IO.userError "actual std start closure source absent")
  let parent := #[ItemArgument.type (.tuple #[])]
  let tuple : ConcreteType := .tuple #[]
  let output : ConcreteType := .primitive "int" "i32"
  let concreteSlots ← checked (builtinClosureVtableCandidates document closure parent .fn tuple output)
  unless concreteSlots.shape.slots.size == 6 && concreteSlots.methods.size == 3 do
    throw (IO.userError "builtin closure slot recipe composition lost source positions")
  let normal ← checked (builtinClosureCandidate document closure parent .fn tuple output)
  let .closureItem key := normal.recipe | throw (IO.userError "Fn closure did not select source Item")
  let items ← checked (instances.filterM fun row => return (← (← row.getObjVal? "instance_kind").getObjValAs? String "kind") == "item")
  let some item := items[0]? | throw (IO.userError "compiler std closure Item absent")
  let _ ← checked (compareKey document key item definitions types)
  unless normal.parentEnvironment == normal.closure.parentEnvironment &&
      !(← checked (normal.parentEnvironment.getObjValAs? (Array Json) "clauses")).isEmpty do
    throw (IO.userError "closure parent premises were silently discarded")
  let once ← checked (builtinClosureCandidate document closure parent .fnOnce tuple output)
  let .closureOnce method onceKey false args := once.recipe | throw (IO.userError "FnOnce adapter source recipe differs")
  unless sameConcrete 64 args tuple && onceKey.arguments.size == key.arguments.size do throw (IO.userError "FnOnce adapter argument source differs")
  let adapters ← checked (instances.filterM fun row => return ((← row.getObjVal? "instance_kind").getObjValAs? String "shim_kind").toOption == some "closure_once")
  let some adapter := adapters[0]? | throw (IO.userError "compiler ClosureOnce adapter absent")
  let _ ← checked (compareTraitArguments document (.closure onceKey) args adapter definitions types)
  let kind ← checked (adapter.getObjVal? "instance_kind")
  unless !(← checked (kind.getObjValAs? Bool "track_caller")) &&
      (← checked (sameDefinition document method definitions (← checked (kind.getObjValAs? Nat "call_once_def_id")))) &&
      (← checked (sameDefinition document closure definitions (← checked (kind.getObjValAs? Nat "closure_def_id")))) do
    throw (IO.userError "compiler ClosureOnce source identity/attributes differ")
  let queries ← checked (oracle.getObjValAs? (Array Json) "compiler_vtable_queries")
  let some query := queries[0]? | throw (IO.userError "compiler closure vtable metadata absent")
  let entries ← checked ((← checked (query.getObjVal? "vtable_metadata")).getObjValAs? (Array Json) "entries")
  unless entries.size == 6 do throw (IO.userError "compiler std closure Fn vtable slot count differs")
  for (requested, slot) in [(SourceClosureKind.fnOnce,3),(.fnMut,4),(.fn,5)] do
    let candidate ← checked (builtinClosureCandidate document closure parent requested tuple output true)
    let some entry := entries[slot]? | throw (IO.userError "compiler closure vtable slot absent")
    let target ← checked (compilerInstance instances (← checked (entry.getObjValAs? Nat "instance_id")))
    match candidate.recipe with
    | .vtable method (.closure key) tuple =>
      let _ ← checked (compareTraitArguments document (.closure key) tuple target definitions types)
      let kind ← checked (target.getObjVal? "instance_kind")
      unless (← checked (kind.getObjValAs? String "shim_kind")) == "vtable" &&
          (← checked (sameDefinition document method definitions (← checked (kind.getObjValAs? Nat "def_id")))) do
        throw (IO.userError "compiler by-value vtable shim recipe differs")
    | .closureItem key => let _ ← checked (compareKey document key target definitions types)
    | _ => throw (IO.userError "unexpected closure vtable recipe")
  -- Structural FnPtr control: concrete compiler vtable uses the separate FnPtr shim family.
  let pointerOracle ← checked (Json.parse (← IO.FS.readFile pointerPath))
  let pointerDefs ← checked (pointerOracle.getObjValAs? (Array Json) "definitions")
  let pointerInstances ← checked (pointerOracle.getObjValAs? (Array Json) "instances")
  let pointerQueries ← checked (pointerOracle.getObjValAs? (Array Json) "compiler_vtable_queries")
  let some pointerQuery := pointerQueries[0]? | throw (IO.userError "compiler FnPtr oracle absent")
  let pointerEntries ← checked ((← checked (pointerQuery.getObjVal? "vtable_metadata")).getObjValAs? (Array Json) "entries")
  let pointer : ConcreteType := .functionPointer #[] output "safe" "rust" false
  for (requested, slot) in [(SourceClosureKind.fnOnce,3),(.fnMut,4),(.fn,5)] do
    let candidate ← checked (builtinFnPointerRecipe document pointer requested tuple output true)
    let some entry := pointerEntries[slot]? | throw (IO.userError "compiler FnPtr vtable slot absent")
    let target ← checked (compilerInstance pointerInstances (← checked (entry.getObjValAs? Nat "instance_id")))
    let kind ← checked (target.getObjVal? "instance_kind")
    let method ← checked (kind.getObjValAs? Nat "def_id")
    match candidate with
    | .vtable expected (.functionPointer self) args =>
      let _ ← checked (compareTraitArguments document (.functionPointer self) args target pointerDefs (← checked (pointerOracle.getObjValAs? (Array Json) "types")))
      unless (← checked (kind.getObjValAs? String "shim_kind")) == "vtable" &&
          (← checked (sameDefinition document expected pointerDefs method)) do throw (IO.userError "FnPtr VTableShim differs")
    | .fnPointer expected self args =>
      let _ ← checked (compareTraitArguments document (.functionPointer self) args target pointerDefs (← checked (pointerOracle.getObjValAs? (Array Json) "types")))
      unless (← checked (kind.getObjValAs? String "shim_kind")) == "fn_pointer" &&
          (← checked (sameDefinition document expected pointerDefs method)) do throw (IO.userError "FnPtrShim differs")
    | _ => throw (IO.userError "unexpected FnPtr source recipe")
  let ordinaryPointer ← checked (builtinFnPointerRecipe document pointer .fnOnce tuple output)
  let .fnPointer pointerMethod self args := ordinaryPointer | throw (IO.userError "ordinary FnOnce fnptr used vtable shim")
  let pointerTypes ← checked (pointerOracle.getObjValAs? (Array Json) "types")
  let mut ordinaryMatches := #[]
  for target in pointerInstances do
    let kind ← checked (target.getObjVal? "instance_kind")
    if (kind.getObjValAs? String "shim_kind").toOption == some "fn_pointer" then
      if ← checked (sameDefinition document pointerMethod pointerDefs (← checked (kind.getObjValAs? Nat "def_id"))) then
        ordinaryMatches := ordinaryMatches.push target
  unless ordinaryMatches.size == 1 do throw (IO.userError "compiler ordinary FnOnce FnPtrShim absent or duplicate")
  let some target := ordinaryMatches[0]? | throw (IO.userError "ordinary FnPtrShim absent")
  let _ ← checked (compareTraitArguments document (.functionPointer self) args target pointerDefs pointerTypes)
  rejects (builtinClosureCandidate document closure #[] .fn tuple output)
  rejects (builtinClosureCandidate document closure parent .fn (.tuple #[output]) output)
  rejects (builtinClosureCandidate document closure parent .fn tuple (.primitive "int" "i64"))
  rejects (builtinFnPointerRecipe document (.functionPointer #[] output "unsafe" "rust" false) .fn tuple output)
  rejects (builtinFnPointerRecipe document (.functionPointer #[] output "safe" "c" false) .fn tuple output)
  rejects (builtinFnPointerRecipe document (.functionPointer #[] output "safe" "rust_call" false) .fn tuple output)
  rejects (builtinFnPointerRecipe document (.functionPointer #[] output "safe" "rust" true) .fn tuple output)
  let body := normal.closure.body
  let missing := document.source.setObjVal! "closure_templates" (toJson (#[body.setObjVal! "track_caller" Json.null] : Array Json))
  rejects (builtinClosureCandidate {document with source := missing} closure parent .fn tuple output true)
  let tracked := document.source.setObjVal! "closure_templates" (toJson (#[body.setObjVal! "track_caller" (toJson true)] : Array Json))
  match builtinClosureCandidate {document with source := tracked} closure parent .fn tuple output true with
  | .error "track-caller closure vtable reification source is unsupported" => pure ()
  | .error e => throw (IO.userError s!"unexpected reification source outcome: {e}")
  | .ok _ => throw (IO.userError "track-caller closure silently used an unadjusted Item")
  unless !(sourceClosureSupports .fnMut .fn) && !(sourceClosureSupports .fnOnce .fn) &&
      !(sourceClosureSupports .fnOnce .fnMut) do throw (IO.userError "weaker closure kind selected stronger builtin Fn")
  IO.println "builtin callable recipes: genuine std closure Item/ClosureOnce/VTable and FnPtr shims match; unresolved parent/shim/ABI/allocation joins remain explicit"
