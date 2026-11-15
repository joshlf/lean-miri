import Miri.Frontend.FoundationClosureShims

open Lean Miri Miri.Frontend.Foundation
private def checked (value : Except String α) : IO α :=
  match value with | .ok result => pure result | .error e => throw (IO.userError e)
private def ensure (value : Bool) (message : String) : Except String Unit :=
  unless value do throw message
private def rejects (value : Except String α) : IO Unit :=
  match value with | .error _ => pure () | .ok _ => throw (IO.userError "unsupported shim source accepted")
private def indexed (rows : Array Json) (id : Nat) : Except String Json := do
  let some row := rows[id]? | throw "oracle ID absent"
  return row
private def sameDef (doc : Document) (source : Nat) (definitions : Array Json) (id : Nat) : Except String Unit := do
  let a ← indexed doc.definitions source
  let b ← indexed definitions id
  ensure ((← a.getObjValAs? Nat "crate_index") == (← b.getObjValAs? Nat "crate") &&
    (← a.getObjValAs? Nat "index") == (← b.getObjValAs? Nat "index")) "shim definition identity differs"
private def checkPlace (value : Json) (localId : Nat) (deref : Bool := false) : Except String Unit := do
  ensure ((← value.getObjValAs? Nat "local") == localId) "shim place local differs"
  let p ← value.getObjValAs? (Array Json) "projection"
  if deref then
    ensure (p.size == 1) "shim receiver projection differs"
    let some projection := p[0]? | throw "shim projection absent"
    ensure ((← projection.getObjValAs? String "kind") == "Deref") "shim receiver not dereferenced"
  else ensure p.isEmpty "unexpected shim projection"
private def checkMoved (value : Json) (localId : Nat) (deref : Bool := false) : Except String Unit := do
  ensure ((← value.getObjValAs? String "kind") == "Move") "shim operand not Move"
  checkPlace (← value.getObjVal? "place") localId deref
private def localType (doc : Document) (closure : Nat) (defs types : Array Json)
    (id : Nat) (expected : ClosureShimType) : Except String Unit := do
  let row ← indexed types id
  let shape ← row.getObjVal? "shape"
  let kind ← shape.getObjValAs? String "kind"
  match expected with
  | .output => ensure (kind == "int" && (← shape.getObjValAs? String "signed_kind") == "i32") "shim output differs"
  | .unit => ensure (kind == "tuple" && (← shape.getObjValAs? (Array Nat) "elements").isEmpty) "shim Args differs"
  | .closure =>
    ensure (kind == "closure") "shim Self not closure"
    sameDef doc closure defs (← shape.getObjValAs? Nat "def_id")
  | .rawMutClosure | .mutRefClosure =>
    ensure (kind == (if expected == .rawMutClosure then "raw_pointer" else "reference") &&
      (← (← shape.getObjVal? "mutability").getObjValAs? String "kind") == "mutable") "shim receiver type differs"
    if expected == .mutRefClosure then
      ensure ((← (← shape.getObjVal? "region").getObjValAs? String "kind") == "erased") "shim borrow region differs"
    let pointee ← indexed types (← shape.getObjValAs? Nat "pointee")
    let pointee ← pointee.getObjVal? "shape"
    ensure ((← pointee.getObjValAs? String "kind") == "closure") "shim receiver pointee not closure"
    sameDef doc closure defs (← pointee.getObjValAs? Nat "def_id")
private def callee (doc : Document) (defs instances : Array Json) (id : Nat)
    (expected : BuiltinCallableRecipe) : Except String Unit := do
  let rows ← instances.filterM fun row => return (← row.getObjValAs? Nat "instance_id") == id
  let some row := rows[0]? | throw "shim call target instance absent"
  let kind ← row.getObjVal? "instance_kind"
  match expected with
  | .closureOnce method key tracked _ =>
    ensure ((← kind.getObjValAs? String "shim_kind") == "closure_once" &&
      (← kind.getObjValAs? Bool "track_caller") == tracked) "ClosureOnce target differs"
    sameDef doc method defs (← kind.getObjValAs? Nat "call_once_def_id")
    sameDef doc key.definition defs (← kind.getObjValAs? Nat "closure_def_id")
  | .closureItem key =>
    ensure ((← kind.getObjValAs? String "kind") == "item") "closure Item target differs"
    sameDef doc key.definition defs (← row.getObjValAs? Nat "def_id")
  | _ => throw "unexpected symbolic shim target"
private def compareBody (doc : Document) (closure : Nat) (oracle body : Json)
    (expected : ClosureShimBody) : Except String Unit := do
  let definitions ← oracle.getObjValAs? (Array Json) "definitions"
  let types ← oracle.getObjValAs? (Array Json) "types"
  let instances ← oracle.getObjValAs? (Array Json) "instances"
  ensure ((← body.getObjValAs? Nat "arg_count") == expected.argumentCount &&
    (← body.getObjValAs? Nat "spread_arg") == expected.spreadArgument &&
    (← body.getObjValAs? (Array Json) "required_consts").isEmpty) "shim body preamble differs"
  let locals ← body.getObjValAs? (Array Json) "locals"
  ensure (locals.size == expected.locals.size) "shim local count differs"
  for (row,ty) in locals.zip expected.locals do
    localType doc closure definitions types (← row.getObjValAs? Nat "type") ty
  let spans ← oracle.getObjValAs? (Array Json) "shim_spans"
  let spanId ← body.getObjValAs? Nat "span"
  let rows ← spans.filterM fun row => return (← row.getObjValAs? Nat "id") == spanId
  let some span := rows[0]? | throw "shim declaration span absent"
  let span ← span.getObjVal? "value"
  ensure ((← span.getObjVal? "start") == (← expected.sourceSpan.getObjVal? "start") &&
    (← span.getObjVal? "end") == (← expected.sourceSpan.getObjVal? "end")) "shim declaration positions differ"
  let blocks ← body.getObjValAs? (Array Json) "basic_blocks"
  ensure (blocks.size == expected.blocks.size) "shim block count differs"
  for (block,want) in blocks.zip expected.blocks do
    ensure ((← block.getObjValAs? Bool "is_cleanup") == want.cleanup) "shim cleanup marker differs"
    let statements ← block.getObjValAs? (Array Json) "statements"
    ensure (statements.size == (if want.borrowReceiverIntoThree then 1 else 0)) "shim statements differ"
    if want.borrowReceiverIntoThree then
      let some statement := statements[0]? | throw "shim borrow absent"
      let kinds ← oracle.getObjValAs? (Array Json) "shim_statements"
      let rows ← kinds.filterM fun row => return (← row.getObjValAs? Nat "id") == (← statement.getObjValAs? Nat "kind")
      let some row := rows[0]? | throw "shim borrow statement absent"
      let value ← row.getObjVal? "value"
      ensure ((← value.getObjValAs? String "variant") == "Assign") "shim borrow not assignment"
      checkPlace (← value.getObjVal? "place") 3
      let value ← value.getObjVal? "rvalue"
      ensure ((← value.getObjValAs? String "kind") == "Ref" &&
        (← value.getObjVal? "borrow_kind") == Json.mkObj [("kind",toJson "mutable"),("mutability_kind",toJson "default")]) "shim borrow kind differs"
      ensure ((← (← value.getObjVal? "region").getObjValAs? String "kind") == "erased") "shim borrow region differs"
      checkPlace (← value.getObjVal? "place") 1
    let term ← (← block.getObjVal? "terminator").getObjVal? "kind"
    let variant ← term.getObjValAs? String "variant"
    match want.terminator with
    | .call method target receiver continuation cleanup =>
      ensure (variant == "Call" && (← term.getObjValAs? Nat "target") == continuation) "shim call target differs"
      ensure ((← (← term.getObjVal? "call_source").getObjValAs? String "kind") == "miscellaneous_desugaring") "shim call source differs"
      let function ← term.getObjVal? "function"
      ensure ((← function.getObjValAs? String "kind") == "Constant") "shim callee not constant"
      let constant ← function.getObjVal? "constant"
      ensure ((← constant.getObjVal? "user_type_annotation") == Json.null &&
        (← (← (← constant.getObjVal? "constant").getObjVal? "value").getObjValAs? String "kind") == "zero_sized") "shim callee value differs"
      let functionType ← indexed types (← constant.getObjValAs? Nat "type")
      let functionShape ← functionType.getObjVal? "shape"
      ensure ((← functionShape.getObjValAs? String "kind") == "function_definition") "shim call target type differs"
      sameDef doc method definitions (← functionShape.getObjValAs? Nat "def_id")
      let functionArgs ← functionShape.getObjValAs? (Array Json) "generic_args"
      ensure (functionArgs.size == 2) "shim callee substitution differs"
      let some self := functionArgs[0]? | throw "shim callee Self absent"
      localType doc closure definitions types (← self.getObjValAs? Nat "value") .closure
      let some tuple := functionArgs[1]? | throw "shim callee Args absent"
      localType doc closure definitions types (← tuple.getObjValAs? Nat "value") .unit
      let args ← term.getObjValAs? (Array Json) "args"
      ensure (args.size == 2) "shim call argument count differs"
      let some a := args[0]? | throw "shim receiver argument absent"
      checkMoved (← a.getObjVal? "operand") (if receiver == .dereferenceLocalOne then 1 else 3) (receiver == .dereferenceLocalOne)
      let some a := args[1]? | throw "shim tuple argument absent"
      checkMoved (← a.getObjVal? "operand") 2
      checkPlace (← term.getObjVal? "destination") 0
      let unwind ← term.getObjVal? "unwind"
      match cleanup with
      | none => ensure ((← unwind.getObjValAs? String "kind") == "Continue") "shim unwind differs"
      | some cleanup => ensure ((← unwind.getObjValAs? String "kind") == "Cleanup" &&
          (← unwind.getObjValAs? Nat "target") == cleanup) "shim cleanup edge differs"
      let resolution ← term.getObjVal? "resolution"
      ensure ((← resolution.getObjValAs? String "kind") == "resolved_instance" &&
        (← resolution.getObjVal? "dispatch_slot") == Json.null &&
        (← resolution.getObjVal? "virtual_resolution") == Json.null) "shim call resolution differs"
      callee doc definitions instances (← resolution.getObjValAs? Nat "instance_id") target
    | .dropReceiver target terminate =>
      ensure (variant == "Drop" && (← term.getObjValAs? Nat "target") == target &&
        !(← term.getObjValAs? Bool "replace")) "shim drop differs"
      checkPlace (← term.getObjVal? "place") 1
      let unwind ← term.getObjVal? "unwind"
      ensure ((← unwind.getObjValAs? String "kind") == (if terminate then "Terminate" else "Continue")) "shim drop unwind differs"
      if terminate then ensure ((← (← unwind.getObjVal? "reason").getObjValAs? String "kind") == "in_cleanup") "shim cleanup termination differs"
    | .returnValue => ensure (variant == "Return") "shim return differs"
    | .resumeUnwind => ensure (variant == "UnwindResume") "shim unwind resume differs"
private def compareMode (mode : Input.AbiPassMode) (value : Json) : Except String Unit := do
  ensure ((← value.getObjValAs? String "kind") == "Direct" && mode.kind == .direct) "shim ABI mode differs"
  let some attr := mode.attributes[0]? | throw "shim ABI attribute absent"
  let value ← value.getObjVal? "attributes"
  ensure ((← value.getObjValAs? Nat "regular_bits") == attr.regularBits &&
    (← value.getObjValAs? Nat "pointee_size_bytes") == attr.pointeeSizeBytes &&
    (← value.getObjValAs? (Option Nat) "pointee_align_bytes") == attr.pointeeAlignBytes &&
    (← (← value.getObjVal? "arg_extension").getObjValAs? String "kind") == "none") "shim ABI attributes differ"
private def compareAbi (doc : Document) (closure : Nat) (oracle abi : Json) (want : ClosureShimAbi) : Except String Unit := do
  ensure ((← (← abi.getObjVal? "calling_convention").getObjValAs? String "kind") == "rust" &&
    (← abi.getObjValAs? Bool "can_unwind") == want.canUnwind &&
    (← abi.getObjValAs? Bool "c_variadic") == want.cVariadic &&
    (← abi.getObjValAs? Nat "fixed_count") == want.fixedCount) "shim ABI preamble differs"
  let args ← abi.getObjValAs? (Array Json) "arguments"
  ensure (args.size == 1) "shim ABI did not untuple unit"
  let some arg := args[0]? | throw "shim ABI receiver absent"
  localType doc closure (← oracle.getObjValAs? (Array Json) "definitions")
    (← oracle.getObjValAs? (Array Json) "types") (← arg.getObjValAs? Nat "type") want.receiver
  compareMode want.receiverMode (← arg.getObjVal? "mode")
  ensure ((← arg.getObjValAs? Nat "layout_size") == want.receiverLayout.size &&
    (← arg.getObjValAs? Nat "layout_align") == want.receiverLayout.align) "shim ABI receiver layout differs"
  let ret ← abi.getObjVal? "return"
  localType doc closure (← oracle.getObjValAs? (Array Json) "definitions")
    (← oracle.getObjValAs? (Array Json) "types") (← ret.getObjValAs? Nat "type") .output
  compareMode want.outputMode (← ret.getObjVal? "mode")
  ensure ((← ret.getObjValAs? Nat "layout_size") == want.outputLayout.size &&
    (← ret.getObjValAs? Nat "layout_align") == want.outputLayout.align) "shim ABI return layout differs"

private def mutateMethods (doc : Document) (change : Json → Json) : Except String Document := do
  let material ← doc.source.getObjVal? "fn_vtable_source"
  let declarations ← (← material.getObjValAs? (Array Json) "declarations").mapM fun row => do
    let items ← (← row.getObjValAs? (Array Json) "associated_items").mapM fun item => do
      if (← item.getObjValAs? String "kind") != "method" then return item
      return item.setObjVal! "method" (change (← item.getObjVal? "method"))
    return row.setObjVal! "associated_items" (toJson items)
  let updated := material.setObjVal! "declarations" (toJson declarations)
  return {doc with source := doc.source.setObjVal! "fn_vtable_source" updated}

private def changeFirstClause (row : Json) (key : String) (value : Json) : Json :=
  match (row.getObjValAs? (Array Json) "clause_source").toOption with
  | some owners => match owners[1]? with
    | some parent => match (parent.getObjValAs? (Array Json) "clauses").toOption with
      | some clauses => match clauses[0]? with
        | some clause => row.setObjVal! "clause_source" (toJson (owners.set! 1
            (parent.setObjVal! "clauses" (toJson (clauses.set! 0 (clause.setObjVal! key value))))))
        | none => row
      | none => row
    | none => row
  | none => row

def main (paths : List String) : IO Unit := do
  let [sourcePath,oraclePath] := paths | throw (IO.userError "expected source and projected oracle")
  let doc ← checked (Json.parse (← IO.FS.readFile sourcePath) >>= decode)
  let oracle ← checked (Json.parse (← IO.FS.readFile oraclePath))
  unless (← checked (oracle.getObjValAs? String "oracle_schema")) == "lean-miri-rustc-mir" &&
      (← checked (oracle.getObjValAs? Nat "oracle_schema_version")) == 12 &&
      (← checked (oracle.getObjValAs? String "rustc_commit")) == "8144389c895da997dbdecaa635e41d6a50be6ffd" do
    throw (IO.userError "shim oracle schema/compiler pin differs")
  let some closure := doc.definitions.findIdx? (fun row => (row.getObjValAs? String "path").toOption == some "std::rt::lang_start::{closure#0}")
    | throw (IO.userError "std closure absent")
  let args := #[ItemArgument.type (.tuple #[])]
  let resolved ← checked (resolveClosureVtableMethods doc closure args (.tuple #[]) (.primitive "int" "i32"))
  unless resolved.methods.size == 3 do throw (IO.userError "resolved slot count differs")
  unless resolved.cells.size == 6 do throw (IO.userError "resolved cell count differs")
  for cell in resolved.cells.extract 3 6 do
    match cell with
    | .method _ => pure ()
    | _ => throw (IO.userError "resolved Fn slot is not Method")
  let instances ← checked (oracle.getObjValAs? (Array Json) "instances")
  for vtable in #[true,false] do
    let kind := if vtable then "vtable" else "closure_once"
    let rows ← checked (instances.filterM fun row => do
      return ((← row.getObjVal? "instance_kind").getObjValAs? String "shim_kind").toOption == some kind)
    let some row := rows[0]? | throw (IO.userError "compiler shim absent")
    let id ← checked (row.getObjValAs? Nat "instance_id")
    let bodies ← checked (oracle.getObjValAs? (Array Json) "shim_bodies")
    let rows ← checked (bodies.filterM fun row => return (← row.getObjValAs? Nat "instance_id") == id)
    let some body := rows[0]? | throw (IO.userError "compiler shim body absent")
    checked (compareBody doc closure oracle body (← checked (closureShimBody doc closure args (.tuple #[]) (.primitive "int" "i32") vtable)))
    let abis ← checked (oracle.getObjValAs? (Array Json) "shim_abis")
    let rows ← checked (abis.filterM fun row => return (← row.getObjValAs? Nat "instance_id") == id)
    let some abi := rows[0]? | throw (IO.userError "compiler shim ABI absent")
    checked (compareAbi doc closure oracle (← checked (abi.getObjVal? "value")) (← checked (closureShimAbi doc closure args (.tuple #[]) (.primitive "int" "i32") vtable)))
  rejects (resolveClosureVtableMethods doc closure #[] (.tuple #[]) (.primitive "int" "i32"))
  rejects (resolveClosureVtableMethods doc closure args (.tuple #[.primitive "int" "i32"]) (.primitive "int" "i32"))
  rejects (resolveClosureVtableMethods doc closure args (.tuple #[]) (.primitive "int" "i64"))
  let missing ← checked (mutateMethods doc (fun row => row.setObjVal! "clause_source" Json.null))
  rejects (resolveClosureVtableMethods missing closure args (.tuple #[]) (.primitive "int" "i32"))
  let incomplete ← checked (mutateMethods doc fun row =>
    row.setObjVal! "clause_source" (toJson (#[] : Array Json)))
  rejects (resolveClosureVtableMethods incomplete closure args (.tuple #[]) (.primitive "int" "i32"))
  -- A concrete clause list with one omitted inherited predicate is not a
  -- witness for an empty/impossible-clause result.
  let dropped ← checked (mutateMethods doc fun row =>
    match (row.getObjValAs? (Array Json) "clause_source").toOption with
    | some owners => match owners[1]? with
      | some parent => match (parent.getObjValAs? (Array Json) "clauses").toOption with
        | some clauses => row.setObjVal! "clause_source" (toJson (owners.set! 1
            (parent.setObjVal! "clauses" (toJson (clauses.extract 1 clauses.size)))))
        | none => row
      | none => row
    | none => row)
  rejects (resolveClosureVtableMethods dropped closure args (.tuple #[]) (.primitive "int" "i32"))
  for (key,value) in #[("polarity",toJson "Negative"),
      ("bound_variables",toJson (#["Region(fake)"] : Array String)),
      ("core_source",toJson false)] do
    let bad ← checked (mutateMethods doc fun row => changeFirstClause row key value)
    rejects (resolveClosureVtableMethods bad closure args (.tuple #[]) (.primitive "int" "i32"))
  let missingAttrs ← checked (mutateMethods doc fun row => row.setObjVal! "never_unwind" Json.null)
  rejects (closureShimAbi missingAttrs closure args (.tuple #[]) (.primitive "int" "i32") true)
  let missingSpan ← checked (mutateMethods doc fun row => row.setObjVal! "source_span_key" Json.null)
  rejects (closureShimBody missingSpan closure args (.tuple #[]) (.primitive "int" "i32") true)
  let comp ← checked (doc.source.getObjVal? "compilation")
  let optimized := {doc with source := doc.source.setObjVal! "compilation" (comp.setObjVal! "opt_level" (toJson "Default"))}
  rejects (closureShimAbi optimized closure args (.tuple #[]) (.primitive "int" "i32") true)
  IO.println "closure slots all Method; generated VTable/ClosureOnce symbolic MIR and ABI match pinned compiler (identities and physical closure registry remain unbound)"
