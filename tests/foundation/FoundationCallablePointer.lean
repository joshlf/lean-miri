import Miri.Frontend.FoundationCallable
open Lean Miri.Frontend.Foundation
private def checked (value : Except String α) : IO α :=
  match value with | .ok result => pure result | .error e => throw (IO.userError e)

def main (paths : List String) : IO Unit := do
  let [path, mode] := paths | throw (IO.userError "expected FnPtr-only source and mode")
  unless #["safe","unsafe","foreign"].contains mode do throw (IO.userError "unknown FnPtr source mode")
  let document ← checked (Json.parse (← IO.FS.readFile path) >>= decode)
  unless (← checked (document.source.getObjValAs? (Array Json) "closure_templates")).isEmpty do
    throw (IO.userError "FnPtr-only fixture unexpectedly has closure templates")
  unless !(document.types.any fun row => ((row.getObjVal? "shape").bind (·.getObjValAs? String "kind")).toOption == some "dynamic") do
    throw (IO.userError "FnPtr-only fixture unexpectedly has a dyn source type")
  let declarations ← checked (readFnVtableDeclarations document.source)
  for name in ["fn","fn_mut","fn_once"] do
    let _ ← checked (fnSourceRoot declarations name)
  let some id := document.types.findIdx? (fun row =>
      ((row.getObjVal? "shape").bind (·.getObjValAs? String "kind")).toOption == some "function_pointer")
    | throw (IO.userError "FnPtr-only source type absent")
  if mode == "foreign" then
    match typeExpr document id with
    | .error "function-pointer ABI unsupported" => pure ()
    | .error e => throw (IO.userError s!"unexpected foreign FnPtr source outcome: {e}")
    | .ok _ => throw (IO.userError "foreign FnPtr was silently treated as Rust-compatible")
  else
    let pointer ← checked (instantiate #[] #[] (← checked (typeExpr document id)))
    for kind in [SourceClosureKind.fn,.fnMut,.fnOnce] do
      let name := match kind with | .fn => "fn" | .fnMut => "fn_mut" | .fnOnce => "fn_once"
      let _ ← checked (fnSourceRoot declarations name)
      for vtable in [false,true] do
        let result := builtinFnPointerRecipe document pointer kind (.tuple #[]) (.primitive "int" "i32") vtable
        if mode == "unsafe" then
          match result with
          | .error "function pointer does not satisfy builtin Fn signature source rule" => pure ()
          | .error e => throw (IO.userError s!"unexpected unsafe FnPtr source outcome: {e}")
          | .ok _ => throw (IO.userError "unsafe FnPtr implemented builtin safe Fn")
        else
          match ← checked result with
          | .vtable .. => unless vtable && kind == .fnOnce do throw (IO.userError "unexpected FnPtr VTableShim")
          | .fnPointer .. => unless !vtable || kind != .fnOnce do throw (IO.userError "FnPtr vtable by-value slot omitted shim")
          | _ => throw (IO.userError "FnPtr-only source selected a closure recipe")
  IO.println s!"FnPtr-only declaration source: {mode} passed"
