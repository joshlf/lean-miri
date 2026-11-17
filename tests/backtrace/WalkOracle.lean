import Miri.Input.Decoder
import Miri.Input.SourceHygiene

open Lean Miri.Input
private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)

private structure Row where
  body : Nat
  span : Nat
  collapsed : Nat
  bytePosition : Nat
  line : Nat
  column : Nat
  filename : String

private structure Fields where
  body : Option Nat := none
  span : Option Nat := none
  collapsed : Option Nat := none
  bytePosition : Option Nat := none
  line : Option Nat := none
  column : Option Nat := none
  filename : Option String := none

private def row : JsonReader.Parser Row := do
  let f ← JsonReader.object ({} : Fields) fun f key => do
    match key with
    | "body_span" => pure {f with body := some (← JsonReader.natural)}
    | "span" => pure {f with span := some (← JsonReader.natural)}
    | "collapsed_span" => pure {f with collapsed := some (← JsonReader.natural)}
    | "byte_position" => pure {f with bytePosition := some (← JsonReader.natural)}
    | "line" => pure {f with line := some (← JsonReader.natural)}
    | "zero_based_char_column" => pure {f with column := some (← JsonReader.natural)}
    | "filename" => pure {f with filename := some (← JsonReader.string)}
    | _ => JsonReader.skipValue; pure f
  return ⟨← JsonReader.required f.body "body_span", ← JsonReader.required f.span "span",
    ← JsonReader.required f.collapsed "collapsed_span", ← JsonReader.required f.bytePosition "byte_position",
    ← JsonReader.required f.line "line", ← JsonReader.required f.column "zero_based_char_column",
    ← JsonReader.required f.filename "filename"⟩

private def rows : JsonReader.Parser (Array Row) := do
  let rows ← JsonReader.object (none : Option (Array Row)) fun rows key => do
    if key == "backtrace_walks" then return some (← JsonReader.array row)
    JsonReader.skipValue
    pure rows
  JsonReader.required rows "backtrace_walks"

def main (args : List String) : IO Unit := do
  let [input,oracle] := args | throw (IO.userError "expected source input and byte-bound Rust oracle")
  let decoded ← must (decodeJson (← IO.FS.readFile input))
  let document := decoded.document
  let expected ← must (JsonReader.run rows (← IO.FS.readFile oracle))
  unless !expected.isEmpty do throw (IO.userError "no Rust source walks were compared")
  for row in expected do
    let id ← must (SourceHygiene.collapse document.spans document.syntaxContexts document.expansions row.span row.body)
    unless id == row.collapsed do throw (IO.userError s!"collapsed span differs: body={row.body} span={row.span}")
    let some source := document.spans[id]? | throw (IO.userError "collapsed source span absent")
    unless source.lo == row.bytePosition && source.start.line == row.line && source.start.column == row.column &&
        document.files[source.runtimeFile]? == some row.filename do
      throw (IO.userError s!"collapsed source position differs: body={row.body} span={row.span}")
  IO.println s!"source hygiene Rust comparison: walks={expected.size}, failures=0; finite comparisons, separate from local kernel lemmas"
