import Miri.Frontend.FoundationSource
import Miri.Input.Model.Types

/-! Relocation of body-local exact rustc Span identities. Equal diagnostic
payloads with distinct compiler identities remain separate physical span rows. -/
namespace Miri.Frontend.Foundation
open Lean

structure SpanRegistry where
  files : Array String
  spans : Array Input.SourceSpanData
  compilerSpans : Array SourceSpan
  backtraces : Array Input.BacktraceSpan

private def internFile (files : Array String) (name : String) : Array String × Nat :=
  match files.findIdx? (· == name) with
  | some index => (files, index)
  | none => (files.push name, files.size)

/-- Construct physical source rows solely from captured compiler identities and
body-relative collapsed positions. No position is inferred from a span start. -/
def buildSpanRegistry (body : Json) : Except String SpanRegistry := do
  validateSourceMetadata body
  let backtraces ← sourceBacktraces body
  let mut sources := backtraces.map (·.span)
  let metadata ← body.getObjVal? "source_metadata"
  for scope in (← metadata.getObjValAs? (Array Json) "scopes") do
    sources := sources.push (← sourceSpan (← scope.getObjVal? "span"))
  let sorted := sources.qsort (fun a b => a.identity < b.identity)
  let mut compilerSpans : Array SourceSpan := #[]
  for entry in sorted do
    if let some previous := compilerSpans[entry.identity]? then
      unless previous == entry do throw "conflicting compiler span identity"
    else
      unless entry.identity == compilerSpans.size do throw "non-dense compiler span identity"
      compilerSpans := compilerSpans.push entry
  let mut files := #[]
  let mut spans := #[]
  for entry in compilerSpans do
    let (updated, file) := internFile files entry.file
    files := updated
    spans := spans.push {
      isDummy := entry.isDummy, lo := entry.lo, hi := entry.hi
      start := ⟨entry.startLine, entry.startColumn⟩
      «end» := ⟨entry.endLine, entry.endColumn⟩
      context := entry.context, file : Input.SourceSpanData }
  let mut positions := #[]
  for entry in backtraces do
    let (updated, file) := internFile files entry.filename
    files := updated
    positions := positions.push {
      spanId := entry.span.identity
      position := ⟨entry.bytePosition, entry.line, entry.zeroBasedCharColumn, file⟩ : Input.BacktraceSpan }
  return ⟨files, spans, compilerSpans, positions⟩

end Miri.Frontend.Foundation
