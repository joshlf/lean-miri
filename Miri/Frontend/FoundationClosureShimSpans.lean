import Miri.Frontend.FoundationClosureShims
import Miri.Frontend.FoundationSpanRegistry

/-! Source spans for generated call shims. build_call_shim uses the method's
actual def_span for the body, every local, statement, terminator and scope, and
session DUMMY_SP for call arguments. With an unhygienic method declaration the
body-relative walk_chain_collapsed is the identity. Other hygiene domains fail
rather than guessing a backtrace position. No rustc body/query is requested. -/
namespace Miri.Frontend.Foundation
open Lean

structure ClosureShimSpans where
  registry : SpanRegistry
  methodSpan : Nat
  argumentSpan : Nat

def closureShimSpans (document : Document) (body : ClosureShimBody) :
    Except String ClosureShimSpans := do
  let key := body.sourceSpanKey
  let lo ← key.getObjValAs? Nat "lo"
  let hi ← key.getObjValAs? Nat "hi"
  let context ← key.getObjValAs? String "ctxt"
  let parent ← key.getObjValAs? (Option Nat) "parent_local_definition"
  unless lo > 0 && lo ≤ hi && context == "#0" && parent.isNone do
    throw "closure shim hygienic/parented/dummy method span unsupported"
  let location := body.sourceSpan
  let start ← location.getObjVal? "start"
  let finish ← location.getObjVal? "end"
  let file ← location.getObjValAs? String "file"
  let line ← start.getObjValAs? Nat "line"
  let column ← start.getObjValAs? Nat "column"
  let endLine ← finish.getObjValAs? Nat "line"
  let endColumn ← finish.getObjValAs? Nat "column"
  unless line > 0 && line ≤ endLine && (line != endLine || column ≤ endColumn) do
    throw "closure shim declaration position invalid"
  let compiler : SourceSpan := ⟨0,parent,false,lo,hi,context,file,line,column,endLine,endColumn⟩
  let source : Input.SourceSpanData := {
    isDummy := false, lo, hi, context, file := 0,
    start := ⟨line,column⟩, «end» := ⟨endLine,endColumn⟩ }
  let registry : SpanRegistry := {
    files := #[file], compilerSpans := #[compiler], spans := #[source],
    backtraces := #[⟨0,⟨lo,line,column,0⟩⟩] }
  let (registry,dummy) ← appendSessionRootSpan registry document.source
  return ⟨registry,0,dummy⟩

end Miri.Frontend.Foundation
