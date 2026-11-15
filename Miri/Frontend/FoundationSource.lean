import Lean

/-! Source metadata retained by finite-material export. These are source facts;
no executable body or query answer is constructed here. Span contexts and file
names are rustc diagnostic renderings, as in the existing MIR exporter. -/
namespace Miri.Frontend.Foundation
open Lean

set_option autoImplicit false in
structure SourceSpan where
  isDummy : Bool
  lo : Nat
  hi : Nat
  context : String
  file : String
  startLine : Nat
  startColumn : Nat
  endLine : Nat
  endColumn : Nat
  deriving Repr, DecidableEq

set_option autoImplicit false in
structure SourceInfo where
  span : SourceSpan
  scope : Nat
  deriving Repr, DecidableEq

private def span (j : Json) : Except String SourceSpan := do
  let start ← j.getObjVal? "start"
  let finish ← j.getObjVal? "end"
  let result : SourceSpan := {
    isDummy := ← j.getObjValAs? Bool "is_dummy"
    lo := ← j.getObjValAs? Nat "lo"
    hi := ← j.getObjValAs? Nat "hi"
    context := ← j.getObjValAs? String "ctxt"
    file := ← j.getObjValAs? String "file"
    startLine := ← start.getObjValAs? Nat "line"
    startColumn := ← start.getObjValAs? Nat "column"
    endLine := ← finish.getObjValAs? Nat "line"
    endColumn := ← finish.getObjValAs? Nat "column"
  }
  unless result.lo ≤ result.hi do throw "source span has reversed byte positions"
  return result

private def info (scopeCount : Nat) (j : Json) : Except String SourceInfo := do
  let scope ← j.getObjValAs? Nat "scope"
  unless scope < scopeCount do throw "source scope is out of bounds"
  return ⟨← span (← j.getObjVal? "span"), scope⟩

/-- Check identities and parallel source arrays against the captured MIR spine.
Inlining is rejected by the producer and remains unsupported here. -/
def validateSourceMetadata (body : Json) : Except String Unit := do
  let source ← body.getObjVal? "source_metadata"
  let _ ← span (← source.getObjVal? "span")
  let _ ← span (← source.getObjVal? "definition_span")
  let phase ← source.getObjVal? "phase"
  unless (← phase.getObjValAs? String "kind") == "runtime" do
    throw "source body is not runtime MIR"
  let _ ← source.getObjVal? "injection_phase"
  let scopes ← source.getObjValAs? (Array Json) "scopes"
  for h : i in [:scopes.size] do
    let scope := scopes[i]
    let _ ← span (← scope.getObjVal? "span")
    let parent ← scope.getObjValAs? (Option Nat) "parent"
    if let some parent := parent then
      unless parent < i do throw "source scope parent must precede child"
    unless (← scope.getObjValAs? (Option Nat) "inlined_parent").isNone do
      throw "inlined source metadata is unsupported"
  let locals ← body.getObjValAs? (Array Json) "locals"
  let declarations ← source.getObjValAs? (Array Json) "locals"
  unless declarations.size == locals.size do throw "source local count mismatch"
  for declaration in declarations do
    let _ ← declaration.getObjValAs? Bool "mutable"
    let _ ← info scopes.size (← declaration.getObjVal? "source_info")
  let blocks ← body.getObjValAs? (Array Json) "blocks"
  let locations ← source.getObjValAs? (Array Json) "blocks"
  unless blocks.size == locations.size do throw "source block count mismatch"
  for (block, location) in blocks.zip locations do
    let statements ← block.getObjValAs? (Array Json) "statements"
    let sources ← location.getObjValAs? (Array Json) "statements"
    unless statements.size == sources.size do throw "source statement count mismatch"
    for entry in sources do let _ ← info scopes.size entry
    let _ ← info scopes.size (← location.getObjVal? "terminator")

/-- Derive storage initialization from finite MIR markers. Pinned rustc
`always_storage_live_locals` removes locals mentioned by either StorageLive or
StorageDead; the return place and arguments are initialized separately. -/
def alwaysStorageLive (body : Json) : Except String (Array Bool) := do
  let declarations ← body.getObjValAs? (Array Json) "locals"
  let mut result := Array.replicate declarations.size true
  for block in (← body.getObjValAs? (Array Json) "blocks") do
    for statement in (← block.getObjValAs? (Array Json) "statements") do
      let kind ← statement.getObjValAs? String "kind"
      if kind == "storage_live" || kind == "storage_dead" then
        let index ← statement.getObjValAs? Nat "local"
        if h : index < result.size then
          result := result.set index false
        else throw "storage marker local is out of bounds"
  return result

end Miri.Frontend.Foundation
