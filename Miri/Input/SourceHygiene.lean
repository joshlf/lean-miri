import Miri.Input.Model.Types
import Miri.Input.JsonReader

namespace Miri.Input.SourceHygiene
open JsonReader

def syntaxContext : Parser SyntaxContext := do
  let f ← object (none : Option (Option Nat)) fun f key => do
    if key == "outer_expansion" then return some (← nullable natural)
    skipValue
    pure f
  pure ⟨← required f "outer_expansion"⟩

def expansion : Parser SourceExpansion := do
  let f ← object ((none,none) : Option Nat × Option Bool) fun f key => do
    match key with
    | "call_site" => pure (some (← natural),f.2)
    | "collapse_debuginfo" => pure (f.1,some (← boolean))
    | _ => skipValue; pure f
  pure ⟨← required f.1 "call_site", ← required f.2 "collapse_debuginfo"⟩

def walk (spans : Array SourceSpanData) (contexts : Array SyntaxContext)
    (expansions : Array SourceExpansion) (bodyContext : Nat) :
    Nat → SpanId → SpanId → Except String SpanId
  | 0,_,_ => throw "cyclic source expansion call-site chain"
  | fuel+1,current,result => do
    let some span := spans[current]? | throw "source hygiene span is absent"
    if span.context == bodyContext then return result
    let some context := contexts[span.context]? | throw "source syntax context is absent"
    let some expansion := context.outerExpansion | return result
    let some declaration := expansions[expansion]? | throw "source expansion is absent"
    walk spans contexts expansions bodyContext fuel declaration.callSite
      (if declaration.collapseDebuginfo then declaration.callSite else result)

def collapse (spans : Array SourceSpanData) (contexts : Array SyntaxContext)
    (expansions : Array SourceExpansion) (current body : SpanId) : Except String SpanId := do
  let some body := spans[body]? | throw "source hygiene body span is absent"
  walk spans contexts expansions body.context (contexts.size+1) current current

def validate (spans : Array SourceSpanData) (contexts : Array SyntaxContext)
    (expansions : Array SourceExpansion) : Except String Unit := do
  let some root := contexts[0]? | throw "source syntax contexts lack the root"
  unless root.outerExpansion.isNone do throw "source root syntax context has an expansion"
  for (context,index) in contexts.toList.zipIdx do
    if index != 0 && context.outerExpansion.isNone then throw "duplicate root syntax context"
    if let some expansion := context.outerExpansion then
      unless expansion < expansions.size do throw "syntax context expansion is absent"
  for expansion in expansions do
    unless expansion.callSite < spans.size do throw "expansion call-site span is absent"
  let mut positions : Std.HashMap Nat (SourcePosition × Nat) := {}
  for span in spans do
    unless span.context < contexts.size do throw "span syntax context is absent"
    unless span.lo < 2^32 && span.hi < 2^32 do throw "source span BytePos exceeds u32"
    let position := (span.start,span.runtimeFile)
    if let some previous := positions[span.lo]? then
      unless previous == position do throw "conflicting exact source positions"
    else positions := positions.insert span.lo position
  for (context,index) in contexts.toList.zipIdx do
    if context.outerExpansion.isSome then
      let mut current := index
      let mut seen : Std.HashSet Nat := {}
      for _ in [:contexts.size+1] do
        if current == 0 then break
        if seen.contains current then throw "cyclic source syntax contexts"
        seen := seen.insert current
        let some context := contexts[current]? | throw "source syntax context is absent"
        let some expansion := context.outerExpansion | throw "non-root context has no expansion"
        let some declaration := expansions[expansion]? | throw "source expansion is absent"
        let some site := spans[declaration.callSite]? | throw "expansion call-site span is absent"
        current := site.context
      unless current == 0 do throw "source syntax context chain does not reach root"

theorem walk_sameContext (spans : Array SourceSpanData) (contexts : Array SyntaxContext)
    (expansions : Array SourceExpansion) (bodyContext fuel current result : Nat)
    (span : SourceSpanData) (found : spans[current]? = some span)
    (same : span.context = bodyContext) :
    walk spans contexts expansions bodyContext (fuel+1) current result = .ok result := by
  simp [walk,found,same] <;> rfl

theorem walk_root (spans : Array SourceSpanData) (contexts : Array SyntaxContext)
    (expansions : Array SourceExpansion) (bodyContext fuel current result : Nat)
    (span : SourceSpanData) (context : SyntaxContext)
    (found : spans[current]? = some span) (different : span.context ≠ bodyContext)
    (foundContext : contexts[span.context]? = some context) (root : context.outerExpansion = none) :
    walk spans contexts expansions bodyContext (fuel+1) current result = .ok result := by
  simp [walk,found,different,foundContext,root] <;> rfl

theorem walk_expansion (spans : Array SourceSpanData) (contexts : Array SyntaxContext)
    (expansions : Array SourceExpansion) (bodyContext fuel current result index : Nat)
    (span : SourceSpanData) (context : SyntaxContext) (declaration : SourceExpansion)
    (found : spans[current]? = some span) (different : span.context ≠ bodyContext)
    (foundContext : contexts[span.context]? = some context) (outer : context.outerExpansion = some index)
    (foundExpansion : expansions[index]? = some declaration) :
    walk spans contexts expansions bodyContext (fuel+1) current result =
      walk spans contexts expansions bodyContext fuel declaration.callSite
        (if declaration.collapseDebuginfo then declaration.callSite else result) := by
  simp [walk,found,different,foundContext,outer,foundExpansion]

inductive Chain (spans : Array SourceSpanData) (contexts : Array SyntaxContext)
    (expansions : Array SourceExpansion) (bodyContext : Nat) : SpanId → List SourceExpansion → Prop
  | same {current : SpanId} {span : SourceSpanData}
      (found : spans[current]? = some span) (same : span.context = bodyContext) :
      Chain spans contexts expansions bodyContext current []
  | root {current : SpanId} {span : SourceSpanData} {context : SyntaxContext}
      (found : spans[current]? = some span) (different : span.context ≠ bodyContext)
      (foundContext : contexts[span.context]? = some context) (root : context.outerExpansion = none) :
      Chain spans contexts expansions bodyContext current []
  | next {current index : Nat} {span : SourceSpanData} {context : SyntaxContext}
      {declaration : SourceExpansion} {tail : List SourceExpansion}
      (found : spans[current]? = some span) (different : span.context ≠ bodyContext)
      (foundContext : contexts[span.context]? = some context) (outer : context.outerExpansion = some index)
      (foundExpansion : expansions[index]? = some declaration)
      (rest : Chain spans contexts expansions bodyContext declaration.callSite tail) :
      Chain spans contexts expansions bodyContext current (declaration :: tail)

def lastCollapsed : List SourceExpansion → Option SpanId
  | [] => none
  | declaration :: tail => (lastCollapsed tail).orElse fun _ =>
      if declaration.collapseDebuginfo then some declaration.callSite else none

theorem walk_of_chain (spans : Array SourceSpanData) (contexts : Array SyntaxContext)
    (expansions : Array SourceExpansion) (bodyContext current : Nat) (trace : List SourceExpansion)
    (chain : Chain spans contexts expansions bodyContext current trace) (fuel result : Nat)
    (enough : trace.length+1 ≤ fuel) :
    walk spans contexts expansions bodyContext fuel current result = .ok ((lastCollapsed trace).getD result) := by
  induction chain generalizing fuel result with
  | same found same =>
    cases fuel with
    | zero => simp at enough
    | succ fuel => simpa [lastCollapsed] using walk_sameContext spans contexts expansions bodyContext fuel _ result _ found same
  | root found different foundContext root =>
    cases fuel with
    | zero => simp at enough
    | succ fuel => simpa [lastCollapsed] using walk_root spans contexts expansions bodyContext fuel _ result _ _ found different foundContext root
  | @next current index span context declaration tail found different foundContext outer foundExpansion rest ih =>
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      rw [walk_expansion spans contexts expansions bodyContext fuel current result index span context declaration
        found different foundContext outer foundExpansion]
      have remaining : tail.length+1 ≤ fuel := by simp at enough; omega
      rw [ih fuel (if declaration.collapseDebuginfo then declaration.callSite else result) remaining]
      cases h : lastCollapsed tail <;> cases flag : declaration.collapseDebuginfo <;>
        simp [lastCollapsed,h,flag]

theorem collapse_of_chain (spans : Array SourceSpanData) (contexts : Array SyntaxContext)
    (expansions : Array SourceExpansion) (current body : SpanId) (bodySpan : SourceSpanData)
    (trace : List SourceExpansion) (foundBody : spans[body]? = some bodySpan)
    (chain : Chain spans contexts expansions bodySpan.context current trace)
    (bounded : trace.length ≤ contexts.size) :
    collapse spans contexts expansions current body = .ok ((lastCollapsed trace).getD current) := by
  simp only [collapse,foundBody]
  exact walk_of_chain spans contexts expansions bodySpan.context current trace chain
    (contexts.size+1) current (by omega)

end Miri.Input.SourceHygiene
