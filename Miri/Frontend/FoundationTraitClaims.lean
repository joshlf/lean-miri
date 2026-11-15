import Miri.Frontend.Foundation

/-! A finite source-header matcher, not a general trait solver. The producer
captures every impl of a local ordinary methodless trait before any demand.
Only unconditional positive primitive headers are supported; no blanket,
negative, automatic or method-dispatch fallback is inferred. -/
namespace Miri.Frontend.Foundation
open Lean

private def primitiveAllowed (kind name : String) : Bool :=
  (kind == "bool" || kind == "char") && name == "" ||
    kind == "int" && #["i8", "i16", "i32", "i64", "i128", "isize"].contains name ||
    kind == "uint" && #["u8", "u16", "u32", "u64", "u128", "usize"].contains name ||
    kind == "float" && #["f16", "f32", "f64", "f128"].contains name

/-- Decide one fully substituted local primitive trait obligation from the
complete source headers. False means no supported source impl matches, whereas
missing or unsupported material returns an error. -/
def localTraitClaim (definition : Json) (self : ConcreteType) : Except String Bool := do
  let source ← definition.getObjVal? "local_trait"
  unless (← source.getObjValAs? String "source_kind") == "local_ordinary_methodless_trait" &&
      (← source.getObjValAs? Bool "complete_impl_headers") do
    throw "unsupported/incomplete local trait source"
  unless (← source.getObjValAs? (Array Json) "associated_items").isEmpty do
    throw "unsupported local trait declaration"
  -- MetaSized is the pinned compiler's implicit supertrait. The supported
  -- primitive Self domain has fixed metadata; no auto-trait fallback is used.
  for clause in (← source.getObjValAs? (Array Json) "super_clauses") do
    unless (← clause.getObjValAs? String "kind") == "self_trait" &&
        (← clause.getObjValAs? String "lang_item") == "meta_sized" &&
        (← clause.getObjValAs? Nat "self_parameter") == 0 do
      throw "unsupported local trait super clause"
  let parameters ← source.getObjValAs? (Array Json) "parameters"
  unless parameters.size == 1 do throw "unsupported local trait parameters"
  let some parameter := parameters[0]? | throw "missing local trait Self"
  unless (← parameter.getObjValAs? String "kind") == "self" &&
      (← parameter.getObjValAs? Nat "index") == 0 do throw "invalid local trait Self"
  let .primitive kind name := self | throw "unsupported local trait self type"
  unless primitiveAllowed kind name do throw "unsupported local trait primitive"
  let mut matchCount := 0
  for header in (← source.getObjValAs? (Array Json) "implementations") do
    unless (← header.getObjValAs? String "polarity") == "positive" &&
        (← header.getObjValAs? (Array Json) "parameters").isEmpty &&
        (← header.getObjValAs? (Array Json) "clauses").isEmpty do
      throw "unsupported local trait impl header"
    let implemented ← header.getObjVal? "self_type"
    let implKind ← implemented.getObjValAs? String "kind"
    let implName ← implemented.getObjValAs? String "name"
    unless primitiveAllowed implKind implName do throw "unsupported local trait impl Self"
    if implKind == kind && implName == name then
      matchCount := matchCount + 1
  unless matchCount ≤ 1 do throw "duplicate matching local trait impls"
  return matchCount == 1

end Miri.Frontend.Foundation
