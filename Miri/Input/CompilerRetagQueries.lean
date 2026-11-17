import Miri.Input.Model.Catalogs

/-! Compilation-local protected-frame attributes from the pinned
tree_borrows/mod.rs:143–148. Validate the entire table once, retaining any
failure until the source operation demands an attribute. -/
namespace Miri.Input.CompilerRetagQueries

structure Prepared where
  private values : Std.HashMap DefinitionRef Bool

def prepare (definitionCount : Nat) (rows : Array Catalog.RetagQuery) :
    Except String Prepared := do
  let mut values : Std.HashMap DefinitionRef Bool := {}
  for row in rows do
    unless row.definition < definitionCount do
      throw "retag compiler definition ID out of bounds"
    if values.contains row.definition then
      throw "duplicate compiler retag definition query"
    values := values.insert row.definition row.rustcNoWritable
  pure ⟨values⟩

/-- Frame existence precedes table errors, just as in the original scan.
Missing attributes remain errors rather than a default false attribute. -/
def lookup (definitionCount : Nat) (prepared : Except String Prepared)
    (id : MIR.DefId) : Except String Bool := do
  unless id < definitionCount do
    throw "retag frame absent from canonical compiler definition table"
  let prepared ← prepared
  let some value := prepared.values[id]?
    | throw "exact compiler retag frame attribute query absent"
  pure value

end Miri.Input.CompilerRetagQueries
