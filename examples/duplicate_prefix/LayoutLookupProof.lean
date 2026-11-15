import duplicate_prefix.NodeLookupProof
import Lean

namespace DuplicatePrefix.LayoutLookupProof
open Miri.Input Miri.ABI
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def firstInsert {Row Value : Type} (key : Row → TypeId) (value : Row → Value)
    (entries : Std.HashMap TypeId Value) (row : Row) :=
  if entries.contains (key row) then entries else entries.insert (key row) (value row)

theorem list_lookup {Row Value : Type} (key : Row → TypeId) (value : Row → Value)
    (rows : List Row) (entries : Std.HashMap TypeId Value) (id : TypeId) :
    (Id.run (forIn rows entries (fun row state => pure (.yield (firstInsert key value state row)))))[id]? =
      (entries[id]?).orElse (fun _ => (rows.find? (fun row => key row == id)).map value) := by
  induction rows generalizing entries with
  | nil => simp [List.forIn_nil]
  | cons row rows ih =>
    simp only [List.forIn_cons, Id.run, pure, bind, Id.instMonad]
    simp only [Id.run, pure, bind] at ih
    rw [ih]
    unfold firstInsert
    cases held : entries[id]? <;> by_cases same : key row = id <;>
      by_cases stored : entries.contains (key row) <;>
      simp_all [-Std.HashMap.isSome_getElem?_eq_contains, List.find?, Std.HashMap.contains_eq_isSome_getElem?,
        Std.HashMap.getElem?_insert, Option.orElse]
    all_goals
      have different : (key row == id) = false := by simpa using same
      rw [different]

/-- Layout lookup uses the layout ID of the checked canonical type row. -/
theorem indexed_lookup_eq (metadata : RuntimeMetadata) (id : TypeId) (node : TypeNode)
    (source : metadata.node id = .ok node) :
    metadata.lookup id = (do
      let layout ← match metadata.source.layouts[node.layoutId]? with
        | some value => Except.ok value
        | none => Except.error (.missing s!"compiler layout ID {node.layoutId} out of bounds")
      pure ⟨id, ← RuntimeMetadata.layout metadata.target layout⟩) := by
  simp only [RuntimeMetadata.lookup, RuntimeMetadata.require, source, bind, Except.bind, pure, Except.pure]
  cases metadata.source.layouts[node.layoutId]? <;> rfl

#print axioms list_lookup
#print axioms indexed_lookup_eq
end DuplicatePrefix.LayoutLookupProof
