import Miri.Input.RuntimeMetadata
import Std.Data.HashMap.Lemmas
import Init.Data.List.Monadic

namespace DuplicatePrefix.NodeLookupProof
open Miri.Input
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def firstInsert {Value : Type} (key : Value → TypeId)
    (entries : Std.HashMap TypeId Value) (node : Value) :=
  if entries.contains (key node) then entries else entries.insert (key node) node

theorem list_lookup {Value : Type} (key : Value → TypeId)
    (nodes : List Value) (entries : Std.HashMap TypeId Value) (id : TypeId) :
    (Id.run (forIn nodes entries (fun node state => pure (.yield (firstInsert key state node)))))[id]? =
      (entries[id]?).orElse (fun _ => nodes.find? (fun node => key node == id)) := by
  induction nodes generalizing entries with
  | nil => simp [List.forIn_nil]
  | cons node nodes ih =>
    simp only [List.forIn_cons, Id.run, pure, bind, Id.instMonad]
    simp only [Id.run, pure, bind] at ih
    rw [ih]
    unfold firstInsert
    cases held : entries[id]? <;> by_cases same : key node = id <;>
      by_cases stored : entries.contains (key node) <;>
      simp_all [-Std.HashMap.isSome_getElem?_eq_contains, List.find?, Std.HashMap.contains_eq_isSome_getElem?,
        Std.HashMap.getElem?_insert, Option.orElse]
    all_goals
      have different : (key node == id) = false := by simpa using same
      rw [different]

/-- The current reader checks both the canonical table index and row identity. -/
theorem indexed_node (metadata : RuntimeMetadata) (id : TypeId) (node : TypeNode)
    (found : metadata.source.types[id]? = some node) (identity : node.id = id) :
    metadata.node id = .ok node := by
  simp [RuntimeMetadata.node, RuntimeMetadata.require, found, identity]
  rfl

#print axioms list_lookup
#print axioms indexed_node
end DuplicatePrefix.NodeLookupProof
