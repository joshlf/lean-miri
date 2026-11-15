import Miri.Input.SourceCompilerTypes

/-! Successful physical interning preserves existing canonical type and layout
rows. These are local transition properties, with no global World invariant. -/
namespace Miri.Input.SourceCompilerWorld
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

theorem internType_pools (before after : World) (shape : TypeShape) (layout : Layout) (display : String) (id : TypeId)
    (result : internType before shape layout display = .ok (after,id)) :
    (after.canonical.types = before.canonical.types ∧ after.canonical.layouts = before.canonical.layouts) ∨
    (∃ node, after.canonical.types = before.canonical.types.push node ∧
      after.canonical.layouts = before.canonical.layouts.push layout) := by
  simp only [internType, bind, Except.bind, pure, Except.pure] at result
  repeat' split at result
  all_goals simp_all only [reduceCtorEq, Except.ok.injEq, Prod.mk.injEq]
  all_goals rcases result with ⟨rfl, rfl⟩
  all_goals first | exact Or.inr ⟨_,rfl,rfl⟩ | exact Or.inl ⟨True.intro,True.intro⟩


theorem internType_preserves_rows (before after : World) (shape : TypeShape)
    (layout : Layout) (display : String) (id : TypeId)
    (result : internType before shape layout display = .ok (after,id)) :
    (∀ (i : Nat) (node : TypeNode), before.canonical.types[i]? = some node → after.canonical.types[i]? = some node) ∧
    (∀ (i : Nat) (row : Layout), before.canonical.layouts[i]? = some row → after.canonical.layouts[i]? = some row) := by
  rcases internType_pools before after shape layout display id result with unchanged | ⟨node,types,layouts⟩
  · rcases unchanged with ⟨types,layouts⟩
    simp only [types,layouts]
    exact ⟨fun _ _ h => h, fun _ _ h => h⟩
  · constructor
    · intro i old present
      rw [types]
      rcases Array.getElem?_eq_some_iff.mp present with ⟨bound,row⟩
      exact (Array.getElem?_push_lt bound).trans (congrArg some row)
    · intro i old present
      rw [layouts]
      rcases Array.getElem?_eq_some_iff.mp present with ⟨bound,row⟩
      exact (Array.getElem?_push_lt bound).trans (congrArg some row)


theorem internDefinition_preserves_physical_pools (before after : World) (raw : DefinitionId) (id : Nat)
    (result : internDefinition before raw = .ok (after,id)) :
    after.canonical.types = before.canonical.types ∧
      after.canonical.layouts = before.canonical.layouts := by
  simp only [internDefinition, bind, Except.bind, pure, Except.pure] at result
  repeat' split at result
  all_goals simp_all only [reduceCtorEq, Except.ok.injEq, Prod.mk.injEq]
  all_goals rcases result with ⟨rfl, rfl⟩
  all_goals simp


theorem internScalarConstant_preserves_physical_pools (before after : World) (typeId bits sizeBytes : Nat) (id : Nat)
    (result : internScalarConstant before typeId bits sizeBytes = .ok (after,id)) :
    after.canonical.types = before.canonical.types ∧
      after.canonical.layouts = before.canonical.layouts := by
  simp only [internScalarConstant, bind, Except.bind, pure, Except.pure] at result
  repeat' split at result
  all_goals simp_all only [reduceCtorEq, Except.ok.injEq, Prod.mk.injEq]
  all_goals rcases result with ⟨rfl, rfl⟩
  all_goals simp


theorem internPredicate_preserves_physical_pools (before after : World) (predicate : VtablePredicate) (id : Nat)
    (result : internPredicate before predicate = .ok (after,id)) :
    after.canonical.types = before.canonical.types ∧
      after.canonical.layouts = before.canonical.layouts := by
  simp only [internPredicate, bind, Except.bind, pure, Except.pure] at result
  repeat' split at result
  all_goals simp_all only [reduceCtorEq, Except.ok.injEq, Prod.mk.injEq]
  all_goals rcases result with ⟨rfl, rfl⟩
  all_goals simp

end Miri.Input.SourceCompilerWorld
