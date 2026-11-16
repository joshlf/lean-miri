import MiriTests.Connected.Proofs.CompilerPatternDecEq219

open Miri.Input

namespace SourceTraitPatternEquality

private theorem orSize (patterns : Array SourceTraitPattern) :
    sizeOf (SourceTraitPattern.or patterns) = sizeOf patterns + 1 := by
  cases patterns using Array.rec with
  | mk toList =>
    induction toList with
    | nil => rfl
    | cons head tail ih =>
      simp [sizeOf, SourceTraitPattern._sizeOf_1, SourceTraitPattern.rec_1,
        SourceTraitPattern.rec_2, Array._sizeOf_1, List._sizeOf_1] at *
      omega

def patternDecEq :
    (left right : SourceTraitPattern) → Decidable (left = right)
  | .range start finish, .range rightStart rightFinish =>
      if h : (start, finish) = (rightStart, rightFinish) then
        isTrue (by cases h; rfl)
      else
        isFalse (by intro hEq; cases hEq; exact h rfl)
  | .or leftPatterns, .or rightPatterns =>
      match PatternEquality219.arrayDecEqWith leftPatterns rightPatterns
          (fun left hLeft right hRight => patternDecEq left right) with
      | isTrue h => isTrue (congrArg SourceTraitPattern.or h)
      | isFalse h => isFalse (by intro hEq; injection hEq with hPatterns; exact h hPatterns)
  | .notNull, .notNull => isTrue rfl
  | .range _ _, .or _ | .range _ _, .notNull
  | .or _, .range _ _ | .or _, .notNull
  | .notNull, .range _ _ | .notNull, .or _ =>
      isFalse (by intro hEq; cases hEq)
termination_by left right => sizeOf left + sizeOf right
decreasing_by
  all_goals
    simp_wf
    have hLeftSize := Array.sizeOf_lt_of_mem hLeft
    have hRightSize := Array.sizeOf_lt_of_mem hRight
    have hLeftCtor : sizeOf leftPatterns < sizeOf (SourceTraitPattern.or leftPatterns) := by
      rw [orSize]
      omega
    have hRightCtor : sizeOf rightPatterns < sizeOf (SourceTraitPattern.or rightPatterns) := by
      rw [orSize]
      omega
    omega


end SourceTraitPatternEquality
