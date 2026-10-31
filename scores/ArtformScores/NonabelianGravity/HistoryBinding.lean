import ArtformScores.NonabelianGravity.HistoryMatrix
import ArtformScores.NonabelianGravity.HistorySolve

/-! # All native matching equations and complete source conditions at arbitrary length -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.HistoryElimination
open Legendre

lemma native_matching_iff {n : ℕ} (x z : Point ℚ) (j y : Vector n) :
    NativeMatch x z j y ↔ (historyMatrix n).mulVec y = sourceResidual x z j := by
  constructor
  · intro h
    funext ti
    rcases ti with ⟨t, i⟩
    have hm := congrFun ((matching_iff (previous x y t) (row y t)
      (following z y t) (row j t)).mp (h t)) i
    rw [matrix_row]
    have h0 : t.val = 0 ↔ ¬0 < t.val := by omega
    have hl : t.val + 1 = n ↔ ¬t.val + 1 < n := by omega
    by_cases hp : 0 < t.val <;> by_cases hn : t.val + 1 < n
    all_goals
      simp [previous, following, sourceResidual, h0, hl, hp, hn, row] at hm ⊢
      linear_combination hm
  · intro h t
    apply (matching_iff (previous x y t) (row y t) (following z y t) (row j t)).mpr
    funext i
    have hm := congrFun h (t, i)
    rw [matrix_row] at hm
    have h0 : t.val = 0 ↔ ¬0 < t.val := by omega
    have hl : t.val + 1 = n ↔ ¬t.val + 1 < n := by omega
    by_cases hp : 0 < t.val <;> by_cases hn : t.val + 1 < n
    all_goals
      simp [previous, following, sourceResidual, h0, hl, hp, hn, row] at hm ⊢
      linear_combination hm

lemma native_certificate_exists (n : ℕ) : Nonempty (Certificate (historyMatrix n)) :=
  certificate_exists _ (history_symmetric n)

lemma native_source_iff {n : ℕ} (c : Certificate (historyMatrix n))
    (x z : Point ℚ) (j : Vector n) :
    (∃ y, NativeMatch x z j y) ↔ Compatible c (sourceResidual x z j) := by
  simp only [native_matching_iff]
  exact solvable_iff c _

lemma native_all_solutions {n : ℕ} (c : Certificate (historyMatrix n))
    (x z : Point ℚ) (j y : Vector n) : NativeMatch x z j y ↔
    Compatible c (sourceResidual x z j) ∧ ∀ t, c.diagonal t ≠ 0 →
      c.backward.mulVec y t = transformedSource c (sourceResidual x z j) t / c.diagonal t := by
  rw [native_matching_iff]
  exact solution_iff c _ _

lemma native_solution_valid {n : ℕ} (c : Certificate (historyMatrix n))
    (x z : Point ℚ) (j free : Vector n) (h : Compatible c (sourceResidual x z j)) :
    NativeMatch x z j (solution c (sourceResidual x z j) free) := by
  rw [native_matching_iff]
  exact solution_valid c _ _ h

lemma native_solution_complete {n : ℕ} (c : Certificate (historyMatrix n))
    (x z : Point ℚ) (j y : Vector n) (h : NativeMatch x z j y) :
    y = solution c (sourceResidual x z j) (c.backward.mulVec y) :=
  solution_complete c y _ ((native_matching_iff x z j y).mp h)

end Artform.Scores.NonabelianGravity.HistoryElimination
