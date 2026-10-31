import ArtformScores.GravityBridge.Native.GreenComposition.SourceBoundaryStatements

/-! # Full source and endpoint covector of the solved two-cell contribution -/

namespace Artform.Scores.GravityBridge.Native.GreenComposition

open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K]

lemma source_complete_square (c a m b j : K) (hc : c ≠ 0) :
    sourceAction c a m b j = sourceEffective c a b j + 2 * c * (m - sourceMiddle c a b j) ^ 2 := by
  unfold sourceAction sourceEffective sourceMiddle
  field_simp [hc]
  ring

lemma source_middle_and_jump (c a m b j : K) (hc : c ≠ 0) :
    2 * c * (m - a) - 2 * c * (b - m) = j ↔ m = sourceMiddle c a b j := by
  unfold sourceMiddle
  constructor
  · intro he
    have hr : (a + b) / 2 + j / (4 * c) = (2 * c * (a + b) + j) / (4 * c) := by
      field_simp [hc]
      ring
    rw [hr, eq_div_iff (mul_ne_zero (by norm_num : (4 : K) ≠ 0) hc)]
    linear_combination he
  · intro he
    rw [he]
    field_simp [hc]
    ring

lemma complete_boundary_source_variation (c a b j da db dj e : K) (hc : c ≠ 0) :
    sourceEffective c (a + e * da) (b + e * db) (j + e * dj) = sourceEffective c a b j +
      e * (-inputMomentum c a b j * da + outputMomentum c a b j * db - sourceMiddle c a b j * dj) +
      e ^ 2 * (c / 2 * (db - da) ^ 2 - dj * (da + db) / 2 - dj ^ 2 / (8 * c)) := by
  unfold sourceEffective inputMomentum outputMomentum sourceMiddle
  field_simp [hc]
  ring

lemma original_two_cell_identification (a m b j : ℚ) :
    sourceAction (1 / 101) a m b j = twoCellTorsion a m b j ∧
    sourceMiddle (1 / 101) a b j = twoCellMiddle a b j ∧
    sourceEffective (1 / 101) a b j = twoCellEffective a b j := by
  norm_num [sourceAction, sourceMiddle, sourceEffective, twoCellTorsion, twoCellMiddle,
    twoCellEffective, nativeEdgeTorsion, kappa]

lemma nonzero_source_heldout :
    sourceMiddle (1 / 101 : ℚ) (-1) 3 (4 / 101) = 2 ∧
    inputMomentum (1 / 101 : ℚ) (-1) 3 (4 / 101) = 6 / 101 ∧
    outputMomentum (1 / 101 : ℚ) (-1) 3 (4 / 101) = 2 / 101 ∧
    sourceEffective (1 / 101 : ℚ) (-1) 3 (4 / 101) = 2 / 101 := by
  norm_num [sourceMiddle, inputMomentum, outputMomentum, sourceEffective]

/-- **GAC2:two-cell-complete-source-covector**
(full source and endpoint covector of the solved two-cell contribution). -/
@[ledger "GAC2:two-cell-complete-source-covector"]
theorem sourceBoundaryLaw : Statement.sourceBoundaryLaw := by
  intro K _ _
  exact ⟨source_complete_square,
    source_middle_and_jump,
    complete_boundary_source_variation,
    original_two_cell_identification,
    nonzero_source_heldout⟩

/-! ## Non-vacuity -/
example : sourceMiddle (1 / 101 : ℚ) 0 2 (2 / 101) = 3 / 2 ∧
    inputMomentum (1 / 101 : ℚ) 0 2 (2 / 101) = 3 / 101 ∧
    outputMomentum (1 / 101 : ℚ) 0 2 (2 / 101) = 1 / 101 := by
  norm_num [sourceMiddle, inputMomentum, outputMomentum]

end Artform.Scores.GravityBridge.Native.GreenComposition
