import ArtformScores.GravityBridge.BoundaryAnchoringStatements
/-! # A component source requires a boundary prescription -/
namespace Artform.Scores.GravityBridge
noncomputable section
open Native
lemma free_boundary_source_iff (a b j : ℚ) :
    freeTwoCellBoundary a b j ↔ a = b ∧ j = 0 := by
  unfold freeTwoCellBoundary
  norm_num [kappa]
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> linarith
  · rintro ⟨rfl, rfl⟩
    norm_num
lemma anchored_complete_square (rho a b j : ℚ) (hr : rho ≠ 0) :
    anchoredTwoCellAction rho a b j = anchoredTwoCellMinimum rho j +
      rho * ((a + b) / 2 - j / (2 * rho)) ^ 2 +
      (kappa / 2 + rho / 4) * (b - a) ^ 2 := by
  dsimp [anchoredTwoCellAction, anchoredTwoCellMinimum, twoCellEffective, kappa]
  field_simp
  ring
lemma anchored_unique_minimum (rho a b j : ℚ) (hr : 0 < rho) :
    anchoredTwoCellMinimum rho j ≤ anchoredTwoCellAction rho a b j ∧
    (anchoredTwoCellAction rho a b j = anchoredTwoCellMinimum rho j ↔
      a = j / (2 * rho) ∧ b = j / (2 * rho)) := by
  rw [anchored_complete_square rho a b j (ne_of_gt hr)]
  have hp : 0 < kappa / 2 + rho / 4 := by norm_num [kappa]; linarith
  have h0 := sq_nonneg ((a + b) / 2 - j / (2 * rho))
  have h1 := sq_nonneg (b - a)
  have ht0 := mul_nonneg hr.le h0
  have ht1 := mul_nonneg hp.le h1
  constructor
  · linarith
  · constructor
    · intro he
      have ha : ((a + b) / 2 - j / (2 * rho)) ^ 2 = 0 := by nlinarith
      have hb : (b - a) ^ 2 = 0 := by nlinarith
      have hsum : (a + b) / 2 - j / (2 * rho) = 0 := sq_eq_zero_iff.mp ha
      have hdiff : b - a = 0 := sq_eq_zero_iff.mp hb
      constructor <;> linarith
    · rintro ⟨rfl, rfl⟩
      ring
/-- **GAC:boundary-anchoring** (a component source requires a boundary prescription). -/
@[ledger "GAC:boundary-anchoring"]
theorem boundaryAnchoringLaw : Statement.boundaryAnchoringLaw := by
  exact ⟨free_boundary_source_iff, anchored_complete_square, anchored_unique_minimum⟩
/-! ## Non-vacuity -/
example : ¬ freeTwoCellBoundary 0 2 (2 / 101) ∧
    anchoredTwoCellAction 1 (1 / 101) (1 / 101) (2 / 101) =
      anchoredTwoCellMinimum 1 (2 / 101) := by
  constructor
  · rw [free_boundary_source_iff]
    norm_num
  · exact (anchored_unique_minimum 1 _ _ _ (by norm_num)).2.mpr ⟨by norm_num, by norm_num⟩
end
end Artform.Scores.GravityBridge
