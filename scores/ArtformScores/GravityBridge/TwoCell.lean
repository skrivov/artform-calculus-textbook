import ArtformScores.GravityBridge.TwoCellStatements

/-! # A two-cell component test retains the full native refinement gap -/

namespace Artform.Scores.GravityBridge

noncomputable section

open Native


lemma native_two_cell_square (a m b j : ℚ) :
    twoCellTorsion a m b j = twoCellEffective a b j +
      2 * kappa * (m - twoCellMiddle a b j) ^ 2 := by
  norm_num [twoCellTorsion, nativeEdgeTorsion, twoCellEffective, twoCellMiddle, kappa]
  ring

lemma native_middle_force (a m b j : ℚ) :
    2 * kappa * (m - a) - 2 * kappa * (b - m) = j ↔ m = twoCellMiddle a b j := by
  norm_num [kappa, twoCellMiddle]
  constructor <;> intro h <;> linarith

lemma native_endpoint_momenta (a b j : ℚ) :
    2 * kappa * (twoCellMiddle a b j - a) = kappa * (b - a) + j / 2 ∧
    2 * kappa * (b - twoCellMiddle a b j) = kappa * (b - a) - j / 2 := by
  norm_num [kappa, twoCellMiddle]
  constructor <;> ring

lemma native_two_cell_minimum (a m b j : ℚ) :
    twoCellEffective a b j ≤ twoCellTorsion a m b j ∧
    (twoCellTorsion a m b j = twoCellEffective a b j ↔ m = twoCellMiddle a b j) := by
  rw [native_two_cell_square]
  have hk : 0 < kappa := by norm_num [kappa]
  have hs := sq_nonneg (m - twoCellMiddle a b j)
  constructor
  · nlinarith
  · constructor
    · intro h
      have hz : (m - twoCellMiddle a b j) ^ 2 = 0 := by nlinarith
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
    · rintro rfl
      simp

/-- **GAC:two-cell-torsion** (a component source reduction with its endpoint covectors). -/
@[ledger "GAC:two-cell-torsion"]
theorem twoCellLaw : Statement.twoCellLaw := by
  exact ⟨native_two_cell_square, native_middle_force,
    native_endpoint_momenta, native_two_cell_minimum⟩

/-! ## Non-vacuity -/

example : twoCellMiddle 0 2 0 = 1 ∧ twoCellEffective 0 2 0 = 2 / 101 ∧
    nativeEdgeTorsion 0 2 = 4 / 101 ∧ twoCellEffective 0 2 0 ≠ nativeEdgeTorsion 0 2 := by
  norm_num [twoCellMiddle, twoCellEffective, nativeEdgeTorsion, kappa]

example : twoCellMiddle 0 2 (2 / 101) = 3 / 2 ∧
    2 * kappa * (twoCellMiddle 0 2 (2 / 101) - 0) = 3 / 101 ∧
    2 * kappa * (2 - twoCellMiddle 0 2 (2 / 101)) = 1 / 101 := by
  norm_num [twoCellMiddle, kappa]

end

end Artform.Scores.GravityBridge
