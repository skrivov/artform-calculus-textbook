import ArtformScores.GravityBridge.RefinementStatements
import ArtformScores.GravityBridge.ChangingGeometry
import ArtformScores.Rules

/-! # Exact detail elimination differs from reversible refinement -/

namespace Artform.Scores.GravityBridge

noncomputable section

lemma refined_complete_square (h0 h1 c d j : ℚ) (h0n : h0 ≠ 0) (h1n : h1 ≠ 0)
    (hH : h0 + h1 ≠ 0) :
    refinedAction h0 h1 c d j = reducedAction h0 h1 c j +
      (h0 + h1) / (2 * h0 * h1) * (d - stationaryDetail h0 h1 j) ^ 2 := by
  dsimp [refinedAction, reducedAction, stationaryDetail]
  field_simp
  ring

lemma refined_minimum (h0 h1 c d j : ℚ) (h0p : 0 < h0) (h1p : 0 < h1) :
    reducedAction h0 h1 c j ≤ refinedAction h0 h1 c d j ∧
    (refinedAction h0 h1 c d j = reducedAction h0 h1 c j ↔
      d = stationaryDetail h0 h1 j) := by
  have hH : h0 + h1 ≠ 0 := ne_of_gt (add_pos h0p h1p)
  rw [refined_complete_square h0 h1 c d j (ne_of_gt h0p) (ne_of_gt h1p) hH]
  have hc : 0 < (h0 + h1) / (2 * h0 * h1) := by positivity
  have hs : 0 ≤ (d - stationaryDetail h0 h1 j) ^ 2 := sq_nonneg _
  constructor
  · nlinarith
  · constructor
    · intro he
      have hz : (d - stationaryDetail h0 h1 j) ^ 2 = 0 := by nlinarith
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
    · intro he
      rw [he]
      simp

lemma detail_intertwines (e : Fin 2 → ℚ) :
    edgeDetailEquiv (unequalFineStep e) = coarseDetailStep (edgeDetailEquiv e) := by
  ext <;> simp [edgeDetailEquiv, unequalFineStep, coarseDetailStep] <;> ring

lemma coarse_two_step (x : ℚ × ℚ) :
    (coarseDetailStep (coarseDetailStep x)).1 = (5 / 2 : ℚ) * (coarseDetailStep x).1 - x.1 := by
  dsimp [coarseDetailStep]
  ring

lemma no_closed_aggregate :
    ¬ ∃ U : ℚ → ℚ, ∀ c d, (coarseDetailStep (c, d)).1 = U c := by
  rintro ⟨U, h⟩
  have h0 := h 0 0
  have h1 := h 0 1
  norm_num [coarseDetailStep] at h0 h1
  linarith

/-- **GAC:refinement-elimination** (detail elimination keeps its source contact and memory). -/
@[ledger "GAC:refinement-elimination"]
theorem refinementLaw : Statement.refinementLaw := by
  exact ⟨refined_complete_square, refined_minimum, detail_intertwines,
    coarse_two_step, no_closed_aggregate⟩

/-! ## Non-vacuity -/

example : refinedAction 1 1 2 0 2 = 1 ∧ refinedAction 1 1 2 1 2 = 0 ∧
    reducedAction 1 1 2 2 = 0 := by norm_num [refinedAction, reducedAction]

example (e : Fin 2 → ℚ) :
    let u : ℚˣ := ⟨2, 1 / 2, by norm_num, by norm_num⟩
    Matrix.mulVec (realize (balancedScore u) : Matrix (Fin 2) (Fin 2) ℚ) e =
      unequalFineStep e := by
  dsimp only
  rw [(balancedRule ℚ (⟨2, 1 / 2, by norm_num, by norm_num⟩ : ℚˣ) 1).2.2, balanced_mat]
  ext i
  fin_cases i <;> norm_num [unequalFineStep, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  all_goals ring

example : edgeDetailEquiv (unequalFineStep ![1, 0]) = (2, 2) := by
  norm_num [edgeDetailEquiv, unequalFineStep]

example : (coarseDetailStep (1, 0)).1 = 5 / 4 ∧
    (coarseDetailStep (coarseDetailStep (1, 0))).1 = 17 / 8 ∧
    ((5 / 4 : ℚ) ^ 2) ≠ 17 / 8 := by norm_num [coarseDetailStep]

end

end Artform.Scores.GravityBridge
