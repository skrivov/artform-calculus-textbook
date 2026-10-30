import ArtformScores

/-!
# Witnesses for the independent scores review of 30 October 2026

These checks document source/translation boundaries; they do not replace any
ledger statement or proof. Run with `lake env lean scores/review/JudgeChecks.lean`.
-/

namespace Artform.Scores.Judge

open Matrix (SpecialLinearGroup)

/-- R4 as a score in the ledger's time order has the opposite diagonal to
`balanced u`, which is defined as a product of laws. -/
example :
    let u : ℚˣ := ⟨2, 1 / 2, by norm_num, by norm_num⟩
    (realize (whitehead u ++ (whitehead (1 : ℚˣ)).reverse) :
      Matrix (Fin 2) (Fin 2) ℚ) = !![1 / 2, 0; 0, 2] := by
  dsimp
  rw [realize_append, timeReversal ℚ, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, whitehead_mat, whitehead_mat]
  norm_num [Matrix.adjugate_fin_two_of, Matrix.mul_fin_two]

/-- The ordinary word commutator has the negative sign under the time-order
realizer; the positive matrix commutator is a different ordering of steps. -/
example :
    realizeC [(⟨0, 1, 1⟩ : ChanStep 3 ℚ), ⟨1, 2, 1⟩, ⟨0, 1, -1⟩, ⟨1, 2, -1⟩] ≠
      (⟨0, 2, 1⟩ : ChanStep 3 ℚ).mat := by
  have h := (steinbergRules' ℚ 3 0 1 2 0 1 1).2.2.2 (by decide) (by decide) (by decide)
  rw [h.2.2]
  intro e
  have := congrFun (congrFun e 0) 2
  norm_num [ChanStep.mat, Matrix.transvection] at this

/-- Cancellation at a degenerate step does not characterize a fair caller.
An iff must quantify over all pulls or assume a nonzero cut coefficient. -/
example :
    cut ((1 / 4 : ℚ) • (splitTick true (0 : ℚ) 1 0 : Matrix (Fin 2) (Fin 2) ℚ) +
      (1 - 1 / 4 : ℚ) • (splitTick false (0 : ℚ) 1 0 : Matrix (Fin 2) (Fin 2) ℚ)) = 0 ∧
      (1 / 4 : ℚ) ≠ 1 / 2 := by
  rw [(callerCut ℚ 0 1 0 (1 / 4)).2.2.2]
  norm_num

/-- An arbitrary score need not have a glued face form: the empty score
has the identity at the zero mode, even with nonzero kick strength. -/
example : Matrix.SpecialLinearGroup.map (atZero ℚ)
    (realize (([] : Score ℚ).map (faceStep 1 1))) = 1 := by
  simp

end Artform.Scores.Judge
