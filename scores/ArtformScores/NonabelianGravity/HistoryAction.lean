import ArtformScores.NonabelianGravity.HistoryBinding

/-! # Complete matrix quadratic action in certified coordinates -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.HistoryElimination
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {H : Matrix ι ι ℚ} (c : Certificate H)

def quadraticAction (r y : ι → ℚ) : ℚ :=
  (1 / 2) * dotProduct y (H.mulVec y) - dotProduct r y

lemma quadratic_diagonal (r w : ι → ℚ) :
    quadraticAction (H := H) r (c.forward.mulVec w) =
      (1 / 2) * ∑ i, c.diagonal i * w i ^ 2 -
        ∑ i, transformedSource c r i * w i := by
  have hq : dotProduct (c.forward.mulVec w) (H.mulVec (c.forward.mulVec w)) =
      dotProduct w ((Matrix.diagonal c.diagonal).mulVec w) := by
    calc
      _ = dotProduct (H.mulVec (c.forward.mulVec w)) (c.forward.mulVec w) :=
        dotProduct_comm _ _
      _ = dotProduct w (c.forward.transpose.mulVec (H.mulVec (c.forward.mulVec w))) :=
        (Matrix.dotProduct_transpose_mulVec c.forward w _).symm
      _ = _ := by rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, c.congruence]
  have hr : dotProduct r (c.forward.mulVec w) = dotProduct (transformedSource c r) w := by
    calc
      _ = dotProduct w (c.forward.transpose.mulVec r) :=
        (Matrix.dotProduct_transpose_mulVec c.forward w r).symm
      _ = _ := dotProduct_comm _ _
  rw [quadraticAction, hq, hr]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  ring

def sourceContact (r : ι → ℚ) : ℚ :=
  ∑ i, transformedSource c r i ^ 2 / c.diagonal i

lemma stationary_quadratic (r free : ι → ℚ) (hr : Compatible c r) :
    quadraticAction (H := H) r (solution c r free) = -(1 / 2) * sourceContact c r := by
  rw [solution, quadratic_diagonal]
  simp only [sourceContact, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : c.diagonal i = 0
  · simp [hi, hr i hi]
  · simp only [hi, ite_false]
    field_simp
    ring

end Artform.Scores.NonabelianGravity.HistoryElimination
