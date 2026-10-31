import ArtformScores.NonabelianGravity.HistoryAction
import ArtformScores.NonabelianGravity.HistoryWick

/-! # Complex continuation of the certified quadratic polynomial -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.HistoryElimination
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {H : Matrix ι ι ℚ} (c : Certificate H)

noncomputable def complexMatrix (M : Matrix ι ι ℚ) : Matrix ι ι ℂ :=
  M.map (Rat.castHom ℂ)

lemma complex_congruence :
    (complexMatrix c.forward).transpose * complexMatrix H * complexMatrix c.forward =
      Matrix.diagonal (fun i => (c.diagonal i : ℂ)) := by
  have h := congrArg (fun M => M.map (Rat.castHom ℂ)) c.congruence
  have ht : c.forward.transpose.map (Rat.castHom ℂ) =
      (c.forward.map (Rat.castHom ℂ)).transpose := by rfl
  simp only [Matrix.map_mul,
    Matrix.diagonal_map (map_zero (Rat.castHom ℂ)), ht] at h
  convert h using 1 <;> rfl

noncomputable def complexAction (r y : ι → ℂ) : ℂ :=
  (1 / 2) * dotProduct y ((complexMatrix H).mulVec y) - dotProduct r y

lemma complex_action_diagonal (r w : ι → ℂ) :
    complexAction (H := H) r ((complexMatrix c.forward).mulVec w) =
      (1 / 2) * ∑ i, (c.diagonal i : ℂ) * w i ^ 2 -
        ∑ i, (complexMatrix c.forward).transpose.mulVec r i * w i := by
  have hq : dotProduct ((complexMatrix c.forward).mulVec w)
      ((complexMatrix H).mulVec ((complexMatrix c.forward).mulVec w)) =
      dotProduct w ((Matrix.diagonal (fun i => (c.diagonal i : ℂ))).mulVec w) := by
    calc
      _ = dotProduct ((complexMatrix H).mulVec ((complexMatrix c.forward).mulVec w))
          ((complexMatrix c.forward).mulVec w) := dotProduct_comm _ _
      _ = dotProduct w ((complexMatrix c.forward).transpose.mulVec
          ((complexMatrix H).mulVec ((complexMatrix c.forward).mulVec w))) :=
        (Matrix.dotProduct_transpose_mulVec (complexMatrix c.forward) w _).symm
      _ = _ := by rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, complex_congruence]
  have hr : dotProduct r ((complexMatrix c.forward).mulVec w) =
      dotProduct ((complexMatrix c.forward).transpose.mulVec r) w := by
    calc
      _ = dotProduct w ((complexMatrix c.forward).transpose.mulVec r) :=
        (Matrix.dotProduct_transpose_mulVec (complexMatrix c.forward) w r).symm
      _ = _ := dotProduct_comm _ _
  rw [complexAction, hq, hr]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma complex_source (r : ι → ℚ) :
    (complexMatrix c.forward).transpose.mulVec (fun i => (r i : ℂ)) =
      fun i => (transformedSource c r i : ℂ) := by
  funext i
  simp [complexMatrix, transformedSource, Matrix.mulVec, dotProduct]

end Artform.Scores.NonabelianGravity.HistoryElimination
