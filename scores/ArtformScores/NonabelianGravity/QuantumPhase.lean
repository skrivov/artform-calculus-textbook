import ArtformScores.NonabelianGravity.QuantumVolume
import ArtformScores.NonabelianGravity.QuantumSliceData

/-! # Both native Schur charts carry the same signature phase -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.QuantumComposition
open HistoryElimination HistoryGaussian

lemma phase_of_counts {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℚ} (c : Certificate H)
    (hp : ((Finset.univ : Finset (Active c)).filter
      (fun i : Active c => 0 < c.diagonal i.val)).card = 37)
    (hm : ((Finset.univ : Finset (Active c)).filter
      (fun i : Active c => ¬0 < c.diagonal i.val)).card = 29) :
    rotationPhase c = 1 := by
  have hw (q : ℚ) : HistoryGaussian.wick (q : ℝ) =
      if 0 < q then (1 + Complex.I) / (Real.sqrt 2 : ℂ)
      else (1 - Complex.I) / (Real.sqrt 2 : ℂ) := by
    simp only [HistoryGaussian.wick, Rat.cast_pos]
  simp only [rotationPhase, activeDiagonal, hw]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  rw [hp, hm]
  let p : ℂ := (1 + Complex.I) / (Real.sqrt 2 : ℂ)
  let m : ℂ := (1 - Complex.I) / (Real.sqrt 2 : ℂ)
  change p ^ 37 * m ^ 29 = 1
  have h₂ : p ^ 2 = Complex.I := by
    simpa [HistoryGaussian.wick, p] using HistoryGaussian.wick_square (1 : ℝ)
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by norm_cast; norm_num
  have hpm : p * m = 1 := by
    calc
      _ = ((1 + Complex.I) * (1 - Complex.I)) / 2 := by
        dsimp [p, m]
        rw [div_mul_div_comm, ← pow_two, hs]
      _ = _ := by ring_nf; norm_num
  calc
    _ = (p ^ 2) ^ 4 * (p * m) ^ 29 := by ring
    _ = _ := by rw [h₂, hpm]; norm_num

end Artform.Scores.NonabelianGravity.QuantumComposition
