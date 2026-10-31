import ArtformScores.NonabelianGravity.HistoryGaussian

/-! # Exact rotated-contour scalar square completion -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.HistoryGaussian

noncomputable def wick (d : ℝ) : ℂ :=
  if 0 < d then (1 + Complex.I) / (Real.sqrt 2 : ℂ)
  else (1 - Complex.I) / (Real.sqrt 2 : ℂ)

lemma wick_square (d : ℝ) :
    wick d ^ 2 = if 0 < d then Complex.I else -Complex.I := by
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    norm_cast
    norm_num
  by_cases h : 0 < d
  · simp only [wick, h, ite_true, div_pow, hs]
    norm_num [add_sq, Complex.I_sq]
  · simp only [wick, h, ite_false, div_pow, hs]
    norm_num [sub_sq, Complex.I_sq]
    ring

lemma wick_damping (d : ℝ) (hd : d ≠ 0) :
    Complex.I * (d : ℂ) * wick d ^ 2 = -((|d| : ℝ) : ℂ) := by
  rw [wick_square]
  by_cases h : 0 < d
  · simp only [h, ite_true, abs_of_pos h]
    calc
      _ = (Complex.I * Complex.I) * (d : ℂ) := by ring
      _ = _ := by simp
  · have hn : d < 0 := lt_of_le_of_ne (le_of_not_gt h) hd
    simp only [h, ite_false, abs_of_neg hn, Complex.ofReal_neg]
    calc
      _ = -(Complex.I * Complex.I) * (d : ℂ) := by ring
      _ = _ := by simp

lemma wick_completion (d r t ℏ : ℝ) (hd : d ≠ 0) (hℏ : ℏ ≠ 0) :
    Complex.I * ((d : ℂ) / 2 * ((r : ℂ) / d + wick d * t) ^ 2 -
      (r : ℂ) * ((r : ℂ) / d + wick d * t)) / ℏ =
    -Complex.I * (r : ℂ) ^ 2 / (2 * (d : ℂ) * ℏ) -
      ((|d| / (2 * ℏ) : ℝ) : ℂ) * (t : ℂ) ^ 2 := by
  have hD : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have hH : (ℏ : ℂ) ≠ 0 := by exact_mod_cast hℏ
  have hw := wick_damping d hd
  push_cast
  field_simp
  linear_combination (d : ℂ) * (t : ℂ) ^ 2 * hw

end Artform.Scores.NonabelianGravity.HistoryGaussian
