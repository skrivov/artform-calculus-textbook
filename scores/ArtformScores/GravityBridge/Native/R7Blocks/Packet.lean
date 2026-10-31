import ArtformScores.GravityBridge.Native.R7Blocks.PacketStatements

/-! # Bounded packet witnesses and operator-norm quantifiers -/

namespace Artform.Scores.GravityBridge.Native.R7Blocks


variable {Y Z : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

lemma bounded_unit_packet_lower_bound (A : Y →L[ℝ] Z) (φ : Z →L[ℝ] ℝ)
    (y : Y) (d : ℝ) (hy : ‖y‖ ≤ 1) (hφ : ‖φ‖ ≤ 1) (hw : d ≤ |φ (A y)|) : d ≤ ‖A‖ := by
  calc
    d ≤ |φ (A y)| := hw
    _ = ‖φ (A y)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖φ‖ * ‖A y‖ := φ.le_opNorm _
    _ ≤ 1 * (‖A‖ * 1) := by
      gcongr
      exact (A.le_opNorm y).trans (mul_le_mul_of_nonneg_left hy (norm_nonneg A))
    _ = ‖A‖ := by ring

lemma operator_packet_stability (A A₀ : Y →L[ℝ] Z) (φ : Z →L[ℝ] ℝ)
    (y : Y) (d ε : ℝ) (hy : ‖y‖ ≤ 1) (hφ : ‖φ‖ ≤ 1)
    (hw : d ≤ |φ (A₀ y)|) (hε : ‖A - A₀‖ ≤ ε) : d - ε ≤ ‖A‖ := by
  have hv : |φ ((A - A₀) y)| ≤ ε := by
    calc
      _ = ‖φ ((A - A₀) y)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖φ‖ * ‖(A - A₀) y‖ := φ.le_opNorm _
      _ ≤ 1 * (‖A - A₀‖ * 1) := by
        gcongr
        exact ((A - A₀).le_opNorm y).trans
          (mul_le_mul_of_nonneg_left hy (norm_nonneg _))
      _ ≤ ε := by simpa using hε
  have ht : |φ (A₀ y)| ≤ |φ (A y)| + |φ ((A - A₀) y)| := by
    have he : φ (A₀ y) = φ (A y) - φ ((A - A₀) y) := by simp
    rw [he]
    exact abs_sub _ _
  apply bounded_unit_packet_lower_bound A φ y (d - ε) hy hφ
  linarith

lemma unnormalized_detector_bound (A : Y →L[ℝ] Z) (φ : Z →L[ℝ] ℝ) (y : Y) :
    |φ (A y)| ≤ ‖φ‖ * ‖A‖ * ‖y‖ := by
  calc
    _ = ‖φ (A y)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖φ‖ * ‖A y‖ := φ.le_opNorm _
    _ ≤ ‖φ‖ * (‖A‖ * ‖y‖) := by gcongr; exact A.le_opNorm y
    _ = _ := by ring

/-- **GAC2:packet-operator-witness**
(bounded packet witnesses and operator-norm quantifiers). -/
@[ledger "GAC2:packet-operator-witness"]
theorem packetLaw : Statement.packetLaw := by
  intro Y Z _ _ _ _
  exact ⟨bounded_unit_packet_lower_bound,
    operator_packet_stability,
    unnormalized_detector_bound⟩

/-! ## Non-vacuity -/

example : (36 / 505 : ℝ) ≤ ‖(36 / 505 : ℝ) • ContinuousLinearMap.id ℝ ℝ‖ := by
  apply bounded_unit_packet_lower_bound
    ((36 / 505 : ℝ) • ContinuousLinearMap.id ℝ ℝ) (ContinuousLinearMap.id ℝ ℝ) 1
  all_goals norm_num

end Artform.Scores.GravityBridge.Native.R7Blocks
