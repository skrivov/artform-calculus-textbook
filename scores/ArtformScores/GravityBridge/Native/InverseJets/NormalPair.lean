import ArtformScores.GravityBridge.Native.InverseJets.NormalPairStatements

/-! # Original normal pair and independent cubic incoming test contacts -/

namespace Artform.Scores.GravityBridge.Native.InverseJets

open Matrix



open Matrix

lemma physical_H1_normal_row (l p q ni nj mij : ℚ) :
    (firstH l p q *ᵥ metricPairZ1 l p q ni nj mij) 2 =
      -(1 / 101 * signedG * signedA : ℚ) * (l - p) * (l - q) * (p * nj - q * ni) / 2 := by
  rw [first_inverse_table]
  norm_num [metricPairZ1, metricGamma0, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    signedG, signedA]
  ring

lemma original_cubic_normal_test (l p q : ℚ) :
    metricPairZ3 l p q p q 0 =
      ![p * q * (p ^ 2 - q ^ 2) * (l - p) / 24, -p * q * (p ^ 2 - q ^ 2) * (l - q) / 24, p ^ 2 *
        q ^ 2 * (p - q) / 24] := by
  ext i
  fin_cases i <;> norm_num [metricPairZ3, metricGamma2, metricGamma0] <;> ring


lemma coordinate_Z1_polynomial (l p q c0 ci cj : ℚ) :
    metricPairZ1 l p q (l * ci + p * c0) (l * cj + q * c0) (p * cj + q * ci) =
      l ^ 2 • ((1 / 2 : ℚ) • ![p * cj, q * ci, 0]) +
      l • ((1 / 2 : ℚ) • ![-p ^ 2 * cj, -q ^ 2 * ci, 0]) +
      (1 / 2 : ℚ) • ![0, 0, -(p - q) * p * q * c0] := by
  ext i
  fin_cases i <;> norm_num [metricPairZ1, metricGamma0] <;> ring

lemma coordinate_Z3_polynomial (l p q c0 ci cj : ℚ) :
    metricPairZ3 l p q (l * ci + p * c0) (l * cj + q * c0) (p * cj + q * ci) =
      l ^ 4 • ((1 / 24 : ℚ) • ![q * ci, p * cj, 0]) +
      l ^ 3 • ((1 / 24 : ℚ) •
        ![-p * (p * cj + q * ci), -q * (q * ci + p * cj), (p - q) * (p * cj + q * ci)]) +
      l ^ 2 • ((1 / 24 : ℚ) • ![p ^ 3 * cj - q ^ 3 * ci, q ^ 3 * ci - p ^ 3 * cj, 0]) +
      l • ((1 / 24 : ℚ) • ![p * q ^ 3 * ci + (p ^ 3 * q - q ^ 3 * p) * c0,
        q * p ^ 3 * cj + (q ^ 3 * p - p ^ 3 * q) * c0, -(p - q) * (p ^ 3 * cj + q ^ 3 * ci)]) +
      (1 / 24 : ℚ) • ![-p * (p ^ 3 * q - q ^ 3 * p) * c0, -q * (q ^ 3 * p - p ^ 3 * q) * c0,
        p ^ 2 * q ^ 2 * (p - q) * c0] := by
  ext i
  fin_cases i <;> norm_num [metricPairZ3, metricGamma2, metricGamma0] <;> ring

lemma coordinate_Z1_highest (p q c0 ci cj : ℚ) :
    highest2 (fun l => metricPairZ1 l p q (l * ci + p * c0) (l * cj + q * c0) (p * cj + q * ci)) =
      (1 / 2 : ℚ) • ![p * cj, q * ci, 0] := by
  ext i
  fin_cases i <;> norm_num [highest2, metricPairZ1, metricGamma0] <;> ring

lemma coordinate_Z3_highest (p q c0 ci cj : ℚ) :
    highest4 (fun l => metricPairZ3 l p q (l * ci + p * c0) (l * cj + q * c0) (p * cj + q * ci)) =
      (1 / 24 : ℚ) • ![q * ci, p * cj, 0] := by
  ext i
  fin_cases i <;> norm_num [highest4, metricPairZ3, metricGamma2, metricGamma0] <;> ring

lemma quartic_coordinate_pair_contact (p q ci cj : ℚ) :
    (secondH 1 0 0 *ᵥ ((1 / 2 : ℚ) • ![p * cj, q * ci, 0])) 2 +
      (signedH0 *ᵥ ((1 / 24 : ℚ) • ![q * ci, p * cj, 0])) 2 =
      ((1 / 101 : ℚ) * signedA ^ 2 / 12) * (q * ci - p * cj) := by
  have he : (1 / 2 : ℚ) • ![p * cj, q * ci, 0] = ![p * cj / 2, q * ci / 2, 0] := by
    ext i; fin_cases i <;> norm_num <;> ring
  rw [he, second_temporal_contact]
  norm_num [signedH0, signedE, signedW, signedA, signedG, rankOne,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.one_apply]
  ring

-- Reflect all differential variables for the true bilinear incoming transpose.
lemma reflected_cubic_test (l p q : ℚ) :
    metricPairZ3 (-l) (-p) (-q) (-p) (-q) 0 =
      l • ![-p * q * (p ^ 2 - q ^ 2) / 24, p * q * (p ^ 2 - q ^ 2) / 24, 0] +
      ![p ^ 2 * q * (p ^ 2 - q ^ 2) / 24, -p * q ^ 2 * (p ^ 2 - q ^ 2) / 24, -p ^ 2 * q ^ 2 * (p
        - q) / 24] := by
  rw [original_cubic_normal_test]
  ext i
  fin_cases i <;> norm_num <;> ring

lemma independent_cubic_test_cancels (p q : ℚ) (value derivative : Fin 3 → ℚ)
    (hv : value = 0) (hs : derivative 0 = derivative 1) :
    incomingCubicTest p q value derivative = 0 := by
  rw [hv]
  simp only [incomingCubicTest, Pi.zero_apply]
  rw [hs]
  ring

lemma symmetric_electric_return (a : ℚ) :
    (signedH0 *ᵥ ![a, a, 0]) 0 = (signedH0 *ᵥ ![a, a, 0]) 1 := by
  norm_num [signedH0, signedA, signedE, signedW, rankOne, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, Matrix.one_apply]
  ring

/-- **GAC2:normal-pair-incoming-contacts**
(original normal pair and independent cubic incoming test contacts). -/
@[ledger "GAC2:normal-pair-incoming-contacts"]
theorem normalPairLaw : Statement.normalPairLaw := by
  exact ⟨physical_H1_normal_row,
    original_cubic_normal_test,
    coordinate_Z1_polynomial,
    coordinate_Z3_polynomial,
    coordinate_Z1_highest,
    coordinate_Z3_highest,
    quartic_coordinate_pair_contact,
    reflected_cubic_test,
    independent_cubic_test_cancels,
    symmetric_electric_return⟩

/-! ## Non-vacuity -/

example : incomingCubicTest 2 3 0 (signedH0 *ᵥ ![1, 1, 0]) = 0 ∧
    ((1 / 101 : ℚ) * signedA ^ 2 / 12) * (3 * 1 - 2 * 2) ≠ 0 := by
  refine ⟨independent_cubic_test_cancels 2 3 _ _ rfl (symmetric_electric_return 1), ?_⟩
  norm_num [signedA]

end Artform.Scores.GravityBridge.Native.InverseJets
