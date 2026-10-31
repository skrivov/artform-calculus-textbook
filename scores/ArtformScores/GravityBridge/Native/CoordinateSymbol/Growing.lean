import ArtformScores.GravityBridge.Native.CoordinateSymbol.GrowingStatements

/-! # Actual native coordinate column and its extra real root -/

namespace Artform.Scores.GravityBridge.Native.CoordinateSymbol

open Matrix

variable {K : Type*} [Field K] [CharZero K]

open Matrix
lemma paired_axis_discriminant (j z a : K) (hj : j ^ 2 = -1) :
    simpleDiscriminant (componentSquares (timeMomentum j z ![a, -a, 0]))
      (timeMomentum j z ![a, -a, 0]) = -(a ^ 2 / 2) * (z ^ 2 - 2 * a ^ 2) * (z ^ 2 + a ^ 2) := by
  have hj4 : j ^ 4 = 1 := by calc j ^ 4 = (j ^ 2) ^ 2 := by ring
                             _ = 1 := by rw [hj]; norm_num
  norm_num [simpleDiscriminant, componentSquares, timeMomentum, lorentzDot, signature,
    Fin.sum_univ_succ]
  ring_nf
  simp only [hj, hj4]
  ring

lemma paired_axis_native_column (j z a : K) (hj : j ^ 2 = -1) :
    nativeUpperSymbol (timeMomentum j z ![a, -a, 0]) *ᵥ ![0, 0, 0, 1] =
      (-(1 / 101 : K) * (9999 / 9991) * a ^ 2 * (z ^ 2 - 2 * a ^ 2) * (z ^ 2 + a ^ 2)) • ![0, 0,
        0, 1] := by
  dsimp only [nativeUpperSymbol]
  rw [paired_axis_discriminant j z a hj]
  ext i
  fin_cases i <;>
    norm_num [lorentzK, simpleFace,
      componentSquares, timeMomentum, signature, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

lemma actual_coordinate_growing_root (j z a : K) (hj : j ^ 2 = -1) (hz : z ^ 2 = 2 * a ^ 2) :
    nativeUpperSymbol (timeMomentum j z ![a, -a, 0]) *ᵥ ![0, 0, 0, 1] = 0 := by
  rw [paired_axis_native_column j z a hj, hz]
  simp

lemma positive_real_growth (a : ℝ) (ha : 0 < a) :
    0 < Real.sqrt 2 * a ∧ (Real.sqrt 2 * a) ^ 2 = 2 * a ^ 2 := by
  constructor
  · positivity
  · rw [mul_pow, Real.sq_sqrt (by norm_num)]

/-- **GAC2:native-coordinate-extra-real-root**
(actual native coordinate column and its extra real root). -/
@[ledger "GAC2:native-coordinate-extra-real-root"]
theorem growingLaw : Statement.growingLaw := by
  intro K _ _
  exact ⟨paired_axis_discriminant,
    paired_axis_native_column,
    actual_coordinate_growing_root⟩

/-! ## Non-vacuity -/
example : nativeUpperSymbol (timeMomentum Complex.I ((Real.sqrt 2 : ℝ) : ℂ) ![1, -1, 0]) *ᵥ
    (![0, 0, 0, 1] : Vec4 (K := ℂ)) = 0 := by
  apply actual_coordinate_growing_root Complex.I _ 1 Complex.I_sq
  norm_cast
  norm_num [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

end Artform.Scores.GravityBridge.Native.CoordinateSymbol
