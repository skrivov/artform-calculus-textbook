import ArtformScores.GravityBridge.Native.CoordinateSymbol.LeadingStatements

/-! # Complete native quartic and its leading inverse -/

namespace Artform.Scores.GravityBridge.Native.CoordinateSymbol

open Matrix

variable {K : Type*} [Field K] [CharZero K]

open Matrix
set_option maxHeartbeats 4000000 in
-- The native quartic coefficient is checked in every original coordinate.
lemma native_quartic_leading (j : K) (k : Fin 3 → K) :
    nativeUpperCoefficients j k 4 = leadingCoordinate k := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [nativeUpperCoefficients, leadingCoordinate, schurFacePair, faceDot, faceCross,
      faceQuadratic, etaMatrix, signature, spatialRadius, Fin.sum_univ_succ] <;> ring

set_option maxHeartbeats 4000000 in
-- The nonzero spatial radius is retained before clearing denominators.
lemma native_leading_two_sided (k : Fin 3 → K) (hR : spatialRadius k ≠ 0) :
    leadingCoordinate k * leadingCoordinateInverse k = 1 ∧
    leadingCoordinateInverse k * leadingCoordinate k = 1 := by
  have hr : k 0 ^ 2 + k 1 ^ 2 + k 2 ^ 2 ≠ 0 := hR
  constructor <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [leadingCoordinate, leadingCoordinateInverse, spatialRadius,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> field_simp [hr] <;> first | assumption | ring

lemma complete_native_leading_binding (j z : K) (k : Fin 3 → K) (hj : j ^ 2 = -1) :
    nativeUpperSymbol (timeMomentum j z k) = matrixPolynomial (nativeUpperCoefficients j k) z ∧
    nativeUpperCoefficients j k 4 = leadingCoordinate k :=
  ⟨complete_native_quartic j z k hj, native_quartic_leading j k⟩

/-- **GAC2:native-quartic-leading-inverse**
(complete native quartic and its leading inverse). -/
@[ledger "GAC2:native-quartic-leading-inverse"]
theorem leadingLaw : Statement.leadingLaw := by
  intro K _ _
  exact ⟨complete_native_leading_binding,
    native_leading_two_sided⟩

/-! ## Non-vacuity -/
example : leadingCoordinate (![1, 2, 3] : Fin 3 → ℚ) * leadingCoordinateInverse ![1, 2, 3] = 1 := by
  exact (native_leading_two_sided ![1, 2, 3] (by norm_num [spatialRadius])).1

end Artform.Scores.GravityBridge.Native.CoordinateSymbol
