import ArtformScores.GravityBridge.Native.CoordinateSymbol.CompanionStatements

/-! # Actual coordinate quartic bound to the complete companion -/

namespace Artform.Scores.GravityBridge.Native.CoordinateSymbol

open Matrix
open SlowCompanion

variable {K : Type*} [Field K] [CharZero K]

open Matrix SlowCompanion
lemma native_end_polynomial (j z : K) (k : Fin 3 → K) (hj : j ^ 2 = -1) :
    coordinatePolynomial (nativeEndCoefficients j k) z =
      Matrix.toLin' (nativeUpperSymbol (timeMomentum j z k)) := by
  rw [complete_native_quartic j z k hj]
  ext v i
  simp [coordinatePolynomial, nativeEndCoefficients, matrixPolynomial, Matrix.toLin'_apply]

lemma actual_companion_inverse (j z : K) (k : Fin 3 → K) (b : Fin 4 → Vec4 (K := K))
    (hj : j ^ 2 = -1) (hR : spatialRadius k ≠ 0)
    (hd : simpleDiscriminant (componentSquares (timeMomentum j z k)) (timeMomentum j z k) ≠ 0) :
    z • nativeCompanionInverse j z k b-
      coordinateStep (nativeEndCoefficients j k) (Matrix.toLin' (leadingCoordinateInverse k))
        (nativeCompanionInverse j z k b) = b := by
  apply companion_resolvent_solves
  · change Matrix.toLin' (leadingCoordinateInverse k) *
      Matrix.toLin' (nativeUpperCoefficients j k 4) = 1
    rw [native_quartic_leading]
    apply LinearMap.ext
    intro v
    change (leadingCoordinateInverse k) *ᵥ ((leadingCoordinate k) *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, (native_leading_two_sided k hR).2, Matrix.one_mulVec]
  · rw [native_end_polynomial j z k hj]
    apply LinearMap.ext
    intro v
    change (nativeUpperSymbol (timeMomentum j z k)) *ᵥ ((nativeCoordinateInverse (timeMomentum j
      z k)) *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, (native_coordinate_both_inverse (timeMomentum j z k) hd).1,
      Matrix.one_mulVec]

lemma actual_companion_unique (j z : K) (k : Fin 3 → K)
    (x b : Fin 4 → Vec4 (K := K)) (hj : j ^ 2 = -1) (hR : spatialRadius k ≠ 0)
    (hd : simpleDiscriminant (componentSquares (timeMomentum j z k)) (timeMomentum j z k) ≠ 0)
    (hx : z • x - coordinateStep (nativeEndCoefficients j k)
      (Matrix.toLin' (leadingCoordinateInverse k)) x = b) :
    x = nativeCompanionInverse j z k b := by
  apply companion_resolvent_unique (nativeEndCoefficients j k)
    (Matrix.toLin' (leadingCoordinateInverse k))
    (Matrix.toLin' (nativeCoordinateInverse (timeMomentum j z k))) z x b _ _ _ hx
  · change Matrix.toLin' (leadingCoordinateInverse k) *
      Matrix.toLin' (nativeUpperCoefficients j k 4) = 1
    rw [native_quartic_leading]
    apply LinearMap.ext
    intro v
    change (leadingCoordinateInverse k) *ᵥ ((leadingCoordinate k) *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, (native_leading_two_sided k hR).2, Matrix.one_mulVec]
  · change Matrix.toLin' (nativeUpperCoefficients j k 4) *
      Matrix.toLin' (leadingCoordinateInverse k) = 1
    rw [native_quartic_leading]
    apply LinearMap.ext
    intro v
    change (leadingCoordinate k) *ᵥ ((leadingCoordinateInverse k) *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, (native_leading_two_sided k hR).1, Matrix.one_mulVec]
  · rw [native_end_polynomial j z k hj]
    apply LinearMap.ext
    intro v
    change (nativeCoordinateInverse (timeMomentum j z k)) *ᵥ ((nativeUpperSymbol (timeMomentum j
      z k)) *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, (native_coordinate_both_inverse (timeMomentum j z k) hd).2,
      Matrix.one_mulVec]

/-- **GAC2:native-quartic-companion-binding**
(actual coordinate quartic bound to the complete companion). -/
@[ledger "GAC2:native-quartic-companion-binding"]
theorem companionLaw : Statement.companionLaw := by
  intro K _ _
  exact ⟨native_end_polynomial,
    actual_companion_inverse,
    actual_companion_unique⟩

/-! ## Non-vacuity -/
example : (0 : ℂ) • nativeCompanionInverse Complex.I 0 ![1, 2, 3] 0-
    coordinateStep (nativeEndCoefficients Complex.I ![1, 2, 3])
      (Matrix.toLin' (leadingCoordinateInverse ![1, 2, 3]))
      (nativeCompanionInverse Complex.I 0 ![1, 2, 3] 0) = 0 := by
  apply actual_companion_inverse Complex.I 0 ![1, 2, 3] 0 Complex.I_sq
  · norm_num [spatialRadius]
  · norm_num [simpleDiscriminant, componentSquares, timeMomentum, lorentzDot, signature,
      Fin.sum_univ_succ]

end Artform.Scores.GravityBridge.Native.CoordinateSymbol
