import ArtformScores.GravityBridge.Native.CoordinateSymbol.AxisStatements

/-! # Axis branches retain the complete mixed numerator -/

namespace Artform.Scores.GravityBridge.Native.CoordinateSymbol

open Matrix

variable {K : Type*} [Field K] [CharZero K]

open Matrix
omit [CharZero K] in
lemma aligned_axis_face_zero (a : K) :
    simpleFace (componentSquares (![a, a, 0, 0] : Vec4 (K := K))) ![a, a, 0, 0] = 0 := by
  ext i l
  fin_cases i <;> fin_cases l <;> norm_num [simpleFace, componentSquares]

lemma aligned_axis_native_zero (a : K) :
    nativeUpperSymbol (![a, a, 0, 0] : Vec4 (K := K)) = 0 := by
  have hf := aligned_axis_face_zero a
  ext i l
  fin_cases i <;> fin_cases l <;>
    norm_num [nativeUpperSymbol, simpleDiscriminant, lorentzDot, lorentzK,
      signature, componentSquares, simpleFace, Fin.sum_univ_succ]

omit [CharZero K] in
lemma aligned_axis_complete_source_zero (j a : K) (Q : Fin 4 → Fin 4 → Fin 4 → K) :
    mixedFaceSource j ![a, a, 0, 0] Q = 0 := by
  ext i
  simp [mixedFaceSource, aligned_axis_face_zero]

lemma opposite_axis_discriminant (a : K) :
    simpleDiscriminant (componentSquares (![-a, a, 0, 0] : Vec4 (K := K))) ![-a, a, 0, 0] = -a ^
      6 := by
  norm_num [simpleDiscriminant, lorentzDot, signature, componentSquares, Fin.sum_univ_succ]
  ring

lemma opposite_axis_inverse (a : K) (ha : a ≠ 0) :
    nativeUpperSymbol (![-a, a, 0, 0] : Vec4 (K := K)) * nativeCoordinateInverse ![-a, a, 0, 0]
      = 1 ∧
    nativeCoordinateInverse (![-a, a, 0, 0] : Vec4 (K := K)) * nativeUpperSymbol ![-a, a, 0, 0]
      = 1 := by
  apply native_coordinate_both_inverse
  rw [opposite_axis_discriminant]
  exact neg_ne_zero.mpr (pow_ne_zero _ ha)

/-- **GAC2:native-axis-complete-source-numerator**
(axis branches retain the complete mixed numerator). -/
@[ledger "GAC2:native-axis-complete-source-numerator"]
theorem axisLaw : Statement.axisLaw := by
  intro K _ _
  exact ⟨aligned_axis_face_zero,
    aligned_axis_native_zero,
    aligned_axis_complete_source_zero,
    opposite_axis_discriminant,
    opposite_axis_inverse⟩

/-! ## Non-vacuity -/
example : nativeUpperSymbol (![-1, 1, 0, 0] : Vec4 (K := ℚ)) *
    nativeCoordinateInverse ![-1, 1, 0, 0] = 1 := (opposite_axis_inverse 1 (by norm_num)).1

end Artform.Scores.GravityBridge.Native.CoordinateSymbol
