import ArtformScores.GravityBridge.Native.TTCross.SourceStatements

/-! # Actual24-connection constitutive return and leading TT cross source -/

namespace Artform.Scores.GravityBridge.Native.TTCross

open Matrix CoordinateSymbol Full40

variable {K : Type*} [Field K] [CharZero K]

open Matrix Full40
omit [CharZero K] in
lemma dot_distinct_input (A : Connection K) (s : Fin 4) (z : Fin 3 → K) :
    dotConnection A (gDistinctInput s z) = dotProduct (gDistinct A s) z := by
  fin_cases s <;>
    norm_num [dotConnection, gDistinctInput, gDistinct, gOriented,
      Retrospective.distinctIndices, wedge, basisVector, dotProduct, Fin.sum_univ_succ]

omit [CharZero K] in
lemma dot_repeated_input (A : Connection K) (b : Fin 4) (z : Fin 3 → K) :
    dotConnection A (gRepeatedInput b z) = dotProduct (gRepeated A b) z := by
  fin_cases b <;>
    norm_num [dotConnection, gRepeatedInput, gRepeated, gOriented, Fin.succAbove, Fin.lt_def,
      wedge, basisVector, dotProduct, Fin.sum_univ_succ]

omit [CharZero K] in
lemma dot_connection_sum (A : Connection K) (x : Fin 4 → Connection K) :
    dotConnection A (∑ i, x i) = ∑ i, dotConnection A (x i) := by
  simp only [dotConnection, Finset.sum_apply, Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext mu
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]

omit [CharZero K] in
lemma actual_coordinate_dot_partition (A : Connection K) (d e : Fin 4 → Fin 3 → K) :
    dotConnection A (gAssemble d e) =
      (∑ s, dotProduct (gDistinct A s) (d s)) + (∑ b, dotProduct (gRepeated A b) (e b)) := by
  have hadd (x y : Connection K) :
      dotConnection A (x + y) = dotConnection A x + dotConnection A y := by
    simp [dotConnection, mul_add, Finset.sum_add_distrib]
  simp only [gAssemble, hadd, dot_connection_sum, dot_distinct_input, dot_repeated_input]

omit [CharZero K] in
lemma gDistinct_add (A B : Connection K) : gDistinct (A + B) = gDistinct A + gDistinct B := by
  ext s a
  simp [gDistinct, gOriented, mul_add, Finset.sum_add_distrib]

omit [CharZero K] in
lemma gRepeated_add (A B : Connection K) : gRepeated (A + B) = gRepeated A + gRepeated B := by
  ext b a
  simp [gRepeated, gOriented, mul_add, Finset.sum_add_distrib]

lemma rational_original_distinct (A : Connection ℚ) : Retrospective.distinctCoordinates A =
  gDistinct A := rfl
lemma rational_original_repeated (A : Connection ℚ) : Retrospective.repeatedCoordinates A =
  gRepeated A := rfl

lemma distinct_original_polarization (s : Fin 4) (x y : Fin 3 → ℚ) :
    Retrospective.distinctDensity s (1 / 101) (x + y) - Retrospective.distinctDensity s (1 / 101) x-
      Retrospective.distinctDensity s (1 / 101) y = dotProduct y (distinctB s *ᵥ x) := by
  fin_cases s <;>
    norm_num [Retrospective.distinctDensity, Retrospective.distinctIndices, eta, distinctB,
      spaceB, signS, timeB, Matrix.mulVec, Matrix.mul_apply, Matrix.vecMul, Matrix.transpose_apply,
      dotProduct, Fin.sum_univ_succ] <;> ring

lemma repeated_original_polarization (b : Fin 4) (x y : Fin 3 → ℚ) :
    Retrospective.repeatedDensity b (1 / 101) (x + y) - Retrospective.repeatedDensity b (1 / 101) x-
      Retrospective.repeatedDensity b (1 / 101) y = dotProduct y (repeatB b *ᵥ x) := by
  fin_cases b <;> norm_num [Retrospective.repeatedDensity, repeatB, eta, Matrix.mulVec,
    dotProduct, Fin.sum_univ_succ] <;> ring

lemma actual_original_hessian_pairing (A B : Connection ℚ) :
    Retrospective.connectionDensity (1 / 101) (A + B) - Retrospective.connectionDensity (1 / 101) A-
      Retrospective.connectionDensity (1 / 101) B = dotConnection B (fullBApply A) := by
  simp only [Retrospective.arbitrary_connection_density, rational_original_distinct,
    rational_original_repeated, fullBApply, actual_coordinate_dot_partition]
  have hD : (∑ s : Fin 4, (Retrospective.distinctDensity s (1 / 101) (gDistinct (A + B) s)-
      Retrospective.distinctDensity s (1 / 101) (gDistinct A s)-
      Retrospective.distinctDensity s (1 / 101) (gDistinct B s))) =
      ∑ s : Fin 4, dotProduct (gDistinct B s) (distinctB s *ᵥ gDistinct A s) := by
    apply Finset.sum_congr rfl
    intro s _
    simpa only [gDistinct_add, Pi.add_apply] using
      distinct_original_polarization s (gDistinct A s) (gDistinct B s)
  have hR : (∑ b : Fin 4, (Retrospective.repeatedDensity b (1 / 101) (gRepeated (A + B) b)-
      Retrospective.repeatedDensity b (1 / 101) (gRepeated A b)-
      Retrospective.repeatedDensity b (1 / 101) (gRepeated B b))) =
      ∑ b : Fin 4, dotProduct (gRepeated B b) (repeatB b *ᵥ gRepeated A b) := by
    apply Finset.sum_congr rfl
    intro b _
    simpa only [gRepeated_add, Pi.add_apply] using
      repeated_original_polarization b (gRepeated A b) (gRepeated B b)
  simp only [Finset.sum_sub_distrib] at hD hR
  linear_combination hD + hR

omit [CharZero K] in
lemma native_gram_three (p m s : Fin 3 → K) :
    nativeFaceGram (threeBlockFace p m s) = threeBlockFace (-p) (-m) s := by
  ext r a
  fin_cases r <;> fin_cases a <;>
    norm_num [nativeFaceGram, threeBlockFace, faceFirst, faceSecond, eta]

omit [CharZero K] in
lemma three_face_sub_smul (p m s p' m' s' : Fin 3 → K) (c : K) :
    threeBlockFace p m s - c • threeBlockFace p' m' s' =
      threeBlockFace (p - c • p') (m - c • m') (s - c • s') := by
  ext r a
  fin_cases r <;> fin_cases a <;> simp [threeBlockFace]

lemma actual_threeblock_constitutive_Q (p m s : Fin 3 → K) :
    nativeConstitutiveQ (threeBlockFace p m s) =
      threeBlockFace (-p - (2 / 101 : K) • ((timeT * timeH * timeT.transpose) *ᵥ p))
        (-m - (2 / 101 : K) • ((timeT * timeH * timeT.transpose) *ᵥ m))
        (s - (2 / 101 : K) • ((spaceT * spaceH * spaceT.transpose) *ᵥ s)) := by
  unfold nativeConstitutiveQ
  rw [native_adjoint_three_blocks, native_H_three_blocks, native_T_three_blocks,
    three_face_sub_smul, native_gram_three]
  have ht (v : Fin 3 → K) :
      -(v - (2 / 101 : K) • (-(timeT *ᵥ (timeH *ᵥ (timeT.transpose *ᵥ v))))) =
        -v - (2 / 101 : K) • ((timeT * timeH * timeT.transpose) *ᵥ v) := by
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    module
  rw [ht p, ht m]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

lemma actual_full24_cross_Q (j z a : K) (hj : j ^ 2 = -1) :
    nativeConstitutiveQ (literalChristoffelZ j z a) = crossQFaces j z a := by
  rw [original_cross_face_support j z a hj, actual_threeblock_constitutive_Q]
  rfl

lemma native_full24_on_TT_source (j z a : K) (hj : j ^ 2 = -1) (hz : z ^ 2 = -2 * a ^ 2) :
    CoordinateSymbol.mixedFaceSource j (CoordinateSymbol.timeMomentum j z ![a, -a, 0])
      (originalFaceInput (nativeConstitutiveQ (literalChristoffelZ j z a))) =
      (-(2 / 101 : K) * (9999 / 9991) * a ^ 4 * z) • ![0, 0, 0, 1] := by
  rw [actual_full24_cross_Q j z a hj]
  exact on_TT_source_reduction j z a hj hz

/-- **GAC2:original-full24-tt-cross-source**
(actual24-connection constitutive return and leading tt cross source). -/
@[ledger "GAC2:original-full24-tt-cross-source"]
theorem sourceLaw : Statement.sourceLaw := by
  intro K _ _
  exact ⟨actual_original_hessian_pairing,
    original_full24_inverse,
    actual_threeblock_constitutive_Q,
    actual_full24_cross_Q,
    native_full24_on_TT_source⟩

/-! ## Non-vacuity -/
example : nativeConstitutiveQ (literalChristoffelZ Complex.I (2 : ℂ) 3) =
    crossQFaces Complex.I 2 3 := actual_full24_cross_Q Complex.I 2 3 Complex.I_sq
example :
    CoordinateSymbol.mixedFaceSource Complex.I
      (CoordinateSymbol.timeMomentum Complex.I (Complex.I * (Real.sqrt 2 : ℂ)) ![1, -1, 0])
      (originalFaceInput (nativeConstitutiveQ
        (literalChristoffelZ Complex.I (Complex.I * (Real.sqrt 2 : ℂ)) 1))) =
      (-(2 / 101 : ℂ) * (9999 / 9991) * (Complex.I * (Real.sqrt 2 : ℂ))) • ![0, 0, 0, 1] := by
  have hr : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  have hz : (Complex.I * (Real.sqrt 2 : ℂ)) ^ 2 = -2 * (1 : ℂ) ^ 2 := by
    rw [mul_pow, Complex.I_sq, hr]
    norm_num
  simpa using native_full24_on_TT_source Complex.I (Complex.I * (Real.sqrt 2 : ℂ)) 1
    Complex.I_sq hz

end Artform.Scores.GravityBridge.Native.TTCross
