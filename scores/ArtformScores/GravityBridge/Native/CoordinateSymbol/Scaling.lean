import ArtformScores.GravityBridge.Native.CoordinateSymbol.ScalingStatements

/-! # Native frequency degrees and source-dependent response -/

namespace Artform.Scores.GravityBridge.Native.CoordinateSymbol

open Matrix

variable {K : Type*} [Field K] [CharZero K]

open Matrix
lemma native_face_scaling (s : K) (p : Vec4 (K := K)) :
    simpleFace (componentSquares (s • p)) (s • p) = s ^ 3 • simpleFace (componentSquares p) p := by
  ext a b
  simp [simpleFace, componentSquares]
  ring

lemma native_discriminant_scaling (s : K) (p : Vec4 (K := K)) :
    simpleDiscriminant (componentSquares (s • p)) (s • p) =
      s ^ 6 * simpleDiscriminant (componentSquares p) p := by
  simp [simpleDiscriminant, lorentzDot, componentSquares, Fin.sum_univ_succ]
  ring

lemma native_symbol_scaling (s : K) (p : Vec4 (K := K)) :
    nativeUpperSymbol (s • p) = s ^ 6 • nativeUpperSymbol p := by
  ext a b
  simp [nativeUpperSymbol, native_discriminant_scaling, lorentzK, native_face_scaling,
    Fin.sum_univ_succ]
  ring

lemma native_source_scaling (j s : K) (p : Vec4 (K := K))
    (Q : Fin 4 → Fin 4 → Fin 4 → K) :
    mixedFaceSource j (s • p) (fun a b c => s ^ 2 * Q a b c) = s ^ 5 • mixedFaceSource j p Q := by
  ext a
  simp [mixedFaceSource, native_face_scaling]
  ring

lemma native_inverse_scaling (s : K) (p : Vec4 (K := K)) (hs : s ≠ 0)
    (hd : simpleDiscriminant (componentSquares p) p ≠ 0) :
    nativeCoordinateInverse (s • p) = (s ^ 6)⁻¹ • nativeCoordinateInverse p := by
  have hds : simpleDiscriminant (componentSquares (s • p)) (s • p) ≠ 0 := by
    rw [native_discriminant_scaling]; exact mul_ne_zero (pow_ne_zero _ hs) hd
  have hi := native_coordinate_both_inverse p hd
  have his := native_coordinate_both_inverse (s • p) hds
  have hz : s ^ 6 ≠ 0 := pow_ne_zero _ hs
  calc
    nativeCoordinateInverse (s • p) = nativeCoordinateInverse (s • p) * 1 := by simp
    _ = nativeCoordinateInverse (s • p) * (nativeUpperSymbol (s • p) *
        ((s ^ 6)⁻¹ • nativeCoordinateInverse p)) := by
      congr 1
      symm
      rw [native_symbol_scaling, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        mul_inv_cancel₀ hz, one_smul, hi.1]
    _ = (s ^ 6)⁻¹ • nativeCoordinateInverse p := by
      rw [← Matrix.mul_assoc, his.2, Matrix.one_mul]

lemma native_lower_inverse_scaling (s : K) (p : Vec4 (K := K)) (hs : s ≠ 0)
    (hd : simpleDiscriminant (componentSquares p) p ≠ 0) :
    nativeLowerInverse (s • p) = (s ^ 6)⁻¹ • nativeLowerInverse p := by
  simp only [nativeLowerInverse, native_inverse_scaling s p hs hd, Matrix.mul_smul,
    Matrix.smul_mul]

lemma forced_response_scaling (j s : K) (p : Vec4 (K := K))
    (Q : Fin 4 → Fin 4 → Fin 4 → K) (hs : s ≠ 0)
    (hd : simpleDiscriminant (componentSquares p) p ≠ 0) :
    nativeLowerInverse (s • p) *ᵥ mixedFaceSource j (s • p) (fun a b c => s ^ 2 * Q a b c) =
      s⁻¹ • (nativeLowerInverse p *ᵥ mixedFaceSource j p Q) := by
  rw [native_lower_inverse_scaling s p hs hd, native_source_scaling]
  simp only [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul]
  congr 1
  field_simp

lemma explicit_native_response :
    nativeLowerInverse (![-1, 1, 0, 0] : Vec4 (K := ℝ)) *ᵥ
      mixedFaceSource 1 ![-1, 1, 0, 0] explicitFaceInput = ![0, 0, 0, -9991 / 9999] := by
  have hp : simpleDiscriminant (componentSquares (![-1, 1, 0, 0] : Vec4 (K := ℝ)))
      ![-1, 1, 0, 0] ≠ 0 := by rw [opposite_axis_discriminant]; norm_num
  have he : nativeLowerSymbol (![-1, 1, 0, 0] : Vec4 (K := ℝ)) *ᵥ
      ![0, 0, 0, -9991 / 9999] = mixedFaceSource 1 ![-1, 1, 0, 0] explicitFaceInput := by
    ext i
    fin_cases i <;> norm_num [nativeLowerSymbol, etaMatrix, nativeUpperSymbol,
      simpleDiscriminant, lorentzDot,
      componentSquares, lorentzK, simpleFace, signature, Matrix.mulVec, dotProduct,
      mixedFaceSource, explicitFaceInput, Fin.sum_univ_succ]
  rw [← he, Matrix.mulVec_mulVec, (native_lower_two_sided _ hp).2,
    Matrix.one_mulVec]

lemma explicit_small_frequency_response (s : ℝ) (hs : s ≠ 0) :
    (nativeLowerInverse (s • (![-1, 1, 0, 0] : Vec4 (K := ℝ))) *ᵥ
      mixedFaceSource 1 (s • ![-1, 1, 0, 0])
        (fun a b c => s ^ 2 * explicitFaceInput a b c)) 3 = -(9991 / 9999 : ℝ) / s := by
  rw [forced_response_scaling 1 s ![-1, 1, 0, 0] explicitFaceInput hs]
  · rw [explicit_native_response]
    simp
    ring
  · rw [opposite_axis_discriminant]; norm_num

/-- **GAC2:native-frequency-response-scaling**
(native frequency degrees and source-dependent response). -/
@[ledger "GAC2:native-frequency-response-scaling"]
theorem scalingLaw : Statement.scalingLaw := by
  intro K _ _
  exact ⟨native_face_scaling,
    native_discriminant_scaling,
    native_symbol_scaling,
    native_source_scaling,
    native_inverse_scaling,
    native_lower_inverse_scaling,
    forced_response_scaling,
    explicit_native_response,
    explicit_small_frequency_response⟩

/-! ## Non-vacuity -/
example : nativeLowerInverse ((2 : ℚ) • (![-1, 1, 0, 0] : Vec4 (K := ℚ))) =
    (64 : ℚ)⁻¹ • nativeLowerInverse ![-1, 1, 0, 0] := by
  apply native_lower_inverse_scaling 2 ![-1, 1, 0, 0] (by norm_num)
  rw [opposite_axis_discriminant]; norm_num

end Artform.Scores.GravityBridge.Native.CoordinateSymbol
