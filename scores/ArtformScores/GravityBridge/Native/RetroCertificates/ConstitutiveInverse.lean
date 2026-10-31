import ArtformScores.GravityBridge.Native.RetroCertificates.ConstitutiveInverseStatements

/-! # Original full face inverse and exact curvature Woodbury return -/

namespace Artform.Scores.GravityBridge.Native.RetroCertificates

open Matrix Full40 TTCross Retrospective

variable {K : Type*} [Field K] [CharZero K]

open Matrix Full40 TTCross
lemma original_curvature_distinct_polarization (s : Fin 4) (x y : Fin 3 → ℚ) :
    Retrospective.distinctDensity s 0 (x + y) - Retrospective.distinctDensity s 0 x-
      Retrospective.distinctDensity s 0 y = dotProduct y (curvatureD s *ᵥ x) := by
  fin_cases s <;>
    norm_num [Retrospective.distinctDensity, Retrospective.distinctIndices, curvatureD,
      signS, eta, Matrix.mulVec, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
        <;> ring

lemma original_curvature_repeated_polarization (b : Fin 4) (x y : Fin 3 → ℚ) :
    Retrospective.repeatedDensity b 0 (x + y) - Retrospective.repeatedDensity b 0 x-
      Retrospective.repeatedDensity b 0 y = dotProduct y (curvatureR b *ᵥ x) := by
  fin_cases b <;> norm_num [Retrospective.repeatedDensity, curvatureR, eta, Matrix.mulVec,
    dotProduct, Fin.sum_univ_succ] <;> ring

lemma actual_original_curvature_Hessian (A B : Connection ℚ) :
    Retrospective.connectionDensity 0 (A + B) - Retrospective.connectionDensity 0 A-
      Retrospective.connectionDensity 0 B = dotConnection B (curvatureApply A) := by
  simp only [Retrospective.arbitrary_connection_density, rational_original_distinct,
    rational_original_repeated, curvatureApply, actual_coordinate_dot_partition]
  have hD : (∑ s : Fin 4, (Retrospective.distinctDensity s 0 (gDistinct (A + B) s)-
      Retrospective.distinctDensity s 0 (gDistinct A s)-
      Retrospective.distinctDensity s 0 (gDistinct B s))) =
      ∑ s : Fin 4, dotProduct (gDistinct B s) (curvatureD s *ᵥ gDistinct A s) := by
    apply Finset.sum_congr rfl
    intro s _
    simpa only [gDistinct_add, Pi.add_apply] using
      original_curvature_distinct_polarization s (gDistinct A s) (gDistinct B s)
  have hR : (∑ b : Fin 4, (Retrospective.repeatedDensity b 0 (gRepeated (A + B) b)-
      Retrospective.repeatedDensity b 0 (gRepeated A b)-
      Retrospective.repeatedDensity b 0 (gRepeated B b))) =
      ∑ b : Fin 4, dotProduct (gRepeated B b) (curvatureR b *ᵥ gRepeated A b) := by
    apply Finset.sum_congr rfl
    intro b _
    simpa only [gRepeated_add, Pi.add_apply] using
      original_curvature_repeated_polarization b (gRepeated A b) (gRepeated B b)
  simp only [Finset.sum_sub_distrib] at hD hR
  linear_combination hD + hR

set_option maxHeartbeats 1000000 in
-- Check both original curvature block inverse orders before using the Woodbury return.
lemma all_original_curvature_inverses :
    (∀ s : Fin 4, curvatureD (K := K) s * curvatureDH s = 1 ∧
      curvatureDH (K := K) s * curvatureD s = 1) ∧
    (∀ b : Fin 4, curvatureR (K := K) b * curvatureRH b = 1 ∧
      curvatureRH (K := K) b * curvatureR b = 1) := by
  constructor <;> intro s <;> constructor <;> ext i j <;>
    fin_cases s <;> fin_cases i <;> fin_cases j <;>
      norm_num [curvatureD, curvatureDH, curvatureR, curvatureRH, signS, eta,
        Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.one_apply, Fin.sum_univ_succ]

lemma original_curvature_return_both (A : Connection K) :
    curvatureApply (curvatureReturn A) = A ∧ curvatureReturn (curvatureApply A) = A := by
  have hd (s : Fin 4) (v : Fin 3 → K) : curvatureD s *ᵥ (curvatureDH s *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, (all_original_curvature_inverses.1 s).1, Matrix.one_mulVec]
  have hd' (s : Fin 4) (v : Fin 3 → K) : curvatureDH s *ᵥ (curvatureD s *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, (all_original_curvature_inverses.1 s).2, Matrix.one_mulVec]
  have hr (b : Fin 4) (v : Fin 3 → K) : curvatureR b *ᵥ (curvatureRH b *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, (all_original_curvature_inverses.2 b).1, Matrix.one_mulVec]
  have hr' (b : Fin 4) (v : Fin 3 → K) : curvatureRH b *ᵥ (curvatureR b *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, (all_original_curvature_inverses.2 b).2, Matrix.one_mulVec]
  constructor <;>
    simp only [curvatureApply, curvatureReturn, generic_partition_distinct,
      generic_partition_repeated,
      hd, hd', hr, hr', generic_partition_left]

lemma original_full_constitutive_inverse (Z : NativeFace K) :
    nativeConstitutiveQ (nativeFaceInverse Z) = Z ∧ nativeFaceInverse (nativeConstitutiveQ Z) =
      Z := by
  constructor
  · calc
      _ = faceAssemble (faceRead (nativeConstitutiveQ (nativeFaceInverse Z))) :=
        (native_face_partition_left _).symm
      _ = faceAssemble (faceRead Z) := by
        congr 1
        funext s
        rw [original_constitutive_face_blocks, nativeFaceInverse, native_face_partition_right,
          Matrix.mulVec_mulVec, (native_face_blocks_inverse s).2, Matrix.one_mulVec]
      _ = Z := native_face_partition_left Z
  · unfold nativeFaceInverse
    have he : (fun s => faceInverseBlock s *ᵥ faceRead (nativeConstitutiveQ Z) s) = faceRead Z := by
      funext s
      rw [original_constitutive_face_blocks, Matrix.mulVec_mulVec,
        (native_face_blocks_inverse s).1, Matrix.one_mulVec]
    rw [he, native_face_partition_left]


set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Compose the original curvature templates with the verified24 signed wires.
lemma actual_original_curvature_return_slots (A : Connection K) :
    curvatureReturn A = directCurvatureReturn A := by
  unfold curvatureReturn
  rw [original_distinct_read_slots, original_repeated_read_slots, original_assembly_slots]
  ext mu a
  fin_cases mu <;> fin_cases a <;>
    norm_num [directCurvatureReturn, directAssembly, directDistinctRead, directRepeatedRead,
      curvatureDH, curvatureRH, signS, eta, Matrix.mulVec, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ] <;> ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Compare the whole original face map; the curvature inverse is used inside Woodbury only.
lemma actual_native_constitutive_Woodbury (Z : NativeFace K) :
    nativeFaceInverse Z = nativeFaceGram Z + (2 / 101 : K) • nativeConnectionT
      (curvatureReturn (nativeSourceAdjoint (nativeFaceGram Z))) := by
  rw [original_native_adjoint_slots, actual_original_curvature_return_slots,
    original_native_T_slots]
  ext r a
  fin_cases r <;> fin_cases a <;>
    norm_num [nativeFaceInverse, faceAssemble, faceInverseBlock, faceRead, faceIndex, faceWire,
      faceAlpha, faceBeta, nativeFaceGram, directNativeT, directNativeAdjoint,
        directCurvatureReturn,
      faceFirst, faceSecond, eta, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

/-- **GAC2:native-full-constitutive-inverse**
(original full face inverse and exact curvature woodbury return). -/
@[ledger "GAC2:native-full-constitutive-inverse"]
theorem constitutiveInverseLaw : Statement.constitutiveInverseLaw := by
  intro K _ _
  exact ⟨actual_original_curvature_Hessian,
    original_curvature_return_both,
    original_full_constitutive_inverse,
    actual_native_constitutive_Woodbury⟩

/-! ## Non-vacuity -/
example : nativeConstitutiveQ (nativeFaceInverse (0 : NativeFace ℚ)) = 0 :=
  (original_full_constitutive_inverse _).1

end Artform.Scores.GravityBridge.Native.RetroCertificates
