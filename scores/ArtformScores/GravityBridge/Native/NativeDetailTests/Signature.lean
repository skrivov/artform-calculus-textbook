import ArtformScores.GravityBridge.Native.NativeDetailTests.SignatureStatements

/-! # Complete original constitutive quadratic has both algebraic signs -/

namespace Artform.Scores.GravityBridge.Native.NativeDetailTests

open Matrix Full40 TTCross RetroCertificates MeasureTheory Set Filter
open scoped ENNReal

variable {K : Type*} [Field K] [CharZero K]

open Matrix Full40 TTCross RetroCertificates
lemma original_modes_two_sided (z : Fin 3 → K) :
    inverseModes (orthogonalModes z) = z ∧ orthogonalModes (inverseModes z) = z := by
  constructor <;> ext i <;> fin_cases i <;> norm_num [orthogonalModes, inverseModes] <;> ring

omit [CharZero K] in
lemma complete_face_dot_partition (Z W : NativeFace K) :
    (∑ r, ∑ a, Z r a * W r a) = ∑ s : Fin 8, ∑ i : Fin 3, faceRead Z s i * faceRead W s i := by
  norm_num [faceRead, faceIndex, faceWire, Fin.sum_univ_succ]
  ring

lemma original_block_mode_diagonal (s : Fin 8) (z : Fin 3 → K) :
    (∑ i, orthogonalModes z i * (faceForwardBlock s *ᵥ orthogonalModes z) i) =
      ∑ i, modeDiagonal s i * (z i) ^ 2 := by
  norm_num [orthogonalModes, faceForwardBlock, modeDiagonal, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ]
  ring

lemma full_original_face_diagonal_congruence (z : Fin 8 → Fin 3 → K) :
    nativeFaceQuadratic (faceModes z) = ∑ s : Fin 8, ∑ i : Fin 3, modeDiagonal s i * (z s i) ^ 2
      := by
  unfold nativeFaceQuadratic
  rw [complete_face_dot_partition]
  simp_rw [original_constitutive_face_blocks]
  simp only [faceModes, native_face_partition_right]
  apply Finset.sum_congr rfl
  intro s _
  exact original_block_mode_diagonal s (z s)

lemma exactly_twelve_positive_and_negative :
    positiveModeCount = 12 ∧ negativeModeCount = 12 ∧
      (∀ s : Fin 8, ∀ i : Fin 3, modeDiagonal (K := ℚ) s i ≠ 0) := by decide +kernel

lemma original_constitutive_both_signs :
    nativeFaceQuadratic (faceModes (fun s => if s = 0 then ![1, 0, 0] else 0) : NativeFace ℚ) =
      202 / 103 ∧
    nativeFaceQuadratic (faceModes (fun s => if s = 1 then ![1, 0, 0] else 0) : NativeFace ℚ) =
      -202 / 103 := by
  constructor <;> rw [full_original_face_diagonal_congruence] <;>
    norm_num [modeDiagonal, faceAlpha, faceBeta, Fin.sum_univ_succ]

/-- **GAC2:native-constitutive-diagonal-signs**
(complete original constitutive quadratic has both algebraic signs). -/
@[ledger "GAC2:native-constitutive-diagonal-signs"]
theorem signatureLaw : Statement.signatureLaw := by
  intro K _ _
  exact ⟨original_modes_two_sided,
    full_original_face_diagonal_congruence,
    exactly_twelve_positive_and_negative,
    original_constitutive_both_signs⟩

/-! ## Non-vacuity -/
example : positiveModeCount = 12 ∧ negativeModeCount = 12 :=
  ⟨exactly_twelve_positive_and_negative.1, exactly_twelve_positive_and_negative.2.1⟩

end Artform.Scores.GravityBridge.Native.NativeDetailTests
