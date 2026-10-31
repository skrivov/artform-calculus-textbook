import ArtformScores.GravityBridge.Native.RetroCertificates.FacePartitionStatements

/-! # All original constitutive face slots in eight signed blocks -/

namespace Artform.Scores.GravityBridge.Native.RetroCertificates

open Matrix Full40 TTCross Retrospective

variable {K : Type*} [Field K] [CharZero K]

open Matrix Full40 TTCross
omit [CharZero K] in
lemma native_face_partition_left (Z : NativeFace K) : faceAssemble (faceRead Z) = Z := by
  ext r a
  fin_cases r <;> fin_cases a <;>
    norm_num [faceAssemble, faceRead, faceIndex, faceWire, Fin.sum_univ_succ]

omit [CharZero K] in
lemma native_face_partition_right (v : Fin 8 → Fin 3 → K) : faceRead (faceAssemble v) = v := by
  ext s i
  fin_cases s <;> fin_cases i <;>
    norm_num [faceAssemble, faceRead, faceIndex, faceWire, Fin.sum_univ_succ]

lemma native_face_block_guards (s : Fin 8) :
    faceAlpha (K := K) s ≠ 0 ∧ faceAlpha (K := K) s + 3 * faceBeta s ≠ 0 := by
  fin_cases s <;> norm_num [faceAlpha, faceBeta]

set_option maxHeartbeats 1000000 in
-- Check all original eight rank-one blocks in both orders.
lemma native_face_blocks_inverse (s : Fin 8) :
    faceInverseBlock (K := K) s * faceForwardBlock s = 1 ∧
      faceForwardBlock (K := K) s * faceInverseBlock s = 1 := by
  constructor <;> ext i j <;> fin_cases s <;> fin_cases i <;> fin_cases j <;>
    norm_num [faceInverseBlock, faceForwardBlock, faceAlpha, faceBeta, Matrix.mul_apply,
      Matrix.one_apply, Fin.sum_univ_succ]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Expand the actual24-face constitutive map once before using its sparse partition.
lemma original_constitutive_face_blocks (Z : NativeFace K) (s : Fin 8) :
    faceRead (nativeConstitutiveQ Z) s = faceForwardBlock s *ᵥ faceRead Z s := by
  unfold nativeConstitutiveQ
  rw [original_native_adjoint_slots, original_native_H_slots, original_native_T_slots]
  ext i
  fin_cases s <;> fin_cases i <;>
    norm_num [faceRead, faceIndex, faceWire, faceForwardBlock, faceAlpha, faceBeta,
      nativeFaceGram, directNativeT, directNativeAdjoint, directNativeH, faceFirst, faceSecond,
      eta, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

/-- **GAC2:native-full-face-rank-partition**
(all original constitutive face slots in eight signed blocks). -/
@[ledger "GAC2:native-full-face-rank-partition"]
theorem facePartitionLaw : Statement.facePartitionLaw := by
  intro K _ _
  exact ⟨native_face_partition_left,
    native_face_partition_right,
    native_face_block_guards,
    native_face_blocks_inverse,
    original_constitutive_face_blocks⟩

/-! ## Non-vacuity -/
example : faceAlpha (K := ℚ) 2 + 3 * faceBeta 2 = -97 / 101 := by norm_num [faceAlpha, faceBeta]

end Artform.Scores.GravityBridge.Native.RetroCertificates
