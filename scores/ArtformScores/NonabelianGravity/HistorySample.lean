import ArtformScores.NonabelianGravity.HistoryBinding
import ArtformScores.NonabelianGravity.HistorySampleLeft
import ArtformScores.NonabelianGravity.HistorySampleRight
import ArtformScores.NonabelianGravity.HistorySampleProduct
import ArtformScores.NonabelianGravity.HistorySampleDiagonal

/-! # A complete emitted certificate and nonvacuity controls -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.HistoryElimination

def sampleCertificate : Certificate (historyMatrix 2) where
  forward := sampleForward
  backward := sampleBackward
  diagonal := sampleDiagonal
  left_inverse := sample_left
  right_inverse := sample_right
  congruence := by
    rw [Matrix.mul_assoc, sample_product]
    exact sample_diagonal

lemma sample_pivots : Fintype.card {i : Index 2 // sampleDiagonal i ≠ 0} = 66 := by
  decide +kernel

lemma zero_history (n : ℕ) : NativeMatch (n := n) 0 0 0 0 := by
  rw [native_matching_iff, Matrix.mulVec_zero]
  funext i
  simp [sourceResidual]

def incompatibleSource : Vector 2 := fun i => if i = (0, 0) then 1 else 0

lemma inactive_row : ∀ j : Index 2, historyMatrix 2 (0, 0) j = 0 := by decide +kernel

lemma incompatible_rejected : ¬ ∃ y, NativeMatch 0 0 incompatibleSource y := by
  rintro ⟨y, hy⟩
  have h := congrFun ((native_matching_iff 0 0 incompatibleSource y).mp hy) (0, 0)
  simp [Matrix.mulVec, dotProduct, inactive_row, sourceResidual, incompatibleSource] at h

end Artform.Scores.NonabelianGravity.HistoryElimination
