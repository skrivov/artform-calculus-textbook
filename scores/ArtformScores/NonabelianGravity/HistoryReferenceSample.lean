import ArtformScores.NonabelianGravity.HistoryReference
import ArtformScores.NonabelianGravity.HistorySample

/-! # Actual native66-dimensional reference carrier and nonzero source contact -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.HistoryElimination
open Legendre

lemma reference_dimension : Fintype.card (Active sampleCertificate) = 66 := sample_pivots

lemma reference_positive_pivots :
    Fintype.card {i : Index 2 // 0 < sampleDiagonal i} = 37 := by decide +kernel

lemma reference_negative_pivots :
    Fintype.card {i : Index 2 // sampleDiagonal i < 0} = 29 := by decide +kernel

lemma reference_phase_one : rotationPhase sampleCertificate = 1 := by
  have hp : ((Finset.univ : Finset (Active sampleCertificate)).filter
      (fun i : Active sampleCertificate =>
        0 < sampleCertificate.diagonal i.val)).card = 37 := by decide +kernel
  have hm : ((Finset.univ : Finset (Active sampleCertificate)).filter
      (fun i : Active sampleCertificate =>
        ¬0 < sampleCertificate.diagonal i.val)).card = 29 := by decide +kernel
  have hw (q : ℚ) : HistoryGaussian.wick (q : ℝ) =
      if 0 < q then (1 + Complex.I) / (Real.sqrt 2 : ℂ)
      else (1 - Complex.I) / (Real.sqrt 2 : ℂ) := by
    simp only [HistoryGaussian.wick, Rat.cast_pos]
  simp only [rotationPhase, activeDiagonal, hw]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  rw [hp, hm]
  let p : ℂ := (1 + Complex.I) / (Real.sqrt 2 : ℂ)
  let m : ℂ := (1 - Complex.I) / (Real.sqrt 2 : ℂ)
  change p ^ 37 * m ^ 29 = 1
  have h₂ : p ^ 2 = Complex.I := by
    simpa [HistoryGaussian.wick, p] using HistoryGaussian.wick_square (1 : ℝ)
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by norm_cast; norm_num
  have hpm : p * m = 1 := by
    calc
      _ = ((1 + Complex.I) * (1 - Complex.I)) / 2 := by
        dsimp [p, m]
        rw [div_mul_div_comm, ← pow_two, hs]
      _ = _ := by ring_nf; norm_num
  calc
    _ = (p ^ 2) ^ 4 * (p * m) ^ 29 := by ring
    _ = _ := by rw [h₂, hpm]; norm_num

def quantumDirection : Vector 2 := fun i => if i = (0, 25) then 1 else 0

def quantumSource : Vector 2 := (historyMatrix 2).mulVec quantumDirection

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- The full native matrix is retained in this nonzero sourced history.
lemma quantum_source_nonzero : quantumSource (0, 25) = 4 / 101 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- The entire80-coordinate quadratic/source pairing, not a discarded phase constant.
lemma quadratic_direction :
    quadraticAction (H := historyMatrix 2) quantumSource quantumDirection = -2 / 101 := by
  decide +kernel

lemma quantum_source_compatible (c : Certificate (historyMatrix 2)) :
    Compatible c quantumSource := (solvable_iff c _).mp ⟨quantumDirection, rfl⟩

lemma quantum_source_contact (c : Certificate (historyMatrix 2)) :
    sourceContact c quantumSource = 4 / 101 := by
  have hy := solution_complete c quantumDirection quantumSource rfl
  have hs := stationary_quadratic c quantumSource (c.backward.mulVec quantumDirection)
    (quantum_source_compatible c)
  rw [← hy, quadratic_direction] at hs
  linarith

lemma zero_reference_admitted (ℏ : ℝ) (hℏ : 0 < ℏ) :
    (nativeReference sampleCertificate 0 0 0 ℏ).isSome := by
  rw [native_reference_admission]
  exact ⟨hℏ, ⟨0, zero_history 2⟩⟩

lemma incompatible_reference_rejected (ℏ : ℝ) :
    nativeReference sampleCertificate 0 0 incompatibleSource ℏ = none := by
  have h : ¬(nativeReference sampleCertificate 0 0 incompatibleSource ℏ).isSome := by
    rw [native_reference_admission]
    exact fun h => incompatible_rejected h.2
  cases hh : nativeReference sampleCertificate 0 0 incompatibleSource ℏ <;> simp_all

end Artform.Scores.NonabelianGravity.HistoryElimination
