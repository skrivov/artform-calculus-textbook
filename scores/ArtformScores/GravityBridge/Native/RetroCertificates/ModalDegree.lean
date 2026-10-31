import ArtformScores.GravityBridge.Native.RetroCertificates.ModalDegreeStatements

/-! # Native modal interpolation requires the fifth-degree term -/

namespace Artform.Scores.GravityBridge.Native.RetroCertificates

open Matrix Full40 TTCross Retrospective



open Matrix Full40 TTCross

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- These are six actual original24-connection modes, not roots of a replacement matrix.
lemma actual_six_native_eigenmodes :
    (∀ i : Fin 6, fullBApply (sixEigenvectors i) = sixEigenvalues i • sixEigenvectors i ∧
      sixEigenvectors i ≠ 0) ∧
    (∀ i j : Fin 6, i ≠ j → sixEigenvalues i ≠ sixEigenvalues j) := by
  decide +kernel

lemma unique_odd_inverse_modal_coefficients (p1 p3 p5 : ℚ)
    (ha : (p1 * (194 / 101) + p3 * (194 / 101) ^ 3 + p5 * (194 / 101) ^ 5) * (194 / 101) = 1)
    (hb : (p1 * (103 / 101) + p3 * (103 / 101) ^ 3 + p5 * (103 / 101) ^ 5) * (103 / 101) = 1)
    (hc : (p1 * (200 / 101) + p3 * (200 / 101) ^ 3 + p5 * (200 / 101) ^ 5) * (200 / 101) = 1) :
    p1 = inverseP1 ∧ p3 = inverseP3 ∧ p5 = inverseP5 := by
  norm_num at ha hb hc
  norm_num [inverseP1, inverseP3, inverseP5]
  constructor
  · linarith
  constructor <;> linarith

lemma no_degree_three_odd_modal_inverse :
    ¬ ∃ p1 p3 : ℚ,
      (p1 * (194 / 101) + p3 * (194 / 101) ^ 3) * (194 / 101) = 1 ∧
      (p1 * (103 / 101) + p3 * (103 / 101) ^ 3) * (103 / 101) = 1 ∧
      (p1 * (200 / 101) + p3 * (200 / 101) ^ 3) * (200 / 101) = 1 := by
  rintro ⟨p1, p3, ha, hb, hc⟩
  have hh := unique_odd_inverse_modal_coefficients p1 p3 0 (by simpa using ha)
    (by simpa using hb) (by simpa using hc)
  norm_num [inverseP5] at hh

/-- **GAC2:native-modal-inverse-degree**
(native modal interpolation requires the fifth-degree term). -/
@[ledger "GAC2:native-modal-inverse-degree"]
theorem modalDegreeLaw : Statement.modalDegreeLaw := by
  exact ⟨actual_six_native_eigenmodes,
    unique_odd_inverse_modal_coefficients,
    no_degree_three_odd_modal_inverse⟩

/-! ## Non-vacuity -/
example : sixEigenvalues 0 ≠ 0 ∧ sixEigenvectors 0 ≠ 0 := by
  refine ⟨by norm_num [sixEigenvalues], (actual_six_native_eigenmodes.1 0).2⟩

end Artform.Scores.GravityBridge.Native.RetroCertificates
