import ArtformScores.GravityBridge.Native.Full40.PhysicalSignStatements
/-! # Original lower-coordinate boost and physical-native connection signs -/
namespace Artform.Scores.GravityBridge.Native.Full40
variable {K : Type*} [Field K] [CharZero K]
lemma gradient_minus_symmetric (H : Frame K) :
    gradientCoframe H - symmetricCoframe H = lie (coordinateLorentz H) := by
  ext I i
  fin_cases I <;> fin_cases i <;>
    simp [gradientCoframe, symmetricCoframe, coordinateLorentz, lie, eta] <;> ring
lemma gradient_lorentz_readout (H : Frame K) :
    coframeLorentz (gradientCoframe H) = coordinateLorentz H := by
  ext a
  fin_cases a <;> simp [coframeLorentz, gradientCoframe, coordinateLorentz, eta] <;> ring
lemma symmetric_lorentz_zero (H : Frame K) : coframeLorentz (symmetricCoframe H) = 0 := by
  ext a
  fin_cases a <;> simp [coframeLorentz, symmetricCoframe, eta] <;> ring
lemma physical_connection_positive_sign (H : Frame K) (dgamma : Connection K) :
    (gradientCoframe H, (0 : Connection K)) -
      physicalLorentzColumn (coordinateLorentz H) dgamma =
        (symmetricCoframe H, dgamma) := by
  apply Prod.ext
  · have he := gradient_minus_symmetric H
    change gradientCoframe H - lie (coordinateLorentz H) = symmetricCoframe H
    rw [← he]
    abel
  · simp [physicalLorentzColumn]
omit [CharZero K] in
lemma physical_native_column_sign (h : K) (gamma : Biv K) (dgamma : Connection K) :
    nativeFromPhysical h (physicalLorentzColumn gamma dgamma) = (lie gamma, h • dgamma) := by
  apply Prod.ext
  · rfl
  · dsimp [nativeFromPhysical, physicalLorentzColumn]
    module
omit [CharZero K] in
lemma lower_temporal_boost (H : Frame K) :
    coordinateLorentz H 0 = (H 0 1 - H 1 0) / 2 ∧
    gradientCoframe H 0 1 = -H 1 0 ∧ gradientCoframe H 1 0 = H 0 1 := by
  simp [coordinateLorentz, gradientCoframe, eta]
/-- **GAC2:lower-boost-physical-native-sign**
(original lower-coordinate boost and physical-native connection signs). -/
@[ledger "GAC2:lower-boost-physical-native-sign"]
theorem physicalSignLaw : Statement.physicalSignLaw := by
  intro K _ _
  exact ⟨gradient_minus_symmetric,
    gradient_lorentz_readout,
    symmetric_lorentz_zero,
    physical_connection_positive_sign,
    physical_native_column_sign,
    lower_temporal_boost⟩
/-! ## Non-vacuity -/
example : coordinateLorentz (!![0, 2, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0] : Frame ℚ) 0 = 1 ∧
    (nativeFromPhysical (1 / 2 : ℚ) (physicalLorentzColumn 0
      (fun _ => ![1, 0, 0, 0, 0, 0]))).2 0 0 = 1 / 2 := by
  norm_num [coordinateLorentz, nativeFromPhysical, physicalLorentzColumn]
end Artform.Scores.GravityBridge.Native.Full40
