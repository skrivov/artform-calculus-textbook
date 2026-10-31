import ArtformScores.GravityBridge.Native.Full40.PhysicalSignDefs
/-! # Original lower-coordinate boost and physical-native connection signs -/
namespace Artform.Scores.GravityBridge.Native.Full40.Statement
/-- **GAC2:lower-boost-physical-native-sign**
(original lower-coordinate boost and physical-native connection signs). -/
@[ledger "GAC2:lower-boost-physical-native-sign"]
def physicalSignLaw : Prop :=
  ∀ (K : Type) [Field K] [CharZero K],
    (∀ (H : Frame K),
    gradientCoframe H - symmetricCoframe H = lie (coordinateLorentz H)) ∧
    (∀ (H : Frame K),
    coframeLorentz (gradientCoframe H) = coordinateLorentz H) ∧
    (∀ (H : Frame K),
    coframeLorentz (symmetricCoframe H) = 0) ∧
    (∀ (H : Frame K) (dgamma : Connection K),
    (gradientCoframe H, (0 : Connection K)) -
      physicalLorentzColumn (coordinateLorentz H) dgamma =
        (symmetricCoframe H, dgamma)) ∧
    (∀ (h : K) (gamma : Biv K) (dgamma : Connection K),
    nativeFromPhysical h (physicalLorentzColumn gamma dgamma) = (lie gamma, h • dgamma)) ∧
    (∀ (H : Frame K),
    coordinateLorentz H 0 = (H 0 1 - H 1 0) / 2 ∧
    gradientCoframe H 0 1 = -H 1 0 ∧ gradientCoframe H 1 0 = H 0 1)
end Artform.Scores.GravityBridge.Native.Full40.Statement
