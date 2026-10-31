import ArtformScores.GravityBridge.Native.Full40.PhysicalSign
/-! # The original temporal boost quarter-contact -/
namespace Artform.Scores.GravityBridge.Native.Full40
variable {K : Type*} [Field K] [CharZero K]
def lowerThirdJet (n : Fin 3 → K) (a : K) : Frame K :=
  !![0, n 0 * a, n 1 * a, n 2 * a; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]
def temporalBoostContact (n : Fin 3 → K) (a : K) : Biv K :=
  (1 / 2 : K) • coordinateLorentz (lowerThirdJet n a)
end Artform.Scores.GravityBridge.Native.Full40
