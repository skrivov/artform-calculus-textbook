import ArtformScores.GravityBridge.Native.Full40.Projector
/-! # Original lower-coordinate boost and physical-native connection signs -/
namespace Artform.Scores.GravityBridge.Native.Full40
variable {K : Type*} [Field K] [CharZero K]
def gradientCoframe (H : Frame K) : Frame K := fun I i => eta I * H i I
def symmetricCoframe (H : Frame K) : Frame K :=
  fun I i => eta I * (H i I + H I i) / 2
def coordinateLorentz (H : Frame K) : Biv K :=
  ![(H 0 1 - H 1 0) / 2, (H 0 2 - H 2 0) / 2, (H 0 3 - H 3 0) / 2,
    (H 3 2 - H 2 3) / 2, (H 1 3 - H 3 1) / 2, (H 2 1 - H 1 2) / 2]
def physicalLorentzColumn (gamma : Biv K) (dgamma : Connection K) : Full K :=
  (lie gamma, -dgamma)
def nativeFromPhysical (h : K) (q : Full K) : Full K := (q.1, -h • q.2)
end Artform.Scores.GravityBridge.Native.Full40
