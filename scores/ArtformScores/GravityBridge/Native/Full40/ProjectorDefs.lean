import ArtformScores.GravityBridge.Native.Full40.Ward
/-! # The coframe Lorentz projector with compatible sources -/
namespace Artform.Scores.GravityBridge.Native.Full40
variable {X K : Type*} [AddCommGroup X] [Field K] [CharZero K]
def coframeLorentz (F : Frame K) : Biv K :=
  ![(F 0 1 + F 1 0) / 2, (F 0 2 + F 2 0) / 2, (F 0 3 + F 3 0) / 2,
    (F 2 3 - F 3 2) / 2, (F 3 1 - F 1 3) / 2, (F 1 2 - F 2 1) / 2]
def lorentzReadout (q : NativeField X K) : X → Biv K := fun x => coframeLorentz (q x).1
def projectField (d : Fin 4 → X) (q : NativeField X K) : NativeField X K :=
  q - gaugeField d (lorentzReadout q)
end Artform.Scores.GravityBridge.Native.Full40
