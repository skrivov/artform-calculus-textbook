import ArtformScores.GravityBridge.Native.Full40.Force
/-! # The full original mixed Lorentz Ward identity -/
namespace Artform.Scores.GravityBridge.Native.Full40
variable {X K : Type*} [AddCommGroup X] [Field K] [CharZero K]
def gaugeField (d : Fin 4 → X) (w : X → Biv K) : NativeField X K :=
  fun x => (lie (w x), gaugeConnection d w x)
def gaugeCorrection (d : Fin 4 → X) (q : NativeField X K) (w : X → Biv K) :
    NativeField X K := fun x => (0, fun i => (-1 / 2 : K) •
      bivBracket ((q x).2 i) (w x + w (x + d i)))
end Artform.Scores.GravityBridge.Native.Full40
