import ArtformScores.GravityBridge.Native.TTCross.Full24

/-! # Actual24-connection constitutive return and leading TT cross source -/

namespace Artform.Scores.GravityBridge.Native.TTCross

open Matrix CoordinateSymbol Full40

variable {K : Type*} [Field K] [CharZero K]

def dotConnection (A B : Connection K) : K := ∑ mu, ∑ a, A mu a * B mu a

end Artform.Scores.GravityBridge.Native.TTCross
