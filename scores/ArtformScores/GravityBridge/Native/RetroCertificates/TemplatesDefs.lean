import ArtformScores.GravityBridge.Native.TTCross.Full24

/-! # Two template checks certify both original24 inverse orders -/

namespace Artform.Scores.GravityBridge.Native.RetroCertificates

open Matrix Full40 TTCross Retrospective

variable {K : Type*} [Field K] [CharZero K]

def templateReturn (D R : Three (K := K)) (A : Connection K) : Connection K :=
  gAssemble (fun s => (if s = 3 then -(signS * D * signS) else D) *ᵥ gDistinct A s)
    (fun b => ((eta (K := K) b) • R) *ᵥ gRepeated A b)

end Artform.Scores.GravityBridge.Native.RetroCertificates
