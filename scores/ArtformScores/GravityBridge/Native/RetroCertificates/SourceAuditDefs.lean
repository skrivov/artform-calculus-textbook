import ArtformScores.GravityBridge.Native.TTCross.Full24

/-! # Selected native sources do not certify the full inverse -/

namespace Artform.Scores.GravityBridge.Native.RetroCertificates

open Matrix Full40 TTCross Retrospective

variable {K : Type*} [Field K] [CharZero K]

def sourceOnlyReturn (A : Connection K) : Connection K :=
  gAssemble (fun s => distinctH s *ᵥ gDistinct A s) (fun _ => 0)

end Artform.Scores.GravityBridge.Native.RetroCertificates
