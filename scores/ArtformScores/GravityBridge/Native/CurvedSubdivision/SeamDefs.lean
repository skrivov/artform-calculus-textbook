import ArtformScores.GravityBridge.Native.CurvedSubdivision.Words

/-! # A fused coarse link does not fix the fine seam -/

namespace Artform.Scores.GravityBridge.Native.CurvedSubdivision

open Matrix Full40

variable {K : Type*} [Field K] [CharZero K]

def rationalBoost (q : K) : Frame K := boost (qC q) (qS q)

def coarseLinkReport (x : K × K) : K := x.1 * x.2

def fineSeamLink (x : K × K) : Frame K := rationalBoost x.1

end Artform.Scores.GravityBridge.Native.CurvedSubdivision
