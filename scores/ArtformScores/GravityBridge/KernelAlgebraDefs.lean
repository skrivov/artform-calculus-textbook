import ArtformScores.GravityBridge.KernelDefs

/-! # Normalized identity for a finite weighted boundary kernel -/

namespace Artform.Scores.GravityBridge

noncomputable section

def weightedUnit {X K : Type*} [Field K] (mu : X → K) : BoundaryKernel X X K := by
  classical
  exact fun x y => if x = y then (mu y)⁻¹ else 0

end

end Artform.Scores.GravityBridge
