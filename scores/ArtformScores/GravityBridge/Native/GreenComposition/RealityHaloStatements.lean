import ArtformScores.GravityBridge.Native.GreenComposition.RealityHaloDefs

/-! # Fourier reality and the actual temporal halo duty -/

namespace Artform.Scores.GravityBridge.Native.GreenComposition.Statement

open scoped BigOperators

/-- **GAC2:fourier-reality-temporal-halo**
(fourier reality and the actual temporal halo duty). -/
@[ledger "GAC2:fourier-reality-temporal-halo"]
def realityHaloLaw : Prop :=
    (∀ (k : ℝ),
    evenScalarSeed (-k) = evenScalarSeed k ∧
    derivedVectorSeed (-k) = star (derivedVectorSeed k) ∧
    derivedVectorSeed (-k) = -derivedVectorSeed k) ∧
    (derivedVectorSeed (-1) ≠ derivedVectorSeed 1) ∧
    (haloRight 0 = 0 ∧ haloRight 1 = 0 ∧
    cutSum (operatorEdge (fun r (a b : ℚ) => if r = 2 then a * b else 0) haloLeft haloRight) 2 0
      = 1 ∧
    cutSum (operatorEdge (fun r (a b : ℚ) => if r = 2 then a * b else 0) haloLeft (fun _ => 0))
      2 0 = 0)

end Artform.Scores.GravityBridge.Native.GreenComposition.Statement
