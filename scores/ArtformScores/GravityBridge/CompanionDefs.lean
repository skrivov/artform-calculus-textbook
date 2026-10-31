import ArtformScores.GravityBridge.MemoryDefs

/-! # Leading companion readout with forced auxiliary jets -/

namespace Artform.Scores.GravityBridge

variable {K Y Z : Type*} [CommRing K] [AddCommGroup Y] [AddCommGroup Z]
  [Module K Y] [Module K Z]

def oscillator (r : K) (y : Y × Y) : Y × Y := (y.2, -r • y.1)

def triangularJet (r : K) (F : (Y × Y) →ₗ[K] Z) (D : (Fin 4 → Z) →ₗ[K] Z)
    (p : (Y × Y) × (Fin 4 → Z)) : (Y × Y) × (Fin 4 → Z) :=
  (oscillator r p.1, ![p.2 1, p.2 2, p.2 3, F p.1 + D p.2])

end Artform.Scores.GravityBridge
