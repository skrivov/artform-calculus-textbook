import ArtformScores.GravityBridge.Companion

/-! # A prepared graph for the leading forced companion -/

namespace Artform.Scores.GravityBridge

noncomputable section

variable {K Y Z : Type*} [Field K] [AddCommGroup Y] [AddCommGroup Z] [Module K Y] [Module K Z]

def forcedJetGraph (r : K) (F : Y →ₗ[K] Z) (y : Y × Y) : Fin 4 → Z :=
  ![(r⁻¹) ^ 2 • F y.1, (r⁻¹) ^ 2 • F y.2, -r⁻¹ • F y.1, -r⁻¹ • F y.2]

end

end Artform.Scores.GravityBridge
