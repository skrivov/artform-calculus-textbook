import ArtformScores.GravityBridge.CompanionDefs

/-! # Triangular companion readout and graph invariance -/

namespace Artform.Scores.GravityBridge.Statement

/-- **GAC:companion-readout** (triangular leading readout differs from full invariance). -/
@[ledger "GAC:companion-readout"]
def companionReadout : Prop :=
  ∀ (K Y Z : Type*) [CommRing K] [AddCommGroup Y] [AddCommGroup Z] [Module K Y] [Module K Z]
    (r : K) (F : (Y × Y) →ₗ[K] Z) (D : (Fin 4 → Z) →ₗ[K] Z),
    (∀ (n : ℕ) (y : Y × Y) (z : Fin 4 → Z),
      (((triangularJet r F D)^[n]) (y, z)).1 = ((oscillator r)^[n]) y) ∧
    ((∀ y, triangularJet r F D (y, 0) = (oscillator r y, 0)) ↔ ∀ y, F y = 0)

end Artform.Scores.GravityBridge.Statement
