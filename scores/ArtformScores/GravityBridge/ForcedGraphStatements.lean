import ArtformScores.GravityBridge.ForcedGraphDefs

/-! # Forced leading jets on an invariant prepared graph -/

namespace Artform.Scores.GravityBridge.Statement

/-- **GAC:forced-jet-graph** (forced leading jets on an invariant prepared graph). -/
@[ledger "GAC:forced-jet-graph"]
def forcedGraphLaw : Prop :=
  ∀ (K Y Z : Type*) [Field K] [AddCommGroup Y] [AddCommGroup Z] [Module K Y] [Module K Z]
    (r : K) (F : Y →ₗ[K] Z), r ≠ 0 →
    (∀ y : Y × Y,
      triangularJet r (F.comp (LinearMap.fst K Y Y)) 0 (y, forcedJetGraph r F y) =
        (oscillator r y, forcedJetGraph r F (oscillator r y))) ∧
    (∀ (n : ℕ) (y : Y × Y),
      (triangularJet r (F.comp (LinearMap.fst K Y Y)) 0)^[n] (y, forcedJetGraph r F y) =
        ((oscillator r)^[n] y, forcedJetGraph r F ((oscillator r)^[n] y))) ∧
    (∀ y : Y × Y, forcedJetGraph r F y = 0 ↔ F y.1 = 0 ∧ F y.2 = 0)

end Artform.Scores.GravityBridge.Statement
