import ArtformScores.GravityBridge.RadiativeAuditDefs
/-! # Finite amplitude response and parameter freedom -/
namespace Artform.Scores.GravityBridge.Statement
/-- **GAC:finite-response-audit** (finite amplitude response and parameter freedom). -/
@[ledger "GAC:finite-response-audit"]
def radiativeAuditLaw : Prop :=
  (∀ (s : ℝ) (_hs : s ^ 2 ≤ 1 / 10000) (_hn : s ≠ 0),
    (9 / 100 : ℝ) * s ^ 2 ≤ regulatorFreeEnergy 0 s - regulatorFreeEnergy 1 s ∧
      0 < regulatorFreeEnergy 0 s - regulatorFreeEnergy 1 s) ∧
  (∀ (bt bs g : ℝ),
    bt + g ^ 2 * regulatorLoopCoefficient 0 = bs + g ^ 2 * regulatorLoopCoefficient 1 ↔
      bt - bs = -(11 / 120 : ℝ) * g ^ 2) ∧
  (∀ (b g : ℝ) (_hg : g ≠ 0),
    b + g ^ 2 * regulatorLoopCoefficient 0 ≠ b + g ^ 2 * regulatorLoopCoefficient 1)
end Artform.Scores.GravityBridge.Statement
