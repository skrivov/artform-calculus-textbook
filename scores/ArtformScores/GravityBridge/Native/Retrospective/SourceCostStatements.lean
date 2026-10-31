import ArtformScores.GravityBridge.Native.Retrospective.SourceCostDefs
/-! # The actual solved source and a declared one-multiplication lower bound -/
namespace Artform.Scores.GravityBridge.Native.Retrospective.Statement
open Matrix
/-- **GAC2:selected-source-work-audit**
(the actual solved source and a declared one-multiplication lower bound). -/
@[ledger "GAC2:selected-source-work-audit"]
def sourceCostLaw : Prop :=
    (∀ (z : ℚ),
    schurCovector z = ![-101 * z / 103, -101 * z / 103, 0]) ∧
    (∀ (z : ℚ),
    oneMultiplySchur z = schurCovector z) ∧
    (¬∃ w : ZeroCostWire,
    ∀ z : ℚ, wireValue w z = oneMultiplySchur z 0)
end Artform.Scores.GravityBridge.Native.Retrospective.Statement
