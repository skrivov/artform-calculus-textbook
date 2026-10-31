import ArtformScores.GravityBridge.MatterTransferDefs
/-! # Clock backreaction and the finite Gaussian domain -/
namespace Artform.Scores.GravityBridge.Statement
open MeasureTheory
/-- **GAC:matter-transfer-obligations** (clock backreaction and the finite gaussian domain). -/
@[ledger "GAC:matter-transfer-obligations"]
def matterTransferLaw : Prop :=
  (∀ (coupling : ℝ) (_hc : coupling ≠ 0),
    ¬ HasDerivAt (fun N : ℝ => coupling / (2 * N)) 0 1) ∧
  (∀ (coupling c : ℝ),
    HasDerivAt (fun N : ℝ => coupling / (2 * N) + c * (N - 1)) (c - coupling / 2) 1) ∧
  (∀ (coupling c : ℝ),
    HasDerivAt (fun N : ℝ => coupling / (2 * N) + c * (N - 1)) 0 1 ↔ c = coupling / 2) ∧
  (¬ Integrable (loopGaussianBlock 1 1 2))
end Artform.Scores.GravityBridge.Statement
