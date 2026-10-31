import ArtformScores.GravityBridge.ControlledPhaseDefs
/-! # Channel equivalence depends on the allowed reference -/
namespace Artform.Scores.GravityBridge.Statement
open Matrix
/-- **GAC:controlled-phase-equivalence** (channel equivalence depends on the allowed reference). -/
@[ledger "GAC:controlled-phase-equivalence"]
def controlledPhaseLaw : Prop :=
  (∀ (gamma : ℂ) (_hg : Complex.normSq gamma = 1)
    (A : Matrix (Fin 2) (Fin 2) ℂ),
    scalarPhaseChannel gamma A = A) ∧
  (∀ (gamma : ℂ) (_hg : gamma ≠ 1),
    referencePhaseChannel gamma binaryX ≠ binaryX) ∧
  (∀ (gamma : ℂ) (_hg : Complex.normSq gamma = 1),
    (referencePhase gamma).conjTranspose * referencePhase gamma = 1) ∧
  (∀ (A : Matrix (Fin 2) (Fin 2) ℂ),
    (binaryFourier * binaryChirp) ^ 3 * A *
      ((binaryFourier * binaryChirp) ^ 3).conjTranspose = A) ∧
  (∀ (gamma : ℂ),
    referenceCircuitAmplitude gamma = (1 + gamma) / 2) ∧
  (Complex.normSq ((1 + binaryGaussPhase) / 2) = (2 + Real.sqrt 2) / 4 ∧
    Complex.normSq ((1 + binaryGaussPhase) / 2) ≠ 1)
end Artform.Scores.GravityBridge.Statement
