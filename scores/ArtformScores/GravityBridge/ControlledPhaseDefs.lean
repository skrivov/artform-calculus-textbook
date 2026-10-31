import ArtformScores.GravityBridge.Phase
/-! # Channel equivalence depends on the allowed reference -/
namespace Artform.Scores.GravityBridge
noncomputable section
open Matrix
def scalarPhaseChannel (gamma : ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (gamma • (1 : Matrix (Fin 2) (Fin 2) ℂ)) * A *
    (gamma • (1 : Matrix (Fin 2) (Fin 2) ℂ)).conjTranspose
def referencePhase (gamma : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, gamma]
def referencePhaseChannel (gamma : ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ := referencePhase gamma * A * (referencePhase gamma).conjTranspose
def referenceCircuitAmplitude (gamma : ℂ) : ℂ :=
  (binaryFourier.conjTranspose * referencePhase gamma * binaryFourier) 0 0
end
end Artform.Scores.GravityBridge
