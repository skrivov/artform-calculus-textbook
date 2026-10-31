import ArtformScores.GravityBridge.PhaseDefs

/-! # Finite quadratic phase and its Weyl bridge -/

namespace Artform.Scores.GravityBridge.Statement

/-- **GAC:finite-gaussian-phase** (finite quadratic phase and its weyl bridge). -/
@[ledger "GAC:finite-gaussian-phase"]
def phaseLaw : Prop :=
  (binaryFourier.conjTranspose * binaryFourier = 1) ∧
  (binaryChirp.conjTranspose * binaryChirp = 1) ∧
  (binaryFourier * binaryX * binaryFourier.conjTranspose = binaryZ ∧
    binaryFourier * binaryZ * binaryFourier.conjTranspose = binaryX) ∧
  (binaryChirp * binaryX * binaryChirp.conjTranspose = Complex.I • (binaryX * binaryZ) ∧
    binaryChirp * binaryZ * binaryChirp.conjTranspose = binaryZ) ∧
  ((classicalFourier * classicalChirp) ^ 3 = 1) ∧
  ((binaryFourier * binaryChirp) ^ 3 = binaryGaussPhase • 1) ∧
  (((Real.sqrt 2 : ℝ) / 2 : ℂ) * (∑ x : Fin 2, Complex.I ^ (x.val ^ 2)) = binaryGaussPhase) ∧
  (Complex.normSq binaryGaussPhase = 1) ∧ (binaryGaussPhase ≠ 1) ∧
  (Complex.normSq (1 + binaryGaussPhase) = 2 + Real.sqrt 2) ∧
  (Complex.normSq (1 + binaryGaussPhase) ≠ 4)

end Artform.Scores.GravityBridge.Statement
