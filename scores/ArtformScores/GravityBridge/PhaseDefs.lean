import ArtformScores.GravityBridge.LinearDefs

/-! # A finite binary quadratic phase pilot with explicit Weyl generators -/

namespace Artform.Scores.GravityBridge

noncomputable section

def binaryFourier : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt 2 : ℝ) / 2 : ℂ) • !![1, 1; 1, -1]

def binaryChirp : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, Complex.I]

def binaryGaussPhase : ℂ := ((Real.sqrt 2 : ℝ) / 2 : ℂ) * (1 + Complex.I)

def classicalFourier : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![0, 1; 1, 0]

def classicalChirp : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![1, 0; 1, 1]

def binaryX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

def binaryZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

end

end Artform.Scores.GravityBridge
