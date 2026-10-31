import ArtformScores.GravityBridge.Native.TTCoordinates.Original

/-! # Original metric momentum and velocity current factors -/

namespace Artform.Scores.GravityBridge.Native.NativeCurrent

open Matrix

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def tensorDot (x y : Matrix (Fin 3) (Fin 3) ℚ) : ℚ := ∑ i, ∑ j, x i j * y i j

def coframeCut (f u g v : Matrix (Fin 3) (Fin 3) ℚ) : ℚ :=
  -(tensorDot f v - tensorDot g u)

def metricMomentumCut (q p r s : Matrix (Fin 3) (Fin 3) ℚ) : ℚ :=
  -(tensorDot q s - tensorDot r p) / 2

def metricVelocityCut (q v r w : Matrix (Fin 3) (Fin 3) ℚ) : ℚ :=
  -(tensorDot q w - tensorDot r v) / 4

end Artform.Scores.GravityBridge.Native.NativeCurrent
