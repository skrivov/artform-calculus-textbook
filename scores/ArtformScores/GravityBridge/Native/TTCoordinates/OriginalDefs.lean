import ArtformScores.GravityBridge.Native.TemporalWitness

/-! # The complete original TT plane and temporal witness -/

namespace Artform.Scores.GravityBridge.Native.TTCoordinates

open Matrix



def nativeU : Fin 3 → ℚ := ![2, -1, 0]

def nativeV : Fin 3 → ℚ := ![3, 6, -5]

def dyadPolarization : Matrix (Fin 3) (Fin 3) ℚ :=
  fun i j => nativeU i * nativeU j / 5 - nativeV i * nativeV j / 70

def frobeniusSquare (q : Matrix (Fin 3) (Fin 3) ℚ) : ℚ := ∑ i, ∑ j, (q i j) ^ 2

def parametricTT (x y : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  !![x, -(10 * x + 13 * y) / 4, (8 * x + 13 * y) / 6;
    -(10 * x + 13 * y) / 4, y, (10 * x + 5 * y) / 12;
    (8 * x + 13 * y) / 6, (10 * x + 5 * y) / 12, -x - y]

end Artform.Scores.GravityBridge.Native.TTCoordinates
