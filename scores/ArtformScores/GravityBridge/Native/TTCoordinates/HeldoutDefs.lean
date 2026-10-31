import ArtformScores.GravityBridge.Native.TemporalWitness

/-! # A second off-axis native temporal forcing test -/

namespace Artform.Scores.GravityBridge.Native.TTCoordinates

open Matrix



def heldoutMomentum : Fin 3 → ℚ := ![1, 2, 4]

def heldoutU : Fin 3 → ℚ := ![2, -1, 0]

def heldoutV : Fin 3 → ℚ := ![4, 8, -5]

def heldoutPolarization : Matrix (Fin 3) (Fin 3) ℚ :=
  !![68 / 105, -74 / 105, 20 / 105;-74 / 105, -43 / 105, 40 / 105;20 / 105, 40 / 105, -25 / 105]

def heldoutDyad : Matrix (Fin 3) (Fin 3) ℚ :=
  fun i j => heldoutU i * heldoutU j / 5 - heldoutV i * heldoutV j / 105

end Artform.Scores.GravityBridge.Native.TTCoordinates
