import ArtformScores.GravityBridge.Native.CoordinateSymbol.Exceptional
import ArtformScores.GravityBridge.Native.TTCoordinates.Original
import ArtformScores.GravityBridge.Native.Retrospective.FirstContact

/-! # Original lower connection response on an angular-zero ray -/

namespace Artform.Scores.GravityBridge.Native.CoordinateSymbol

open Matrix



def pairedTT : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1 / 2, -1 / 2, 0;-1 / 2, 1 / 2, 0;0, 0, -1]

end Artform.Scores.GravityBridge.Native.CoordinateSymbol
