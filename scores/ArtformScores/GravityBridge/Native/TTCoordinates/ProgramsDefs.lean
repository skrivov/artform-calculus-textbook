import ArtformScores.GravityBridge.Native.TTCoordinates.Original

/-! # Matched exact programs for the original temporal forcing -/

namespace Artform.Scores.GravityBridge.Native.TTCoordinates

open Matrix



inductive TTExpr where
  | read (i j : Fin 3)
  | scale (c : ℚ) (e : TTExpr)
  | add (e f : TTExpr)

def evalTTExpr (q : Matrix (Fin 3) (Fin 3) ℚ) : TTExpr → ℚ
  | .read i j => q i j
  | .scale c e => c * evalTTExpr q e
  | .add e f => evalTTExpr q e + evalTTExpr q f

def ttScales : TTExpr → ℕ
  | .read _ _ => 0
  | .scale _ e => 1 + ttScales e
  | .add e f => ttScales e + ttScales f

def ttAdds : TTExpr → ℕ
  | .read _ _ => 0
  | .scale _ e => ttAdds e
  | .add e f => 1 + ttAdds e + ttAdds f

def literalForcingProgram : TTExpr :=
  .add (.add (.scale (-7 / 101) (.read 0 0)) (.scale (-14 / 101) (.read 1 1)))
    (.scale (-21 / 101) (.read 2 2))

def contractedForcingProgram : TTExpr := .scale (84 / 505) (.read 1 2)

end Artform.Scores.GravityBridge.Native.TTCoordinates
