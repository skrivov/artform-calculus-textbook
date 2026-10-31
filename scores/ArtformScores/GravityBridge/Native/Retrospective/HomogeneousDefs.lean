import ArtformScores.GravityBridge.Native.Retrospective.IndexedBlocks
/-! # The full original24 homogeneous connection partition and density -/
namespace Artform.Scores.GravityBridge.Native.Retrospective
open Matrix
open Full40
def assembleConnection (d e : Fin 4 → Fin 3 → ℚ) : Connection ℚ :=
  (∑ s : Fin 4, distinctInput s (d s)) + ∑ b : Fin 4, repeatedInput b (e b)
def orientedComponent (A : Connection ℚ) (mu i j : Fin 4) : ℚ :=
  ∑ a : Fin 6, wedge (basisVector i) (basisVector j) a * A mu a
def distinctCoordinates (A : Connection ℚ) (s : Fin 4) (j : Fin 3) : ℚ :=
  orientedComponent A (distinctIndices s j) (distinctIndices s (j + 1))
    (distinctIndices s (j + 2))
def repeatedCoordinates (A : Connection ℚ) (b : Fin 4) (j : Fin 3) : ℚ :=
  orientedComponent A (b.succAbove j) (b.succAbove j) b
end Artform.Scores.GravityBridge.Native.Retrospective
