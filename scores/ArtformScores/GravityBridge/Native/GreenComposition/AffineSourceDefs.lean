import ArtformScores.GravityBridge.Native.GreenComposition.SourceBoundary

/-! # Affine boundary composition retains independent source contacts -/

namespace Artform.Scores.GravityBridge.Native.GreenComposition

open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K]

def boundaryStep (c j : K) (x : K × K) : K × K :=
  (x.1 + (x.2 - j / 2) / c, x.2 - j)

def composeEffective (c a b j l : K) : K :=
  c / 4 * (b - a) ^ 2 - (j * (3 * a + b) + l * (a + 3 * b)) / 4 - (j ^ 2 + l ^ 2) / (8 * c) - (j
    + l) ^ 2 / (16 * c)

def composeMiddle (c a b j l : K) : K := (a + b) / 2 + (j + l) / (4 * c)

end Artform.Scores.GravityBridge.Native.GreenComposition
