import ArtformScores.GravityBridge.TwoCell

/-! # Full source and endpoint covector of the solved two-cell contribution -/

namespace Artform.Scores.GravityBridge.Native.GreenComposition

open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K]

def sourceMiddle (c a b j : K) : K := (a + b) / 2 + j / (4 * c)

def sourceAction (c a m b j : K) : K := c * (m - a) ^ 2 + c * (b - m) ^ 2 - j * m

def sourceEffective (c a b j : K) : K := c / 2 * (b - a) ^ 2 - j * (a + b) / 2 - j ^ 2 / (8 * c)

def inputMomentum (c a b j : K) : K := c * (b - a) + j / 2

def outputMomentum (c a b j : K) : K := c * (b - a) - j / 2

end Artform.Scores.GravityBridge.Native.GreenComposition
