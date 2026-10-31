import ArtformScores.GravityBridge.Native.CoordinateSymbol.ExceptionalDefs

/-! # R7 band and R8 angular exceptional domains -/

namespace Artform.Scores.GravityBridge.Native.CoordinateSymbol.Statement

open Matrix

/-- **GAC2:native-angular-exceptional-domains**
(r7 band and r8 angular exceptional domains). -/
@[ledger "GAC2:native-angular-exceptional-domains"]
def exceptionalLaw : Prop :=
    (∀ (k : Fin 3 → ℝ),
    radiusSquared k * spatialFourth k - cubicMoment k ^ 2 = angularSquares k) ∧
    (∀ (k : Fin 3 → ℝ) (_hR : radiusSquared k ≠ 0),
    radiusSquared k * angularPsi k = angularSquares k) ∧
    (∀ (k : Fin 3 → ℝ),
    0 ≤ angularSquares k) ∧
    (∀ (k : Fin 3 → ℝ) (_hR : radiusSquared k ≠ 0),
    angularPsi k = 0 ↔
      (k 0 = 0 ∨ k 1 = 0 ∨ k 0 = k 1) ∧
      (k 0 = 0 ∨ k 2 = 0 ∨ k 0 = k 2) ∧
      (k 1 = 0 ∨ k 2 = 0 ∨ k 1 = k 2)) ∧
    (fixedBand ![3, 3, 0] ∧ fixedBand ![3, -3, 0] ∧
    angularPsi ![3, 3, 0] = 0 ∧ angularPsi ![3, -3, 0] = 162)

end Artform.Scores.GravityBridge.Native.CoordinateSymbol.Statement
