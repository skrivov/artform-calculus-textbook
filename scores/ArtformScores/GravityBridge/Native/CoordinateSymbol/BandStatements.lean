import ArtformScores.GravityBridge.Native.CoordinateSymbol.BandDefs

/-! # Compact reflected native band and both light-cone inverse guards -/

namespace Artform.Scores.GravityBridge.Native.CoordinateSymbol.Statement

open Matrix

/-- **GAC2:native-reflected-band-inverse-guards**
(compact reflected native band and both light-cone inverse guards). -/
@[ledger "GAC2:native-reflected-band-inverse-guards"]
def bandLaw : Prop :=
    (∀ (k : Fin 3 → ℝ),
    fixedBand (-k) ↔ fixedBand k) ∧
    (fixedBand ![1, 2, 3] ∧ fixedBand ![1, 2, 4]) ∧
    (∀ (k : Fin 3 → ℝ) (_hk : fixedBand k),
    3 ≤ Real.sqrt (radiusSquared k) ∧ Real.sqrt (radiusSquared k) ≤ 5 ∧
      ∀ i, |k i| ≤ (9 / 10 : ℝ) * Real.sqrt (radiusSquared k)) ∧
    (IsCompact {k : Fin 3 → ℝ | fixedBand k}) ∧
    (∀ (k : Fin 3 → ℝ) (ρ ε : ℝ)
    (_hR : ρ ^ 2 = radiusSquared k) (_hk : ∀ i, |k i| ≤ (1 - ε) * ρ),
    |cubicMoment k| ≤ (1 - ε) * ρ ^ 3) ∧
    (∀ (k : Fin 3 → ℝ) (ρ ε : ℝ) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hbound : |cubicMoment k| ≤ (1 - ε) * ρ ^ 3),
    lightConeDiscriminant 1 ρ k ≤ -ε ^ 2 * ρ ^ 6 / 4 ∧
    lightConeDiscriminant (-1) ρ k ≤ -ε ^ 2 * ρ ^ 6 / 4) ∧
    (∀ (k : Fin 3 → ℝ) (_hk : fixedBand k),
    simpleDiscriminant
      (componentSquares (lightConeMomentum 1 (Real.sqrt (radiusSquared k)) k))
      (lightConeMomentum 1 (Real.sqrt (radiusSquared k)) k) ≤ -729 / 400 ∧
    simpleDiscriminant
      (componentSquares (lightConeMomentum (-1) (Real.sqrt (radiusSquared k)) k))
      (lightConeMomentum (-1) (Real.sqrt (radiusSquared k)) k) ≤ -729 / 400) ∧
    (∀ (k : Fin 3 → ℝ) (_hk : fixedBand k),
    (nativeUpperSymbol (lightConeMomentum 1 (Real.sqrt (radiusSquared k)) k) *
      nativeCoordinateInverse (lightConeMomentum 1 (Real.sqrt (radiusSquared k)) k) = 1 ∧
     nativeCoordinateInverse (lightConeMomentum 1 (Real.sqrt (radiusSquared k)) k) *
      nativeUpperSymbol (lightConeMomentum 1 (Real.sqrt (radiusSquared k)) k) = 1) ∧
    (nativeUpperSymbol (lightConeMomentum (-1) (Real.sqrt (radiusSquared k)) k) *
      nativeCoordinateInverse (lightConeMomentum (-1) (Real.sqrt (radiusSquared k)) k) = 1 ∧
     nativeCoordinateInverse (lightConeMomentum (-1) (Real.sqrt (radiusSquared k)) k) *
      nativeUpperSymbol (lightConeMomentum (-1) (Real.sqrt (radiusSquared k)) k) = 1))

end Artform.Scores.GravityBridge.Native.CoordinateSymbol.Statement
