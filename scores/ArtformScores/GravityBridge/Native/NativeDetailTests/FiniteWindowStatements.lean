import ArtformScores.GravityBridge.Native.NativeDetailTests.FiniteWindowDefs

/-! # Bounded native detail interval has explicit finite positive mass -/

namespace Artform.Scores.GravityBridge.Native.NativeDetailTests.Statement

open Matrix CurvedSubdivision Full40 MeasureTheory Set Filter
open scoped ENNReal

/-- **GAC2:native-finite-detail-weight**
(bounded native detail interval has explicit finite positive mass). -/
@[ledger "GAC2:native-finite-detail-weight"]
def finiteWindowLaw : Prop :=
    (∀ (b u r r0 L : ℝ) (_hb : 0 < b) (_hu : 0 < u) (_hL : 0 ≤ L)
    (_hc : Real.cosh r0 = stationaryC (Real.cosh u) (Real.sinh u))
    (_hs : Real.sinh r0 = stationaryS (Real.cosh u) (Real.sinh u)) (_hr : |r - r0| ≤ L),
    positiveRealWeight b u r ≤ boundedWeightCeiling b u L) ∧
    (∀ (b u r0 L : ℝ) (_hb : 0 < b) (_hu : 0 < u) (_hL : 0 ≤ L)
    (_hc : Real.cosh r0 = stationaryC (Real.cosh u) (Real.sinh u))
    (_hs : Real.sinh r0 = stationaryS (Real.cosh u) (Real.sinh u)),
    (∫⁻ r in Icc (r0 - L) (r0 + L), positiveRealWeight b u r) ≤
      boundedWeightCeiling b u L * ENNReal.ofReal (2 * L)) ∧
    (∀ (b u r0 L : ℝ) (_hb : 0 < b) (_hu : 0 < u) (_hL : 0 < L)
    (_hc : Real.cosh r0 = stationaryC (Real.cosh u) (Real.sinh u))
    (_hs : Real.sinh r0 = stationaryS (Real.cosh u) (Real.sinh u)),
    0 < (∫⁻ r in Icc (r0 - L) (r0 + L), positiveRealWeight b u r) ∧
      (∫⁻ r in Icc (r0 - L) (r0 + L), positiveRealWeight b u r) < ∞)

end Artform.Scores.GravityBridge.Native.NativeDetailTests.Statement
