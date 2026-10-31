import ArtformScores.GravityBridge.Native.NativeDetailTests.UnrestrictedDefs

/-! # Unrestricted positive real weight is not a finite normalization -/

namespace Artform.Scores.GravityBridge.Native.NativeDetailTests.Statement

open Matrix CurvedSubdivision Full40 MeasureTheory Set Filter
open scoped ENNReal

/-- **GAC2:native-unrestricted-positive-weight**
(unrestricted positive real weight is not a finite normalization). -/
@[ledger "GAC2:native-unrestricted-positive-weight"]
def unrestrictedLaw : Prop :=
    (∀ (b u : ℝ),
    Continuous (positiveRealWeight b u)) ∧
    (∀ (b u r : ℝ) (_hb : 0 < b) (_hu : 0 < u),
    1 ≤ positiveRealWeight b u r) ∧
    (∀ (b u : ℝ) (_hb : 0 < b) (_hu : 0 < u),
    (∫⁻ r : ℝ, positiveRealWeight b u r) = ∞)

end Artform.Scores.GravityBridge.Native.NativeDetailTests.Statement
