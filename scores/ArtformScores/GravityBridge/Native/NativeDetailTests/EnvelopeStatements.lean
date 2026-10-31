import ArtformScores.GravityBridge.Native.NativeDetailTests.EnvelopeDefs

/-! # Original source envelope retains its derivative and susceptibility -/

namespace Artform.Scores.GravityBridge.Native.NativeDetailTests.Statement

open Matrix CurvedSubdivision Full40 MeasureTheory Set Filter
open scoped ENNReal

/-- **GAC2:native-source-envelope-contacts**
(original source envelope retains its derivative and susceptibility). -/
@[ledger "GAC2:native-source-envelope-contacts"]
def envelopeLaw : Prop :=
    (∀ (b u r0 j : ℝ),
    HasDerivAt (sourceRapidity b u r0) (sourceSlope b u j) j) ∧
    (∀ (b u r0 j : ℝ) (_hb : b ≠ 0) (_hu : 0 < u)
    (_hc : Real.cosh r0 = stationaryC (Real.cosh u) (Real.sinh u))
    (_hs : Real.sinh r0 = stationaryS (Real.cosh u) (Real.sinh u)),
    literalTwoChildAction b u (sourceRapidity b u r0 j) - j * sourceRapidity b u r0 j =
      nativeEnvelope b u r0 j) ∧
    (∀ (b u r0 j : ℝ) (_hb : 0 < b) (_hu : 0 < u),
    HasDerivAt (nativeEnvelope b u r0) (-sourceRapidity b u r0 j) j) ∧
    (∀ (b u r0 j : ℝ),
    HasDerivAt (fun x => -sourceRapidity b u r0 x)
      ((Real.sqrt (1 + (j / (b * detailRoot u)) ^ 2))⁻¹ / (b * detailRoot u)) j) ∧
    (∀ (b u j : ℝ) (_hb : 0 < b) (_hu : 0 < u),
    0 < (Real.sqrt (1 + (j / (b * detailRoot u)) ^ 2))⁻¹ / (b * detailRoot u)) ∧
    (∀ (b u r0 : ℝ) (_hb : 0 < b) (_hu : 0 < u),
    HasDerivAt (rawEnvelope b u r0) 0 0 ∧
      HasDerivAt (nativeEnvelope b u r0) (-r0) 0) ∧
    (∀ (b u : ℝ) (_hb : 0 < b) (_hu : 0 < u),
    ∃ r0 : ℝ, Real.cosh r0 = stationaryC (Real.cosh u) (Real.sinh u) ∧
      Real.sinh r0 = stationaryS (Real.cosh u) (Real.sinh u) ∧ r0 < 0 ∧
      HasDerivAt (rawEnvelope b u r0) 0 0 ∧
      HasDerivAt (nativeEnvelope b u r0) (-r0) 0 ∧ 0 < -r0)

end Artform.Scores.GravityBridge.Native.NativeDetailTests.Statement
