import ArtformScores.GravityBridge.Native.CurvedSubdivision.CellDefs

/-! # Complete current cubical cell law and symmetric merge defect -/

namespace Artform.Scores.GravityBridge.Native.CurvedSubdivision.Statement

open Matrix Full40

/-- **GAC2:native-current-curved-cell**
(complete current cubical cell law and symmetric merge defect). -/
@[ledger "GAC2:native-current-curved-cell"]
def cellLaw : Prop :=
  ∀ (K : Type) [Field K] [CharZero K],
    (∀ (h b c0 s0 c1 s1 : K),
    fullOriginalMean h b c0 s0 c1 s1 0 = fiveTermComplement c0 s0 c1 s1 b) ∧
    (∀ (h b c0 s0 c1 s1 : K) (_h0 : c0 ^ 2 - s0 ^ 2 = 1),
    fullOriginalCurvature h b c0 s0 c1 s1 = -b * (c0 * s1 - s0 * c1)) ∧
    (∀ (h b c0 s0 c1 s1 : K) (_hh : h ≠ 0) (_hb : b ≠ 0)
    (_h0 : c0 ^ 2 - s0 ^ 2 = 1),
    fullOriginalCell h b c0 s0 c1 s1 =
      -b * (c0 * s1 - s0 * c1) - (2 / 101 : K) * h * b * (c0 - 1)) ∧
    (∀ (b c s : K) (_hb : b ≠ 0) (_hc : c ^ 2 - s ^ 2 = 1),
    fullOriginalCell (1 / 2) b 1 0 c s +
      fullOriginalCell (1 / 2) b c s (c ^ 2 + s ^ 2) (2 * c * s)-
      fullOriginalCell 1 b 1 0 (c ^ 2 + s ^ 2) (2 * c * s) =
      b * (c - 1) * (2 * s - (1 / 101 : K)))

end Artform.Scores.GravityBridge.Native.CurvedSubdivision.Statement
