import ArtformScores.GravityBridge.Native.R2ExceptionDefs

/-! # Exact exclusion of the native all-zero affine-row stratum -/

namespace Artform.Scores.GravityBridge.Native.R2.Statement

/-- **GAC:r2-zero-row-exclusion** (all eight coefficient zeros are impossible off b=0). -/
@[ledger "GAC:r2-zero-row-exclusion"]
def zeroRowExclusion : Prop :=
  (∀ R a G : ℝ, 2 - 3 * a ≠ 0 →
    ¬ ((∀ i, ell a G (rowPolys R a G i) = 0) ∧
       (∀ i, remainderConst a G (rowPolys R a G i) = 0))) ∧
  (∀ R a G s : ℝ, normal a G s = 0 → 0 ≤ G → 1 / 3 < s →
    ¬ ((∀ i, ell a G (rowPolys R a G i) = 0) ∧
       (∀ i, remainderConst a G (rowPolys R a G i) = 0))) ∧
  (∀ q R a G gamma s : ℝ, q ^ 2 = 103 / 2 → gamma ^ 2 = G → normal a G s = 0 →
    q ≠ 0 → gamma ≠ 0 → 0 ≤ G → 1 / 3 < s →
    originalJ q R a gamma s = 0 → originalJ q R a (-gamma) s = 0 →
    ∃ i, ell a G (rowPolys R a G i) ≠ 0)

end Artform.Scores.GravityBridge.Native.R2.Statement
