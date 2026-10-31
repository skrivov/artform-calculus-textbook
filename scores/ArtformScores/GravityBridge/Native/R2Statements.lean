import ArtformScores.GravityBridge.Native.R2Defs

/-! # Original R2 trace reduction and retained denominator guards -/

namespace Artform.Scores.GravityBridge.Native.R2.Statement

/-- **GAC:r2-trace-reduction** (the original four rows and every monic remainder). -/
@[ledger "GAC:r2-trace-reduction"]
def traceReduction : Prop :=
  (∀ q R a G gamma s : ℝ, q ^ 2 = 103 / 2 → gamma ^ 2 = G → normal a G s = 0 →
    originalJ q R a gamma s =
      (rows R a G s 0 : ℂ) + Complex.I * q * rows R a G s 1 +
        gamma * (q * rows R a G s 2 + Complex.I * rows R a G s 3)) ∧
  (∀ (R a G : ℝ) (i : Fin 4), (rowPolys R a G i).natDegree ≤ 3) ∧
  (∀ (P : Polynomial ℝ), P.natDegree ≤ 3 → ∀ a G s : ℝ,
    P.eval s - (ell a G P * s + remainderConst a G P) =
      normal a G s * (P.coeff 3 * s + P.coeff 2 -
        (5 - 8 * a + 6 * G) * P.coeff 3)) ∧
  (∀ q R a G gamma s : ℝ, q ^ 2 = 103 / 2 → gamma ^ 2 = G → normal a G s = 0 →
    q ≠ 0 → gamma ≠ 0 →
    ((originalJ q R a gamma s = 0 ∧ originalJ q R a (-gamma) s = 0) ↔
      ∀ i, ell a G (rowPolys R a G i) * s + remainderConst a G (rowPolys R a G i) = 0)) ∧
  (∀ q R a gamma s : ℝ, s ≠ 0 → 3 - s ≠ 0 → 1 - zeta a gamma ≠ 0 →
    phaseDelta q R a gamma ≠ 0 →
    (traceResidual q R a gamma s = 0 ↔ originalJ q R a gamma s = 0))

end Artform.Scores.GravityBridge.Native.R2.Statement
