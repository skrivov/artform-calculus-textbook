import ArtformScores.GravityBridge.Native.R2PhaseDefs

/-! # Broader normal-chart exclusion and guarded original phase transfer -/

namespace Artform.Scores.GravityBridge.Native.R2.Statement

/-- **GAC:r2-norm-chart** (the odd norm equation excludes the shared factor). -/
@[ledger "GAC:r2-norm-chart"]
def normChart : Prop :=
  (∀ q R a gamma s : ℝ,
    phaseNorm q R a gamma s - phaseNorm q R a (-gamma) s =
      16 * q * R * gamma * (2 * q ^ 2 * (a * s + (2 - 3 * a)) ^ 2 -
        s * (3 - s) * evenDelta q R a (gamma ^ 2))) ∧
  (∀ q R a G s : ℝ, q ^ 2 = 103 / 2 → 0 < R → 0 ≤ G → 0 < s → normal a G s = 0 →
    s * (3 - s) * evenDelta q R a G = 2 * q ^ 2 * (a * s + (2 - 3 * a)) ^ 2 →
    2 - 3 * a ≠ 0 ∧
      ¬ ((∀ i, ell a G (rowPolys R a G i) = 0) ∧
        (∀ i, remainderConst a G (rowPolys R a G i) = 0))) ∧
  (∀ q R a gamma s : ℝ, q ^ 2 = 103 / 2 → 0 < R → 0 < s → gamma ≠ 0 →
    normal a (gamma ^ 2) s = 0 → phaseNorm q R a gamma s = 0 →
    phaseNorm q R a (-gamma) s = 0 → originalJ q R a gamma s = 0 →
    originalJ q R a (-gamma) s = 0 → ∃ i, ell a (gamma ^ 2) (rowPolys R a (gamma ^ 2) i) ≠ 0) ∧
  (∀ R a G s u : ℝ, 2 - 3 * a ≠ 0 → normal a G s = 0 → normal a G u = 0 →
    (∀ i, rows R a G s i = 0) → (∀ i, rows R a G u i = 0) → s = u)

/-- **GAC:r2-phase-transfer** (the original phase inverse with all clearing guards). -/
@[ledger "GAC:r2-phase-transfer"]
def phaseTransfer : Prop :=
  (∀ q R a gamma : ℝ,
    Complex.normSq (phaseP q R a gamma) - Complex.normSq (phaseQ q a gamma) =
      phaseDelta q R a gamma) ∧
  (∀ q R a gamma : ℝ,
    star (phaseP q R a gamma) * phaseL q R -
      phaseQ q a gamma * star (phaseL q R) = phaseT q R a gamma) ∧
  (∀ (q R a gamma H : ℝ) (V : ℂ), phaseDelta q R a gamma ≠ 0 →
    ((phaseP q R a gamma * V + phaseQ q a gamma * star V =
      (-2 * H : ℝ) * phaseL q R) ↔ V = regularV q R a gamma H)) ∧
  (∀ q R a gamma K H s : ℝ, K ^ 2 = s → K * H = a * s + (2 - 3 * a) → K ≠ 0 →
    phaseDelta q R a gamma ≠ 0 →
    (Complex.normSq (regularV q R a gamma H) = R * (3 - s) ↔ phaseNorm q R a gamma s = 0)) ∧
  (∀ (q R a gamma K H s : ℝ) (V : ℂ), K ^ 2 = s → K * H = a * s + (2 - 3 * a) →
    K ≠ 0 → s ≠ 0 → 3 - s ≠ 0 → 1 - zeta a gamma ≠ 0 → phaseDelta q R a gamma ≠ 0 →
    (((phaseP q R a gamma * V + phaseQ q a gamma * star V =
        (-2 * H : ℝ) * phaseL q R) ∧
      Complex.normSq V = R * (3 - s) ∧ traceResidual q R a gamma s = 0) ↔
    (V = regularV q R a gamma H ∧ phaseNorm q R a gamma s = 0 ∧
      originalJ q R a gamma s = 0)))

end Artform.Scores.GravityBridge.Native.R2.Statement
