import ArtformScores.GravityBridge.Native.R8Defs

/-! # Scoped native leading inverse, locality, remainder and domain tests -/

namespace Artform.Scores.GravityBridge.Native.R8.Statement

/-- **GAC:r8-angular-conditioning** (explicit distance cost for the native leading scalar). -/
@[ledger "GAC:r8-angular-conditioning"]
def angularConditioning : Prop :=
  (∀ k : Fin 3 → ℝ, radialSq k ≠ 0 →
    (∑ i, (projectedSquare k i) ^ 2) = angularDefect k ∧
      radialSq k * angularDefect k = pairNumerator k) ∧
  (∀ k : Fin 3 → ℝ, 0 < radialSq k → ∃ m b, m ≠ 0 ∧ (∃ i, b i = true) ∧
    radialSq k * rayError k m b ≤ 36 * angularDefect k) ∧
  (∀ (k : Fin 3 → ℝ) (delta : ℝ), 0 < radialSq k → RaySeparated k delta →
    radialSq k * delta ^ 2 ≤ 36 * angularDefect k) ∧
  (1 / (24 * 101) : ℝ) < (metricCoefficient : ℝ) ∧
  (∀ (k : Fin 3 → ℝ) (delta : ℝ), 0 < radialSq k → 0 < delta → RaySeparated k delta →
    leadingScalar k ≠ 0 ∧ |(leadingScalar k)⁻¹| ≤ 87264 / (radialSq k * delta ^ 2))

/-- **GAC:r8-leading-local-inverse** (no polynomial-symbol inverse of the leading scalar). -/
@[ledger "GAC:r8-leading-local-inverse"]
def leadingLocalInverse : Prop :=
  (∀ (c a b : ℝ) (P : Polynomial ℝ), a < b →
    ¬ ∀ t ∈ Set.Ioo a b, c * t ^ 4 * P.eval t = 1) ∧
  (∀ (c : ℂ) (a b : ℝ) (P : Polynomial ℂ), a < b →
    ¬ ∀ t ∈ Set.Ioo a b, c * (t : ℂ) ^ 4 * P.eval (t : ℂ) = 1) ∧
  (∀ P : Polynomial ℂ, ¬ ∀ t ∈ Set.Ioo (1 : ℝ) 2,
    (leadingScalar (fun i => t * (![1, 2, 3] : Fin 3 → ℝ) i) : ℂ) * P.eval (t : ℂ) = 1)

/-- **GAC:r8-gap-remainder** (finite-h inverse conditional on the actual remainder budget). -/
@[ledger "GAC:r8-gap-remainder"]
def gapRemainder : Prop :=
  ∀ (k : Fin 3 → ℝ) (delta h M D : ℝ), 0 < radialSq k → 0 < delta → RaySeparated k delta →
    0 < h → 0 ≤ M → M * h ≤ radialSq k * delta ^ 2 / 174528 →
    |D - h ^ 4 * leadingScalar k| ≤ M * h ^ 5 →
    D ≠ 0 ∧ |D⁻¹| ≤ 174528 / (h ^ 4 * radialSq k * delta ^ 2)

/-- **GAC:r8-nonuniform-domain** (a fixed-annulus ray sequence and radial scaling). -/
@[ledger "GAC:r8-nonuniform-domain"]
def nonuniformDomain : Prop :=
  (∀ e : ℝ, 0 < e → e ≤ 1 →
    (2 ≤ radialSq (approachingRay e) ∧ radialSq (approachingRay e) ≤ 5) ∧
      (0 < angularDefect (approachingRay e) ∧ angularDefect (approachingRay e) ≤ e ^ 2)) ∧
  (∀ n : ℕ, let e : ℝ := 1 / (n + 1 : ℝ)
    2 ≤ radialSq (approachingRay e) ∧ radialSq (approachingRay e) ≤ 5 ∧
      leadingScalar (approachingRay e) ≠ 0 ∧
      (n + 1 : ℝ) ^ 2 / (metricCoefficient : ℝ) ≤ |(leadingScalar (approachingRay e))⁻¹|) ∧
  (¬ ∃ M : ℝ, ∀ n : ℕ, |(leadingScalar (approachingRay (1 / (n + 1 : ℝ))))⁻¹| ≤ M) ∧
  (∀ (k : Fin 3 → ℝ) (t : ℝ), leadingScalar (fun i => t * k i) = t ^ 4 * leadingScalar k)

end Artform.Scores.GravityBridge.Native.R8.Statement
