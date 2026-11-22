import ArtformStages.Speed

/-!
# One speed of light along the axes and the diagonals

Finding 450 of the research ledger on a layered universe proved that light along an axis of the
torus moves at the speed `c = √(κ λ)` at long waves. Here the speed is compared across directions
(finding 456 of the ledger):

* `four_sin_sq_half_bounds` (IS1): `θ² - θ⁴ / 12 ≤ 4 sin² (θ / 2) ≤ θ²`;
* `level_isotropic` (IS2): so the level of every plane wave is the square of the length of its
  wave vector up to the fourth order, in every direction;
* `torus_diagonal_wave` (IS3): on the torus of `n` by `n` squares the diagonal wave of wave numbers
  `(p, p)` turns by `axisAngle √(2 κ λ) θ₁` per step;
* `diagonalAngle_hasDerivAt` (IS4): as a function of the length of its wave vector, that angle has
  the derivative `c` at `0`, as along an axis.
-/

open Matrix

open scoped Real

namespace Artform.Stages

/-- `x² - x⁴ / 3 ≤ sin² x` for every real `x`. -/
theorem sin_sq_lower (x : ℝ) : x ^ 2 - x ^ 4 / 3 ≤ Real.sin x ^ 2 := by
  have h1 := Real.abs_sub_sin_le x
  have h2 : |x| - |Real.sin x| ≤ |x - Real.sin x| := abs_sub_abs_le_abs_sub x (Real.sin x)
  have ha := abs_nonneg x
  have hs := abs_nonneg (Real.sin x)
  have hx2 : |x| ^ 2 = x ^ 2 := sq_abs x
  have hs2 : |Real.sin x| ^ 2 = Real.sin x ^ 2 := sq_abs _
  have h4 : x ^ 4 = |x| ^ 4 := by
    rw [show x ^ 4 = (x ^ 2) ^ 2 by ring, ← hx2]
    ring
  rw [← hx2, ← hs2, h4]
  by_cases hc : |x| ^ 2 ≤ 6
  · have hge : |x| - |x| ^ 3 / 6 ≤ |Real.sin x| := by linarith
    have hnn : 0 ≤ |x| - |x| ^ 3 / 6 := by nlinarith
    have hsq := pow_le_pow_left₀ hnn hge 2
    nlinarith [sq_nonneg (|x| ^ 3)]
  · rw [not_le] at hc
    have hp : 0 ≤ |x| ^ 2 * (|x| ^ 2 - 6) := mul_nonneg (by positivity) (by linarith)
    nlinarith [sq_nonneg |Real.sin x|]

/-- **IS1.** `θ² - θ⁴ / 12 ≤ 4 sin² (θ / 2) ≤ θ²` for every real `θ`. -/
theorem four_sin_sq_half_bounds (θ : ℝ) :
    θ ^ 2 - θ ^ 4 / 12 ≤ 4 * Real.sin (θ / 2) ^ 2 ∧ 4 * Real.sin (θ / 2) ^ 2 ≤ θ ^ 2 := by
  constructor
  · have := sin_sq_lower (θ / 2)
    nlinarith [this]
  · have := Real.sin_sq_le_sq (x := θ / 2)
    nlinarith [this]

/-- **IS2.** The level `4 - 2 cos θ₁ - 2 cos θ₂` of the plane wave of angles `θ₁` and `θ₂` lies
between `θ₁² + θ₂² - (θ₁⁴ + θ₂⁴) / 12` and `θ₁² + θ₂²`. -/
theorem level_isotropic (θ₁ θ₂ : ℝ) :
    θ₁ ^ 2 + θ₂ ^ 2 - (θ₁ ^ 4 + θ₂ ^ 4) / 12 ≤ 4 - 2 * Real.cos θ₁ - 2 * Real.cos θ₂ ∧
      4 - 2 * Real.cos θ₁ - 2 * Real.cos θ₂ ≤ θ₁ ^ 2 + θ₂ ^ 2 := by
  rw [dispersion_identity]
  obtain ⟨a1, b1⟩ := four_sin_sq_half_bounds θ₁
  obtain ⟨a2, b2⟩ := four_sin_sq_half_bounds θ₂
  constructor <;> linarith

/-- **IS3.** On the torus of `n` by `n` squares with one `κ` and one `λ`, `0 ≤ 2 κ λ ≤ 1`, the
transverse plane wave of wave numbers `(p, p)` turns by `axisAngle √(2 κ λ) θ₁` per step. -/
theorem torus_diagonal_wave (n : ℕ) [NeZero n] [Fact (1 < n)] (p : ZMod n) (κ l : ℝ)
    (h0 : 0 ≤ κ * l) (h1 : 2 * (κ * l) ≤ 1) (k : ℕ) :
    (pair ((torus n n).incidenceᵀ * diagonal (fun _ : ZMod n × ZMod n => κ) * (torus n n).incidence)
        (diagonal fun _ : (ZMod n × ZMod n) × Fin 2 => l))^[k]
      ((2 * Real.sin (axisAngle (Real.sqrt (2 * (κ * l))) (2 * π * p.val / n) / 2)) •
          ((torus n n).incidenceᵀ *ᵥ fun w => (planeWave p p w).re),
        (-Real.sin (axisAngle (Real.sqrt (2 * (κ * l))) (2 * π * p.val / n) / 2)) •
          (((torus n n).incidenceᵀ * diagonal (fun _ : ZMod n × ZMod n => κ) *
            (torus n n).incidence) *ᵥ
              ((torus n n).incidenceᵀ *ᵥ fun w => (planeWave p p w).re))) =
      ((2 * Real.sin (axisAngle (Real.sqrt (2 * (κ * l))) (2 * π * p.val / n) / 2) *
            Real.cos (2 * k * (axisAngle (Real.sqrt (2 * (κ * l))) (2 * π * p.val / n) / 2))) •
          ((torus n n).incidenceᵀ *ᵥ fun w => (planeWave p p w).re),
        Real.sin ((2 * k - 1) * (axisAngle (Real.sqrt (2 * (κ * l))) (2 * π * p.val / n) / 2)) •
          (((torus n n).incidenceᵀ * diagonal (fun _ : ZMod n × ZMod n => κ) *
            (torus n n).incidence) *ᵥ
              ((torus n n).incidenceᵀ *ᵥ fun w => (planeWave p p w).re))) := by
  apply torus_dispersion
  have hc : Real.sqrt (2 * (κ * l)) ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt h1
  have hc0 := Real.sqrt_nonneg (2 * (κ * l))
  have hs1 := Real.sin_le_one (2 * π * p.val / n / 2)
  have hs2 := Real.neg_one_le_sin (2 * π * p.val / n / 2)
  have hb1 : -1 ≤ Real.sqrt (2 * (κ * l)) * Real.sin (2 * π * p.val / n / 2) := by nlinarith
  have hb2 : Real.sqrt (2 * (κ * l)) * Real.sin (2 * π * p.val / n / 2) ≤ 1 := by nlinarith
  rw [axisAngle_dispersion _ _ hb1 hb2, Real.sq_sqrt (by linarith), Real.cos_zero]
  ring

/-- **IS4.** As a function of the length `t` of its wave vector, the diagonal wave's angle
`axisAngle (√2 c) (t / √2)` has the derivative `c` at `0`, as the axis wave's angle has. -/
theorem diagonalAngle_hasDerivAt (c : ℝ) :
    HasDerivAt (fun t => axisAngle (Real.sqrt 2 * c) (t / Real.sqrt 2)) c 0 := by
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have h1 : HasDerivAt (fun t : ℝ => t / Real.sqrt 2) (1 / Real.sqrt 2) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).div_const (Real.sqrt 2)
  have h2 : HasDerivAt (axisAngle (Real.sqrt 2 * c)) (Real.sqrt 2 * c) (0 / Real.sqrt 2) := by
    rw [zero_div]
    exact axisAngle_hasDerivAt _
  have h := h2.comp 0 h1
  rw [show Real.sqrt 2 * c * (1 / Real.sqrt 2) = c by
    rw [mul_comm (Real.sqrt 2) c, mul_assoc, mul_one_div_cancel hs, mul_one]] at h
  exact h

end Artform.Stages
