import ArtformStages.Dispersion

/-!
# The speed of light

Along an axis of the torus, light of angle `θ` turns by `ω (θ) = 2 arcsin (c sin (θ / 2))` per
step, with `c = √(κ λ)`; `ω` has the derivative `c` at `θ = 0`, so long waves move at `c` cells per
step (finding 450 of the research ledger on a layered universe):

* `axisAngle_zero`, `axisAngle_hasDerivAt` (SP1): `ω 0 = 0` and `ω' 0 = c`;
* `axisAngle_dispersion` (SP2): `ω` meets the dispersion of finding 447 along an axis;
* `torus_axis_wave` (SP3): on the torus with one `κ` and one `λ`, `0 ≤ κ λ ≤ 1`, the transverse
  plane wave of wave numbers `(p, 0)` turns by `ω (θ₁)` per step.
-/

open Matrix

open scoped Real

namespace Artform.Stages

/-- The angle per step of light of angle `θ` along an axis: `2 arcsin (c sin (θ / 2))`. -/
noncomputable def axisAngle (c θ : ℝ) : ℝ := 2 * Real.arcsin (c * Real.sin (θ / 2))

/-- SP1. Light of angle `0` does not turn. -/
theorem axisAngle_zero (c : ℝ) : axisAngle c 0 = 0 := by
  simp [axisAngle]

/-- SP1. The angle per step has the derivative `c` at `θ = 0`: long waves move at `c` cells per
step. -/
theorem axisAngle_hasDerivAt (c : ℝ) : HasDerivAt (axisAngle c) c 0 := by
  have h1 : HasDerivAt (fun θ : ℝ => θ / 2) (1 / 2) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).div_const 2
  have hg : HasDerivAt (fun θ : ℝ => c * Real.sin (θ / 2)) (c * (Real.cos (0 / 2) * (1 / 2))) 0 :=
    h1.sin.const_mul c
  have ha : HasDerivAt Real.arcsin (1 / Real.sqrt (1 - (c * Real.sin (0 / 2)) ^ 2))
      (c * Real.sin (0 / 2)) :=
    Real.hasDerivAt_arcsin (by simp) (by simp)
  have h := (ha.comp 0 hg).const_mul 2
  have e : 2 * (1 / Real.sqrt (1 - (c * Real.sin (0 / 2)) ^ 2) * (c * (Real.cos (0 / 2) * (1 / 2))))
      = c := by
    simp
    ring
  rw [e] at h
  exact h

/-- SP2. The angle per step meets the dispersion of finding 447 along an axis. -/
theorem axisAngle_dispersion (c θ : ℝ) (h1 : -1 ≤ c * Real.sin (θ / 2))
    (h2 : c * Real.sin (θ / 2) ≤ 1) :
    4 * Real.sin (axisAngle c θ / 2) ^ 2 = c ^ 2 * (4 - 2 * Real.cos θ - 2 * Real.cos 0) := by
  rw [axisAngle, show 2 * Real.arcsin (c * Real.sin (θ / 2)) / 2 =
      Real.arcsin (c * Real.sin (θ / 2)) by ring, Real.sin_arcsin h1 h2, dispersion_identity]
  simp
  ring

/-- SP3. On the torus with one `κ` and one `λ`, `0 ≤ κ λ ≤ 1`, the transverse plane wave of wave
numbers `(p, 0)` turns by `axisAngle √(κ λ) θ₁` per step. -/
theorem torus_axis_wave (n m : ℕ) [NeZero n] [NeZero m] [Fact (1 < n)] [Fact (1 < m)]
    (p : ZMod n) (κ l : ℝ) (h0 : 0 ≤ κ * l) (h1 : κ * l ≤ 1) (k : ℕ) :
    (pair ((torus n m).incidenceᵀ * diagonal (fun _ : ZMod n × ZMod m => κ) * (torus n m).incidence)
        (diagonal fun _ : (ZMod n × ZMod m) × Fin 2 => l))^[k]
      ((2 * Real.sin (axisAngle (Real.sqrt (κ * l)) (2 * π * p.val / n) / 2)) •
          ((torus n m).incidenceᵀ *ᵥ fun w => (planeWave p (0 : ZMod m) w).re),
        (-Real.sin (axisAngle (Real.sqrt (κ * l)) (2 * π * p.val / n) / 2)) •
          (((torus n m).incidenceᵀ * diagonal (fun _ : ZMod n × ZMod m => κ) *
            (torus n m).incidence) *ᵥ
              ((torus n m).incidenceᵀ *ᵥ fun w => (planeWave p (0 : ZMod m) w).re))) =
      ((2 * Real.sin (axisAngle (Real.sqrt (κ * l)) (2 * π * p.val / n) / 2) *
            Real.cos (2 * k * (axisAngle (Real.sqrt (κ * l)) (2 * π * p.val / n) / 2))) •
          ((torus n m).incidenceᵀ *ᵥ fun w => (planeWave p (0 : ZMod m) w).re),
        Real.sin ((2 * k - 1) * (axisAngle (Real.sqrt (κ * l)) (2 * π * p.val / n) / 2)) •
          (((torus n m).incidenceᵀ * diagonal (fun _ : ZMod n × ZMod m => κ) *
            (torus n m).incidence) *ᵥ
              ((torus n m).incidenceᵀ *ᵥ fun w => (planeWave p (0 : ZMod m) w).re))) := by
  apply torus_dispersion
  have hc : Real.sqrt (κ * l) ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt h1
  have hc0 := Real.sqrt_nonneg (κ * l)
  have hs1 := Real.sin_le_one (2 * π * p.val / n / 2)
  have hs2 := Real.neg_one_le_sin (2 * π * p.val / n / 2)
  have hb1 : -1 ≤ Real.sqrt (κ * l) * Real.sin (2 * π * p.val / n / 2) := by nlinarith
  have hb2 : Real.sqrt (κ * l) * Real.sin (2 * π * p.val / n / 2) ≤ 1 := by nlinarith
  rw [axisAngle_dispersion _ _ hb1 hb2, Real.sq_sqrt h0]
  simp
  ring

end Artform.Stages
