import ArtformStages.Isotropy

/-!
# One speed of light in every direction

Finding 456 of the research ledger on a layered universe proved that light has the speed `c` at
long waves along the axes and the diagonals of the torus, and bounded the level of a plane wave in
every direction. Here the speed is found in every direction (finding 460 of the ledger):

* `le_arcsin_self`, `arcsin_le_div_sqrt` (EV1): `y ≤ arcsin y ≤ y / √(1 - y²)`;
* `planeAngle_bounds` (EV2): the angle per step of the plane wave of wave vector `t u`, for every
  direction `u`, lies between `c t √(1 - t² / 12)` and `c t / √(1 - c² t² / 4)`;
* `planeAngle_speed` (EV3): so its ratio to `t` tends to `c` as `t` tends to `0`;
* `torus_plane_wave` (EV4): on the torus every plane wave turns by that angle per step.
-/

open Matrix Filter Topology

open scoped Real

namespace Artform.Stages

/-- **EV1.** `y ≤ arcsin y` for `0 ≤ y ≤ 1`. -/
theorem le_arcsin_self {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : y ≤ Real.arcsin y := by
  have hz : 0 ≤ Real.arcsin y := Real.arcsin_nonneg.mpr h0
  have h := Real.sin_le hz
  rwa [Real.sin_arcsin (by linarith) h1] at h

/-- **EV1.** `arcsin y ≤ y / √(1 - y²)` for `0 ≤ y < 1`. -/
theorem arcsin_le_div_sqrt {y : ℝ} (h0 : 0 ≤ y) (h1 : y < 1) :
    Real.arcsin y ≤ y / Real.sqrt (1 - y ^ 2) := by
  have hz : 0 ≤ Real.arcsin y := Real.arcsin_nonneg.mpr h0
  have hz' : Real.arcsin y < π / 2 := Real.arcsin_lt_pi_div_two.mpr h1
  have h := Real.le_tan hz hz'
  rwa [Real.tan_arcsin] at h

/-- The plane angle: the angle per step that the dispersion gives the plane wave of angles `θ₁`
and `θ₂` for the speed `c`. -/
noncomputable def planeAngle (c θ₁ θ₂ : ℝ) : ℝ :=
  2 * Real.arcsin (c / 2 * Real.sqrt (4 - 2 * Real.cos θ₁ - 2 * Real.cos θ₂))

/-- Along a direction `u`, the level of the plane wave of wave vector `t u` lies between
`t² - t⁴ / 12` and `t²`. -/
theorem level_direction (u₁ u₂ t : ℝ) (hu : u₁ ^ 2 + u₂ ^ 2 = 1) :
    t ^ 2 - t ^ 4 / 12 ≤ 4 - 2 * Real.cos (t * u₁) - 2 * Real.cos (t * u₂) ∧
      4 - 2 * Real.cos (t * u₁) - 2 * Real.cos (t * u₂) ≤ t ^ 2 := by
  obtain ⟨h1, h2⟩ := level_isotropic (t * u₁) (t * u₂)
  have e2 : (t * u₁) ^ 2 + (t * u₂) ^ 2 = t ^ 2 := by
    have : (t * u₁) ^ 2 + (t * u₂) ^ 2 = t ^ 2 * (u₁ ^ 2 + u₂ ^ 2) := by ring
    rw [this, hu, mul_one]
  have e4 : (t * u₁) ^ 4 + (t * u₂) ^ 4 ≤ t ^ 4 := by
    have hsq : (u₁ ^ 2 + u₂ ^ 2) ^ 2 = 1 := by rw [hu]; norm_num
    have h4 : u₁ ^ 4 + u₂ ^ 4 ≤ 1 := by nlinarith [sq_nonneg (u₁ * u₂)]
    have : (t * u₁) ^ 4 + (t * u₂) ^ 4 = t ^ 4 * (u₁ ^ 4 + u₂ ^ 4) := by ring
    rw [this]
    exact mul_le_of_le_one_right (by positivity) h4
  constructor
  · rw [e2] at h1
    linarith
  · rw [e2] at h2
    exact h2

/-- **EV2.** For every direction `u`, every `c ≥ 0` and every `t > 0` with `c t < 2`, the plane
angle of the wave vector `t u` lies between `c t √(1 - t² / 12)` and `c t / √(1 - c² t² / 4)`. -/
theorem planeAngle_bounds (c u₁ u₂ t : ℝ) (hu : u₁ ^ 2 + u₂ ^ 2 = 1) (hc : 0 ≤ c) (ht : 0 < t)
    (hct : c * t < 2) :
    c * t * Real.sqrt (1 - t ^ 2 / 12) ≤ planeAngle c (t * u₁) (t * u₂) ∧
      planeAngle c (t * u₁) (t * u₂) ≤ c * t / Real.sqrt (1 - c ^ 2 * t ^ 2 / 4) := by
  obtain ⟨hlo, hhi⟩ := level_direction u₁ u₂ t hu
  unfold planeAngle
  set L := 4 - 2 * Real.cos (t * u₁) - 2 * Real.cos (t * u₂) with hL
  have hsL : Real.sqrt L ≤ t := by
    calc Real.sqrt L ≤ Real.sqrt (t ^ 2) := Real.sqrt_le_sqrt hhi
      _ = t := Real.sqrt_sq ht.le
  set y := c / 2 * Real.sqrt L with hy
  have hy0 : 0 ≤ y := by positivity
  have hyle : y ≤ c * t / 2 := by
    have := mul_le_mul_of_nonneg_left hsL (by positivity : (0 : ℝ) ≤ c / 2)
    rw [hy]
    linarith
  have hct0 : 0 ≤ c * t := mul_nonneg hc ht.le
  have hy1 : y < 1 := by linarith
  constructor
  · have hsq : t * Real.sqrt (1 - t ^ 2 / 12) ≤ Real.sqrt L := by
      have e : t * Real.sqrt (1 - t ^ 2 / 12) = Real.sqrt (t ^ 2 * (1 - t ^ 2 / 12)) := by
        rw [Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht.le]
      rw [e]
      apply Real.sqrt_le_sqrt
      nlinarith [hlo]
    have h1 : c * t * Real.sqrt (1 - t ^ 2 / 12) ≤ 2 * y := by
      have := mul_le_mul_of_nonneg_left hsq hc
      rw [hy]
      linarith
    have h2 := le_arcsin_self hy0 hy1.le
    linarith
  · have h3 := arcsin_le_div_sqrt hy0 hy1
    have hD' : 0 < Real.sqrt (1 - c ^ 2 * t ^ 2 / 4) := by
      apply Real.sqrt_pos.mpr
      nlinarith [hct, hct0]
    have hD : Real.sqrt (1 - c ^ 2 * t ^ 2 / 4) ≤ Real.sqrt (1 - y ^ 2) := by
      apply Real.sqrt_le_sqrt
      nlinarith [hyle, hy0, hct0]
    have hDpos : 0 < Real.sqrt (1 - y ^ 2) := lt_of_lt_of_le hD' hD
    have h4 : y / Real.sqrt (1 - y ^ 2) ≤ (c * t / 2) / Real.sqrt (1 - c ^ 2 * t ^ 2 / 4) := by
      rw [div_le_div_iff₀ hDpos hD']
      exact mul_le_mul hyle hD hD'.le (by linarith)
    calc 2 * Real.arcsin y ≤ 2 * (y / Real.sqrt (1 - y ^ 2)) := by linarith
      _ ≤ 2 * ((c * t / 2) / Real.sqrt (1 - c ^ 2 * t ^ 2 / 4)) := by linarith
      _ = c * t / Real.sqrt (1 - c ^ 2 * t ^ 2 / 4) := by ring

/-- **EV3.** In every direction `u` and for every `c ≥ 0`, the plane angle of the wave vector `t u`
divided by `t` tends to `c` as `t` tends to `0` from above. -/
theorem planeAngle_speed (c u₁ u₂ : ℝ) (hu : u₁ ^ 2 + u₂ ^ 2 = 1) (hc : 0 ≤ c) :
    Tendsto (fun t => planeAngle c (t * u₁) (t * u₂) / t) (𝓝[>] 0) (𝓝 c) := by
  have hg : Tendsto (fun t : ℝ => c * Real.sqrt (1 - t ^ 2 / 12)) (𝓝[>] 0) (𝓝 c) := by
    have h : Tendsto (fun t : ℝ => c * Real.sqrt (1 - t ^ 2 / 12)) (𝓝 0)
        (𝓝 (c * Real.sqrt (1 - 0 ^ 2 / 12))) := by
      apply Continuous.tendsto
      fun_prop
    simpa using h.mono_left nhdsWithin_le_nhds
  have hh : Tendsto (fun t : ℝ => c / Real.sqrt (1 - c ^ 2 * t ^ 2 / 4)) (𝓝[>] 0) (𝓝 c) := by
    have h1 : Tendsto (fun t : ℝ => Real.sqrt (1 - c ^ 2 * t ^ 2 / 4)) (𝓝 0)
        (𝓝 (Real.sqrt (1 - c ^ 2 * 0 ^ 2 / 4))) := by
      apply Continuous.tendsto
      fun_prop
    have h2 : Tendsto (fun t : ℝ => c / Real.sqrt (1 - c ^ 2 * t ^ 2 / 4)) (𝓝 0)
        (𝓝 (c / Real.sqrt (1 - c ^ 2 * 0 ^ 2 / 4))) :=
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => c) (𝓝 0) (𝓝 c)).div h1 (by simp)
    simpa using h2.mono_left nhdsWithin_le_nhds
  have hε : (0 : ℝ) < 1 / (c + 1) := by positivity
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Set.Ioo 0 (1 / (c + 1)) := Ioo_mem_nhdsGT hε
  have hct : ∀ t ∈ Set.Ioo (0 : ℝ) (1 / (c + 1)), c * t < 2 := by
    rintro t ⟨-, ht1⟩
    have h1 : c * t ≤ c * (1 / (c + 1)) := mul_le_mul_of_nonneg_left ht1.le hc
    have h2 : c * (1 / (c + 1)) < 1 := by
      rw [mul_one_div, div_lt_one (by positivity)]
      linarith
    linarith
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hg hh ?_ ?_
  · filter_upwards [hev] with t ht
    obtain ⟨hlo, -⟩ := planeAngle_bounds c u₁ u₂ t hu hc ht.1 (hct t ht)
    rw [le_div_iff₀ ht.1]
    linarith
  · filter_upwards [hev] with t ht
    obtain ⟨-, hhi⟩ := planeAngle_bounds c u₁ u₂ t hu hc ht.1 (hct t ht)
    rw [div_le_iff₀ ht.1]
    calc planeAngle c (t * u₁) (t * u₂) ≤ c * t / Real.sqrt (1 - c ^ 2 * t ^ 2 / 4) := hhi
      _ = c / Real.sqrt (1 - c ^ 2 * t ^ 2 / 4) * t := by ring

/-- **EV4.** On the torus with one `κ` and one `λ`, `0 ≤ κ λ ≤ 1 / 2`, the transverse plane wave of
wave numbers `(p, q)` turns per step by the plane angle of `√(κ λ)`. -/
theorem torus_plane_wave (n m : ℕ) [NeZero n] [NeZero m] [Fact (1 < n)] [Fact (1 < m)]
    (p : ZMod n) (q : ZMod m) (κ l : ℝ) (h0 : 0 ≤ κ * l) (h1 : κ * l ≤ 1 / 2) (k : ℕ) :
    (pair ((torus n m).incidenceᵀ * diagonal (fun _ : ZMod n × ZMod m => κ) * (torus n m).incidence)
        (diagonal fun _ : (ZMod n × ZMod m) × Fin 2 => l))^[k]
      ((2 * Real.sin (planeAngle (Real.sqrt (κ * l)) (2 * π * p.val / n) (2 * π * q.val / m) / 2)) •
          ((torus n m).incidenceᵀ *ᵥ fun w => (planeWave p q w).re),
        (-Real.sin (planeAngle (Real.sqrt (κ * l)) (2 * π * p.val / n) (2 * π * q.val / m) / 2)) •
          (((torus n m).incidenceᵀ * diagonal (fun _ : ZMod n × ZMod m => κ) *
            (torus n m).incidence) *ᵥ ((torus n m).incidenceᵀ *ᵥ fun w => (planeWave p q w).re))) =
      ((2 * Real.sin (planeAngle (Real.sqrt (κ * l)) (2 * π * p.val / n) (2 * π * q.val / m) / 2) *
            Real.cos (2 * k *
              (planeAngle (Real.sqrt (κ * l)) (2 * π * p.val / n) (2 * π * q.val / m) / 2))) •
          ((torus n m).incidenceᵀ *ᵥ fun w => (planeWave p q w).re),
        Real.sin ((2 * k - 1) *
            (planeAngle (Real.sqrt (κ * l)) (2 * π * p.val / n) (2 * π * q.val / m) / 2)) •
          (((torus n m).incidenceᵀ * diagonal (fun _ : ZMod n × ZMod m => κ) *
            (torus n m).incidence) *ᵥ
              ((torus n m).incidenceᵀ *ᵥ fun w => (planeWave p q w).re))) := by
  apply torus_dispersion
  unfold planeAngle
  set L := 4 - 2 * Real.cos (2 * π * p.val / n) - 2 * Real.cos (2 * π * q.val / m) with hL
  have hL0 : 0 ≤ L := by
    have := Real.cos_le_one (2 * π * p.val / n)
    have := Real.cos_le_one (2 * π * q.val / m)
    linarith
  have hL8 : L ≤ 8 := by
    have := Real.neg_one_le_cos (2 * π * p.val / n)
    have := Real.neg_one_le_cos (2 * π * q.val / m)
    linarith
  have hy0 : 0 ≤ Real.sqrt (κ * l) / 2 * Real.sqrt L := by positivity
  have hsq : (Real.sqrt (κ * l) / 2 * Real.sqrt L) ^ 2 ≤ 1 := by
    rw [mul_pow, div_pow, Real.sq_sqrt h0, Real.sq_sqrt hL0]
    nlinarith [mul_le_mul h1 hL8 hL0 (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hy1 : Real.sqrt (κ * l) / 2 * Real.sqrt L ≤ 1 := by nlinarith
  rw [show 2 * Real.arcsin (Real.sqrt (κ * l) / 2 * Real.sqrt L) / 2 =
      Real.arcsin (Real.sqrt (κ * l) / 2 * Real.sqrt L) by ring,
    Real.sin_arcsin (by linarith) hy1, mul_pow, div_pow, Real.sq_sqrt h0, Real.sq_sqrt hL0]
  ring

end Artform.Stages
