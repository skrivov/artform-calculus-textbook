import ArtformStages.SpeedEveryDirection
import ArtformStages.SolidWaves

/-!
# The speed of light in a solid

Finding 460 of the research ledger on a layered universe found the one speed of light in every
direction of the plane, and finding 465 the dispersion of light in a solid of cubes. Here the speed
is found in every direction of a solid (finding 467 of the ledger):

* `solid_level_direction` (VS1): in every direction `u` the level of the plane wave of wave vector
  `t u` lies between `t² - t⁴ / 12` and `t²`;
* `angle_of_level_bounds` (VS2): a level between those bounds gives an angle per step between
  `c t √(1 - t² / 12)` and `c t / √(1 - c² t² / 4)`;
* `solidAngle_bounds`, `solidAngle_speed` (VS3): so the angle per step of a plane wave in every
  direction of a solid lies between them, and its ratio to `t` tends to `c`;
* `cube_plane_wave` (VS4): on the cubic torus every transverse plane wave turns by that angle.
-/

open Matrix Filter Topology

open scoped Real

namespace Artform.Stages

/-- **VS1.** In every direction `u` of a solid the level of the plane wave of wave vector `t u` lies
between `t² - t⁴ / 12` and `t²`. -/
theorem solid_level_direction (u : Fin 3 → ℝ) (t : ℝ) (hu : ∑ d, u d ^ 2 = 1) :
    t ^ 2 - t ^ 4 / 12 ≤ ∑ d, (2 - 2 * Real.cos (t * u d)) ∧
      ∑ d, (2 - 2 * Real.cos (t * u d)) ≤ t ^ 2 := by
  have e : ∀ x : ℝ, 2 - 2 * Real.cos x = 4 * Real.sin (x / 2) ^ 2 := by
    intro x
    have h := Real.cos_two_mul (x / 2)
    rw [show 2 * (x / 2) = x by ring] at h
    rw [h, Real.cos_sq']
    ring
  simp only [e, Fin.sum_univ_three]
  rw [Fin.sum_univ_three] at hu
  obtain ⟨a0, b0⟩ := four_sin_sq_half_bounds (t * u 0)
  obtain ⟨a1, b1⟩ := four_sin_sq_half_bounds (t * u 1)
  obtain ⟨a2, b2⟩ := four_sin_sq_half_bounds (t * u 2)
  have h2 : (t * u 0) ^ 2 + (t * u 1) ^ 2 + (t * u 2) ^ 2 = t ^ 2 := by
    have : (t * u 0) ^ 2 + (t * u 1) ^ 2 + (t * u 2) ^ 2 =
        t ^ 2 * (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2) := by ring
    rw [this, hu, mul_one]
  have h4 : (t * u 0) ^ 4 + (t * u 1) ^ 4 + (t * u 2) ^ 4 ≤ t ^ 4 := by
    have h4u : u 0 ^ 4 + u 1 ^ 4 + u 2 ^ 4 ≤ 1 := by
      have hsq : (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2) ^ 2 = 1 := by rw [hu]; norm_num
      nlinarith [sq_nonneg (u 0 * u 1), sq_nonneg (u 1 * u 2), sq_nonneg (u 0 * u 2)]
    have : (t * u 0) ^ 4 + (t * u 1) ^ 4 + (t * u 2) ^ 4 =
        t ^ 4 * (u 0 ^ 4 + u 1 ^ 4 + u 2 ^ 4) := by ring
    rw [this]
    exact mul_le_of_le_one_right (by positivity) h4u
  constructor <;> linarith

/-- **VS2.** For `c ≥ 0` and `t > 0` with `c t < 2`, a level `L` between `t² - t⁴ / 12` and `t²`
gives an angle per step `2 arcsin ((c / 2) √L)` between `c t √(1 - t² / 12)` and
`c t / √(1 - c² t² / 4)`. -/
theorem angle_of_level_bounds (c t L : ℝ) (hc : 0 ≤ c) (ht : 0 < t) (hct : c * t < 2)
    (hlo : t ^ 2 - t ^ 4 / 12 ≤ L) (hhi : L ≤ t ^ 2) :
    c * t * Real.sqrt (1 - t ^ 2 / 12) ≤ 2 * Real.arcsin (c / 2 * Real.sqrt L) ∧
      2 * Real.arcsin (c / 2 * Real.sqrt L) ≤ c * t / Real.sqrt (1 - c ^ 2 * t ^ 2 / 4) := by
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

/-- The angle per step that the dispersion gives the plane wave of angles `θ` in a solid, for the
speed `c`. -/
noncomputable def solidAngle (c : ℝ) (θ : Fin 3 → ℝ) : ℝ :=
  2 * Real.arcsin (c / 2 * Real.sqrt (∑ d, (2 - 2 * Real.cos (θ d))))

/-- **VS3.** In every direction `u` of a solid the angle per step of the plane wave of wave vector
`t u` lies between `c t √(1 - t² / 12)` and `c t / √(1 - c² t² / 4)`. -/
theorem solidAngle_bounds (c t : ℝ) (u : Fin 3 → ℝ) (hu : ∑ d, u d ^ 2 = 1) (hc : 0 ≤ c)
    (ht : 0 < t) (hct : c * t < 2) :
    c * t * Real.sqrt (1 - t ^ 2 / 12) ≤ solidAngle c (fun d => t * u d) ∧
      solidAngle c (fun d => t * u d) ≤ c * t / Real.sqrt (1 - c ^ 2 * t ^ 2 / 4) := by
  obtain ⟨hlo, hhi⟩ := solid_level_direction u t hu
  exact angle_of_level_bounds c t _ hc ht hct hlo hhi

/-- **VS3.** So in every direction `u` of a solid and for every `c ≥ 0`, the angle per step divided
by `t` tends to `c` as `t` tends to `0` from above. -/
theorem solidAngle_speed (c : ℝ) (u : Fin 3 → ℝ) (hu : ∑ d, u d ^ 2 = 1) (hc : 0 ≤ c) :
    Tendsto (fun t => solidAngle c (fun d => t * u d) / t) (𝓝[>] 0) (𝓝 c) := by
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
    obtain ⟨hlo, -⟩ := solidAngle_bounds c t u hu hc ht.1 (hct t ht)
    rw [le_div_iff₀ ht.1]
    linarith
  · filter_upwards [hev] with t ht
    obtain ⟨-, hhi⟩ := solidAngle_bounds c t u hu hc ht.1 (hct t ht)
    rw [div_le_iff₀ ht.1]
    calc solidAngle c (fun d => t * u d) ≤ c * t / Real.sqrt (1 - c ^ 2 * t ^ 2 / 4) := hhi
      _ = c / Real.sqrt (1 - c ^ 2 * t ^ 2 / 4) * t := by ring

variable (n : ℕ) [NeZero n]

/-- The solid angle per step of the wave vector `p` of the cubic torus, for one `κ` and one `λ`. -/
noncomputable def cubeAngle (κ l : ℝ) (p : CubePoint n) : ℝ :=
  solidAngle (Real.sqrt (κ * l)) (fun d => 2 * π * (p d).val / n)

/-- **VS4.** On the cubic torus with one `κ` and one `λ`, `0 ≤ κ λ ≤ 1 / 3`, the wave of every
amplitude with no divergence at `p` turns per step by the solid angle of `√(κ λ)`. -/
theorem cube_plane_wave (p : CubePoint n) (a : Fin 3 → ℂ) (ha : NoDivergence n p a) (κ l : ℝ)
    (h0 : 0 ≤ κ * l) (h1 : κ * l ≤ 1 / 3) (k : ℕ) :
    (pair ((cubeIncidence n)ᵀ * diagonal (fun _ : CubePoint n × Fin 3 => κ) * cubeIncidence n)
        (diagonal fun _ : CubePoint n × Fin 3 => l))^[k]
      ((2 * Real.sin (cubeAngle n κ l p / 2)) • cubeWaveField n p a,
        (-Real.sin (cubeAngle n κ l p / 2)) •
          (((cubeIncidence n)ᵀ * diagonal (fun _ : CubePoint n × Fin 3 => κ) * cubeIncidence n) *ᵥ
            cubeWaveField n p a)) =
      ((2 * Real.sin (cubeAngle n κ l p / 2) * Real.cos (2 * k * (cubeAngle n κ l p / 2))) •
          cubeWaveField n p a,
        Real.sin ((2 * k - 1) * (cubeAngle n κ l p / 2)) •
          (((cubeIncidence n)ᵀ * diagonal (fun _ : CubePoint n × Fin 3 => κ) * cubeIncidence n) *ᵥ
            cubeWaveField n p a)) := by
  apply cube_dispersion n p a ha κ l
  unfold cubeAngle solidAngle
  have hlev : (∑ d, (2 - 2 * Real.cos ((fun d => 2 * π * ((p d).val : ℝ) / n) d))) =
      cubeLevel n p := rfl
  rw [hlev]
  set L := cubeLevel n p with hL
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun d _ => by
    have := Real.cos_le_one (2 * π * ((p d).val : ℝ) / n)
    linarith
  have hL12 : L ≤ 12 := by
    have hb : ∀ d, 2 - 2 * Real.cos (2 * π * ((p d).val : ℝ) / n) ≤ 4 := fun d => by
      have := Real.neg_one_le_cos (2 * π * ((p d).val : ℝ) / n)
      linarith
    calc L = ∑ d, (2 - 2 * Real.cos (2 * π * ((p d).val : ℝ) / n)) := rfl
      _ ≤ ∑ _d : Fin 3, (4 : ℝ) := Finset.sum_le_sum fun d _ => hb d
      _ = 12 := by norm_num
  have hy0 : 0 ≤ Real.sqrt (κ * l) / 2 * Real.sqrt L := by positivity
  have hsq : (Real.sqrt (κ * l) / 2 * Real.sqrt L) ^ 2 ≤ 1 := by
    rw [mul_pow, div_pow, Real.sq_sqrt h0, Real.sq_sqrt hL0]
    nlinarith [mul_le_mul h1 hL12 hL0 (by norm_num : (0 : ℝ) ≤ 1 / 3)]
  have hy1 : Real.sqrt (κ * l) / 2 * Real.sqrt L ≤ 1 := by nlinarith
  rw [show 2 * Real.arcsin (Real.sqrt (κ * l) / 2 * Real.sqrt L) / 2 =
      Real.arcsin (Real.sqrt (κ * l) / 2 * Real.sqrt L) by ring,
    Real.sin_arcsin (by linarith) hy1, mul_pow, div_pow, Real.sq_sqrt h0, Real.sq_sqrt hL0]
  ring

end Artform.Stages
