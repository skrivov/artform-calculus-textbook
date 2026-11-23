import ArtformStages.WilsonWalk

/-!
# A walk in space with its speed (finding 495)

Wave N5 of campaign 15 of road DP. In space no walk's speed was on file. Here two walks are read.

* `planeShift_quat_z`, `planeShift_quat_y`, `planeShift_quat_x`, `spaceSymbol`, `spaceSymbol_det`,
  `spaceSymbol_trace`, `IsSpaceLevel`, `space_level_iff` (WS1): the two-component walk in space,
  the conditional shifts `e^{-i α_j k_j}` with `α_x = σz`, `α_y = σy`, `α_z = σx`,
  `W = S_z S_y S_x`, has determinant `1` and half its trace
  `cos k₁ cos k₂ cos k₃ - sin k₁ sin k₂ sin k₃`;
* `abs_sub_le_add`, `three_sym_bounds`, `quartic_le_one`, `space_one_speed` (WS2): along every
  direction and at every `t` half that trace is `1 - t² / 2` up to `|t|³ + 13 t⁴ / 72`: one speed,
  `1`, in every direction;
* `wilsonLayer_zero`, `naiveCoin_three`, `spaceMidWord`, `spaceEndWord`, `spaceEnd3Word`,
  `spaceMid_trace`, `spaceEnd_trace`, `spaceEnd3_trace` (WS3): the book's Wilson word in space,
  `(G_x G_y G_z C)(G_z G_y G_x C)`, at the massless point `ν = 3ϑ`, read along one axis with the
  Pauli tables `β = -σx` and `α = σz`: along the middle axis half the trace is
  `2 (cos² ϑ + sin² ϑ cos k)² - 1`, and along the first and the third it is that plus
  `8 cos² ϑ sin⁴ ϑ sin² k`;
* `spaceMid_level_iff`, `spaceEnd_level_iff`, `spaceEnd_slower` (WS4): so along the middle axis the
  word turns by twice the angle `ω` with `cos ω = cos² ϑ + sin² ϑ cos k`, light's dispersion with
  `c = sin ϑ`, and along the first axis by less, at every wave and every partial hop.

None of this is new: the first walk is the Weyl walk of the conditional shifts, and the Wilson word
is the book's exercise; the proofs multiply quaternions.
-/

open Matrix Complex Set
open scoped Real Quaternion

namespace Artform.Stages

/-! ### WS1: the two-component walk in space -/

/-- WS1. The shift along `σz` is the table of a unit quaternion. -/
theorem planeShift_quat_z (k : ℝ) :
    planeShift pauliZ k = quatTable ⟨Real.cos k, 0, 0, Real.sin k⟩ := by
  rw [planeShift_pauliZ, quatTable_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- WS1. The shift along `σy` is the table of a unit quaternion. -/
theorem planeShift_quat_y (k : ℝ) :
    planeShift pauliY k = quatTable ⟨Real.cos k, 0, Real.sin k, 0⟩ := by
  rw [planeShift_pauliY, quatTable_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- WS1. The shift along `σx` is the table of a unit quaternion. -/
theorem planeShift_quat_x (k : ℝ) :
    planeShift pauliX k = quatTable ⟨Real.cos k, Real.sin k, 0, 0⟩ := by
  rw [quatTable_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [planeShift, pauliX]

/-- **The two-component walk in space** at the wave number `(k₁, k₂, k₃)`: `W = S_z S_y S_x`, with
`α_x = σz`, `α_y = σy` and `α_z = σx`. -/
noncomputable def spaceSymbol (k₁ k₂ k₃ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  planeShift pauliX k₃ * planeShift pauliY k₂ * planeShift pauliZ k₁

/-- WS1. The walk in space has determinant `1`. -/
theorem spaceSymbol_det (k₁ k₂ k₃ : ℝ) : det (spaceSymbol k₁ k₂ k₃) = 1 := by
  have hx : det (quatTable ⟨Real.cos k₃, Real.sin k₃, 0, 0⟩) = 1 :=
    quatTable_det_of_unit _ (by simp only; linear_combination Real.cos_sq_add_sin_sq k₃)
  have hy : det (quatTable ⟨Real.cos k₂, 0, Real.sin k₂, 0⟩) = 1 :=
    quatTable_det_of_unit _ (by simp only; linear_combination Real.cos_sq_add_sin_sq k₂)
  have hz : det (quatTable ⟨Real.cos k₁, 0, 0, Real.sin k₁⟩) = 1 :=
    quatTable_det_of_unit _ (by simp only; linear_combination Real.cos_sq_add_sin_sq k₁)
  rw [spaceSymbol, det_mul, det_mul, planeShift_quat_x, planeShift_quat_y, planeShift_quat_z, hx,
    hy, hz, one_mul, one_mul]

/-- WS1. **Half the trace of the walk in space** is
`cos k₁ cos k₂ cos k₃ - sin k₁ sin k₂ sin k₃`. -/
theorem spaceSymbol_trace (k₁ k₂ k₃ : ℝ) :
    trace (spaceSymbol k₁ k₂ k₃) =
      2 * ((Real.cos k₁ * Real.cos k₂ * Real.cos k₃ -
        Real.sin k₁ * Real.sin k₂ * Real.sin k₃ : ℝ) : ℂ) := by
  rw [spaceSymbol, planeShift_quat_x, planeShift_quat_y, planeShift_quat_z, ← quatTable_mul,
    ← quatTable_mul, quatTable_trace]
  congr 2
  simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
  ring

/-- A level of the walk in space: `e^{-iε}` is an eigenvalue of its table. -/
def IsSpaceLevel (k₁ k₂ k₃ ε : ℝ) : Prop :=
  ∃ v : Fin 2 → ℂ, v ≠ 0 ∧ spaceSymbol k₁ k₂ k₃ *ᵥ v = Complex.exp (-(ε : ℂ) * I) • v

/-- WS1. **The levels of the walk in space** obey
`cos ε = cos k₁ cos k₂ cos k₃ - sin k₁ sin k₂ sin k₃`. -/
theorem space_level_iff (k₁ k₂ k₃ ε : ℝ) :
    IsSpaceLevel k₁ k₂ k₃ ε ↔
      Real.cos ε = Real.cos k₁ * Real.cos k₂ * Real.cos k₃ -
        Real.sin k₁ * Real.sin k₂ * Real.sin k₃ :=
  level_iff_of_det_one (spaceSymbol_det k₁ k₂ k₃) (spaceSymbol_trace k₁ k₂ k₃) ε

/-! ### WS2: one speed, `1`, in every direction -/

theorem abs_sub_le_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  have h := abs_add_le a (-b)
  rwa [← sub_eq_add_neg, abs_neg] at h

/-- The symmetric functions of three numbers in `[0, 1]`. -/
theorem three_sym_bounds {y₁ y₂ y₃ : ℝ} (h0₁ : 0 ≤ y₁) (h0₂ : 0 ≤ y₂) (h0₃ : 0 ≤ y₃)
    (h1₁ : y₁ ≤ 1) (h1₂ : y₂ ≤ 1) (h1₃ : y₃ ≤ 1) :
    y₁ * y₂ + y₁ * y₃ + y₂ * y₃ ≤ (y₁ + y₂ + y₃) ^ 2 / 3 ∧
      3 * (y₁ * y₂ * y₃) ≤ y₁ * y₂ + y₁ * y₃ + y₂ * y₃ := by
  refine ⟨by nlinarith [sq_nonneg (y₁ - y₂), sq_nonneg (y₁ - y₃), sq_nonneg (y₂ - y₃)], ?_⟩
  have a1 : y₁ * y₂ * y₃ ≤ y₁ * y₂ := mul_le_of_le_one_right (mul_nonneg h0₁ h0₂) h1₃
  have a2 : y₁ * y₂ * y₃ ≤ y₁ * y₃ := by
    calc y₁ * y₂ * y₃ = y₁ * y₃ * y₂ := by ring
      _ ≤ y₁ * y₃ := mul_le_of_le_one_right (mul_nonneg h0₁ h0₃) h1₂
  have a3 : y₁ * y₂ * y₃ ≤ y₂ * y₃ := by
    calc y₁ * y₂ * y₃ = y₂ * y₃ * y₁ := by ring
      _ ≤ y₂ * y₃ := mul_le_of_le_one_right (mul_nonneg h0₂ h0₃) h1₁
  linarith

/-- On the unit sphere the fourth powers sum to at most `1`. -/
theorem quartic_le_one {u₁ u₂ u₃ : ℝ} (hu : u₁ ^ 2 + u₂ ^ 2 + u₃ ^ 2 = 1) :
    u₁ ^ 4 + u₂ ^ 4 + u₃ ^ 4 ≤ 1 := by
  have h : (u₁ ^ 2 + u₂ ^ 2 + u₃ ^ 2) ^ 2 = 1 := by rw [hu, one_pow]
  nlinarith [sq_nonneg (u₁ * u₂), sq_nonneg (u₁ * u₃), sq_nonneg (u₂ * u₃)]

/-- WS2. **One speed in every direction**: along every direction `u` and at every `t`, half the
trace of the walk in space is `1 - t² / 2` up to `|t|³ + 13 t⁴ / 72`. -/
theorem space_one_speed (u₁ u₂ u₃ t : ℝ) (hu : u₁ ^ 2 + u₂ ^ 2 + u₃ ^ 2 = 1) :
    |Real.cos (t * u₁) * Real.cos (t * u₂) * Real.cos (t * u₃) -
        Real.sin (t * u₁) * Real.sin (t * u₂) * Real.sin (t * u₃) - (1 - t ^ 2 / 2)| ≤
      |t| ^ 3 + 13 * t ^ 4 / 72 := by
  set y₁ := Real.sin (t * u₁ / 2) ^ 2 with hy₁
  set y₂ := Real.sin (t * u₂ / 2) ^ 2 with hy₂
  set y₃ := Real.sin (t * u₃ / 2) ^ 2 with hy₃
  have hc₁ : Real.cos (t * u₁) = 1 - 2 * y₁ := cos_eq_one_sub_sin_sq_half _
  have hc₂ : Real.cos (t * u₂) = 1 - 2 * y₂ := cos_eq_one_sub_sin_sq_half _
  have hc₃ : Real.cos (t * u₃) = 1 - 2 * y₃ := cos_eq_one_sub_sin_sq_half _
  have h0₁ : 0 ≤ y₁ := sq_nonneg _
  have h0₂ : 0 ≤ y₂ := sq_nonneg _
  have h0₃ : 0 ≤ y₃ := sq_nonneg _
  have h1₁ : y₁ ≤ 1 := Real.sin_sq_le_one _
  have h1₂ : y₂ ≤ 1 := Real.sin_sq_le_one _
  have h1₃ : y₃ ≤ 1 := Real.sin_sq_le_one _
  obtain ⟨hl₁, hu₁⟩ := four_sin_sq_half_bounds (t * u₁)
  obtain ⟨hl₂, hu₂⟩ := four_sin_sq_half_bounds (t * u₂)
  obtain ⟨hl₃, hu₃⟩ := four_sin_sq_half_bounds (t * u₃)
  have hsq : (t * u₁) ^ 2 + (t * u₂) ^ 2 + (t * u₃) ^ 2 = t ^ 2 := by
    rw [mul_pow, mul_pow, mul_pow, ← mul_add, ← mul_add, hu, mul_one]
  have hq4 : (t * u₁) ^ 4 + (t * u₂) ^ 4 + (t * u₃) ^ 4 ≤ t ^ 4 := by
    have h4 := quartic_le_one hu
    have ht4 : 0 ≤ t ^ 4 := by positivity
    calc (t * u₁) ^ 4 + (t * u₂) ^ 4 + (t * u₃) ^ 4 = t ^ 4 * (u₁ ^ 4 + u₂ ^ 4 + u₃ ^ 4) := by
          ring
      _ ≤ t ^ 4 * 1 := mul_le_mul_of_nonneg_left h4 ht4
      _ = t ^ 4 := mul_one _
  obtain ⟨he₂, he₃⟩ := three_sym_bounds h0₁ h0₂ h0₃ h1₁ h1₂ h1₃
  have he₂0 : 0 ≤ y₁ * y₂ + y₁ * y₃ + y₂ * y₃ := by positivity
  have he₃0 : 0 ≤ y₁ * y₂ * y₃ := by positivity
  set Y := y₁ + y₂ + y₃ with hY
  have hYle : Y ≤ t ^ 2 / 4 := by linarith
  have hYge : t ^ 2 / 4 - t ^ 4 / 48 ≤ Y := by linarith
  have hY0 : 0 ≤ Y := by linarith
  set e₂ := y₁ * y₂ + y₁ * y₃ + y₂ * y₃ with he₂def
  set e₃ := y₁ * y₂ * y₃ with he₃def
  have hY2 : Y ^ 2 ≤ t ^ 4 / 16 := by
    calc Y ^ 2 ≤ (t ^ 2 / 4) ^ 2 := pow_le_pow_left₀ hY0 hYle 2
      _ = t ^ 4 / 16 := by ring
  have hprod : Real.cos (t * u₁) * Real.cos (t * u₂) * Real.cos (t * u₃) =
      1 - 2 * Y + 4 * e₂ - 8 * e₃ := by
    rw [hc₁, hc₂, hc₃]
    ring
  have hsin : ∀ u : ℝ, u ^ 2 ≤ 1 → |Real.sin (t * u)| ≤ |t| := fun u hu1 => by
    have hu' : |u| ≤ 1 := (sq_le_one_iff_abs_le_one u).mp hu1
    calc |Real.sin (t * u)| ≤ |t * u| := Real.abs_sin_le_abs
      _ = |t| * |u| := abs_mul _ _
      _ ≤ |t| * 1 := mul_le_mul_of_nonneg_left hu' (abs_nonneg t)
      _ = |t| := mul_one _
  have hs : |Real.sin (t * u₁) * Real.sin (t * u₂) * Real.sin (t * u₃)| ≤ |t| ^ 3 := by
    have b1 := hsin u₁ (by linarith [sq_nonneg u₂, sq_nonneg u₃])
    have b2 := hsin u₂ (by linarith [sq_nonneg u₁, sq_nonneg u₃])
    have b3 := hsin u₃ (by linarith [sq_nonneg u₁, sq_nonneg u₂])
    rw [abs_mul, abs_mul]
    calc |Real.sin (t * u₁)| * |Real.sin (t * u₂)| * |Real.sin (t * u₃)| ≤ |t| * |t| * |t| := by
          gcongr
      _ = |t| ^ 3 := by ring
  have ht4' : 0 ≤ t ^ 4 := by positivity
  have hA : |4 * e₂ - 8 * e₃| ≤ t ^ 4 / 12 := by
    rw [abs_le]
    constructor <;> linarith
  have hB : |2 * Y - t ^ 2 / 2| ≤ t ^ 4 / 24 := by
    rw [abs_le]
    constructor <;> linarith
  have key : Real.cos (t * u₁) * Real.cos (t * u₂) * Real.cos (t * u₃) -
      Real.sin (t * u₁) * Real.sin (t * u₂) * Real.sin (t * u₃) - (1 - t ^ 2 / 2) =
      (4 * e₂ - 8 * e₃) - (2 * Y - t ^ 2 / 2) -
        Real.sin (t * u₁) * Real.sin (t * u₂) * Real.sin (t * u₃) := by
    rw [hprod]
    ring
  rw [key]
  have ht4 : 0 ≤ t ^ 4 := by positivity
  calc |(4 * e₂ - 8 * e₃) - (2 * Y - t ^ 2 / 2) -
        Real.sin (t * u₁) * Real.sin (t * u₂) * Real.sin (t * u₃)|
      ≤ |(4 * e₂ - 8 * e₃) - (2 * Y - t ^ 2 / 2)| +
          |Real.sin (t * u₁) * Real.sin (t * u₂) * Real.sin (t * u₃)| := abs_sub_le_add _ _
    _ ≤ |4 * e₂ - 8 * e₃| + |2 * Y - t ^ 2 / 2| +
          |Real.sin (t * u₁) * Real.sin (t * u₂) * Real.sin (t * u₃)| := by
        gcongr
        exact abs_sub_le_add _ _
    _ ≤ t ^ 4 / 12 + t ^ 4 / 24 + |t| ^ 3 := by gcongr
    _ ≤ |t| ^ 3 + 13 * t ^ 4 / 72 := by linarith

/-! ### WS3: the book's Wilson word in space, along an axis -/

/-- WS3. **At the wave `0` a layer is `e^{iϑβ}`, whatever its axis' table.** -/
theorem wilsonLayer_zero (α : Matrix (Fin 2) (Fin 2) ℂ) (ϑ : ℝ) :
    wilsonLayer α ϑ 0 = quatTable ⟨Real.cos ϑ, Real.sin ϑ, 0, 0⟩ := by
  rw [quatTable_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wilsonLayer, naiveBeta, pauliX]

/-- WS3. The coin of the massless point, `C(3ϑ)`, is `C(ϑ)³`. -/
theorem naiveCoin_three (ϑ : ℝ) : naiveCoin (3 * ϑ) = naiveCoin ϑ * naiveCoin ϑ * naiveCoin ϑ := by
  rw [naiveCoin_quat, naiveCoin_quat, ← quatTable_mul, ← quatTable_mul]
  congr 1
  ext
  · simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
    rw [Real.cos_three_mul]
    linear_combination 3 * Real.cos ϑ * Real.sin_sq_add_cos_sq ϑ
  · simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
    rw [Real.sin_three_mul]
    linear_combination 3 * Real.sin ϑ * Real.sin_sq_add_cos_sq ϑ
  · simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
    ring
  · simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
    ring

/-- The book's Wilson word in space at the massless point, read **along its middle axis**: the
layers of the other axes are at the wave `0`. -/
noncomputable def spaceMidWord (ϑ k : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  wilsonLayer pauliZ ϑ 0 * wilsonLayer pauliZ ϑ k * wilsonLayer pauliZ ϑ 0 * naiveCoin (3 * ϑ) *
    (wilsonLayer pauliZ ϑ 0 * wilsonLayer pauliZ ϑ k * wilsonLayer pauliZ ϑ 0 * naiveCoin (3 * ϑ))

/-- The same word **along its first axis**. -/
noncomputable def spaceEndWord (ϑ k : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  wilsonLayer pauliZ ϑ k * wilsonLayer pauliZ ϑ 0 * wilsonLayer pauliZ ϑ 0 * naiveCoin (3 * ϑ) *
    (wilsonLayer pauliZ ϑ 0 * wilsonLayer pauliZ ϑ 0 * wilsonLayer pauliZ ϑ k * naiveCoin (3 * ϑ))

/-- The same word **along its third axis**. -/
noncomputable def spaceEnd3Word (ϑ k : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  wilsonLayer pauliZ ϑ 0 * wilsonLayer pauliZ ϑ 0 * wilsonLayer pauliZ ϑ k * naiveCoin (3 * ϑ) *
    (wilsonLayer pauliZ ϑ k * wilsonLayer pauliZ ϑ 0 * wilsonLayer pauliZ ϑ 0 * naiveCoin (3 * ϑ))

/-- The real part does not see the order of two factors. -/
theorem quat_re_mul_comm (a b : ℍ[ℝ]) : (a * b).re = (b * a).re := by
  simp only [Quaternion.re_mul]
  ring

/-- The half trace of the reduced words, in `g = cos ϑ`, `h = sin ϑ`, `c = cos k`, `s = sin k`. -/
theorem spaceMid_re (g h c s : ℝ) :
    ((⟨g, h, 0, 0⟩ * (⟨g, h * c, 0, h * s⟩ * (⟨g, -h, 0, 0⟩ * (⟨g, h * c, 0, h * s⟩ *
      (⟨g, -h, 0, 0⟩ * ⟨g, -h, 0, 0⟩))))) : ℍ[ℝ]).re =
      (g ^ 2 + h ^ 2) * ((g ^ 2 + h ^ 2 * c) ^ 2 - (g * h * c - g * h) ^ 2 - (h ^ 2 * s) ^ 2 -
        (g * h * s) ^ 2) := by
  simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
  ring

theorem spaceEnd_re (g h c s : ℝ) :
    ((⟨g, h * c, 0, h * s⟩ * (⟨g, h, 0, 0⟩ * (⟨g, h * c, 0, h * s⟩ * (⟨g, -h, 0, 0⟩ *
      (⟨g, -h, 0, 0⟩ * ⟨g, -h, 0, 0⟩))))) : ℍ[ℝ]).re =
      (g ^ 2 + h ^ 2) * ((g ^ 2 + h ^ 2 * c) ^ 2 - (g * h * c - g * h) ^ 2 - (h ^ 2 * s) ^ 2 -
        (g * h * s) ^ 2) + 8 * g ^ 2 * h ^ 4 * s ^ 2 := by
  simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
  ring

theorem spaceEnd3_re (g h c s : ℝ) :
    ((⟨g, h * c, 0, h * s⟩ * (⟨g, -h, 0, 0⟩ * (⟨g, -h, 0, 0⟩ * (⟨g, -h, 0, 0⟩ *
      (⟨g, h * c, 0, h * s⟩ * ⟨g, h, 0, 0⟩))))) : ℍ[ℝ]).re =
      (g ^ 2 + h ^ 2) * ((g ^ 2 + h ^ 2 * c) ^ 2 - (g * h * c - g * h) ^ 2 - (h ^ 2 * s) ^ 2 -
        (g * h * s) ^ 2) + 8 * g ^ 2 * h ^ 4 * s ^ 2 := by
  simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
  ring

/-- On the circle, the reduced half trace is `2 (g² + h² c)² - 1`. -/
theorem spaceMid_circle (ϑ k : ℝ) :
    (Real.cos ϑ ^ 2 + Real.sin ϑ ^ 2) * ((Real.cos ϑ ^ 2 + Real.sin ϑ ^ 2 * Real.cos k) ^ 2 -
      (Real.cos ϑ * Real.sin ϑ * Real.cos k - Real.cos ϑ * Real.sin ϑ) ^ 2 -
      (Real.sin ϑ ^ 2 * Real.sin k) ^ 2 - (Real.cos ϑ * Real.sin ϑ * Real.sin k) ^ 2) =
      2 * (Real.cos ϑ ^ 2 + Real.sin ϑ ^ 2 * Real.cos k) ^ 2 - 1 := by
  have hϑ := Real.cos_sq_add_sin_sq ϑ
  have hk := Real.cos_sq_add_sin_sq k
  set g := Real.cos ϑ
  set h := Real.sin ϑ
  set c := Real.cos k
  set s := Real.sin k
  linear_combination
    (2 * (g ^ 2 + h ^ 2 * c) ^ 2 - (g ^ 2 + h ^ 2) ^ 2 - (g ^ 2 + h ^ 2) - 1) * hϑ -
      (g ^ 2 + h ^ 2) ^ 2 * h ^ 2 * hk

/-- The quaternions of the layers at `0` cancel those of the coin of one step. -/
theorem quat_r_mul_ri (ϑ : ℝ) :
    (⟨Real.cos ϑ, Real.sin ϑ, 0, 0⟩ * ⟨Real.cos ϑ, -Real.sin ϑ, 0, 0⟩ : ℍ[ℝ]) = 1 := by
  ext <;> simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
    Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one]
  · linear_combination Real.cos_sq_add_sin_sq ϑ
  all_goals ring

theorem quat_ri_mul_r (ϑ : ℝ) :
    (⟨Real.cos ϑ, -Real.sin ϑ, 0, 0⟩ * ⟨Real.cos ϑ, Real.sin ϑ, 0, 0⟩ : ℍ[ℝ]) = 1 := by
  ext <;> simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
    Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one]
  · linear_combination Real.cos_sq_add_sin_sq ϑ
  all_goals ring

/-- WS3. **Along the middle axis** half the trace is `2 (cos² ϑ + sin² ϑ cos k)² - 1`. -/
theorem spaceMid_trace (ϑ k : ℝ) :
    trace (spaceMidWord ϑ k) =
      2 * ((2 * (Real.cos ϑ ^ 2 + Real.sin ϑ ^ 2 * Real.cos k) ^ 2 - 1 : ℝ) : ℂ) := by
  have h1 := quat_r_mul_ri ϑ
  have h2 := quat_ri_mul_r ϑ
  have c1 : ∀ x : ℍ[ℝ], (⟨Real.cos ϑ, Real.sin ϑ, 0, 0⟩ : ℍ[ℝ]) *
      ((⟨Real.cos ϑ, -Real.sin ϑ, 0, 0⟩ : ℍ[ℝ]) * x) = x := fun x => by
    rw [← mul_assoc, h1, one_mul]
  have c2 : ∀ x : ℍ[ℝ], (⟨Real.cos ϑ, -Real.sin ϑ, 0, 0⟩ : ℍ[ℝ]) *
      ((⟨Real.cos ϑ, Real.sin ϑ, 0, 0⟩ : ℍ[ℝ]) * x) = x := fun x => by
    rw [← mul_assoc, h2, one_mul]
  rw [spaceMidWord, naiveCoin_three, wilsonLayer_zero, wilsonLayer_pauliZ, naiveCoin_quat]
  simp only [← quatTable_mul]
  rw [quatTable_trace]
  conv_lhs => simp only [mul_assoc, c1, c2]
  rw [spaceMid_re, spaceMid_circle]

/-- WS3. **Along the first axis** half the trace is that of the middle axis plus
`8 cos² ϑ sin⁴ ϑ sin² k`. -/
theorem spaceEnd_trace (ϑ k : ℝ) :
    trace (spaceEndWord ϑ k) =
      2 * ((2 * (Real.cos ϑ ^ 2 + Real.sin ϑ ^ 2 * Real.cos k) ^ 2 - 1 +
        8 * Real.cos ϑ ^ 2 * Real.sin ϑ ^ 4 * Real.sin k ^ 2 : ℝ) : ℂ) := by
  have h1 := quat_r_mul_ri ϑ
  have h2 := quat_ri_mul_r ϑ
  have c1 : ∀ x : ℍ[ℝ], (⟨Real.cos ϑ, Real.sin ϑ, 0, 0⟩ : ℍ[ℝ]) *
      ((⟨Real.cos ϑ, -Real.sin ϑ, 0, 0⟩ : ℍ[ℝ]) * x) = x := fun x => by
    rw [← mul_assoc, h1, one_mul]
  have c2 : ∀ x : ℍ[ℝ], (⟨Real.cos ϑ, -Real.sin ϑ, 0, 0⟩ : ℍ[ℝ]) *
      ((⟨Real.cos ϑ, Real.sin ϑ, 0, 0⟩ : ℍ[ℝ]) * x) = x := fun x => by
    rw [← mul_assoc, h2, one_mul]
  rw [spaceEndWord, naiveCoin_three, wilsonLayer_zero, wilsonLayer_pauliZ, naiveCoin_quat]
  simp only [← quatTable_mul]
  rw [quatTable_trace]
  conv_lhs => simp only [mul_assoc, c1, c2]
  rw [spaceEnd_re, spaceMid_circle]

/-- WS3. **Along the third axis** half the trace is that of the first. -/
theorem spaceEnd3_trace (ϑ k : ℝ) :
    trace (spaceEnd3Word ϑ k) =
      2 * ((2 * (Real.cos ϑ ^ 2 + Real.sin ϑ ^ 2 * Real.cos k) ^ 2 - 1 +
        8 * Real.cos ϑ ^ 2 * Real.sin ϑ ^ 4 * Real.sin k ^ 2 : ℝ) : ℂ) := by
  have h1 := quat_r_mul_ri ϑ
  have h2 := quat_ri_mul_r ϑ
  have c1 : ∀ x : ℍ[ℝ], (⟨Real.cos ϑ, Real.sin ϑ, 0, 0⟩ : ℍ[ℝ]) *
      ((⟨Real.cos ϑ, -Real.sin ϑ, 0, 0⟩ : ℍ[ℝ]) * x) = x := fun x => by
    rw [← mul_assoc, h1, one_mul]
  have c2 : ∀ x : ℍ[ℝ], (⟨Real.cos ϑ, -Real.sin ϑ, 0, 0⟩ : ℍ[ℝ]) *
      ((⟨Real.cos ϑ, Real.sin ϑ, 0, 0⟩ : ℍ[ℝ]) * x) = x := fun x => by
    rw [← mul_assoc, h2, one_mul]
  rw [spaceEnd3Word, naiveCoin_three, wilsonLayer_zero, wilsonLayer_pauliZ, naiveCoin_quat]
  have cyc : ∀ x : ℍ[ℝ], ((⟨Real.cos ϑ, Real.sin ϑ, 0, 0⟩ : ℍ[ℝ]) *
      ((⟨Real.cos ϑ, Real.sin ϑ, 0, 0⟩ : ℍ[ℝ]) * x)).re =
      (x * ((⟨Real.cos ϑ, Real.sin ϑ, 0, 0⟩ : ℍ[ℝ]) * ⟨Real.cos ϑ, Real.sin ϑ, 0, 0⟩)).re :=
    fun x => by rw [← mul_assoc, quat_re_mul_comm]
  simp only [← quatTable_mul]
  rw [quatTable_trace]
  conv_lhs => simp only [mul_assoc, c1, c2]
  rw [cyc]
  conv_lhs => simp only [mul_assoc, c1, c2]
  rw [spaceEnd3_re, spaceMid_circle]

/-! ### WS4: the levels along the axes, and the middle axis faster -/

/-- The table of the middle-axis word has determinant `1`. -/
theorem spaceMidWord_det (ϑ k : ℝ) : det (spaceMidWord ϑ k) = 1 := by
  have hR : det (wilsonLayer pauliZ ϑ 0) = 1 := by
    rw [wilsonLayer_zero]
    exact quatTable_det_of_unit _ (by simp only; linear_combination Real.cos_sq_add_sin_sq ϑ)
  have hG : det (wilsonLayer pauliZ ϑ k) = 1 := by
    rw [wilsonLayer_pauliZ]
    exact quatTable_det_of_unit _ (by
      simp only
      linear_combination Real.sin ϑ ^ 2 * Real.sin_sq_add_cos_sq k + Real.sin_sq_add_cos_sq ϑ)
  have hC : det (naiveCoin (3 * ϑ)) = 1 := by
    rw [naiveCoin_quat]
    exact quatTable_det_of_unit _
      (by simp only; linear_combination Real.cos_sq_add_sin_sq (3 * ϑ))
  simp only [spaceMidWord, det_mul, hR, hG, hC, mul_one]

/-- The table of the first-axis word has determinant `1`. -/
theorem spaceEndWord_det (ϑ k : ℝ) : det (spaceEndWord ϑ k) = 1 := by
  have hR : det (wilsonLayer pauliZ ϑ 0) = 1 := by
    rw [wilsonLayer_zero]
    exact quatTable_det_of_unit _ (by simp only; linear_combination Real.cos_sq_add_sin_sq ϑ)
  have hG : det (wilsonLayer pauliZ ϑ k) = 1 := by
    rw [wilsonLayer_pauliZ]
    exact quatTable_det_of_unit _ (by
      simp only
      linear_combination Real.sin ϑ ^ 2 * Real.sin_sq_add_cos_sq k + Real.sin_sq_add_cos_sq ϑ)
  have hC : det (naiveCoin (3 * ϑ)) = 1 := by
    rw [naiveCoin_quat]
    exact quatTable_det_of_unit _
      (by simp only; linear_combination Real.cos_sq_add_sin_sq (3 * ϑ))
  simp only [spaceEndWord, det_mul, hR, hG, hC, mul_one]

/-- WS4. **Along the middle axis**, `e^{-iΩ}` is a level exactly when
`cos Ω = 2 (cos² ϑ + sin² ϑ cos k)² - 1`: the word turns by twice the angle `ω` with
`cos ω = cos² ϑ + sin² ϑ cos k`, light's dispersion with `c = sin ϑ`. -/
theorem spaceMid_level_iff (ϑ k Ω : ℝ) :
    (∃ v : Fin 2 → ℂ, v ≠ 0 ∧ spaceMidWord ϑ k *ᵥ v = Complex.exp (-(Ω : ℂ) * I) • v) ↔
      Real.cos Ω = 2 * (Real.cos ϑ ^ 2 + Real.sin ϑ ^ 2 * Real.cos k) ^ 2 - 1 :=
  level_iff_of_det_one (spaceMidWord_det ϑ k) (spaceMid_trace ϑ k) Ω

/-- WS4. **Along the first axis**, `e^{-iΩ}` is a level exactly when `cos Ω` is the middle axis'
value plus `8 cos² ϑ sin⁴ ϑ sin² k`. -/
theorem spaceEnd_level_iff (ϑ k Ω : ℝ) :
    (∃ v : Fin 2 → ℂ, v ≠ 0 ∧ spaceEndWord ϑ k *ᵥ v = Complex.exp (-(Ω : ℂ) * I) • v) ↔
      Real.cos Ω = 2 * (Real.cos ϑ ^ 2 + Real.sin ϑ ^ 2 * Real.cos k) ^ 2 - 1 +
        8 * Real.cos ϑ ^ 2 * Real.sin ϑ ^ 4 * Real.sin k ^ 2 :=
  level_iff_of_det_one (spaceEndWord_det ϑ k) (spaceEnd_trace ϑ k) Ω

/-- WS4. **The first axis is slower**: for every partial hop `0 < ϑ < π / 2`, at every wave
`0 < k < π`, the angle of the word along the first axis, in `[0, π]`, is less than along the middle
one. -/
theorem spaceEnd_slower {ϑ k Ω₁ Ω₂ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ < π / 2) (hk : 0 < k) (hk' : k < π)
    (h₁ : Ω₁ ∈ Icc 0 π) (h₂ : Ω₂ ∈ Icc 0 π)
    (hmid : Real.cos Ω₁ = 2 * (Real.cos ϑ ^ 2 + Real.sin ϑ ^ 2 * Real.cos k) ^ 2 - 1)
    (hend : Real.cos Ω₂ = 2 * (Real.cos ϑ ^ 2 + Real.sin ϑ ^ 2 * Real.cos k) ^ 2 - 1 +
      8 * Real.cos ϑ ^ 2 * Real.sin ϑ ^ 4 * Real.sin k ^ 2) :
    Ω₂ < Ω₁ := by
  have hc : 0 < Real.cos ϑ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hϑ'⟩
  have hs : 0 < Real.sin ϑ := Real.sin_pos_of_pos_of_lt_pi hϑ (by linarith [Real.pi_pos])
  have hsk : 0 < Real.sin k := Real.sin_pos_of_pos_of_lt_pi hk hk'
  have hpos : 0 < 8 * Real.cos ϑ ^ 2 * Real.sin ϑ ^ 4 * Real.sin k ^ 2 := by positivity
  have hlt : Real.cos Ω₁ < Real.cos Ω₂ := by rw [hmid, hend]; linarith
  by_contra hge
  have := Real.strictAntiOn_cos.antitoneOn h₁ h₂ (not_lt.mp hge)
  linarith

end Artform.Stages
