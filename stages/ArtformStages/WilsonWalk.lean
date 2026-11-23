import ArtformStages.OneSpeed

/-!
# The Wilson walk's speed in every direction (finding 494)

Wave N4 of campaign 15 of road DP. The fifteenth edition's OC asks that the walk of a universe with
light have light's speed in every direction; on the plane the walk that can meet it is the book's
Wilson walk, the word `(G_x G_y C)(G_y G_x C)` of the layers
`G_j(k) = cos ϑ - i sin ϑ (α_j sin k - β cos k)` and the coin `C(ν) = e^{-iνβ}`, with the book's
tables `α_x = σz`, `α_y = σy` and `β = -σx`. Here its speed is found in every direction.

* `quatTable`, `quatTable_eq`, `quatTable_mul`, `quatTable_trace`, `quatTable_det` (WW1): a
  quaternion `a + b i + c j + d k` read as the table `a - i (b σx + c σy + d σz)`; products go to
  products, the trace is `2 a`, the determinant `a² + b² + c² + d²`;
* `wilsonLayer`, `wilsonSymbol`, `wilsonLayer_pauliZ`, `wilsonLayer_pauliY`, `naiveCoin_quat`,
  `wilsonSymbol_det` (WW2): each factor of the word is the table of a unit quaternion, and the word
  has determinant `1`;
* `halfPull`, `halfProd`, `wilsonF`, `wilsonSymbol_trace`, `wilsonF_zero` (WW3): half the word's
  trace is a polynomial `F(S, P)` in light's pull over four, `S = sin²(k₁/2) + sin²(k₂/2)`, and in
  `P = sin²(k₁/2) sin²(k₂/2)`, and `F(0, 0) = cos (2 (ν - 2ϑ))`;
* `IsWilsonLevel`, `wilson_level_iff`, `wilson_level_swap`, `wilson_level_neg` (WW4): the levels
  obey `cos Ω = F(S, P)`, so the square's eight symmetries keep them;
* `wilsonK`, `wilson_one_speed` (WW5): along every direction `u` and at every `t`, half the trace
  is `F(0, 0) + F_S t² / 4` up to `K t⁴`, with `F_S` and `K` the same in every direction.

The proofs multiply quaternions, so that no `i` is left to square. None of this is new: the tables
of determinant `1` are the unit quaternions, and the walk is Wilson's on the square.
-/

open Matrix Complex
open scoped Real Quaternion

namespace Artform.Stages

/-! ### WW1: quaternions as tables -/

/-- A quaternion `a + b i + c j + d k` read as the table `a - i (b σx + c σy + d σz)`. -/
noncomputable def quatTable (q : ℍ[ℝ]) : Matrix (Fin 2) (Fin 2) ℂ :=
  (q.re : ℂ) • 1 - I • ((q.imI : ℂ) • pauliX + (q.imJ : ℂ) • pauliY + (q.imK : ℂ) • pauliZ)

/-- WW1. The table of a quaternion, entry by entry. -/
theorem quatTable_eq (q : ℍ[ℝ]) :
    quatTable q = !![(q.re : ℂ) - I * q.imK, -(I * q.imI) - q.imJ;
      -(I * q.imI) + q.imJ, (q.re : ℂ) + I * q.imK] := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [quatTable, pauliX, pauliY, pauliZ]
  · simp [quatTable, pauliX, pauliY, pauliZ]
    linear_combination (q.imJ : ℂ) * I_sq
  · simp [quatTable, pauliX, pauliY, pauliZ]
    linear_combination -(q.imJ : ℂ) * I_sq
  · simp [quatTable, pauliX, pauliY, pauliZ]

/-- WW1. **Products go to products.** -/
theorem quatTable_mul (p q : ℍ[ℝ]) : quatTable (p * q) = quatTable p * quatTable q := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [quatTable_eq, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- WW1. The trace of the table is twice the real part. -/
theorem quatTable_trace (q : ℍ[ℝ]) : trace (quatTable q) = 2 * (q.re : ℂ) := by
  rw [quatTable_eq, Matrix.trace_fin_two_of]
  ring

/-- WW1. The determinant of the table is the quaternion's square size. -/
theorem quatTable_det (q : ℍ[ℝ]) :
    det (quatTable q) = ((q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 : ℝ) : ℂ) := by
  rw [quatTable_eq, Matrix.det_fin_two_of]
  push_cast
  linear_combination (-((q.imI : ℂ) ^ 2 + (q.imK : ℂ) ^ 2)) * I_sq

/-! ### WW2: the book's layers, coin and word -/

/-- **The book's layer** along an axis of table `α` at the wave number `k`:
`cos ϑ - i sin ϑ (α sin k - β cos k)`, with `β = -σx`. -/
noncomputable def wilsonLayer (α : Matrix (Fin 2) (Fin 2) ℂ) (ϑ k : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (Real.cos ϑ : ℂ) • 1 - (I * Real.sin ϑ) • ((Real.sin k : ℂ) • α - (Real.cos k : ℂ) • naiveBeta)

/-- **The book's Wilson walk** on the plane at the wave number `(k₁, k₂)`: the word
`(G_x G_y C)(G_y G_x C)`, two ticks long, with `α_x = σz` and `α_y = σy`. -/
noncomputable def wilsonSymbol (ϑ ν k₁ k₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  wilsonLayer pauliZ ϑ k₁ * wilsonLayer pauliY ϑ k₂ * naiveCoin ν *
    (wilsonLayer pauliY ϑ k₂ * wilsonLayer pauliZ ϑ k₁ * naiveCoin ν)

/-- WW2. The layer along the first axis is the table of a unit quaternion. -/
theorem wilsonLayer_pauliZ (ϑ k : ℝ) :
    wilsonLayer pauliZ ϑ k =
      quatTable ⟨Real.cos ϑ, Real.sin ϑ * Real.cos k, 0, Real.sin ϑ * Real.sin k⟩ := by
  rw [quatTable_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wilsonLayer, naiveBeta, pauliX, pauliZ] <;> ring

/-- WW2. The layer along the second axis is the table of a unit quaternion. -/
theorem wilsonLayer_pauliY (ϑ k : ℝ) :
    wilsonLayer pauliY ϑ k =
      quatTable ⟨Real.cos ϑ, Real.sin ϑ * Real.cos k, Real.sin ϑ * Real.sin k, 0⟩ := by
  rw [quatTable_eq]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [wilsonLayer, naiveBeta, pauliX, pauliY]
  · simp [wilsonLayer, naiveBeta, pauliX, pauliY]
    linear_combination Complex.sin ϑ * Complex.sin k * I_sq
  · simp [wilsonLayer, naiveBeta, pauliX, pauliY]
    linear_combination -(Complex.sin ϑ * Complex.sin k) * I_sq
  · simp [wilsonLayer, naiveBeta, pauliX, pauliY]

/-- WW2. The book's coin is the table of a unit quaternion. -/
theorem naiveCoin_quat (ν : ℝ) : naiveCoin ν = quatTable ⟨Real.cos ν, -Real.sin ν, 0, 0⟩ := by
  rw [quatTable_eq, naiveCoin_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The table of a unit quaternion has determinant `1`. -/
theorem quatTable_det_of_unit (q : ℍ[ℝ]) (h : q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 = 1) :
    det (quatTable q) = 1 := by
  rw [quatTable_det, h, Complex.ofReal_one]

/-- WW2. **The Wilson word has determinant `1`.** -/
theorem wilsonSymbol_det (ϑ ν k₁ k₂ : ℝ) : det (wilsonSymbol ϑ ν k₁ k₂) = 1 := by
  have hZ : det (wilsonLayer pauliZ ϑ k₁) = 1 := by
    rw [wilsonLayer_pauliZ]
    refine quatTable_det_of_unit _ ?_
    simp only
    linear_combination Real.sin ϑ ^ 2 * Real.sin_sq_add_cos_sq k₁ + Real.sin_sq_add_cos_sq ϑ
  have hY : det (wilsonLayer pauliY ϑ k₂) = 1 := by
    rw [wilsonLayer_pauliY]
    refine quatTable_det_of_unit _ ?_
    simp only
    linear_combination Real.sin ϑ ^ 2 * Real.sin_sq_add_cos_sq k₂ + Real.sin_sq_add_cos_sq ϑ
  have hC : det (naiveCoin ν) = 1 := by
    rw [naiveCoin_quat]
    refine quatTable_det_of_unit _ ?_
    simp only
    linear_combination Real.sin_sq_add_cos_sq ν
  rw [wilsonSymbol, det_mul, det_mul, det_mul, det_mul, det_mul, hZ, hY, hC]
  ring

/-! ### WW3: half the trace, a polynomial in light's pull -/

/-- Light's pull on the plane over four: `sin²(k₁/2) + sin²(k₂/2)`. -/
noncomputable def halfPull (k₁ k₂ : ℝ) : ℝ := Real.sin (k₁ / 2) ^ 2 + Real.sin (k₂ / 2) ^ 2

/-- The product `sin²(k₁/2) sin²(k₂/2)`. -/
noncomputable def halfProd (k₁ k₂ : ℝ) : ℝ := Real.sin (k₁ / 2) ^ 2 * Real.sin (k₂ / 2) ^ 2

/-- The coefficients of half the word's trace, in `g = cos ϑ`, `h = sin ϑ`, `p = cos ν`,
`q = sin ν`: the constant. -/
def wilsonC00 (g h p q : ℝ) : ℝ :=
  (p ^ 2 - q ^ 2) * (g ^ 2 - h ^ 2) ^ 2 + 8 * p * q * g * h * (g ^ 2 - h ^ 2) +
    8 * q ^ 2 * g ^ 2 * h ^ 2 - 4 * (p ^ 2 + q ^ 2) * g ^ 2 * h ^ 2

/-- The coefficient of `S`. -/
def wilsonC10 (g h p q : ℝ) : ℝ :=
  4 * h ^ 2 * (g ^ 2 - h ^ 2) * (p ^ 2 - q ^ 2) +
    8 * p * q * g * h * (2 * h ^ 2 - (g ^ 2 - h ^ 2)) -
    16 * q ^ 2 * g ^ 2 * h ^ 2 + 4 * (p ^ 2 + q ^ 2) * (g ^ 2 * h ^ 2 + h ^ 4)

/-- The coefficient of `P`. -/
def wilsonC01 (g h p q : ℝ) : ℝ :=
  -8 * h ^ 2 * (g ^ 2 - h ^ 2) * (p ^ 2 - q ^ 2) - 32 * p * q * g * h ^ 3 - 32 * q ^ 2 * h ^ 4 -
    8 * (p ^ 2 + q ^ 2) * (g ^ 2 * h ^ 2 + h ^ 4)

/-- The coefficient of `S²`. -/
def wilsonC20 (g h p q : ℝ) : ℝ :=
  4 * h ^ 4 * (p ^ 2 - q ^ 2) - 16 * p * q * g * h ^ 3 + 8 * q ^ 2 * g ^ 2 * h ^ 2 -
    4 * (p ^ 2 + q ^ 2) * h ^ 4

/-- The coefficient of `S P`. -/
def wilsonC11 (g h p q : ℝ) : ℝ :=
  -16 * h ^ 4 * (p ^ 2 - q ^ 2) + 32 * p * q * g * h ^ 3 + 32 * q ^ 2 * h ^ 4 +
    16 * (p ^ 2 + q ^ 2) * h ^ 4

/-- The coefficient of `P²`. -/
def wilsonC02 (_g h p q : ℝ) : ℝ :=
  16 * h ^ 4 * (p ^ 2 - q ^ 2) - 32 * q ^ 2 * h ^ 4 - 16 * (p ^ 2 + q ^ 2) * h ^ 4

/-- The polynomial `F(S, P)`. -/
def wilsonPoly (g h p q S P : ℝ) : ℝ :=
  wilsonC00 g h p q + wilsonC10 g h p q * S + wilsonC01 g h p q * P + wilsonC20 g h p q * S ^ 2 +
    wilsonC11 g h p q * S * P + wilsonC02 g h p q * P ^ 2

/-- **Half the Wilson word's trace**, as a function of `S` and `P`. -/
noncomputable def wilsonF (ϑ ν S P : ℝ) : ℝ :=
  wilsonPoly (Real.cos ϑ) (Real.sin ϑ) (Real.cos ν) (Real.sin ν) S P

/-- Half the trace in the cosines and the squared sines of the wave numbers. -/
def wilsonRaw (g h p q c₁ t₁ c₂ t₂ : ℝ) : ℝ :=
  (p ^ 2 - q ^ 2) * (g ^ 2 - h ^ 2 * c₁ * c₂) ^ 2 +
    4 * p * q * (g ^ 2 - h ^ 2 * c₁ * c₂) * g * h * (c₁ + c₂) +
    2 * q ^ 2 * (g ^ 2 * h ^ 2 * (c₁ + c₂) ^ 2 - h ^ 4 * t₁ * t₂) -
    (p ^ 2 + q ^ 2) * (g ^ 2 * h ^ 2 * (c₁ ^ 2 + t₁ + c₂ ^ 2 + t₂ + 2 * c₁ * c₂) -
      h ^ 4 * (t₁ * t₂ + t₁ * c₂ ^ 2 + c₁ ^ 2 * t₂))

/-- The real part of the word's quaternion. -/
theorem wilson_re (g h p q c₁ s₁ c₂ s₂ : ℝ) :
    ((⟨g, h * c₁, 0, h * s₁⟩ * ⟨g, h * c₂, h * s₂, 0⟩ * ⟨p, -q, 0, 0⟩ *
      (⟨g, h * c₂, h * s₂, 0⟩ * ⟨g, h * c₁, 0, h * s₁⟩ * ⟨p, -q, 0, 0⟩) : ℍ[ℝ])).re =
      wilsonRaw g h p q c₁ (s₁ ^ 2) c₂ (s₂ ^ 2) := by
  simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
  unfold wilsonRaw
  ring

/-- In the half angles, the raw form is `F(S, P)`. -/
theorem wilsonRaw_half (g h p q x₁ x₂ : ℝ) :
    wilsonRaw g h p q (1 - 2 * x₁) (4 * x₁ * (1 - x₁)) (1 - 2 * x₂) (4 * x₂ * (1 - x₂)) =
      wilsonPoly g h p q (x₁ + x₂) (x₁ * x₂) := by
  unfold wilsonRaw wilsonPoly wilsonC00 wilsonC10 wilsonC01 wilsonC20 wilsonC11 wilsonC02
  ring

/-- `sin² k = 4 sin²(k/2) (1 - sin²(k/2))`. -/
theorem sin_sq_eq_half (k : ℝ) :
    Real.sin k ^ 2 = 4 * Real.sin (k / 2) ^ 2 * (1 - Real.sin (k / 2) ^ 2) := by
  have h1 : Real.sin k = 2 * Real.sin (k / 2) * Real.cos (k / 2) := by
    rw [← Real.sin_two_mul]
    ring_nf
  rw [h1]
  linear_combination (4 * Real.sin (k / 2) ^ 2) * Real.sin_sq_add_cos_sq (k / 2)

/-- WW3. **Half the Wilson word's trace is `F(S, P)`.** -/
theorem wilsonSymbol_trace (ϑ ν k₁ k₂ : ℝ) :
    trace (wilsonSymbol ϑ ν k₁ k₂) = 2 * (wilsonF ϑ ν (halfPull k₁ k₂) (halfProd k₁ k₂) : ℂ) := by
  rw [wilsonSymbol, wilsonLayer_pauliZ, wilsonLayer_pauliY, naiveCoin_quat]
  simp only [← quatTable_mul]
  rw [quatTable_trace, wilson_re, cos_eq_one_sub_sin_sq_half k₁, cos_eq_one_sub_sin_sq_half k₂,
    sin_sq_eq_half k₁, sin_sq_eq_half k₂, wilsonRaw_half]
  rfl

/-- WW3. At the wave `0`, half the trace is `cos (2 (ν - 2ϑ))`: the book's mass per tick is
`ν - 2ϑ`. -/
theorem wilsonF_zero (ϑ ν : ℝ) : wilsonF ϑ ν 0 0 = Real.cos (2 * (ν - 2 * ϑ)) := by
  have e : 2 * (ν - 2 * ϑ) = 2 * ν - 2 * (2 * ϑ) := by ring
  rw [e, Real.cos_sub, Real.cos_two_mul ν, Real.sin_two_mul ν, Real.cos_two_mul (2 * ϑ),
    Real.sin_two_mul (2 * ϑ), Real.cos_two_mul ϑ, Real.sin_two_mul ϑ]
  unfold wilsonF wilsonPoly wilsonC00
  simp only [Real.sin_sq]
  ring

/-! ### WW4: the levels and the square's symmetries -/

/-- A level of the Wilson walk at the wave number `(k₁, k₂)`: `e^{-iΩ}` is an eigenvalue of its
word. -/
def IsWilsonLevel (ϑ ν k₁ k₂ Ω : ℝ) : Prop :=
  ∃ v : Fin 2 → ℂ, v ≠ 0 ∧ wilsonSymbol ϑ ν k₁ k₂ *ᵥ v = Complex.exp (-(Ω : ℂ) * I) • v

/-- WW4. **The levels**: `e^{-iΩ}` is a level exactly when `cos Ω = F(S, P)`. -/
theorem wilson_level_iff (ϑ ν k₁ k₂ Ω : ℝ) :
    IsWilsonLevel ϑ ν k₁ k₂ Ω ↔ Real.cos Ω = wilsonF ϑ ν (halfPull k₁ k₂) (halfProd k₁ k₂) :=
  level_iff_of_det_one (wilsonSymbol_det ϑ ν k₁ k₂) (wilsonSymbol_trace ϑ ν k₁ k₂) Ω

/-- WW4. **The axes may be swapped.** -/
theorem wilson_level_swap (ϑ ν k₁ k₂ Ω : ℝ) :
    IsWilsonLevel ϑ ν k₂ k₁ Ω ↔ IsWilsonLevel ϑ ν k₁ k₂ Ω := by
  have hS : halfPull k₂ k₁ = halfPull k₁ k₂ := add_comm _ _
  have hP : halfProd k₂ k₁ = halfProd k₁ k₂ := mul_comm _ _
  rw [wilson_level_iff, wilson_level_iff, hS, hP]

/-- WW4. **Either wave number may change its sign.** With the swap, the square's eight symmetries
keep the levels. -/
theorem wilson_level_neg (ϑ ν k₁ k₂ Ω : ℝ) :
    (IsWilsonLevel ϑ ν (-k₁) k₂ Ω ↔ IsWilsonLevel ϑ ν k₁ k₂ Ω) ∧
      (IsWilsonLevel ϑ ν k₁ (-k₂) Ω ↔ IsWilsonLevel ϑ ν k₁ k₂ Ω) := by
  have h : ∀ k : ℝ, Real.sin (-k / 2) ^ 2 = Real.sin (k / 2) ^ 2 := fun k => by
    rw [neg_div, Real.sin_neg, neg_sq]
  refine ⟨?_, ?_⟩ <;> rw [wilson_level_iff, wilson_level_iff, halfPull, halfPull, halfProd,
    halfProd, h]

/-! ### WW5: one speed in every direction -/

/-- The bound of the fourth order, made from the sizes of the coefficients. -/
noncomputable def wilsonK (ϑ ν : ℝ) : ℝ :=
  let g := Real.cos ϑ
  let h := Real.sin ϑ
  let p := Real.cos ν
  let q := Real.sin ν
  |wilsonC10 g h p q| / 48 + |wilsonC01 g h p q| / 64 + |wilsonC20 g h p q| / 16 +
    |wilsonC11 g h p q| / 32 + |wilsonC02 g h p q| / 64

theorem abs_add_five (a b c d f : ℝ) : |a + b + c + d + f| ≤ |a| + |b| + |c| + |d| + |f| := by
  calc |a + b + c + d + f| ≤ |a + b + c + d| + |f| := abs_add_le _ _
    _ ≤ |a + b + c| + |d| + |f| := by gcongr; exact abs_add_le _ _
    _ ≤ |a + b| + |c| + |d| + |f| := by gcongr; exact abs_add_le _ _
    _ ≤ |a| + |b| + |c| + |d| + |f| := by gcongr; exact abs_add_le _ _

/-- WW5. **One speed in every direction**: along every direction `u` and at every `t`, half the
Wilson word's trace is `F(0, 0) + F_S t² / 4` up to `K t⁴`, with `F_S` and `K` the same in every
direction. -/
theorem wilson_one_speed (ϑ ν u₁ u₂ t : ℝ) (hu : u₁ ^ 2 + u₂ ^ 2 = 1) :
    |wilsonF ϑ ν (halfPull (t * u₁) (t * u₂)) (halfProd (t * u₁) (t * u₂)) - wilsonF ϑ ν 0 0 -
        wilsonC10 (Real.cos ϑ) (Real.sin ϑ) (Real.cos ν) (Real.sin ν) * t ^ 2 / 4| ≤
      wilsonK ϑ ν * t ^ 4 := by
  set g := Real.cos ϑ
  set h := Real.sin ϑ
  set p := Real.cos ν
  set q := Real.sin ν
  set x₁ := Real.sin (t * u₁ / 2) ^ 2 with hx₁
  set x₂ := Real.sin (t * u₂ / 2) ^ 2 with hx₂
  have hS : halfPull (t * u₁) (t * u₂) = x₁ + x₂ := rfl
  have hP : halfProd (t * u₁) (t * u₂) = x₁ * x₂ := rfl
  rw [hS, hP]
  set S := x₁ + x₂ with hSdef
  set P := x₁ * x₂ with hPdef
  -- the sizes of the half angles
  have h0₁ : 0 ≤ x₁ := sq_nonneg _
  have h0₂ : 0 ≤ x₂ := sq_nonneg _
  have h1₁ : x₁ ≤ 1 := Real.sin_sq_le_one _
  have h1₂ : x₂ ≤ 1 := Real.sin_sq_le_one _
  obtain ⟨hl₁, hu₁⟩ := four_sin_sq_half_bounds (t * u₁)
  obtain ⟨hl₂, hu₂⟩ := four_sin_sq_half_bounds (t * u₂)
  have hsq : (t * u₁) ^ 2 + (t * u₂) ^ 2 = t ^ 2 := by
    rw [mul_pow, mul_pow, ← mul_add, hu, mul_one]
  have hq4 : (t * u₁) ^ 4 + (t * u₂) ^ 4 ≤ t ^ 4 := by
    have h4 : u₁ ^ 4 + u₂ ^ 4 ≤ 1 := by nlinarith [sq_nonneg (u₁ * u₂)]
    have ht4 : 0 ≤ t ^ 4 := by positivity
    calc (t * u₁) ^ 4 + (t * u₂) ^ 4 = t ^ 4 * (u₁ ^ 4 + u₂ ^ 4) := by ring
      _ ≤ t ^ 4 * 1 := mul_le_mul_of_nonneg_left h4 ht4
      _ = t ^ 4 := mul_one _
  have hSle : S ≤ t ^ 2 / 4 := by linarith
  have hSge : t ^ 2 / 4 - t ^ 4 / 48 ≤ S := by linarith
  have hS0 : 0 ≤ S := by linarith
  have hS2 : S ≤ 2 := by linarith
  have hP0 : 0 ≤ P := mul_nonneg h0₁ h0₂
  have hP1 : P ≤ 1 := by nlinarith
  have hPS : P ≤ S ^ 2 / 4 := by nlinarith [sq_nonneg (x₁ - x₂)]
  -- the bounds of each term
  have bS : |S - t ^ 2 / 4| ≤ t ^ 4 / 48 := by
    rw [abs_le]
    constructor <;> linarith
  have bS2 : S ^ 2 ≤ t ^ 4 / 16 := by
    have := pow_le_pow_left₀ hS0 hSle 2
    calc S ^ 2 ≤ (t ^ 2 / 4) ^ 2 := this
      _ = t ^ 4 / 16 := by ring
  have bP : P ≤ t ^ 4 / 64 := by linarith
  have bSP : S * P ≤ t ^ 4 / 32 := by
    have h1 : S * P ≤ S * (S ^ 2 / 4) := mul_le_mul_of_nonneg_left hPS hS0
    have h2 : S * (S ^ 2 / 4) ≤ S ^ 2 / 2 := by nlinarith
    linarith
  have bP2 : P ^ 2 ≤ t ^ 4 / 64 := by nlinarith
  -- the difference, term by term
  have hdiff : wilsonF ϑ ν S P - wilsonF ϑ ν 0 0 - wilsonC10 g h p q * t ^ 2 / 4 =
      wilsonC10 g h p q * (S - t ^ 2 / 4) + wilsonC01 g h p q * P + wilsonC20 g h p q * S ^ 2 +
        wilsonC11 g h p q * (S * P) + wilsonC02 g h p q * P ^ 2 := by
    unfold wilsonF wilsonPoly
    ring
  rw [hdiff]
  have term : ∀ c X B : ℝ, |X| ≤ B → |c * X| ≤ |c| * B := fun c X B hX => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hX (abs_nonneg c)
  have k1 := term (wilsonC10 g h p q) _ _ bS
  have k2 := term (wilsonC01 g h p q) P (t ^ 4 / 64) (by rw [abs_of_nonneg hP0]; exact bP)
  have k3 := term (wilsonC20 g h p q) (S ^ 2) (t ^ 4 / 16)
    (by rw [abs_of_nonneg (sq_nonneg S)]; exact bS2)
  have k4 := term (wilsonC11 g h p q) (S * P) (t ^ 4 / 32)
    (by rw [abs_of_nonneg (mul_nonneg hS0 hP0)]; exact bSP)
  have k5 := term (wilsonC02 g h p q) (P ^ 2) (t ^ 4 / 64)
    (by rw [abs_of_nonneg (sq_nonneg P)]; exact bP2)
  have k0 := abs_add_five (wilsonC10 g h p q * (S - t ^ 2 / 4)) (wilsonC01 g h p q * P)
    (wilsonC20 g h p q * S ^ 2) (wilsonC11 g h p q * (S * P)) (wilsonC02 g h p q * P ^ 2)
  have hK : wilsonK ϑ ν * t ^ 4 =
      |wilsonC10 g h p q| * (t ^ 4 / 48) + |wilsonC01 g h p q| * (t ^ 4 / 64) +
        |wilsonC20 g h p q| * (t ^ 4 / 16) + |wilsonC11 g h p q| * (t ^ 4 / 32) +
        |wilsonC02 g h p q| * (t ^ 4 / 64) := by
    simp only [wilsonK]
    ring
  rw [hK]
  linarith

end Artform.Stages
