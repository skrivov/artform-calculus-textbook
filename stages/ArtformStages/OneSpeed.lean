import ArtformStages.TheWalk
import ArtformStages.WeylKind
import ArtformStages.SpeedEveryDirection

/-!
# One speed: the walk's waves beside light's (finding 488)

Wave L6 of campaign 14 of road DP. On a line the walk of finding 476, whose levels `e^{-iε}` obey
`cos ε = cos μ cos k`, and light on one mode, Pair's table `modeTick` of finding 483 on the mode of
pull `4 sin²(k/2)`, have dispersions of one shape: `sin²(ε/2) = sin²(μ/2) + cos μ sin²(k/2)` and
`sin²(ω/2) = κl sin²(k/2)` (OS1). At `μ = 0` and `κl = 1` they are one (OS2); at the shortest wave
`k = π` light is then at its limit, where its table is not a swing.

On the plane, the book's naive walk `W = S_y S_x C(μ)`, with `α_x = σz`, `α_y = σy` and `β = -σx`,
has half its trace `cos μ cos k₁ cos k₂ + sin μ sin k₁ sin k₂`; along an axis it is the walk of
the line, and at `μ = 0` there it is the bare shift, one cell at every tick, at every wave. Light
below Courant's limit in the plane, `κl ≤ 1/2`, turns by less than the wave number at every wave
along an axis, so it is slower than the massless walk there (OS3).
-/

open Matrix Complex Set
open scoped Real

namespace Artform.Stages

/-! ### OS1: two dispersions of one shape -/

/-- `cos x = 1 - 2 sin²(x/2)`. -/
theorem cos_eq_one_sub_sin_sq_half (x : ℝ) : Real.cos x = 1 - 2 * Real.sin (x / 2) ^ 2 := by
  have h := Real.cos_sq_add_sin_sq (x / 2)
  have h2 := Real.cos_two_mul (x / 2)
  rw [show 2 * (x / 2) = x by ring] at h2
  linarith

/-- **OS1**, the walk: `e^{-iε}` is a level of the walk on a line at the wave number `k` exactly
when `sin²(ε/2) = sin²(μ/2) + cos μ sin²(k/2)`. -/
theorem walk_level_iff_half (μ k ε : ℝ) :
    IsWalkLevel μ k ε ↔
      Real.sin (ε / 2) ^ 2 = Real.sin (μ / 2) ^ 2 + Real.cos μ * Real.sin (k / 2) ^ 2 := by
  rw [walk_level_iff]
  have hε := cos_eq_one_sub_sin_sq_half ε
  have hμ := cos_eq_one_sub_sin_sq_half μ
  have hk := cos_eq_one_sub_sin_sq_half k
  constructor
  · intro h
    linear_combination (-1 / 2 : ℝ) * h + (1 / 2 : ℝ) * hε + (-1 / 2 : ℝ) * hμ +
      (-Real.cos μ / 2) * hk
  · intro h
    linear_combination (-2 : ℝ) * h + hε - hμ - Real.cos μ * hk

/-- **OS1**, light: the trace of Pair on the mode of pull `4 sin²(k/2)` is `2 cos ω` exactly when
`sin²(ω/2) = κl sin²(k/2)`. -/
theorem light_turn_iff_half (κ l k ω : ℝ) :
    (modeTick κ l (4 * Real.sin (k / 2) ^ 2)).trace = 2 * Real.cos ω ↔
      Real.sin (ω / 2) ^ 2 = κ * l * Real.sin (k / 2) ^ 2 := by
  rw [modeTick_trace]
  have hω := cos_eq_one_sub_sin_sq_half ω
  constructor
  · intro h
    linear_combination (1 / 4 : ℝ) * h + (1 / 2 : ℝ) * hω
  · intro h
    linear_combination (4 : ℝ) * h - (2 : ℝ) * hω

/-! ### OS2: one speed on a line -/

/-- The massless walk is the bare shift: the first number of every place moves one place on and
the second one place back, at every tick. -/
theorem coin_zero : coin 0 = 1 := by
  simp [coin]

theorem walk_zero {N : ℕ} (ψ : ZMod N → Fin 2 → ℂ) : walk 0 ψ = partShift ψ := by
  simp [walk, coin_zero]

/-- **OS2**: at `μ = 0` and `κl = 1` the massless walk and light on a line have one dispersion,
`sin²(ε/2) = sin²(k/2) = sin²(ω/2)`. -/
theorem one_speed_on_a_line {κ l k ε ω : ℝ} (hκl : κ * l = 1) (hε : IsWalkLevel 0 k ε)
    (hω : (modeTick κ l (4 * Real.sin (k / 2) ^ 2)).trace = 2 * Real.cos ω) :
    Real.sin (ε / 2) ^ 2 = Real.sin (k / 2) ^ 2 ∧ Real.sin (ω / 2) ^ 2 = Real.sin (k / 2) ^ 2 := by
  refine ⟨?_, ?_⟩
  · have h := (walk_level_iff_half 0 k ε).mp hε
    simpa using h
  · have h := (light_turn_iff_half κ l k ω).mp hω
    rwa [hκl, one_mul] at h

/-- On `[0, π]` an angle is fixed by the square of the sine of its half. -/
theorem eq_of_sin_sq_half_eq {x y : ℝ} (hx : x ∈ Icc 0 π) (hy : y ∈ Icc 0 π)
    (h : Real.sin (x / 2) ^ 2 = Real.sin (y / 2) ^ 2) : x = y := by
  have hx' : x / 2 ∈ Icc (-(π / 2)) (π / 2) := ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2]⟩
  have hy' : y / 2 ∈ Icc (-(π / 2)) (π / 2) := ⟨by linarith [hy.1, Real.pi_pos], by linarith [hy.2]⟩
  have sx : 0 ≤ Real.sin (x / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hx.1]) (by linarith [hx.2, Real.pi_pos])
  have sy : 0 ≤ Real.sin (y / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hy.1]) (by linarith [hy.2, Real.pi_pos])
  have hs := (sq_eq_sq₀ sx sy).mp h
  have := Real.injOn_sin hx' hy' hs
  linarith

/-- **OS2**: so with the angles in `[0, π]`, the massless walk's level and light's turn are both
the wave number: `ε = k` and `ω = k`, at every wave. -/
theorem one_speed_on_a_line_eq {κ l k ε ω : ℝ} (hκl : κ * l = 1) (hk : k ∈ Icc 0 π)
    (hε0 : ε ∈ Icc 0 π) (hω0 : ω ∈ Icc 0 π) (hε : IsWalkLevel 0 k ε)
    (hω : (modeTick κ l (4 * Real.sin (k / 2) ^ 2)).trace = 2 * Real.cos ω) : ε = k ∧ ω = k := by
  obtain ⟨h1, h2⟩ := one_speed_on_a_line hκl hε hω
  exact ⟨eq_of_sin_sq_half_eq hε0 hk h1, eq_of_sin_sq_half_eq hω0 hk h2⟩

/-- At the limit, `κ l g = 4`, Pair's table on the mode is not a swing: it is `-1` plus a table
that is not `0` and whose square is `0`, so the mode grows by one step at every tick. On a line at
`κl = 1` this is the shortest wave, `k = π`. -/
theorem modeTick_at_limit {κ l g : ℝ} (h : κ * l * g = 4) :
    modeTick κ l g + 1 ≠ 0 ∧ (modeTick κ l g + 1) ^ 2 = 0 := by
  have hM : modeTick κ l g + 1 = !![2 - κ * l * g, -l; κ * g, 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [modeTick] <;> ring
  rw [hM]
  constructor
  · intro h0
    have := congrFun (congrFun h0 1) 1
    simp at this
  · rw [sq, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    · linear_combination (κ * l * g - 1) * h
    · linear_combination l * h
    · linear_combination (-(κ * g)) * h
    · linear_combination (-1 : ℝ) * h

/-! ### OS3: the naive walk on the plane -/

/-- The book's `β = -σx`; with `α_x = σz` and `α_y = σy` the three square to `1` and anticommute in
pairs. -/
def naiveBeta : Matrix (Fin 2) (Fin 2) ℂ := -pauliX

/-- The conditional shift on a plane wave, `e^{-i α k} = cos k - i α sin k`. -/
noncomputable def planeShift (α : Matrix (Fin 2) (Fin 2) ℂ) (k : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Real.cos k : ℂ) • 1 - (I * Real.sin k) • α

/-- The book's coin, `C(μ) = e^{-iμβ} = cos μ - i β sin μ`. -/
noncomputable def naiveCoin (μ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Real.cos μ : ℂ) • 1 - (I * Real.sin μ) • naiveBeta

/-- The book's naive walk on the plane at the wave number `(k₁, k₂)`: `W = S_y S_x C(μ)`, the coin
first. -/
noncomputable def naiveSymbol (μ k₁ k₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  planeShift pauliY k₂ * planeShift pauliZ k₁ * naiveCoin μ

theorem planeShift_pauliZ (k : ℝ) :
    planeShift pauliZ k =
      !![(Real.cos k : ℂ) - I * Real.sin k, 0; 0, (Real.cos k : ℂ) + I * Real.sin k] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [planeShift, pauliZ]

theorem planeShift_pauliY (k : ℝ) :
    planeShift pauliY k =
      !![(Real.cos k : ℂ), -(Real.sin k : ℂ); (Real.sin k : ℂ), Real.cos k] := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [planeShift, pauliY]
  · simp [planeShift, pauliY]
    linear_combination Complex.sin (k : ℂ) * Complex.I_sq
  · simp [planeShift, pauliY]
    linear_combination -Complex.sin (k : ℂ) * Complex.I_sq
  · simp [planeShift, pauliY]

theorem naiveCoin_eq (μ : ℝ) :
    naiveCoin μ = !![(Real.cos μ : ℂ), I * Real.sin μ; I * Real.sin μ, (Real.cos μ : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [naiveCoin, naiveBeta, pauliX]

/-- **OS3**: half the trace of the naive walk is `cos μ cos k₁ cos k₂ + sin μ sin k₁ sin k₂`. -/
theorem naiveSymbol_trace (μ k₁ k₂ : ℝ) :
    trace (naiveSymbol μ k₁ k₂) =
      2 * ((Real.cos μ * Real.cos k₁ * Real.cos k₂ +
        Real.sin μ * Real.sin k₁ * Real.sin k₂ : ℝ) : ℂ) := by
  rw [naiveSymbol, planeShift_pauliY, planeShift_pauliZ, naiveCoin_eq, Matrix.mul_fin_two,
    Matrix.mul_fin_two, Matrix.trace_fin_two_of]
  simp only [Complex.ofReal_add, Complex.ofReal_mul]
  linear_combination (-2 * (Real.sin μ : ℂ) * Real.sin k₁ * Real.sin k₂) * Complex.I_sq

theorem cos_sq_add_sin_sq_complex (x : ℝ) : (Real.cos x : ℂ) ^ 2 + (Real.sin x : ℂ) ^ 2 = 1 := by
  exact_mod_cast Real.cos_sq_add_sin_sq x

/-- **OS3**: the naive walk's table has determinant `1`. -/
theorem naiveSymbol_det (μ k₁ k₂ : ℝ) : det (naiveSymbol μ k₁ k₂) = 1 := by
  have hY : det (planeShift pauliY k₂) = 1 := by
    rw [planeShift_pauliY, Matrix.det_fin_two_of]
    linear_combination cos_sq_add_sin_sq_complex k₂
  have hZ : det (planeShift pauliZ k₁) = 1 := by
    rw [planeShift_pauliZ, Matrix.det_fin_two_of]
    linear_combination cos_sq_add_sin_sq_complex k₁ - (Real.sin k₁ : ℂ) ^ 2 * Complex.I_sq
  have hC : det (naiveCoin μ) = 1 := by
    rw [naiveCoin_eq, Matrix.det_fin_two_of]
    linear_combination cos_sq_add_sin_sq_complex μ - (Real.sin μ : ℂ) ^ 2 * Complex.I_sq
  rw [naiveSymbol, det_mul, det_mul, hY, hZ, hC, one_mul, one_mul]

/-- For a table of determinant `1` and trace `2t`, `t` real, `e^{-iε}` is an eigenvalue exactly when
`cos ε = t`. -/
theorem level_iff_of_det_one {M : Matrix (Fin 2) (Fin 2) ℂ} {t : ℝ} (hdet : M.det = 1)
    (htr : M.trace = 2 * (t : ℂ)) (ε : ℝ) :
    (∃ v : Fin 2 → ℂ, v ≠ 0 ∧ M *ᵥ v = Complex.exp (-(ε : ℂ) * I) • v) ↔ Real.cos ε = t := by
  have h1 : Complex.exp (-(ε : ℂ) * I) * Complex.exp ((ε : ℂ) * I) = 1 := by
    rw [← Complex.exp_add, neg_mul, neg_add_cancel, Complex.exp_zero]
  have h2 := Complex.two_cos (ε : ℂ)
  rw [← Complex.ofReal_cos] at h2
  have hc : ∀ c : ℂ, (M - c • 1).det = c ^ 2 - M.trace * c + M.det := by
    intro c
    rw [det_fin_two, trace_fin_two, det_fin_two]
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    rw [Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
      Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), mul_zero, sub_zero, sub_zero]
    ring
  have key : (M - Complex.exp (-(ε : ℂ) * I) • 1).det =
      Complex.exp (-(ε : ℂ) * I) * (2 * ((Real.cos ε : ℂ) - (t : ℂ))) := by
    rw [hc, htr, hdet]
    linear_combination -h1 - Complex.exp (-(ε : ℂ) * I) * h2
  rw [eigen_iff_det, key, mul_eq_zero, mul_eq_zero, sub_eq_zero]
  simp only [Complex.exp_ne_zero, two_ne_zero, false_or]
  exact_mod_cast Iff.rfl

/-- A level of the naive walk at the wave number `(k₁, k₂)`: `e^{-iε}` is an eigenvalue of its
table. -/
def IsNaiveLevel (μ k₁ k₂ ε : ℝ) : Prop :=
  ∃ v : Fin 2 → ℂ, v ≠ 0 ∧ naiveSymbol μ k₁ k₂ *ᵥ v = Complex.exp (-(ε : ℂ) * I) • v

/-- **OS3**: `e^{-iε}` is a level of the naive walk exactly when
`cos ε = cos μ cos k₁ cos k₂ + sin μ sin k₁ sin k₂`. -/
theorem naive_level_iff (μ k₁ k₂ ε : ℝ) :
    IsNaiveLevel μ k₁ k₂ ε ↔
      Real.cos ε =
        Real.cos μ * Real.cos k₁ * Real.cos k₂ + Real.sin μ * Real.sin k₁ * Real.sin k₂ :=
  level_iff_of_det_one (naiveSymbol_det μ k₁ k₂) (naiveSymbol_trace μ k₁ k₂) ε

/-- The book's coin is the coin of finding 476 at the opposite angle. -/
theorem naiveCoin_eq_coin (μ : ℝ) : naiveCoin μ = coin (-μ) := by
  rw [naiveCoin_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coin, pauliX]

/-- **OS3**: along the first axis the naive walk is the walk of the line, at the opposite angle. -/
theorem naiveSymbol_axis (μ k : ℝ) : naiveSymbol μ k 0 = walkSymbol (-μ) k := by
  have hY : planeShift pauliY 0 = 1 := by
    simp [planeShift]
  rw [naiveSymbol, hY, one_mul, naiveCoin_eq_coin, walkSymbol, walkShift_diagonal, planeShift]

/-- **OS3**: at `μ = 0` along the first axis the naive walk is the bare shift,
`diag(e^{-ik}, e^{ik})`: one cell at every tick, at every wave. -/
theorem naive_massless_axis (k : ℝ) :
    naiveSymbol 0 k 0 = diagonal ![Complex.exp (-(k : ℂ) * I), Complex.exp ((k : ℂ) * I)] := by
  rw [naiveSymbol_axis, neg_zero, walkSymbol, coin_zero, mul_one]

/-- **OS3**: at `μ = 0` along either axis the naive walk's levels obey `cos ε = cos k`. -/
theorem naive_massless_axes_level (k ε : ℝ) :
    (IsNaiveLevel 0 k 0 ε ↔ Real.cos ε = Real.cos k) ∧
      (IsNaiveLevel 0 0 k ε ↔ Real.cos ε = Real.cos k) := by
  rw [naive_level_iff, naive_level_iff]
  simp

/-- Along the first axis of the plane the pull of the wave `(k, 0)` is `4 sin²(k/2)`. -/
theorem axis_pull (k : ℝ) :
    ∑ j : Fin 2, 4 * Real.sin (![k, 0] j / 2) ^ 2 = 4 * Real.sin (k / 2) ^ 2 := by
  simp [Fin.sum_univ_two]

/-- **OS3**, light: below the limit of the line, `κl < 1`, light on the mode of pull `4 sin²(k/2)`
turns by `ω < k` at every wave `0 < k ≤ π`. -/
theorem light_slower {κ l k ω : ℝ} (hκl : κ * l < 1) (hk : 0 < k) (hkπ : k ≤ π) (hω : 0 ≤ ω)
    (hωπ : ω ≤ π) (h : (modeTick κ l (4 * Real.sin (k / 2) ^ 2)).trace = 2 * Real.cos ω) :
    ω < k := by
  have h1 := (light_turn_iff_half κ l k ω).mp h
  have hs : 0 < Real.sin (k / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hω' : 0 ≤ Real.sin (ω / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  have hsq : Real.sin (ω / 2) ^ 2 < Real.sin (k / 2) ^ 2 := by
    rw [h1]
    have := pow_pos hs 2
    nlinarith
  have hlt : Real.sin (ω / 2) < Real.sin (k / 2) := by
    by_contra hc
    have hc' := not_lt.mp hc
    nlinarith
  have hmem : ∀ x : ℝ, 0 ≤ x → x ≤ π → x / 2 ∈ Icc (-(π / 2)) (π / 2) := fun x h0 h1 =>
    ⟨by linarith [Real.pi_pos], by linarith⟩
  have := (Real.strictMonoOn_sin.lt_iff_lt (hmem ω hω hωπ) (hmem k hk.le hkπ)).mp hlt
  linarith

/-- **OS3**: below Courant's limit in the plane, `κl ≤ 1/2`, light along an axis is slower than the
massless naive walk: at every wave `0 < k ≤ π` along the first axis, with its angles in `[0, π]`,
the walk's level is `ε = k` and light's turn `ω` is less. -/
theorem light_slower_than_naive_walk {κ l k ε ω : ℝ} (hκl : κ * l ≤ 1 / 2) (hk : 0 < k)
    (hkπ : k ≤ π) (hε : ε ∈ Icc 0 π) (hω : ω ∈ Icc 0 π) (hlev : IsNaiveLevel 0 k 0 ε)
    (h : (modeTick κ l (∑ j : Fin 2, 4 * Real.sin (![k, 0] j / 2) ^ 2)).trace = 2 * Real.cos ω) :
    ε = k ∧ ω < ε := by
  have hεk : ε = k :=
    Real.injOn_cos hε ⟨hk.le, hkπ⟩ (((naive_massless_axes_level k ε).1).mp hlev)
  rw [axis_pull] at h
  refine ⟨hεk, ?_⟩
  rw [hεk]
  exact light_slower (by linarith) hk hkπ hω.1 hω.2 h

/-- In finding 460's terms: along the first axis, light of speed `0 ≤ c < 1` turns by
`planeAngle c k 0 < k` at every wave `0 < k ≤ π`. -/
theorem planeAngle_axis_lt {c k : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (hk : 0 < k) (hkπ : k ≤ π) :
    planeAngle c k 0 < k := by
  have hs : 0 < Real.sin (k / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hs1 : Real.sin (k / 2) ≤ 1 := Real.sin_le_one _
  have hroot : Real.sqrt (4 - 2 * Real.cos k - 2 * Real.cos 0) = 2 * Real.sin (k / 2) := by
    rw [Real.cos_zero, cos_eq_one_sub_sin_sq_half k]
    rw [show 4 - 2 * (1 - 2 * Real.sin (k / 2) ^ 2) - 2 * 1 = (2 * Real.sin (k / 2)) ^ 2 by ring]
    exact Real.sqrt_sq (by linarith)
  unfold planeAngle
  rw [hroot, show c / 2 * (2 * Real.sin (k / 2)) = c * Real.sin (k / 2) by ring]
  have hlt : c * Real.sin (k / 2) < Real.sin (k / 2) := by nlinarith
  have hmem1 : c * Real.sin (k / 2) ∈ Icc (-1 : ℝ) 1 :=
    ⟨by nlinarith, by nlinarith⟩
  have hmem2 : Real.sin (k / 2) ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, hs1⟩
  have h1 := Real.strictMonoOn_arcsin hmem1 hmem2 hlt
  rw [Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith)] at h1
  linarith

end Artform.Stages
