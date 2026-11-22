import ArtformStages.InnerDirection

/-!
# The walk

Finding 476 of the research ledger on a layered universe: the charge's move, with the half part
of two rows as its inner direction, is forced up to its angles. The exchange is `σx` and the coin
of angle `μ` is `cos μ · 1 - i sin μ · σx`. The walk on a ring of `N` places makes the coin at
every place and then shifts the first number of every place one place on and the second one
place back. Its table at the wave number `k` is `diag(e^{-ik}, e^{ik})` times the coin, and a
level is an eigenvalue `e^{-iε}` of that table.

* `exchange_unitary_iff` (WK1): a table `a · 1 + b · σx` keeps the sum of the squares of the
  sizes of every two numbers exactly when `|a|² + |b|² = 1` and `a conj b` has real part `0`, and
  exactly when `a = u cos θ` and `b = u i sin θ` for one `u` of size 1 and one angle `θ`.
* `walkSymbol`, `walk_acts_by_symbol`, `walkSymbol_trace`, `walkSymbol_det` (WK2): on the wave
  `e^{ikx}` times a vector of two numbers, `k = 2 π j / N`, the walk acts by its table, whose
  trace is `2 cos μ cos k` and whose determinant is `1`.
* `walk_level_iff`, `walk_levels_pair` (WK3): `e^{-iε}` is a level at `k` exactly when
  `cos ε = cos μ cos k`; with `ε` a level, `-ε` is one too.
* `walkSymbol_add_pi` (WK4): the table at `k + π` is minus the table at `k`, so every level of
  `ε` at `k` has the twin `-e^{-iε}`, the level of `ε + π`, at `k + π`.

None of this is new: it is the one-dimensional Dirac walk of quantum walks and quantum lattice
gases, and its doubled level at `k + π` is the doubling of the lattice fermion.
-/

open Matrix Complex ComplexConjugate
open scoped Real

namespace Artform.Stages

/-! ### WK1: the form, up to an angle -/

/-- The sum of the squares of the sizes of two numbers after the table `a · 1 + b · σx`. -/
theorem exchange_sum_sq (a b : ℂ) (v : Fin 2 → ℂ) :
    ∑ i, ‖((a • 1 + b • pauliX) *ᵥ v) i‖ ^ 2 =
      (‖a‖ ^ 2 + ‖b‖ ^ 2) * (‖v 0‖ ^ 2 + ‖v 1‖ ^ 2) +
        4 * (a * conj b).re * (v 0 * conj (v 1)).re := by
  simp [Fin.sum_univ_two, mulVec, dotProduct, pauliX, Complex.sq_norm, Complex.normSq_apply]
  ring

/-- **WK1** (MATTER.md T18(a)). A table `a · 1 + b · σx` keeps the sum of the squares of the
sizes of every two numbers exactly when `|a|² + |b|² = 1` and the real part of `a conj b` is `0`;
and exactly when `a = u cos θ` and `b = u i sin θ`, for one number `u` of size 1 and one angle
`θ`: the link gate of `θ`, times `u`. -/
theorem exchange_unitary_iff (a b : ℂ) :
    ((∀ v : Fin 2 → ℂ, ∑ i, ‖((a • 1 + b • pauliX) *ᵥ v) i‖ ^ 2 = ∑ i, ‖v i‖ ^ 2) ↔
        ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1 ∧ (a * conj b).re = 0) ∧
      ((∀ v : Fin 2 → ℂ, ∑ i, ‖((a • 1 + b • pauliX) *ᵥ v) i‖ ^ 2 = ∑ i, ‖v i‖ ^ 2) ↔
        ∃ u : ℂ, ∃ θ : ℝ, ‖u‖ = 1 ∧ a = u * Real.cos θ ∧ b = u * (I * Real.sin θ)) := by
  have hPQ : (∀ v : Fin 2 → ℂ, ∑ i, ‖((a • 1 + b • pauliX) *ᵥ v) i‖ ^ 2 = ∑ i, ‖v i‖ ^ 2) ↔
      ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1 ∧ (a * conj b).re = 0 := by
    constructor
    · intro h
      have h1 : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1 := by
        have e := h ![1, 0]
        rw [exchange_sum_sq, Fin.sum_univ_two] at e
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, norm_one, norm_zero, map_zero,
          mul_zero, Complex.zero_re] at e
        linear_combination e
      refine ⟨h1, ?_⟩
      have e := h ![1, 1]
      rw [exchange_sum_sq, Fin.sum_univ_two] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, norm_one, map_one, mul_one,
        Complex.one_re] at e
      linear_combination e / 4 - h1 / 2
    · rintro ⟨h1, h2⟩ v
      rw [exchange_sum_sq, h1, h2, Fin.sum_univ_two]
      ring
  have hQR : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1 ∧ (a * conj b).re = 0 ↔
      ∃ u : ℂ, ∃ θ : ℝ, ‖u‖ = 1 ∧ a = u * Real.cos θ ∧ b = u * (I * Real.sin θ) := by
    constructor
    · rintro ⟨h1, h2⟩
      set p := a + b with hpdef
      set q := a - b with hqdef
      have hp1 : ‖p‖ ^ 2 = 1 := by
        rw [hpdef, Complex.sq_norm, Complex.normSq_add, ← Complex.sq_norm, ← Complex.sq_norm]
        linarith
      have hq1 : ‖q‖ ^ 2 = 1 := by
        rw [hqdef, Complex.sq_norm, Complex.normSq_sub, ← Complex.sq_norm, ← Complex.sq_norm]
        linarith
      have hpn : ‖p‖ = 1 := by
        have := norm_nonneg p
        nlinarith
      have hqn : ‖q‖ = 1 := by
        have := norm_nonneg q
        nlinarith
      set α := Complex.arg p
      set β := Complex.arg q
      have hp : Complex.exp (α * I) = p := by
        have := Complex.norm_mul_exp_arg_mul_I p
        rwa [hpn, Complex.ofReal_one, one_mul] at this
      have hq : Complex.exp (β * I) = q := by
        have := Complex.norm_mul_exp_arg_mul_I q
        rwa [hqn, Complex.ofReal_one, one_mul] at this
      set u := Complex.exp (↑((α + β) / 2) * I) with hu
      set θ : ℝ := (α - β) / 2 with hθ
      have e1 : u * Complex.exp (↑θ * I) = Complex.exp (α * I) := by
        rw [hu, hθ, ← Complex.exp_add]
        congr 1
        push_cast
        ring
      have e2 : u * Complex.exp (-↑θ * I) = Complex.exp (β * I) := by
        rw [hu, hθ, ← Complex.exp_add]
        congr 1
        push_cast
        ring
      have ha : a = (p + q) / 2 := by
        rw [hpdef, hqdef]
        ring
      have hb : b = (p - q) / 2 := by
        rw [hpdef, hqdef]
        ring
      refine ⟨u, θ, Complex.norm_exp_ofReal_mul_I _, ?_, ?_⟩
      · rw [Complex.ofReal_cos, Complex.cos]
        linear_combination ha - hp / 2 - hq / 2 - e1 / 2 - e2 / 2
      · rw [Complex.ofReal_sin, Complex.sin]
        linear_combination hb - hp / 2 + hq / 2 - e1 / 2 + e2 / 2 +
          (u * (Complex.exp (↑θ * I) - Complex.exp (-↑θ * I)) / 2) * Complex.I_sq
    · rintro ⟨u, θ, hu, rfl, rfl⟩
      have hu2 : u.re * u.re + u.im * u.im = 1 := by
        have := congrArg (· ^ 2) hu
        simp only [Complex.sq_norm, Complex.normSq_apply, one_pow] at this
        exact this
      have hcs := Real.cos_sq_add_sin_sq θ
      constructor
      · simp only [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
        linear_combination (Real.cos θ ^ 2 + Real.sin θ ^ 2) * hu2 + hcs
      · simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
        ring
  exact ⟨hPQ, hPQ.trans hQR⟩

/-! ### WK2: the walk's table -/

/-- The coin of angle `μ`: `cos μ` times `1` less `i sin μ` times the exchange `σx`. -/
noncomputable def coin (μ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Real.cos μ : ℂ) • 1 - (I * Real.sin μ) • pauliX

/-- The shift of the walk: the first number of every place moves one place on, and the second
one place back. -/
def partShift {N : ℕ} (φ : ZMod N → Fin 2 → ℂ) : ZMod N → Fin 2 → ℂ :=
  fun x => ![φ (x - 1) 0, φ (x + 1) 1]

/-- The walk on the ring of `N` places: the coin at every place, and then the shift. -/
noncomputable def walk {N : ℕ} (μ : ℝ) (ψ : ZMod N → Fin 2 → ℂ) : ZMod N → Fin 2 → ℂ :=
  partShift fun x => coin μ *ᵥ ψ x

/-- The walk's table at the wave number `k`: `diag(e^{-ik}, e^{ik})` times the coin. -/
noncomputable def walkSymbol (μ k : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  diagonal ![Complex.exp (-(k : ℂ) * I), Complex.exp ((k : ℂ) * I)] * coin μ

/-- The diagonal table of the shift is `cos k · 1 - i sin k · σz`. -/
theorem walkShift_diagonal (k : ℝ) :
    (diagonal ![Complex.exp (-(k : ℂ) * I), Complex.exp ((k : ℂ) * I)] :
        Matrix (Fin 2) (Fin 2) ℂ) = (Real.cos k : ℂ) • 1 - (I * Real.sin k) • pauliZ := by
  have e1 : Complex.exp (-(k : ℂ) * I) = Complex.cos k - Complex.sin k * I := by
    rw [Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    ring
  rw [e1, Complex.exp_mul_I]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliZ, Complex.ofReal_cos, Complex.ofReal_sin] <;> ring

/-- The wave number `k = 2 π j / N` of the `j`-th wave of the ring of `N` places. -/
noncomputable def waveNumber (N : ℕ) (j : ZMod N) : ℝ := 2 * π * j.val / N

/-- The wave `e^{ikx}` of the ring of `N` places, of the wave number `k = 2 π j / N`. -/
noncomputable def ringWave (N : ℕ) (j x : ZMod N) : ℂ :=
  Complex.exp (↑(waveNumber N j * x.val) * I)

theorem ringWave_eq {N : ℕ} [NeZero N] (j x : ZMod N) :
    ringWave N j x = ZMod.stdAddChar (j * x) := by
  have e : j * x = ((j.val * x.val : ℕ) : ZMod N) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  rw [ZMod.stdAddChar_apply, e, ZMod.toCircle_natCast, ringWave, waveNumber]
  congr 1
  push_cast
  ring

/-- One place on, the wave gains the factor `e^{ik}`. -/
theorem ringWave_add_one {N : ℕ} [NeZero N] (j x : ZMod N) :
    ringWave N j (x + 1) = Complex.exp (↑(waveNumber N j) * I) * ringWave N j x := by
  rw [ringWave_eq, ringWave_eq, mul_add, mul_one, AddChar.map_add_eq_mul,
    mul_comm (ZMod.stdAddChar (j * x))]
  congr 1
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply, waveNumber]
  congr 1
  push_cast
  ring

/-- One place back, the wave gains the factor `e^{-ik}`. -/
theorem ringWave_sub_one {N : ℕ} [NeZero N] (j x : ZMod N) :
    ringWave N j (x - 1) = Complex.exp (-↑(waveNumber N j) * I) * ringWave N j x := by
  have h := ringWave_add_one j (x - 1)
  rw [sub_add_cancel] at h
  rw [h, ← mul_assoc, ← Complex.exp_add, neg_mul, neg_add_cancel, Complex.exp_zero, one_mul]

theorem walkSymbol_mulVec (μ k : ℝ) (v : Fin 2 → ℂ) :
    walkSymbol μ k *ᵥ v =
      ![Complex.exp (-(k : ℂ) * I) * (coin μ *ᵥ v) 0,
        Complex.exp ((k : ℂ) * I) * (coin μ *ᵥ v) 1] := by
  rw [walkSymbol, ← Matrix.mulVec_mulVec]
  funext i
  rw [Matrix.mulVec_diagonal]
  fin_cases i <;> rfl

/-- **WK2**: on the wave `e^{ikx}` times a vector `v` of two numbers, with `k = 2 π j / N`, the
walk acts by its table at `k`. -/
theorem walk_acts_by_symbol {N : ℕ} [NeZero N] (μ : ℝ) (j : ZMod N) (v : Fin 2 → ℂ) :
    walk μ (fun x => ringWave N j x • v) =
      fun x => ringWave N j x • (walkSymbol μ (waveNumber N j) *ᵥ v) := by
  funext x
  rw [walkSymbol_mulVec]
  ext i
  fin_cases i
  · change (coin μ *ᵥ (ringWave N j (x - 1) • v)) 0 =
      ringWave N j x * (Complex.exp (-(↑(waveNumber N j) : ℂ) * I) * (coin μ *ᵥ v) 0)
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, ringWave_sub_one]
    ring
  · change (coin μ *ᵥ (ringWave N j (x + 1) • v)) 1 =
      ringWave N j x * (Complex.exp ((↑(waveNumber N j) : ℂ) * I) * (coin μ *ᵥ v) 1)
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, ringWave_add_one]
    ring

theorem walkSymbol_entries (μ k : ℝ) :
    walkSymbol μ k 0 0 = Complex.exp (-(k : ℂ) * I) * Real.cos μ ∧
      walkSymbol μ k 0 1 = Complex.exp (-(k : ℂ) * I) * (-(I * Real.sin μ)) ∧
      walkSymbol μ k 1 0 = Complex.exp ((k : ℂ) * I) * (-(I * Real.sin μ)) ∧
      walkSymbol μ k 1 1 = Complex.exp ((k : ℂ) * I) * Real.cos μ := by
  simp [walkSymbol, coin, pauliX]

/-- **WK2**: the trace of the walk's table is `2 cos μ cos k`. -/
theorem walkSymbol_trace (μ k : ℝ) :
    trace (walkSymbol μ k) = 2 * (Real.cos μ : ℂ) * (Real.cos k : ℂ) := by
  obtain ⟨h00, -, -, h11⟩ := walkSymbol_entries μ k
  rw [trace_fin_two, h00, h11, Complex.ofReal_cos k]
  have h := Complex.two_cos (k : ℂ)
  linear_combination -(Real.cos μ : ℂ) * h

/-- **WK2**: the determinant of the walk's table is `1`. -/
theorem walkSymbol_det (μ k : ℝ) : det (walkSymbol μ k) = 1 := by
  obtain ⟨h00, h01, h10, h11⟩ := walkSymbol_entries μ k
  rw [det_fin_two, h00, h01, h10, h11]
  have hE : Complex.exp (-(k : ℂ) * I) * Complex.exp ((k : ℂ) * I) = 1 := by
    rw [← Complex.exp_add, neg_mul, neg_add_cancel, Complex.exp_zero]
  have hcs : (Real.cos μ : ℂ) ^ 2 + (Real.sin μ : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq μ
  linear_combination ((Real.cos μ : ℂ) ^ 2 + (Real.sin μ : ℂ) ^ 2) * hE + hcs -
    Complex.exp (-(k : ℂ) * I) * Complex.exp ((k : ℂ) * I) * (Real.sin μ : ℂ) ^ 2 *
      Complex.I_sq

/-! ### WK3: the levels -/

/-- A level of the walk at the wave number `k`: `e^{-iε}` is an eigenvalue of its table. -/
def IsWalkLevel (μ k ε : ℝ) : Prop :=
  ∃ v : Fin 2 → ℂ, v ≠ 0 ∧ walkSymbol μ k *ᵥ v = Complex.exp (-(ε : ℂ) * I) • v

/-- A number is an eigenvalue of a table exactly when the table less it has determinant `0`. -/
theorem eigen_iff_det {M : Matrix (Fin 2) (Fin 2) ℂ} {c : ℂ} :
    (∃ v : Fin 2 → ℂ, v ≠ 0 ∧ M *ᵥ v = c • v) ↔ (M - c • 1).det = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero]

theorem walkSymbol_charpoly (μ k : ℝ) (c : ℂ) :
    (walkSymbol μ k - c • 1).det = c ^ 2 - 2 * (Real.cos μ : ℂ) * (Real.cos k : ℂ) * c + 1 := by
  have htr := walkSymbol_trace μ k
  have hdet := walkSymbol_det μ k
  rw [trace_fin_two] at htr
  rw [det_fin_two] at hdet
  rw [det_fin_two]
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
  rw [Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), mul_zero, sub_zero, sub_zero]
  linear_combination hdet - c * htr

/-- **WK3**: `e^{-iε}` is a level of the walk's table at `k` exactly when `cos ε = cos μ cos k`. -/
theorem walk_level_iff (μ k ε : ℝ) :
    IsWalkLevel μ k ε ↔ Real.cos ε = Real.cos μ * Real.cos k := by
  have h1 : Complex.exp (-(ε : ℂ) * I) * Complex.exp ((ε : ℂ) * I) = 1 := by
    rw [← Complex.exp_add, neg_mul, neg_add_cancel, Complex.exp_zero]
  have h2 := Complex.two_cos (ε : ℂ)
  rw [← Complex.ofReal_cos] at h2
  have key : (walkSymbol μ k - Complex.exp (-(ε : ℂ) * I) • 1).det =
      Complex.exp (-(ε : ℂ) * I) *
        (2 * ((Real.cos ε : ℂ) - (Real.cos μ : ℂ) * (Real.cos k : ℂ))) := by
    rw [walkSymbol_charpoly]
    linear_combination -h1 - Complex.exp (-(ε : ℂ) * I) * h2
  rw [IsWalkLevel, eigen_iff_det, key, mul_eq_zero, mul_eq_zero, sub_eq_zero]
  simp only [Complex.exp_ne_zero, two_ne_zero, false_or]
  exact_mod_cast Iff.rfl

/-- **WK3**: with the level `e^{-iε}`, its inverse `e^{iε}` is a level too: the levels come in
pairs of opposite sign. -/
theorem walk_levels_pair {μ k ε : ℝ} (h : IsWalkLevel μ k ε) : IsWalkLevel μ k (-ε) := by
  rw [walk_level_iff] at h ⊢
  rwa [Real.cos_neg]

/-! ### WK4: the twin -/

/-- The walk's table at `k + π` is minus its table at `k`. -/
theorem walkSymbol_add_pi_eq (μ k : ℝ) : walkSymbol μ (k + π) = -walkSymbol μ k := by
  have e1 : Complex.exp (-(↑(k + π) : ℂ) * I) = -Complex.exp (-(k : ℂ) * I) := by
    rw [show -(↑(k + π) : ℂ) * I = -(k : ℂ) * I + -(↑π * I) by push_cast; ring,
      Complex.exp_add, Complex.exp_neg, Complex.exp_pi_mul_I]
    ring
  have e2 : Complex.exp ((↑(k + π) : ℂ) * I) = -Complex.exp ((k : ℂ) * I) := by
    rw [show (↑(k + π) : ℂ) * I = (k : ℂ) * I + ↑π * I by push_cast; ring, Complex.exp_add,
      Complex.exp_pi_mul_I]
    ring
  have hd : (diagonal ![Complex.exp (-(↑(k + π) : ℂ) * I), Complex.exp ((↑(k + π) : ℂ) * I)] :
      Matrix (Fin 2) (Fin 2) ℂ) =
      -diagonal ![Complex.exp (-(k : ℂ) * I), Complex.exp ((k : ℂ) * I)] := by
    rw [e1, e2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [walkSymbol, walkSymbol, hd, Matrix.neg_mul]

/-- **WK4**: the walk's table at `k + π` is minus its table at `k`; so every level `e^{-iε}` at
`k` has the twin `-e^{-iε}`, the level of `ε + π`, at `k + π`. -/
theorem walkSymbol_add_pi (μ k : ℝ) :
    walkSymbol μ (k + π) = -walkSymbol μ k ∧
      ∀ ε : ℝ, IsWalkLevel μ k ε → IsWalkLevel μ (k + π) (ε + π) ∧
        Complex.exp (-(↑(ε + π) : ℂ) * I) = -Complex.exp (-(ε : ℂ) * I) := by
  have hε : ∀ ε : ℝ, Complex.exp (-(↑(ε + π) : ℂ) * I) = -Complex.exp (-(ε : ℂ) * I) :=
    fun ε => by
      rw [show -(↑(ε + π) : ℂ) * I = -(ε : ℂ) * I + -(↑π * I) by push_cast; ring,
        Complex.exp_add, Complex.exp_neg, Complex.exp_pi_mul_I]
      ring
  refine ⟨walkSymbol_add_pi_eq μ k, fun ε ⟨v, hv, h⟩ => ⟨⟨v, hv, ?_⟩, hε ε⟩⟩
  rw [walkSymbol_add_pi_eq, Matrix.neg_mulVec, h, hε, neg_smul]

end Artform.Stages
