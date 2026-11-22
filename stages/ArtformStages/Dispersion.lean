import ArtformStages.Converse
import ArtformStages.Waves

/-!
# The dispersion of light

Along a level of `L S` at `μ = 4 sin² θ`, Pair carries a sampled wave that turns by `2 θ` per step;
on the torus with one `κ` and one `λ` this gives the dispersion of light, `sin² (ω / 2) = κ λ
(sin² (θ₁ / 2) + sin² (θ₂ / 2))` (finding 447 of the research ledger on a layered universe):

* `pairOne_wave` (DI1): the Pair of one place with `μ = 4 sin² θ` sends `(2 sin θ, - sin θ)` after
  `k` steps to `(2 sin θ cos (2 k θ), sin ((2 k - 1) θ))`;
* `exists_angle` (DI2): every `μ` in `[0, 4]` is `4 sin² θ`;
* `level_wave` (DI3): so Pair carries every level at `4 sin² θ` as that wave;
* `dispersion_identity`, `dispersion_relation` (DI4): `4 - 2 cos θ₁ - 2 cos θ₂ =
  4 (sin² (θ₁ / 2) + sin² (θ₂ / 2))`;
* `torus_dispersion` (DI5): on the torus, the transverse plane wave of finding 443 turns by `2 θ`
  per step.
-/

open Matrix

open scoped Real

namespace Artform.Stages

/-- DI1. The Pair of one place with `μ = 4 sin² θ` carries `(2 sin θ, - sin θ)` as a wave that
turns by `2 θ` per step. -/
theorem pairOne_wave (θ : ℝ) (k : ℕ) :
    (pairOne 1 (4 * Real.sin θ ^ 2))^[k] (2 * Real.sin θ, -Real.sin θ) =
      (2 * Real.sin θ * Real.cos (2 * k * θ), Real.sin ((2 * k - 1) * θ)) := by
  induction k with
  | zero => simp [Real.sin_neg]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    have e1 : (2 * ((k + 1 : ℕ) : ℝ) - 1) * θ = 2 * k * θ + θ := by push_cast; ring
    have e2 : 2 * ((k + 1 : ℕ) : ℝ) * θ = 2 * k * θ + 2 * θ := by push_cast; ring
    have e3 : (2 * (k : ℝ) - 1) * θ = 2 * k * θ - θ := by ring
    rw [e1, e2, e3]
    simp only [pairOne, one_mul, Prod.mk.injEq]
    rw [Real.sin_add, Real.sin_sub, Real.cos_add, Real.cos_two_mul, Real.sin_two_mul]
    constructor
    · linear_combination (-4 * Real.sin θ * Real.cos (2 * k * θ)) * Real.sin_sq_add_cos_sq θ
    · ring

/-- DI2. Every `μ` with `0 ≤ μ ≤ 4` is `4 sin² θ` for some angle `θ`. -/
theorem exists_angle {μ : ℝ} (h0 : 0 ≤ μ) (h4 : μ ≤ 4) : ∃ θ : ℝ, 4 * Real.sin θ ^ 2 = μ := by
  refine ⟨Real.arcsin (Real.sqrt μ / 2), ?_⟩
  have h1 : Real.sqrt μ / 2 ≤ 1 := by
    have hs : Real.sqrt μ ≤ 2 := by
      calc Real.sqrt μ ≤ Real.sqrt 4 := Real.sqrt_le_sqrt h4
        _ = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith
  have h2 : -1 ≤ Real.sqrt μ / 2 := by
    have := Real.sqrt_nonneg μ
    linarith
  rw [Real.sin_arcsin h2 h1, div_pow, Real.sq_sqrt h0]
  ring

/-- DI3. Pair carries every level of `L S` at `4 sin² θ` as the wave of `pairOne_wave`. -/
theorem level_wave {n : Type*} [Fintype n] (S L : Matrix n n ℝ) (v : n → ℝ) (θ : ℝ)
    (hv : L *ᵥ (S *ᵥ v) = (4 * Real.sin θ ^ 2) • v) (k : ℕ) :
    (pair S L)^[k] ((2 * Real.sin θ) • v, (-Real.sin θ) • (S *ᵥ v)) =
      ((2 * Real.sin θ * Real.cos (2 * k * θ)) • v, Real.sin ((2 * k - 1) * θ) • (S *ᵥ v)) := by
  have h :=
    pair_iterate_on_pair_level S L v (4 * Real.sin θ ^ 2) hv (2 * Real.sin θ, -Real.sin θ) k
  simpa only [pairOne_wave] using h

/-- DI4. `4 - 2 cos θ₁ - 2 cos θ₂ = 4 (sin² (θ₁ / 2) + sin² (θ₂ / 2))`. -/
theorem dispersion_identity (θ₁ θ₂ : ℝ) :
    4 - 2 * Real.cos θ₁ - 2 * Real.cos θ₂ =
      4 * (Real.sin (θ₁ / 2) ^ 2 + Real.sin (θ₂ / 2) ^ 2) := by
  have h : ∀ x : ℝ, Real.cos x = 1 - 2 * Real.sin (x / 2) ^ 2 := by
    intro x
    have := Real.cos_two_mul (x / 2)
    rw [show 2 * (x / 2) = x by ring] at this
    rw [this, Real.cos_sq']
    ring
  rw [h θ₁, h θ₂]
  ring

/-- DI4. The dispersion relation: `4 sin² θ = λ κ (4 - 2 cos θ₁ - 2 cos θ₂)` is
`sin² θ = λ κ (sin² (θ₁ / 2) + sin² (θ₂ / 2))`. -/
theorem dispersion_relation (l κ θ θ₁ θ₂ : ℝ)
    (h : 4 * Real.sin θ ^ 2 = l * (κ * (4 - 2 * Real.cos θ₁ - 2 * Real.cos θ₂))) :
    Real.sin θ ^ 2 = l * κ * (Real.sin (θ₁ / 2) ^ 2 + Real.sin (θ₂ / 2) ^ 2) := by
  rw [dispersion_identity] at h
  linarith

/-- DI5. On the torus with one `κ` and one `λ`, the transverse plane wave of wave numbers
`(p, q)` turns by `2 θ` per step, for every `θ` with `4 sin² θ = λ κ (4 - 2 cos θ₁ - 2 cos θ₂)`. -/
theorem torus_dispersion (n m : ℕ) [NeZero n] [NeZero m] [Fact (1 < n)] [Fact (1 < m)]
    (p : ZMod n) (q : ZMod m) (κ l θ : ℝ)
    (hθ : 4 * Real.sin θ ^ 2 =
      l * (κ * (4 - 2 * Real.cos (2 * π * p.val / n) - 2 * Real.cos (2 * π * q.val / m))))
    (k : ℕ) :
    (pair ((torus n m).incidenceᵀ * diagonal (fun _ : ZMod n × ZMod m => κ) * (torus n m).incidence)
        (diagonal fun _ : (ZMod n × ZMod m) × Fin 2 => l))^[k]
      ((2 * Real.sin θ) • ((torus n m).incidenceᵀ *ᵥ fun w => (planeWave p q w).re),
        (-Real.sin θ) •
          (((torus n m).incidenceᵀ * diagonal (fun _ : ZMod n × ZMod m => κ) *
            (torus n m).incidence) *ᵥ ((torus n m).incidenceᵀ *ᵥ fun w => (planeWave p q w).re))) =
      ((2 * Real.sin θ * Real.cos (2 * k * θ)) •
          ((torus n m).incidenceᵀ *ᵥ fun w => (planeWave p q w).re),
        Real.sin ((2 * k - 1) * θ) •
          (((torus n m).incidenceᵀ * diagonal (fun _ : ZMod n × ZMod m => κ) *
            (torus n m).incidence) *ᵥ
              ((torus n m).incidenceᵀ *ᵥ fun w => (planeWave p q w).re))) := by
  apply level_wave
  have hD : ∀ u : (ZMod n × ZMod m) × Fin 2 → ℝ,
      (diagonal fun _ : (ZMod n × ZMod m) × Fin 2 => l) *ᵥ u = l • u := by
    intro u
    funext i
    simp [mulVec_diagonal]
  rw [torus_transverse_wave, mulVec_smul, hD, smul_smul, hθ]
  congr 1
  ring

end Artform.Stages
