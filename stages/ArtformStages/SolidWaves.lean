import ArtformStages.Solid
import ArtformStages.Waves
import ArtformStages.Dispersion

/-!
# Waves in a solid

Finding 442 of the research ledger on a layered universe built the cubic torus with its three maps,
and finding 443 found the waves of light on the torus of squares. Here light in a solid of cubes is
found (finding 465 of the ledger):

* `cube_transpose_mulVec`, `cube_gaugeT_mulVec` (WS1): `Cᵀ ψ` and `Gᵀ A` read on the lines and the
  corners;
* `cube_hodge_laplacian` (WS2): `Cᵀ C + G Gᵀ` is the stencil of seven points on each direction;
* `cube_stencil_wave` (WS3): the plane waves are its levels at `6 - 2 cos θ₁ - 2 cos θ₂ - 2 cos θ₃`;
* `cube_transverse_wave` (WS4): the wave of an amplitude with no divergence is transverse light at
  `κ` times that level;
* `cube_polarizations` (WS5): for each wave vector other than `0` such amplitudes form a plane;
* `cube_dispersion`, `cube_dispersion_relation` (WS6): Pair turns it by `2 θ` per step with
  `sin² θ = κ λ (sin² (θ₁ / 2) + sin² (θ₂ / 2) + sin² (θ₃ / 2))`.
-/

open Matrix Module

open scoped Real

namespace Artform.Stages

variable (n : ℕ) [NeZero n]

/-- **WS1.** `Cᵀ ψ` at the line `(w, d)` of the cubic torus. -/
theorem cube_transpose_mulVec (ψ : CubePoint n × Fin 3 → ℝ) (w : CubePoint n) (d : Fin 3) :
    ((cubeIncidence n)ᵀ *ᵥ ψ) (w, d) = ψ (w, d + 2) - ψ (w - cubeStep n (d + 1), d + 2) +
      ψ (w - cubeStep n (d + 2), d + 1) - ψ (w, d + 1) := by
  have key : ∀ (g : CubePoint n × Fin 3 → CubePoint n × Fin 3) (σ₀ : CubePoint n × Fin 3),
      (∀ σ, (w, d) = g σ ↔ σ = σ₀) →
      ∑ σ, (if (w, d) = g σ then (1 : ℝ) else 0) * ψ σ = ψ σ₀ := by
    intro g σ₀ hg
    rw [Fintype.sum_eq_single σ₀ fun σ hσ => by
        rw [ite_eq_right (fun h => hσ ((hg σ).mp h)), zero_mul],
      ite_eq_left ((hg σ₀).mpr rfl), one_mul]
  have e1 : ∀ x : Fin 3, x + 2 + 1 = x := by decide
  have e2 : ∀ x : Fin 3, x + 1 + 2 = x := by decide
  have e3 : ∀ x : Fin 3, x + 1 + 1 = x + 2 := by decide
  have e4 : ∀ x : Fin 3, x + 2 + 2 = x + 1 := by decide
  have h1 : ∀ σ : CubePoint n × Fin 3, (w, d) = (σ.1, σ.2 + 1) ↔ σ = (w, d + 2) := by
    rintro ⟨u, k⟩
    simp only [Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨rfl, (e2 k).symm⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨rfl, (e1 d).symm⟩
  have h2 : ∀ σ : CubePoint n × Fin 3,
      (w, d) = (σ.1 + cubeStep n (σ.2 + 1), σ.2 + 2) ↔ σ = (w - cubeStep n (d + 2), d + 1) := by
    rintro ⟨u, k⟩
    simp only [Prod.mk.injEq]
    constructor
    · rintro ⟨hw, rfl⟩
      refine ⟨?_, (e1 k).symm⟩
      rw [e4, hw, add_sub_cancel_right]
    · rintro ⟨rfl, rfl⟩
      refine ⟨?_, (e2 d).symm⟩
      rw [e3, sub_add_cancel]
  have h3 : ∀ σ : CubePoint n × Fin 3,
      (w, d) = (σ.1 + cubeStep n (σ.2 + 2), σ.2 + 1) ↔ σ = (w - cubeStep n (d + 1), d + 2) := by
    rintro ⟨u, k⟩
    simp only [Prod.mk.injEq]
    constructor
    · rintro ⟨hw, rfl⟩
      refine ⟨?_, (e2 k).symm⟩
      rw [e3, hw, add_sub_cancel_right]
    · rintro ⟨rfl, rfl⟩
      refine ⟨?_, (e1 d).symm⟩
      rw [e4, sub_add_cancel]
  have h4 : ∀ σ : CubePoint n × Fin 3, (w, d) = (σ.1, σ.2 + 2) ↔ σ = (w, d + 1) := by
    rintro ⟨u, k⟩
    simp only [Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨rfl, (e1 k).symm⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨rfl, (e2 d).symm⟩
  simp only [mulVec, dotProduct, transpose_apply, cubeIncidence, Matrix.of_apply, add_mul, sub_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [key _ _ h1, key _ _ h2, key _ _ h3, key _ _ h4]
  ring

/-- **WS1.** `Gᵀ A` at the corner `w` of the cubic torus: what flows in less what flows out. -/
theorem cube_gaugeT_mulVec (A : CubePoint n × Fin 3 → ℝ) (w : CubePoint n) :
    ((cubeGauge n)ᵀ *ᵥ A) w = ∑ d, (A (w - cubeStep n d, d) - A (w, d)) := by
  simp only [mulVec, dotProduct, transpose_apply, cubeGauge, Matrix.of_apply, sub_mul, ite_mul,
    one_mul, zero_mul, Finset.sum_sub_distrib]
  rw [Fintype.sum_prod_type_right, Fintype.sum_prod_type_right]
  congr 1
  · refine Finset.sum_congr rfl fun d _ => ?_
    rw [Fintype.sum_eq_single (w - cubeStep n d)]
    · simp
    · intro u hu
      exact ite_eq_right fun h => hu (eq_sub_of_add_eq h)
  · simp

/-- The stencil of seven points on each direction of the lines. -/
def lineStencil (A : CubePoint n × Fin 3 → ℝ) (ℓ : CubePoint n × Fin 3) : ℝ :=
  ∑ k, ((A ℓ - A (ℓ.1 + cubeStep n k, ℓ.2)) + (A ℓ - A (ℓ.1 - cubeStep n k, ℓ.2)))

/-- **WS2.** On the cubic torus `Cᵀ C + G Gᵀ` is the stencil of seven points on each direction. -/
theorem cube_hodge_laplacian (A : CubePoint n × Fin 3 → ℝ) :
    ((cubeIncidence n)ᵀ * cubeIncidence n + cubeGauge n * (cubeGauge n)ᵀ) *ᵥ A =
      lineStencil n A := by
  funext ⟨w, d⟩
  rw [add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, Pi.add_apply, cube_transpose_mulVec,
    cubeGauge_mulVec]
  simp only [cubeIncidence_mulVec, cube_gaugeT_mulVec, lineStencil, Fin.sum_univ_three]
  fin_cases d <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceAdd] <;>
    ring_nf

/-- The plane wave of wave vector `p` on the cubic torus. -/
noncomputable def cubeWave (p w : CubePoint n) : ℂ := ZMod.stdAddChar (∑ d, p d * w d)

/-- A step along `k` multiplies the plane wave by the character at `p k`. -/
theorem cubeWave_add (p w : CubePoint n) (k : Fin 3) :
    cubeWave n p (w + cubeStep n k) = cubeWave n p w * ZMod.stdAddChar (p k) := by
  unfold cubeWave
  rw [← AddChar.map_add_eq_mul]
  congr 1
  fin_cases k <;> simp [Fin.sum_univ_three, cubeStep, mul_add, Pi.single_apply] <;> ring

/-- A step back along `k` multiplies it by the character at `-p k`. -/
theorem cubeWave_sub (p w : CubePoint n) (k : Fin 3) :
    cubeWave n p (w - cubeStep n k) = cubeWave n p w * ZMod.stdAddChar (-(p k)) := by
  have h := cubeWave_add n p (w - cubeStep n k) k
  rw [sub_add_cancel] at h
  rw [h, mul_assoc, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, mul_one]

/-- The level of the plane wave of wave vector `p`: `6 - 2 cos θ₁ - 2 cos θ₂ - 2 cos θ₃`. -/
noncomputable def cubeLevel (p : CubePoint n) : ℝ :=
  ∑ d, (2 - 2 * Real.cos (2 * π * (p d).val / n))

/-- **WS3.** The plane wave is a level of the stencil of seven points at `cubeLevel p`. -/
theorem cube_stencil_wave (p w : CubePoint n) :
    ∑ k, ((cubeWave n p w - cubeWave n p (w + cubeStep n k)) +
        (cubeWave n p w - cubeWave n p (w - cubeStep n k))) =
      (cubeLevel n p : ℂ) * cubeWave n p w := by
  simp only [cubeWave_add, cubeWave_sub, cubeLevel]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h := stdAddChar_add_neg (p k)
  push_cast at h
  linear_combination (-(cubeWave n p w)) * h

/-- The wave of an amplitude `a`: the real field `Re (a d * f_p w)` on the lines. -/
noncomputable def cubeWaveField (p : CubePoint n) (a : Fin 3 → ℂ) : CubePoint n × Fin 3 → ℝ :=
  fun ℓ => (a ℓ.2 * cubeWave n p ℓ.1).re

/-- The divergence of an amplitude at `p`, a linear form on the amplitudes. -/
noncomputable def divergenceForm (p : CubePoint n) : (Fin 3 → ℂ) →ₗ[ℂ] ℂ where
  toFun a := ∑ d, a d * (ZMod.stdAddChar (-(p d)) - 1)
  map_add' a b := by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

/-- An amplitude with no divergence at `p`. -/
def NoDivergence (p : CubePoint n) (a : Fin 3 → ℂ) : Prop := divergenceForm n p a = 0

/-- **WS4.** The wave of an amplitude with no divergence has no divergence, and `Cᵀ diag κ C`
takes it to `κ` times the level times itself. -/
theorem cube_transverse_wave (p : CubePoint n) (a : Fin 3 → ℂ) (ha : NoDivergence n p a) (κ : ℝ) :
    (cubeGauge n)ᵀ *ᵥ cubeWaveField n p a = 0 ∧
      ((cubeIncidence n)ᵀ * diagonal (fun _ : CubePoint n × Fin 3 => κ) * cubeIncidence n) *ᵥ
          cubeWaveField n p a = (κ * cubeLevel n p) • cubeWaveField n p a := by
  have hdiv : (cubeGauge n)ᵀ *ᵥ cubeWaveField n p a = 0 := by
    funext w
    rw [cube_gaugeT_mulVec, Pi.zero_apply]
    simp only [cubeWaveField, cubeWave_sub]
    have hc : ∑ d, (a d * (cubeWave n p w * ZMod.stdAddChar (-(p d))) - a d * cubeWave n p w) =
        cubeWave n p w * divergenceForm n p a := by
      simp only [divergenceForm, LinearMap.coe_mk, AddHom.coe_mk, Finset.mul_sum]
      exact Finset.sum_congr rfl fun d _ => by ring
    rw [show (0 : ℝ) = (cubeWave n p w * divergenceForm n p a).re by rw [ha, mul_zero]; rfl, ← hc,
      Complex.re_sum]
    simp only [Complex.sub_re]
  have hS : lineStencil n (cubeWaveField n p a) = cubeLevel n p • cubeWaveField n p a := by
    funext ⟨w, d⟩
    have hZ : ∑ k, ((a d * cubeWave n p w - a d * cubeWave n p (w + cubeStep n k)) +
        (a d * cubeWave n p w - a d * cubeWave n p (w - cubeStep n k))) =
        (cubeLevel n p : ℂ) * (a d * cubeWave n p w) := by
      calc _ = a d * ∑ k, ((cubeWave n p w - cubeWave n p (w + cubeStep n k)) +
              (cubeWave n p w - cubeWave n p (w - cubeStep n k))) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun k _ => by ring
        _ = _ := by rw [cube_stencil_wave]; ring
    have hre := congrArg Complex.re hZ
    simp only [Complex.re_sum, Complex.add_re, Complex.sub_re, Complex.re_ofReal_mul] at hre
    simp only [lineStencil, cubeWaveField, Pi.smul_apply, smul_eq_mul]
    exact hre
  have hL : ((cubeIncidence n)ᵀ * cubeIncidence n) *ᵥ cubeWaveField n p a +
      cubeGauge n *ᵥ ((cubeGauge n)ᵀ *ᵥ cubeWaveField n p a) =
        lineStencil n (cubeWaveField n p a) := by
    rw [mulVec_mulVec, ← add_mulVec]
    exact cube_hodge_laplacian n _
  rw [hdiv, mulVec_zero, add_zero, hS] at hL
  have hD : ∀ u : CubePoint n × Fin 3 → ℝ,
      (diagonal fun _ : CubePoint n × Fin 3 => κ) *ᵥ u = κ • u := by
    intro u
    funext ℓ
    simp [mulVec_diagonal]
  refine ⟨hdiv, ?_⟩
  rw [← mulVec_mulVec, ← mulVec_mulVec, hD, mulVec_smul, mulVec_mulVec, hL, smul_smul]

/-- **WS5.** For every wave vector `p` other than `0`, the amplitudes with no divergence at `p` form
a space of dimension `2`: two polarizations. -/
theorem cube_polarizations (p : CubePoint n) (hp : p ≠ 0) :
    finrank ℂ (LinearMap.ker (divergenceForm n p)) = 2 := by
  obtain ⟨d₀, hd₀⟩ : ∃ d, p d ≠ 0 := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    exact hp (funext h)
  have hz : ZMod.stdAddChar (-(p d₀)) - 1 ≠ 0 := by
    intro h
    rw [sub_eq_zero, ← AddChar.map_zero_eq_one (ZMod.stdAddChar (N := n))] at h
    exact hd₀ (neg_eq_zero.mp (ZMod.injective_stdAddChar h))
  have hsurj : LinearMap.range (divergenceForm n p) = ⊤ := by
    refine LinearMap.range_eq_top.mpr fun c =>
      ⟨Pi.single d₀ (c / (ZMod.stdAddChar (-(p d₀)) - 1)), ?_⟩
    simp [divergenceForm, Pi.single_apply, div_mul_cancel₀ _ hz]
  have h := LinearMap.finrank_range_add_finrank_ker (divergenceForm n p)
  rw [hsurj, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h
  omega

/-- **WS6.** On the cubic torus with one `κ` and one `λ`, Pair turns the wave of an amplitude with
no divergence by `2 θ` per step, for every `θ` with `4 sin² θ = λ κ` times the level. -/
theorem cube_dispersion (p : CubePoint n) (a : Fin 3 → ℂ) (ha : NoDivergence n p a) (κ l θ : ℝ)
    (hθ : 4 * Real.sin θ ^ 2 = l * (κ * cubeLevel n p)) (k : ℕ) :
    (pair ((cubeIncidence n)ᵀ * diagonal (fun _ : CubePoint n × Fin 3 => κ) * cubeIncidence n)
        (diagonal fun _ : CubePoint n × Fin 3 => l))^[k]
      ((2 * Real.sin θ) • cubeWaveField n p a,
        (-Real.sin θ) • (((cubeIncidence n)ᵀ * diagonal (fun _ : CubePoint n × Fin 3 => κ) *
          cubeIncidence n) *ᵥ cubeWaveField n p a)) =
      ((2 * Real.sin θ * Real.cos (2 * k * θ)) • cubeWaveField n p a,
        Real.sin ((2 * k - 1) * θ) • (((cubeIncidence n)ᵀ *
          diagonal (fun _ : CubePoint n × Fin 3 => κ) * cubeIncidence n) *ᵥ
            cubeWaveField n p a)) := by
  apply level_wave
  rw [(cube_transverse_wave n p a ha κ).2, mulVec_smul]
  have hD : (diagonal fun _ : CubePoint n × Fin 3 => l) *ᵥ cubeWaveField n p a =
      l • cubeWaveField n p a := by
    funext ℓ
    simp [mulVec_diagonal]
  rw [hD, smul_smul, hθ]
  congr 1
  ring

omit [NeZero n] in
/-- **WS6.** Then `sin² θ = κ λ (sin² (θ₁ / 2) + sin² (θ₂ / 2) + sin² (θ₃ / 2))`. -/
theorem cube_dispersion_relation (p : CubePoint n) (κ l θ : ℝ)
    (hθ : 4 * Real.sin θ ^ 2 = l * (κ * cubeLevel n p)) :
    Real.sin θ ^ 2 = κ * l * ∑ d, Real.sin (π * (p d).val / n) ^ 2 := by
  have e : ∀ d,
      2 - 2 * Real.cos (2 * π * (p d).val / n) = 4 * Real.sin (π * (p d).val / n) ^ 2 := by
    intro d
    rw [show 2 * π * ((p d).val : ℝ) / n = 2 * (π * (p d).val / n) by ring, Real.cos_two_mul,
      Real.cos_sq']
    ring
  simp only [cubeLevel] at hθ
  rw [Finset.sum_congr rfl fun d _ => e d, ← Finset.mul_sum] at hθ
  linear_combination hθ / 4

end Artform.Stages
