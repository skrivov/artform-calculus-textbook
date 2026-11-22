import ArtformStages.TorusHarmonic
import ArtformStages.Coulomb

/-!
# The modes of light on the torus

Finding 455 of the research ledger on a layered universe found the harmonic fields of the torus.
Here the three parts of a field on the torus are counted (finding 459 of the ledger):

* `torus_transpose_ker`, `torus_gauge_ker` (MD1, MD2): `Cᵀ ψ = 0` and `G φ = 0` only for constants;
* `torus_gradient_finrank`, `torus_transverse_finrank` (MD3): the gradients and the transverse
  fields each form a space of dimension `n m - 1`;
* `torus_harmonic_finrank` (MD4): the harmonic fields form a space of dimension `2`;
* `torus_finrank_sum` (MD5): together they have the dimension of the fields, the `2 n m` lines.
-/

open Matrix Module

namespace Artform.Stages

/-- The uniform field of two numbers, as a linear map. -/
def uniformMap (n m : ℕ) : (Fin 2 → ℝ) →ₗ[ℝ] ((ZMod n × ZMod m) × Fin 2 → ℝ) where
  toFun c := uniformField n m (c 0) (c 1)
  map_add' c c' := by
    funext ℓ
    by_cases h : ℓ.2 = 0 <;> simp [uniformField, h]
  map_smul' a c := by
    funext ℓ
    by_cases h : ℓ.2 = 0 <;> simp [uniformField, h]

variable (n m : ℕ) [NeZero n] [NeZero m] [Fact (1 < n)] [Fact (1 < m)]

/-- **MD1.** On the torus, `Cᵀ ψ = 0` exactly when `ψ` is the same on every square. -/
theorem torus_transpose_ker (ψ : ZMod n × ZMod m → ℝ) :
    (torus n m).incidenceᵀ *ᵥ ψ = 0 ↔ ∀ σ, ψ σ = ψ 0 := by
  constructor
  · intro h σ
    have hr : ∀ ρ, ψ ρ = ψ (ρ + (1, 0)) := fun ρ => by
      have := congrFun h (ρ + (1, 0), 1)
      rw [torus_transpose_mulVec_one, add_sub_cancel_right] at this
      simpa [sub_eq_zero] using this
    have hu : ∀ ρ, ψ ρ = ψ (ρ + (0, 1)) := fun ρ => by
      have := congrFun h (ρ + (0, 1), 0)
      rw [torus_transpose_mulVec_zero, add_sub_cancel_right, Pi.zero_apply, sub_eq_zero] at this
      exact this.symm
    have hj := torus_steps_join n m (fun x y => ψ x = ψ y) hr hu 0 σ
    induction hj with
    | refl => rfl
    | tail _ hbc ih => exact hbc.symm.trans ih
  · intro h
    funext ℓ
    obtain ⟨w, d⟩ := ℓ
    fin_cases d
    · simp [torus_transpose_mulVec_zero, h w, h (w - (0, 1))]
    · simp [torus_transpose_mulVec_one, h w, h (w - (1, 0))]

/-- **MD2.** On the torus, `G φ = 0` exactly when `φ` is the same at every corner. -/
theorem torus_gauge_ker (φ : ZMod n × ZMod m → ℝ) :
    (torus n m).gauge *ᵥ φ = 0 ↔ ∀ w, φ w = φ 0 := by
  constructor
  · intro h w
    exact (torus n m).gauge_const (torus_corners_joined n m) φ h w 0
  · intro h
    funext ℓ
    rw [Board.gauge_mulVec, h, h (Board.tail (torus n m) ℓ), sub_self, Pi.zero_apply]

/-- **MD3.** The gradients of the torus form a space of dimension `n m - 1`. -/
theorem torus_gradient_finrank :
    finrank ℝ (LinearMap.range (torus n m).gauge.mulVecLin) = n * m - 1 := by
  have hker : LinearMap.ker (torus n m).gauge.mulVecLin = Submodule.span ℝ {fun _ => (1 : ℝ)} := by
    ext φ
    rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
    constructor
    · intro h
      have hc := (torus_gauge_ker n m φ).mp h
      exact ⟨φ 0, funext fun w => by simp [hc w]⟩
    · rintro ⟨c, rfl⟩
      exact (torus_gauge_ker n m _).mpr fun w => rfl
  have h1 : finrank ℝ (LinearMap.ker (torus n m).gauge.mulVecLin) = 1 := by
    rw [hker]
    refine finrank_span_singleton fun h0 => ?_
    have := congrFun h0 0
    simp at this
  have hT := LinearMap.finrank_range_add_finrank_ker (torus n m).gauge.mulVecLin
  rw [h1, Module.finrank_fintype_fun_eq_card, Fintype.card_prod, ZMod.card, ZMod.card] at hT
  omega

/-- **MD3.** The transverse fields of the torus form a space of dimension `n m - 1`. -/
theorem torus_transverse_finrank :
    finrank ℝ (LinearMap.range (torus n m).incidenceᵀ.mulVecLin) = n * m - 1 := by
  have hker : LinearMap.ker (torus n m).incidenceᵀ.mulVecLin =
      Submodule.span ℝ {fun _ => (1 : ℝ)} := by
    ext ψ
    rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
    constructor
    · intro h
      have hc := (torus_transpose_ker n m ψ).mp h
      exact ⟨ψ 0, funext fun σ => by simp [hc σ]⟩
    · rintro ⟨c, rfl⟩
      exact (torus_transpose_ker n m _).mpr fun σ => rfl
  have h1 : finrank ℝ (LinearMap.ker (torus n m).incidenceᵀ.mulVecLin) = 1 := by
    rw [hker]
    refine finrank_span_singleton fun h0 => ?_
    have := congrFun h0 0
    simp at this
  have hT := LinearMap.finrank_range_add_finrank_ker (torus n m).incidenceᵀ.mulVecLin
  rw [h1, Module.finrank_fintype_fun_eq_card, Fintype.card_prod, ZMod.card, ZMod.card] at hT
  omega

/-- **MD4.** The harmonic fields of the torus form a space of dimension `2`. -/
theorem torus_harmonic_finrank :
    finrank ℝ ↥(LinearMap.ker (torus n m).gaugeᵀ.mulVecLin ⊓
      LinearMap.ker (torus n m).incidence.mulVecLin) = 2 := by
  have hrange : LinearMap.ker (torus n m).gaugeᵀ.mulVecLin ⊓
      LinearMap.ker (torus n m).incidence.mulVecLin = LinearMap.range (uniformMap n m) := by
    ext h
    rw [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker, LinearMap.mem_range]
    simp only [Matrix.mulVecLin_apply]
    rw [torus_harmonic_iff]
    constructor
    · rintro ⟨c₀, c₁, rfl⟩
      exact ⟨![c₀, c₁], rfl⟩
    · rintro ⟨c, rfl⟩
      exact ⟨c 0, c 1, rfl⟩
  have hinj : Function.Injective (uniformMap n m) := by
    intro c c' h
    have h0 := congrFun h ((0 : ZMod n × ZMod m), 0)
    have h1 := congrFun h ((0 : ZMod n × ZMod m), 1)
    simp [uniformMap, uniformField] at h0 h1
    funext i
    fin_cases i
    · simpa using h0
    · simpa using h1
  rw [hrange, LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun]

/-- **MD5.** The three dimensions add up to the number of lines, `2 n m`. -/
theorem torus_finrank_sum :
    finrank ℝ (LinearMap.range (torus n m).gauge.mulVecLin) +
        finrank ℝ (LinearMap.range (torus n m).incidenceᵀ.mulVecLin) +
        finrank ℝ ↥(LinearMap.ker (torus n m).gaugeᵀ.mulVecLin ⊓
          LinearMap.ker (torus n m).incidence.mulVecLin) =
      Fintype.card ((ZMod n × ZMod m) × Fin 2) := by
  rw [torus_gradient_finrank, torus_transverse_finrank, torus_harmonic_finrank, Fintype.card_prod,
    Fintype.card_prod, ZMod.card, ZMod.card, Fintype.card_fin]
  have := Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne n)) (Nat.pos_of_ne_zero (NeZero.ne m))
  omega

end Artform.Stages
