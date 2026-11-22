import ArtformStages.TorusJoined
import ArtformStages.Hodge
import ArtformStages.Holonomy
import ArtformStages.Waves

/-!
# The two harmonic fields of the torus

Finding 451 of the research ledger on a layered universe split every field into a gradient, a
transverse field and a harmonic field, one with no divergence and no curl. Here the harmonic fields
of the torus are found (finding 455 of the ledger): they are the uniform fields, one number on the
lines of each direction.

* `torus_gaugeT_mulVec`, `torus_incidence_mulVec` (HM1): `Gᵀ h` and `C h` on the torus;
* `torus_harmonic_uniform`, `torus_uniform_harmonic`, `torus_harmonic_iff` (HM2 to HM4): a field
  with no divergence and no curl is uniform, and every uniform field is one;
* `rowField_uniform` (HM5): finding 446's row field is a uniform field;
* `torus_hodge`, `torus_hodge_mean` (HM6): every field is a gradient, a transverse field and the
  uniform field of its two means, and the two numbers are always its means;
* `torus_pair_mean` (HM7): Pair keeps the means of `E`.

The proof of HM2 shows that each component of a harmonic field has the five-point Laplacian `0`,
so that the sum of the squares of its differences, which is minus its sum against the Laplacian,
is `0`: the component is the same at the two ends of every step, and so everywhere.
-/

open Matrix

namespace Artform.Stages

/-- The uniform field of `c₀` and `c₁`: `c₀` on every line `(w, 0)`, `c₁` on every line `(w, 1)`. -/
def uniformField (n m : ℕ) (c₀ c₁ : ℝ) : (ZMod n × ZMod m) × Fin 2 → ℝ :=
  fun ℓ => if ℓ.2 = 0 then c₀ else c₁

/-- The mean of a field over the lines `(w, d)` of the direction `d`. -/
noncomputable def torusMean {n m : ℕ} [NeZero n] [NeZero m] (E : (ZMod n × ZMod m) × Fin 2 → ℝ)
    (d : Fin 2) : ℝ :=
  (∑ w, E (w, d)) / ((n : ℝ) * m)

/-- **HM5.** Finding 446's row field of `a` is the uniform field of `a` and `0`. -/
theorem rowField_uniform (n m : ℕ) (a : ℝ) : rowField n m a = uniformField n m a 0 := rfl

variable (n m : ℕ) [NeZero n] [NeZero m]

/-- A sum over the points of the torus is the same with every point moved by `c`. -/
theorem torus_sum_shift (g : ZMod n × ZMod m → ℝ) (c : ZMod n × ZMod m) :
    ∑ w, g (w + c) = ∑ w, g w :=
  Equiv.sum_comp (Equiv.addRight c) g

/-- The same, with every point moved back by `c`. -/
theorem torus_sum_sub (g : ZMod n × ZMod m → ℝ) (c : ZMod n × ZMod m) :
    ∑ w, g (w - c) = ∑ w, g w := by
  simp only [sub_eq_add_neg]
  exact torus_sum_shift n m g (-c)

/-- The sum of the squares of the differences of `a` along the two axes is minus the sum of `a`
against its five-point Laplacian. -/
theorem torus_energy (a : ZMod n × ZMod m → ℝ) :
    ∑ w, ((a (w + (1, 0)) - a w) ^ 2 + (a (w + (0, 1)) - a w) ^ 2) =
      -∑ w, a w * (a (w + (1, 0)) + a (w - (1, 0)) + a (w + (0, 1)) + a (w - (0, 1)) -
        4 * a w) := by
  have s1 : ∑ w, a (w + (1, 0)) ^ 2 = ∑ w, a w ^ 2 := torus_sum_shift n m (fun w => a w ^ 2) _
  have s2 : ∑ w, a (w + (0, 1)) ^ 2 = ∑ w, a w ^ 2 := torus_sum_shift n m (fun w => a w ^ 2) _
  have s3 : ∑ w, a w * a (w - (1, 0)) = ∑ w, a (w + (1, 0)) * a w := by
    rw [← torus_sum_shift n m (fun w => a w * a (w - (1, 0))) (1, 0)]
    simp only [add_sub_cancel_right]
  have s4 : ∑ w, a w * a (w - (0, 1)) = ∑ w, a (w + (0, 1)) * a w := by
    rw [← torus_sum_shift n m (fun w => a w * a (w - (0, 1))) (0, 1)]
    simp only [add_sub_cancel_right]
  have e1 : ∑ w, ((a (w + (1, 0)) - a w) ^ 2 + (a (w + (0, 1)) - a w) ^ 2) =
      ∑ w, a (w + (1, 0)) ^ 2 + ∑ w, a (w + (0, 1)) ^ 2 + 2 * ∑ w, a w ^ 2 -
        2 * ∑ w, a (w + (1, 0)) * a w - 2 * ∑ w, a (w + (0, 1)) * a w := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun w _ => by ring
  have e2 : ∑ w, a w * (a (w + (1, 0)) + a (w - (1, 0)) + a (w + (0, 1)) + a (w - (0, 1)) -
      4 * a w) = ∑ w, a (w + (1, 0)) * a w + ∑ w, a w * a (w - (1, 0)) +
        ∑ w, a (w + (0, 1)) * a w + ∑ w, a w * a (w - (0, 1)) - 4 * ∑ w, a w ^ 2 := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun w _ => by ring
  rw [e1, e2, s1, s2, s3, s4]
  ring

/-- A function on the torus whose five-point Laplacian is `0` is the same everywhere. -/
theorem torus_harmonic_const (a : ZMod n × ZMod m → ℝ)
    (hΔ : ∀ w, a (w + (1, 0)) + a (w - (1, 0)) + a (w + (0, 1)) + a (w - (0, 1)) - 4 * a w = 0)
    (w : ZMod n × ZMod m) : a w = a 0 := by
  have hsum := torus_energy n m a
  simp only [hΔ, mul_zero, Finset.sum_const_zero, neg_zero] at hsum
  have hz := (Finset.sum_eq_zero_iff_of_nonneg fun w _ => by positivity).mp hsum
  have hd1 : ∀ σ, a σ = a (σ + (1, 0)) := fun σ => by
    have := hz σ (Finset.mem_univ σ)
    nlinarith [sq_nonneg (a (σ + (1, 0)) - a σ), sq_nonneg (a (σ + (0, 1)) - a σ)]
  have hd2 : ∀ σ, a σ = a (σ + (0, 1)) := fun σ => by
    have := hz σ (Finset.mem_univ σ)
    nlinarith [sq_nonneg (a (σ + (1, 0)) - a σ), sq_nonneg (a (σ + (0, 1)) - a σ)]
  have hj := torus_steps_join n m (fun x y => a x = a y) hd1 hd2 0 w
  induction hj with
  | refl => rfl
  | tail _ hbc ih => exact hbc.symm.trans ih

variable [Fact (1 < n)] [Fact (1 < m)]

/-- **HM1.** On the torus, `Gᵀ h` at the corner `w` is what the lines bring in less what they take
out. -/
theorem torus_gaugeT_mulVec (h : (ZMod n × ZMod m) × Fin 2 → ℝ) (w : ZMod n × ZMod m) :
    ((torus n m).gaugeᵀ *ᵥ h) w = h (w - (1, 0), 0) + h (w - (0, 1), 1) - h (w, 0) - h (w, 1) := by
  have e : ((torus n m).gaugeᵀ *ᵥ h) w =
      (∑ ℓ, if (torus n m).head ℓ = w then h ℓ else 0) -
        ∑ ℓ, if (torus n m).tail ℓ = w then h ℓ else 0 := by
    simp only [mulVec, dotProduct, transpose_apply, Board.gauge, Matrix.of_apply, sub_mul, ite_mul,
      one_mul, zero_mul, Finset.sum_sub_distrib]
  have hne : ((w - (1, 0), 0) : (ZMod n × ZMod m) × Fin 2) ≠ (w - (0, 1), 1) := by
    simp [Prod.ext_iff]
  have hne' : ((w, 0) : (ZMod n × ZMod m) × Fin 2) ≠ (w, 1) := by
    simp [Prod.ext_iff]
  have h1 : (∑ ℓ, if (torus n m).head ℓ = w then h ℓ else 0) =
      h (w - (1, 0), 0) + h (w - (0, 1), 1) := by
    rw [Fintype.sum_eq_add _ _ hne]
    · simp [torus]
    · rintro ⟨u, d⟩ ⟨h1, h2⟩
      refine ite_eq_right fun hu => ?_
      exfalso
      fin_cases d
      · apply h1
        simp [torus] at hu
        simp [← hu]
      · apply h2
        simp [torus] at hu
        simp [← hu]
  have h2 : (∑ ℓ, if (torus n m).tail ℓ = w then h ℓ else 0) = h (w, 0) + h (w, 1) := by
    rw [Fintype.sum_eq_add _ _ hne']
    · simp [torus]
    · rintro ⟨u, d⟩ ⟨h1, h2⟩
      refine ite_eq_right fun hu => ?_
      exfalso
      simp only [torus] at hu
      subst hu
      fin_cases d
      · exact h1 rfl
      · exact h2 rfl
  rw [e, h1, h2]
  ring

/-- **HM1.** On the torus, `C h` at the square `σ` is `h` summed round it, each side with its
sign. -/
theorem torus_incidence_mulVec (h : (ZMod n × ZMod m) × Fin 2 → ℝ) (σ : ZMod n × ZMod m) :
    ((torus n m).incidence *ᵥ h) σ =
      h (σ, 0) + h (σ + (1, 0), 1) - h (σ + (0, 1), 0) - h (σ, 1) := by
  have s0 : (torus n m).side σ 0 = (σ, 0) := by simp [torus]
  have s1 : (torus n m).side σ 1 = (σ + (1, 0), 1) := by simp [torus]
  have s2 : (torus n m).side σ 2 = (σ + (0, 1), 0) := by simp [torus]
  have s3 : (torus n m).side σ 3 = (σ, 1) := by simp [torus]
  have a0 : (torus n m).along σ 0 = true := by simp [torus]
  have a1 : (torus n m).along σ 1 = true := by simp [torus]
  have a2 : (torus n m).along σ 2 = false := by simp [torus]
  have a3 : (torus n m).along σ 3 = false := by simp [torus]
  have t1 : Board.turnSign true = 1 := by simp [Board.turnSign]
  have t2 : Board.turnSign false = -1 := by simp [Board.turnSign]
  rw [Board.incidence_mulVec, Fin.sum_univ_four, s0, s1, s2, s3, a0, a1, a2, a3, t1, t2]
  ring

/-- **HM2.** On the torus, a field with no divergence and no curl is uniform. -/
theorem torus_harmonic_uniform (h : (ZMod n × ZMod m) × Fin 2 → ℝ)
    (hG : (torus n m).gaugeᵀ *ᵥ h = 0) (hC : (torus n m).incidence *ᵥ h = 0) :
    ∃ c₀ c₁ : ℝ, h = uniformField n m c₀ c₁ := by
  have D : ∀ x, h (x - (1, 0), 0) + h (x - (0, 1), 1) - h (x, 0) - h (x, 1) = 0 := fun x => by
    rw [← torus_gaugeT_mulVec]
    exact congrFun hG x
  have R : ∀ x, h (x, 0) + h (x + (1, 0), 1) - h (x + (0, 1), 0) - h (x, 1) = 0 := fun x => by
    rw [← torus_incidence_mulVec]
    exact congrFun hC x
  have ha : ∀ w, h (w + (1, 0), 0) + h (w - (1, 0), 0) + h (w + (0, 1), 0) + h (w - (0, 1), 0) -
      4 * h (w, 0) = 0 := by
    intro w
    have d1 := D (w + (1, 0))
    have d2 := D w
    have r1 := R (w - (0, 1))
    have r2 := R w
    rw [add_sub_cancel_right] at d1
    rw [sub_add_cancel, show w - (0, 1) + (1, 0) = w + (1, 0) - (0, 1) by abel] at r1
    linear_combination -d1 + d2 + r1 - r2
  have hb : ∀ w, h (w + (1, 0), 1) + h (w - (1, 0), 1) + h (w + (0, 1), 1) + h (w - (0, 1), 1) -
      4 * h (w, 1) = 0 := by
    intro w
    have r2 := R w
    have r3 := R (w - (1, 0))
    have d3 := D (w + (0, 1))
    have d2 := D w
    rw [sub_add_cancel, show w - (1, 0) + (0, 1) = w + (0, 1) - (1, 0) by abel] at r3
    rw [add_sub_cancel_right] at d3
    linear_combination r2 - r3 - d3 + d2
  have c0 := torus_harmonic_const n m (fun w => h (w, 0)) ha
  have c1 := torus_harmonic_const n m (fun w => h (w, 1)) hb
  refine ⟨h (0, 0), h (0, 1), funext fun ℓ => ?_⟩
  obtain ⟨w, d⟩ := ℓ
  fin_cases d
  · simpa [uniformField] using c0 w
  · simpa [uniformField] using c1 w

/-- **HM3.** Every uniform field has no divergence and no curl. -/
theorem torus_uniform_harmonic (c₀ c₁ : ℝ) :
    (torus n m).gaugeᵀ *ᵥ uniformField n m c₀ c₁ = 0 ∧
      (torus n m).incidence *ᵥ uniformField n m c₀ c₁ = 0 := by
  constructor
  · funext w
    rw [torus_gaugeT_mulVec]
    simp [uniformField]
  · funext σ
    rw [torus_incidence_mulVec]
    simp [uniformField]

/-- **HM4.** The harmonic fields of the torus are exactly the uniform fields: two numbers. -/
theorem torus_harmonic_iff (h : (ZMod n × ZMod m) × Fin 2 → ℝ) :
    ((torus n m).gaugeᵀ *ᵥ h = 0 ∧ (torus n m).incidence *ᵥ h = 0) ↔
      ∃ c₀ c₁ : ℝ, h = uniformField n m c₀ c₁ := by
  constructor
  · rintro ⟨hG, hC⟩
    exact torus_harmonic_uniform n m h hG hC
  · rintro ⟨c₀, c₁, rfl⟩
    exact torus_uniform_harmonic n m c₀ c₁

/-- A gradient sums to `0` over the lines of each direction. -/
theorem torus_sum_gauge (φ : ZMod n × ZMod m → ℝ) (d : Fin 2) :
    ∑ w, ((torus n m).gauge *ᵥ φ) (w, d) = 0 := by
  simp only [Board.gauge_mulVec]
  fin_cases d
  · simp only [torus, Fin.zero_eta, Matrix.cons_val_zero]
    rw [Finset.sum_sub_distrib, torus_sum_shift n m φ, sub_self]
  · simp only [torus, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [Finset.sum_sub_distrib, torus_sum_shift n m φ, sub_self]

/-- A transverse field sums to `0` over the lines of each direction. -/
theorem torus_sum_transpose (y : ZMod n × ZMod m → ℝ) (d : Fin 2) :
    ∑ w, ((torus n m).incidenceᵀ *ᵥ y) (w, d) = 0 := by
  fin_cases d
  · simp only [Fin.zero_eta, torus_transpose_mulVec_zero]
    rw [Finset.sum_sub_distrib, torus_sum_sub n m y, sub_self]
  · simp only [Fin.mk_one, torus_transpose_mulVec_one]
    rw [Finset.sum_sub_distrib, torus_sum_sub n m y, sub_self]

/-- **HM6.** In every sum `G φ + Cᵀ ψ + u(c₀, c₁)` of a field, the two numbers are its means. -/
theorem torus_hodge_mean (E : (ZMod n × ZMod m) × Fin 2 → ℝ) (φ ψ : ZMod n × ZMod m → ℝ)
    (c₀ c₁ : ℝ) (h : E = (torus n m).gauge *ᵥ φ + (torus n m).incidenceᵀ *ᵥ ψ +
      uniformField n m c₀ c₁) :
    c₀ = torusMean E 0 ∧ c₁ = torusMean E 1 := by
  have hnm : ((n : ℝ) * m) ≠ 0 := by
    have := NeZero.ne n
    have := NeZero.ne m
    positivity
  have hs : ∀ d : Fin 2,
      ∑ w, E (w, d) = (n * m : ℝ) * uniformField n m c₀ c₁ ((0 : ZMod n × ZMod m), d) := by
    intro d
    rw [h]
    simp only [Pi.add_apply, Finset.sum_add_distrib, torus_sum_gauge, torus_sum_transpose, zero_add]
    by_cases hd : d = 0
    · simp [uniformField, hd]
    · simp [uniformField, hd]
  constructor
  · rw [torusMean, hs 0, mul_comm, mul_div_assoc, div_self hnm, mul_one]
    simp [uniformField]
  · rw [torusMean, hs 1, mul_comm, mul_div_assoc, div_self hnm, mul_one]
    simp [uniformField]

/-- **HM6.** Every field on the torus is a gradient, a transverse field and the uniform field of its
two means. -/
theorem torus_hodge (E : (ZMod n × ZMod m) × Fin 2 → ℝ) :
    ∃ (φ ψ : ZMod n × ZMod m → ℝ), E = (torus n m).gauge *ᵥ φ + (torus n m).incidenceᵀ *ᵥ ψ +
      uniformField n m (torusMean E 0) (torusMean E 1) := by
  obtain ⟨φ, ψ, h, hE, hG, hC⟩ :=
    hodge_exists (torus n m).incidence (torus n m).gauge (torus n m).incidence_mul_gauge E
  obtain ⟨c₀, c₁, rfl⟩ := torus_harmonic_uniform n m h hG hC
  obtain ⟨e0, e1⟩ := torus_hodge_mean n m E φ ψ c₀ c₁ hE
  exact ⟨φ, ψ, by rw [← e0, ← e1]; exact hE⟩

/-- **HM7.** Pair with every kick `Cᵀ K C` and every drift keeps the means of `E`. -/
theorem torus_pair_mean (K : Matrix (ZMod n × ZMod m) (ZMod n × ZMod m) ℝ)
    (L : Matrix ((ZMod n × ZMod m) × Fin 2) ((ZMod n × ZMod m) × Fin 2) ℝ)
    (A E : (ZMod n × ZMod m) × Fin 2 → ℝ) (d : Fin 2) :
    torusMean (pair ((torus n m).incidenceᵀ * K * (torus n m).incidence) L (A, E)).2 d =
      torusMean E d := by
  simp only [torusMean, pair]
  congr 1
  rw [← mulVec_mulVec, ← mulVec_mulVec]
  simp only [Pi.add_apply, Finset.sum_add_distrib, torus_sum_transpose, add_zero]

end Artform.Stages
