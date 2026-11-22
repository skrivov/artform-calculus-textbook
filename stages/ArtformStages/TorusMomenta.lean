import ArtformStages.TorusHarmonic
import ArtformStages.Maxwell

/-!
# The two momenta of the torus

Finding 455 of the research ledger on a layered universe found the two harmonic fields of the
torus, the uniform ones, and that Pair keeps the means of `E`. Here the means are followed through
the motion (finding 457 of the ledger):

* `torus_pairWith_mean` (MO1): Pair with a current `J` moves the means of `E` by minus the means of
  `J`;
* `torus_pair_iterate_mean` (MO2): with no current, every number of steps keeps the means of `E`;
* `torus_pair_mean_A`, `torus_pair_iterate_mean_A` (MO3, MO4): with one drift `λ`, each step
  moves the means of `A` by `-λ` times the means of `E`, so after `k` steps they have moved by
  `-k λ` times them.
-/

open Matrix

namespace Artform.Stages

variable (n m : ℕ) [NeZero n] [NeZero m]

/-- The mean of a sum is the sum of the means. -/
theorem torusMean_add (E F : (ZMod n × ZMod m) × Fin 2 → ℝ) (d : Fin 2) :
    torusMean (E + F) d = torusMean E d + torusMean F d := by
  simp only [torusMean, Pi.add_apply, Finset.sum_add_distrib, add_div]

/-- The mean of a difference is the difference of the means. -/
theorem torusMean_sub (E F : (ZMod n × ZMod m) × Fin 2 → ℝ) (d : Fin 2) :
    torusMean (E - F) d = torusMean E d - torusMean F d := by
  simp only [torusMean, Pi.sub_apply, Finset.sum_sub_distrib, sub_div]

/-- The mean of a multiple is the multiple of the mean. -/
theorem torusMean_smul (c : ℝ) (E : (ZMod n × ZMod m) × Fin 2 → ℝ) (d : Fin 2) :
    torusMean (c • E) d = c * torusMean E d := by
  simp only [torusMean, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, mul_div_assoc]

variable [Fact (1 < n)] [Fact (1 < m)]

/-- A transverse field has the means `0`. -/
theorem torusMean_transpose (y : ZMod n × ZMod m → ℝ) (d : Fin 2) :
    torusMean ((torus n m).incidenceᵀ *ᵥ y) d = 0 := by
  simp only [torusMean, torus_sum_transpose, zero_div]

/-- **MO1.** On the torus, Pair with every kick `Cᵀ K C` and a current `J` moves the means of `E`
by minus the means of `J`. -/
theorem torus_pairWith_mean (K : Matrix (ZMod n × ZMod m) (ZMod n × ZMod m) ℝ)
    (L : Matrix ((ZMod n × ZMod m) × Fin 2) ((ZMod n × ZMod m) × Fin 2) ℝ)
    (J A E : (ZMod n × ZMod m) × Fin 2 → ℝ) (d : Fin 2) :
    torusMean (pairWith ((torus n m).incidenceᵀ * K * (torus n m).incidence) L J (A, E)).2 d =
      torusMean E d - torusMean J d := by
  simp only [pairWith]
  rw [← mulVec_mulVec, ← mulVec_mulVec, torusMean_sub, torusMean_add, torusMean_transpose,
    add_zero]

/-- **MO2.** With no current, every number of steps of Pair keeps the means of `E`. -/
theorem torus_pair_iterate_mean (K : Matrix (ZMod n × ZMod m) (ZMod n × ZMod m) ℝ)
    (L : Matrix ((ZMod n × ZMod m) × Fin 2) ((ZMod n × ZMod m) × Fin 2) ℝ)
    (x : LightState ℝ ((ZMod n × ZMod m) × Fin 2)) (d : Fin 2) (k : ℕ) :
    torusMean ((pair ((torus n m).incidenceᵀ * K * (torus n m).incidence) L)^[k] x).2 d =
      torusMean x.2 d := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih]
    have h := torus_pair_mean n m K L x.1 x.2 d
    rw [Prod.mk.eta] at h
    exact h

/-- **MO3.** With one drift `λ`, a step of Pair moves the means of `A` by `-λ` times the means of
`E`. -/
theorem torus_pair_mean_A (K : Matrix (ZMod n × ZMod m) (ZMod n × ZMod m) ℝ) (l : ℝ)
    (x : LightState ℝ ((ZMod n × ZMod m) × Fin 2)) (d : Fin 2) :
    torusMean (pair ((torus n m).incidenceᵀ * K * (torus n m).incidence)
        (diagonal fun _ : (ZMod n × ZMod m) × Fin 2 => l) x).1 d =
      torusMean x.1 d - l * torusMean x.2 d := by
  have hE := torus_pair_mean n m K (diagonal fun _ : (ZMod n × ZMod m) × Fin 2 => l) x.1 x.2 d
  simp only [pair] at hE ⊢
  have hD : ∀ u : (ZMod n × ZMod m) × Fin 2 → ℝ,
      (diagonal fun _ : (ZMod n × ZMod m) × Fin 2 => l) *ᵥ u = l • u := by
    intro u
    funext ℓ
    simp [mulVec_diagonal]
  rw [hD, torusMean_sub, torusMean_smul, hE]

/-- **MO4.** After `k` steps of Pair with one drift `λ` and no current, the means of `A` are those
at the start less `k λ` times the means of `E`. -/
theorem torus_pair_iterate_mean_A (K : Matrix (ZMod n × ZMod m) (ZMod n × ZMod m) ℝ) (l : ℝ)
    (x : LightState ℝ ((ZMod n × ZMod m) × Fin 2)) (d : Fin 2) (k : ℕ) :
    torusMean ((pair ((torus n m).incidenceᵀ * K * (torus n m).incidence)
        (diagonal fun _ : (ZMod n × ZMod m) × Fin 2 => l))^[k] x).1 d =
      torusMean x.1 d - k * l * torusMean x.2 d := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih, torus_pair_mean_A]
    have h := torus_pair_mean n m K (diagonal fun _ : (ZMod n × ZMod m) × Fin 2 => l) x.1 x.2 d
    rw [Prod.mk.eta] at h
    rw [h]
    push_cast
    ring

end Artform.Stages
