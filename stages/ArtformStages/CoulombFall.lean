import ArtformStages.TorusHarmonic
import ArtformStages.Maxwell

/-!
# Coulomb's fall in the plane

Finding 445 of the research ledger on a layered universe proved Gauss's theorem over every set of
cells. Here it is read on a box of corners of the torus, and it says how the field of a charge falls
with distance (finding 469 of the ledger):

* `torus_box_gauss` (CP1): the divergence summed over the box of side `s` is the flux out through
  the `4 s` lines of its ring;
* `torus_ring_mean` (CP2): so at distance `r` from a lone charge `q` the mean outward field on the
  ring is `q / (8 r + 4)`;
* `torus_ring_strongest` (CP3): some line of the ring carries at least the mean.
-/

open Matrix

namespace Artform.Stages

/-- A telescoping sum along a ring of numbers. -/
theorem sum_range_shift_sub {R : Type*} [AddGroupWithOne R] (F : R → ℝ) (s : ℕ) :
    ∑ i ∈ Finset.range s, (F (i : R) - F ((i : R) - 1)) = F ((s : R) - 1) - F (-1) := by
  have h := Finset.sum_range_sub (fun i : ℕ => F ((i : R) - 1)) s
  simp only [Nat.cast_succ, add_sub_cancel_right, Nat.cast_zero, zero_sub] at h
  exact h

/-- If each of four numbers, read outward, is below `X`, their sum is below `4 X`. -/
theorem four_lt_of_max_lt (a b c d X : ℝ) (h : max (max a (-b)) (max c (-d)) < X) :
    (a - b) + (c - d) < 4 * X := by
  have h1 := le_max_left (max a (-b)) (max c (-d))
  have h2 := le_max_right (max a (-b)) (max c (-d))
  have h3 := le_max_left a (-b)
  have h4 := le_max_right a (-b)
  have h5 := le_max_left c (-d)
  have h6 := le_max_right c (-d)
  linarith

variable (n m : ℕ) [NeZero n] [NeZero m] [Fact (1 < n)] [Fact (1 < m)]

/-- The divergence of `E` at the corner `c + (i, j)` of the torus: what flows out across and up. -/
theorem torus_divergence_at (E : (ZMod n × ZMod m) × Fin 2 → ℝ) (c : ZMod n × ZMod m)
    (i : ZMod n) (j : ZMod m) :
    divergence (torus n m).gauge E (c + (i, j)) =
      (E (c + (i, j), 0) - E (c + (i - 1, j), 0)) +
        (E (c + (i, j), 1) - E (c + (i, j - 1), 1)) := by
  have h1 : c + (i, j) - (1, 0) = c + (i - 1, j) := by
    ext <;> simp [add_sub_assoc]
  have h2 : c + (i, j) - (0, 1) = c + (i, j - 1) := by
    ext <;> simp [add_sub_assoc]
  simp only [divergence, Pi.neg_apply, torus_gaugeT_mulVec, h1, h2]
  ring

/-- The flux out of the box of side `s` at the corner `c`, through the `4 s` lines of its ring, each
read leaving the box. -/
def ringFlux (E : (ZMod n × ZMod m) × Fin 2 → ℝ) (c : ZMod n × ZMod m) (s : ℕ) : ℝ :=
  ∑ j ∈ Finset.range s,
      (E (c + ((s : ZMod n) - 1, (j : ZMod m)), 0) - E (c + (-1, (j : ZMod m)), 0)) +
    ∑ i ∈ Finset.range s,
      (E (c + ((i : ZMod n), (s : ZMod m) - 1), 1) - E (c + ((i : ZMod n), -1), 1))

/-- **CP1.** The divergence summed over the box of side `s` at `c` is the flux out through its
ring. -/
theorem torus_box_gauss (E : (ZMod n × ZMod m) × Fin 2 → ℝ) (c : ZMod n × ZMod m) (s : ℕ) :
    ∑ i ∈ Finset.range s, ∑ j ∈ Finset.range s,
        divergence (torus n m).gauge E (c + ((i : ZMod n), (j : ZMod m))) = ringFlux n m E c s := by
  simp only [torus_divergence_at, Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    exact sum_range_shift_sub (fun x : ZMod n => E (c + (x, (j : ZMod m)), 0)) s
  · refine Finset.sum_congr rfl fun i _ => ?_
    exact sum_range_shift_sub (fun y : ZMod m => E (c + ((i : ZMod n), y), 1)) s

/-- **CP2.** If the only charge in the box of side `2 r + 1` at `c` is `q`, at its middle corner,
the mean outward field on the ring is `q / (8 r + 4)`. -/
theorem torus_ring_mean (E : (ZMod n × ZMod m) × Fin 2 → ℝ) (c : ZMod n × ZMod m) (r : ℕ) (q : ℝ)
    (hρ : ∀ i < 2 * r + 1, ∀ j < 2 * r + 1,
      divergence (torus n m).gauge E (c + ((i : ZMod n), (j : ZMod m))) =
        if i = r ∧ j = r then q else 0) :
    ringFlux n m E c (2 * r + 1) / (4 * (2 * r + 1 : ℕ)) = q / (8 * r + 4) := by
  rw [← torus_box_gauss]
  have hr : r ∈ Finset.range (2 * r + 1) := Finset.mem_range.mpr (by omega)
  have hsum : ∑ i ∈ Finset.range (2 * r + 1), ∑ j ∈ Finset.range (2 * r + 1),
      divergence (torus n m).gauge E (c + ((i : ZMod n), (j : ZMod m))) = q := by
    rw [Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj =>
      hρ i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)]
    simp only [ite_and]
    rw [Finset.sum_eq_single r]
    · rw [Finset.sum_eq_single r]
      · simp
      · intro j _ hj
        simp [hj]
      · intro h
        exact absurd hr h
    · intro i _ hi
      simp [hi]
    · intro h
      exact absurd hr h
  rw [hsum]
  congr 1
  push_cast
  ring

omit [NeZero n] [NeZero m] [Fact (1 < n)] [Fact (1 < m)] in
/-- **CP3.** For every `s ≥ 1`, some line of the ring carries an outward field at least the flux
divided by `4 s`. -/
theorem torus_ring_strongest (E : (ZMod n × ZMod m) × Fin 2 → ℝ) (c : ZMod n × ZMod m) (s : ℕ)
    (hs : 0 < s) :
    ∃ j ∈ Finset.range s, ringFlux n m E c s / (4 * s) ≤
      max (max (E (c + ((s : ZMod n) - 1, (j : ZMod m)), 0)) (-E (c + (-1, (j : ZMod m)), 0)))
        (max (E (c + ((j : ZMod n), (s : ZMod m) - 1), 1)) (-E (c + ((j : ZMod n), -1), 1))) := by
  by_contra h
  simp only [not_exists, not_and, not_le] at h
  have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have hlt : ringFlux n m E c s < ringFlux n m E c s := by
    calc ringFlux n m E c s = ∑ j ∈ Finset.range s,
          ((E (c + ((s : ZMod n) - 1, (j : ZMod m)), 0) - E (c + (-1, (j : ZMod m)), 0)) +
            (E (c + ((j : ZMod n), (s : ZMod m) - 1), 1) - E (c + ((j : ZMod n), -1), 1))) := by
          rw [ringFlux, ← Finset.sum_add_distrib]
      _ < ∑ _j ∈ Finset.range s, ringFlux n m E c s / s := by
          refine Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_range.mpr hs⟩ fun j hj => ?_
          calc _ < 4 * (ringFlux n m E c s / (4 * s)) := four_lt_of_max_lt _ _ _ _ _ (h j hj)
            _ = ringFlux n m E c s / s := by field_simp
      _ = ringFlux n m E c s := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          field_simp
  exact lt_irrefl _ hlt

end Artform.Stages
