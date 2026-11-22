import ArtformStages.CoulombFall
import ArtformStages.SolidWaves

/-!
# Coulomb's fall in a solid

Finding 469 of the research ledger on a layered universe read Gauss's theorem on a box of corners
of the torus. Here it is read on a cube of corners of the cubic torus (finding 470 of the ledger):

* `cube_box_gauss` (CS1): the divergence summed over the cube of side `s` is the flux out through
  the `6 s²` lines of its shell;
* `cube_shell_mean` (CS2): so at distance `r` from a lone charge `q` the mean outward field on the
  shell is `q / (6 (2 r + 1)²)`;
* `cube_shell_strongest` (CS3): some line of the shell carries at least the mean.
-/

open Matrix

namespace Artform.Stages

/-- If each of six numbers, read outward, is below `X`, their sum is below `6 X`. -/
theorem six_lt_of_max_lt (a b c d e f X : ℝ)
    (h : max (max (max a (-b)) (max c (-d))) (max e (-f)) < X) :
    (a - b) + (c - d) + (e - f) < 6 * X := by
  have h1 := le_max_left (max (max a (-b)) (max c (-d))) (max e (-f))
  have h2 := le_max_right (max (max a (-b)) (max c (-d))) (max e (-f))
  have h3 := le_max_left (max a (-b)) (max c (-d))
  have h4 := le_max_right (max a (-b)) (max c (-d))
  have h5 := le_max_left a (-b)
  have h6 := le_max_right a (-b)
  have h7 := le_max_left c (-d)
  have h8 := le_max_right c (-d)
  have h9 := le_max_left e (-f)
  have h10 := le_max_right e (-f)
  linarith

variable (n : ℕ)

/-- The corner `c + (x, y, z)` of the cubic torus. -/
def cubePt (c : CubePoint n) (x y z : ZMod n) : CubePoint n := c + ![x, y, z]

theorem cubePt_sub_zero (c : CubePoint n) (x y z : ZMod n) :
    cubePt n c x y z - cubeStep n 0 = cubePt n c (x - 1) y z := by
  funext d
  fin_cases d <;> simp [cubePt, cubeStep, add_sub_assoc] <;> rfl

theorem cubePt_sub_one (c : CubePoint n) (x y z : ZMod n) :
    cubePt n c x y z - cubeStep n 1 = cubePt n c x (y - 1) z := by
  funext d
  fin_cases d <;> simp [cubePt, cubeStep, add_sub_assoc] <;> rfl

theorem cubePt_sub_two (c : CubePoint n) (x y z : ZMod n) :
    cubePt n c x y z - cubeStep n 2 = cubePt n c x y (z - 1) := by
  funext d
  fin_cases d <;> simp [cubePt, cubeStep, add_sub_assoc] <;> rfl

/-- The flux out of the cube of side `s` at the corner `c`, through the `6 s²` lines of its shell,
each read leaving the cube. -/
def shellFlux (E : CubePoint n × Fin 3 → ℝ) (c : CubePoint n) (s : ℕ) : ℝ :=
  ∑ j ∈ Finset.range s, ∑ k ∈ Finset.range s,
      (E (cubePt n c ((s : ZMod n) - 1) j k, 0) - E (cubePt n c (-1) j k, 0)) +
    ∑ i ∈ Finset.range s, ∑ k ∈ Finset.range s,
      (E (cubePt n c i ((s : ZMod n) - 1) k, 1) - E (cubePt n c i (-1) k, 1)) +
    ∑ i ∈ Finset.range s, ∑ j ∈ Finset.range s,
      (E (cubePt n c i j ((s : ZMod n) - 1), 2) - E (cubePt n c i j (-1), 2))

/-- **CS3.** For every `s ≥ 1`, some line of the shell carries an outward field at least the flux
divided by `6 s²`. -/
theorem cube_shell_strongest (E : CubePoint n × Fin 3 → ℝ) (c : CubePoint n) (s : ℕ) (hs : 0 < s) :
    ∃ p ∈ Finset.range s, ∃ q ∈ Finset.range s, shellFlux n E c s / (6 * s ^ 2) ≤
      max (max (max (E (cubePt n c ((s : ZMod n) - 1) p q, 0)) (-E (cubePt n c (-1) p q, 0)))
          (max (E (cubePt n c p ((s : ZMod n) - 1) q, 1)) (-E (cubePt n c p (-1) q, 1))))
        (max (E (cubePt n c p q ((s : ZMod n) - 1), 2)) (-E (cubePt n c p q (-1), 2))) := by
  by_contra h
  simp only [not_exists, not_and, not_le] at h
  have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have hne : (Finset.range s).Nonempty := ⟨0, Finset.mem_range.mpr hs⟩
  have hlt : shellFlux n E c s < shellFlux n E c s := by
    calc shellFlux n E c s = ∑ p ∈ Finset.range s, ∑ q ∈ Finset.range s,
          ((E (cubePt n c ((s : ZMod n) - 1) p q, 0) - E (cubePt n c (-1) p q, 0)) +
            (E (cubePt n c p ((s : ZMod n) - 1) q, 1) - E (cubePt n c p (-1) q, 1)) +
            (E (cubePt n c p q ((s : ZMod n) - 1), 2) - E (cubePt n c p q (-1), 2))) := by
          rw [shellFlux]
          simp only [Finset.sum_add_distrib]
      _ < ∑ _p ∈ Finset.range s, ∑ _q ∈ Finset.range s, shellFlux n E c s / s ^ 2 := by
          refine Finset.sum_lt_sum_of_nonempty hne fun p hp => ?_
          refine Finset.sum_lt_sum_of_nonempty hne fun q hq => ?_
          calc _ < 6 * (shellFlux n E c s / (6 * s ^ 2)) :=
                six_lt_of_max_lt _ _ _ _ _ _ _ (h p hp q hq)
            _ = shellFlux n E c s / s ^ 2 := by field_simp
      _ = shellFlux n E c s := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          field_simp
  exact lt_irrefl _ hlt

variable [NeZero n]

/-- The divergence of `E` at the corner `c + (x, y, z)` of the cubic torus: what flows out along
the three directions. -/
theorem cube_divergence_at (E : CubePoint n × Fin 3 → ℝ) (c : CubePoint n) (x y z : ZMod n) :
    divergence (cubeGauge n) E (cubePt n c x y z) =
      (E (cubePt n c x y z, 0) - E (cubePt n c (x - 1) y z, 0)) +
        (E (cubePt n c x y z, 1) - E (cubePt n c x (y - 1) z, 1)) +
          (E (cubePt n c x y z, 2) - E (cubePt n c x y (z - 1), 2)) := by
  simp only [divergence, Pi.neg_apply, cube_gaugeT_mulVec, Fin.sum_univ_three, cubePt_sub_zero,
    cubePt_sub_one, cubePt_sub_two]
  ring

/-- **CS1.** The divergence summed over the cube of side `s` at `c` is the flux out through its
shell. -/
theorem cube_box_gauss (E : CubePoint n × Fin 3 → ℝ) (c : CubePoint n) (s : ℕ) :
    ∑ i ∈ Finset.range s, ∑ j ∈ Finset.range s, ∑ k ∈ Finset.range s,
        divergence (cubeGauge n) E (cubePt n c i j k) = shellFlux n E c s := by
  simp only [cube_divergence_at, Finset.sum_add_distrib]
  unfold shellFlux
  congr 1
  · congr 1
    · conv_lhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      conv_lhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      exact sum_range_shift_sub (fun x : ZMod n => E (cubePt n c x j k, 0)) s
    · refine Finset.sum_congr rfl fun i _ => ?_
      conv_lhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      exact sum_range_shift_sub (fun y : ZMod n => E (cubePt n c i y k, 1)) s
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    exact sum_range_shift_sub (fun z : ZMod n => E (cubePt n c i j z, 2)) s

/-- **CS2.** If the only charge in the cube of side `2 r + 1` at `c` is `q`, at its middle corner,
the mean outward field on the shell is `q / (6 (2 r + 1)²)`. -/
theorem cube_shell_mean (E : CubePoint n × Fin 3 → ℝ) (c : CubePoint n) (r : ℕ) (q : ℝ)
    (hρ : ∀ i < 2 * r + 1, ∀ j < 2 * r + 1, ∀ k < 2 * r + 1,
      divergence (cubeGauge n) E (cubePt n c i j k) = if i = r ∧ j = r ∧ k = r then q else 0) :
    shellFlux n E c (2 * r + 1) / (6 * ((2 * r + 1 : ℕ) : ℝ) ^ 2) = q / (6 * (2 * r + 1) ^ 2) := by
  rw [← cube_box_gauss]
  have hr : r ∈ Finset.range (2 * r + 1) := Finset.mem_range.mpr (by omega)
  have hsum : ∑ i ∈ Finset.range (2 * r + 1), ∑ j ∈ Finset.range (2 * r + 1),
      ∑ k ∈ Finset.range (2 * r + 1), divergence (cubeGauge n) E (cubePt n c i j k) = q := by
    rw [Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj =>
      Finset.sum_congr rfl fun k hk => hρ i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) k
        (Finset.mem_range.mp hk)]
    rw [Finset.sum_eq_single r (fun i _ hi => by simp [hi]) (fun h => absurd hr h),
      Finset.sum_eq_single r (fun j _ hj => by simp [hj]) (fun h => absurd hr h),
      Finset.sum_eq_single r (fun k _ hk => by simp [hk]) (fun h => absurd hr h)]
    simp
  rw [hsum]
  norm_num

end Artform.Stages
