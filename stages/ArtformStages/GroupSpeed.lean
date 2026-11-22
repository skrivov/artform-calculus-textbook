import ArtformStages.SolidSpeed
import ArtformStages.Speed

/-!
# The group speed

Findings 450, 460 and 467 of the research ledger on a layered universe found the speed of long waves
of light. Here the speed of a packet of waves at every wave is bounded (finding 468 of the ledger):

* `waveAngle_hasDerivAt`, `waveAngle_two`, `waveAngle_three` (GS1): the angle per step of a plane
  wave in `k` dimensions, `2 arcsin (c √S)`, and its derivative in each angle, the group velocity;
  in two and three dimensions it is the plane angle and the solid angle;
* `groupVel_sq_le` (GS2): where `c² k ≤ 1` the group velocity has the size at most `c`;
* `axisAngle_hasDerivAt_at`, `axis_group_speed_lt`, `axis_group_speed_pi` (GS3): along an axis
  the group speed is below `c` at every shorter wave and `0` at the shortest.
-/

open Filter Topology

open scoped Real

namespace Artform.Stages

/-- `S θ`: the sum of the squares of the sines of the half angles, a quarter of the level. -/
noncomputable def halfLevel {k : ℕ} (θ : Fin k → ℝ) : ℝ := ∑ d, Real.sin (θ d / 2) ^ 2

/-- The angle per step of the plane wave of angles `θ` in `k` dimensions, for the speed `c`. -/
noncomputable def waveAngle {k : ℕ} (c : ℝ) (θ : Fin k → ℝ) : ℝ :=
  2 * Real.arcsin (c * Real.sqrt (halfLevel θ))

/-- The group velocity, its component along `j`. -/
noncomputable def groupVel {k : ℕ} (c : ℝ) (θ : Fin k → ℝ) (j : Fin k) : ℝ :=
  c * (Real.sin (θ j / 2) * Real.cos (θ j / 2)) /
    (Real.sqrt (halfLevel θ) * Real.sqrt (1 - c ^ 2 * halfLevel θ))

/-- `2 - 2 cos x = 4 sin² (x / 2)`. -/
theorem two_sub_two_cos (x : ℝ) : 2 - 2 * Real.cos x = 4 * Real.sin (x / 2) ^ 2 := by
  have h := Real.cos_two_mul (x / 2)
  rw [show 2 * (x / 2) = x by ring] at h
  rw [h, Real.cos_sq']
  ring

/-- `√4 = 2`. -/
theorem sqrt_four : Real.sqrt 4 = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- **GS1.** In the plane the angle per step is finding 460's plane angle. -/
theorem waveAngle_two (c θ₁ θ₂ : ℝ) : waveAngle c ![θ₁, θ₂] = planeAngle c θ₁ θ₂ := by
  unfold waveAngle planeAngle halfLevel
  rw [dispersion_identity, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), sqrt_four]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring_nf

/-- **GS1.** In a solid the angle per step is finding 467's solid angle. -/
theorem waveAngle_three (c : ℝ) (θ : Fin 3 → ℝ) : waveAngle c θ = solidAngle c θ := by
  unfold waveAngle solidAngle halfLevel
  simp only [two_sub_two_cos]
  rw [← Finset.mul_sum, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), sqrt_four]
  ring_nf

/-- **GS1.** Where `S θ > 0` and `c² S θ < 1`, the angle per step has in `θ j`, the other angles
held, the derivative `groupVel c θ j`. -/
theorem waveAngle_hasDerivAt {k : ℕ} (c : ℝ) (θ : Fin k → ℝ) (j : Fin k) (hc : 0 ≤ c)
    (hS : 0 < halfLevel θ) (h1 : c ^ 2 * halfLevel θ < 1) :
    HasDerivAt (fun x => waveAngle c (Function.update θ j x)) (groupVel c θ j) (θ j) := by
  have hS' : HasDerivAt (fun x => halfLevel (Function.update θ j x))
      (Real.sin (θ j / 2) * Real.cos (θ j / 2)) (θ j) := by
    unfold halfLevel
    have hd : ∀ d ∈ (Finset.univ : Finset (Fin k)),
        HasDerivAt (fun x => Real.sin (Function.update θ j x d / 2) ^ 2)
          (if d = j then Real.sin (θ j / 2) * Real.cos (θ j / 2) else 0) (θ j) := by
      intro d _
      by_cases hdj : d = j
      · subst hdj
        simp only [Function.update_self, ↓reduceIte]
        have h2 : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) (θ d) := by
          simpa using (hasDerivAt_id (θ d)).div_const 2
        exact (h2.sin.pow 2).congr_deriv (by norm_num; ring)
      · simp only [Function.update_of_ne hdj, hdj, ↓reduceIte]
        exact hasDerivAt_const _ _
    have hsum := HasDerivAt.fun_sum hd
    simpa [Finset.sum_ite_eq'] using hsum
  have hpt : Function.update θ j (θ j) = θ := Function.update_eq_self j θ
  have hsq : HasDerivAt (fun x => Real.sqrt (halfLevel (Function.update θ j x)))
      (Real.sin (θ j / 2) * Real.cos (θ j / 2) / (2 * Real.sqrt (halfLevel θ))) (θ j) := by
    have h := hS'.sqrt (by rw [hpt]; exact hS.ne')
    rwa [hpt] at h
  have hy0 : 0 ≤ c * Real.sqrt (halfLevel θ) := mul_nonneg hc (Real.sqrt_nonneg _)
  have hy2 : (c * Real.sqrt (halfLevel θ)) ^ 2 = c ^ 2 * halfLevel θ := by
    rw [mul_pow, Real.sq_sqrt hS.le]
  have hy1 : c * Real.sqrt (halfLevel θ) < 1 := by nlinarith
  have ha : HasDerivAt Real.arcsin (1 / Real.sqrt (1 - (c * Real.sqrt (halfLevel θ)) ^ 2))
      (c * Real.sqrt (halfLevel θ)) :=
    Real.hasDerivAt_arcsin (by linarith) hy1.ne
  have hcomp := ha.comp_of_eq (θ j) (hsq.const_mul c) (by simp)
  have hD : 0 < 1 - c ^ 2 * halfLevel θ := by linarith
  have hsD : Real.sqrt (1 - c ^ 2 * halfLevel θ) ≠ 0 := (Real.sqrt_pos.mpr hD).ne'
  have hsS : Real.sqrt (halfLevel θ) ≠ 0 := (Real.sqrt_pos.mpr hS).ne'
  refine (hcomp.const_mul 2).congr_deriv ?_
  rw [hy2]
  unfold groupVel
  field_simp

/-- **GS2.** Where `c² k ≤ 1`, at every wave with `S θ > 0` the group velocity has the size at
most `c`. -/
theorem groupVel_sq_le {k : ℕ} (c : ℝ) (θ : Fin k → ℝ) (hS : 0 < halfLevel θ)
    (hck : c ^ 2 * k ≤ 1) : ∑ j, groupVel c θ j ^ 2 ≤ c ^ 2 := by
  by_cases hD : 1 - c ^ 2 * halfLevel θ ≤ 0
  · have h0 : ∀ j, groupVel c θ j = 0 := fun j => by
      simp only [groupVel, Real.sqrt_eq_zero'.mpr hD, mul_zero, div_zero]
    rw [Finset.sum_eq_zero fun j _ => by rw [h0 j]; ring]
    positivity
  · rw [not_le] at hD
    have hsS : Real.sqrt (halfLevel θ) ^ 2 = halfLevel θ := Real.sq_sqrt hS.le
    have hsD : Real.sqrt (1 - c ^ 2 * halfLevel θ) ^ 2 = 1 - c ^ 2 * halfLevel θ :=
      Real.sq_sqrt hD.le
    have hden : 0 < halfLevel θ * (1 - c ^ 2 * halfLevel θ) := mul_pos hS hD
    have hv : ∀ j, groupVel c θ j ^ 2 = c ^ 2 * (Real.sin (θ j / 2) ^ 2 *
        (1 - Real.sin (θ j / 2) ^ 2)) / (halfLevel θ * (1 - c ^ 2 * halfLevel θ)) := by
      intro j
      unfold groupVel
      rw [div_pow, mul_pow, mul_pow, mul_pow, hsS, hsD, Real.cos_sq']
    simp only [hv]
    rw [← Finset.sum_div, div_le_iff₀ hden, ← Finset.mul_sum]
    have hcs : halfLevel θ ^ 2 ≤ k * ∑ j, Real.sin (θ j / 2) ^ 4 := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ))
        (fun j => Real.sin (θ j / 2) ^ 2)
      simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one] at h
      calc halfLevel θ ^ 2 = (∑ j, Real.sin (θ j / 2) ^ 2) ^ 2 := rfl
        _ ≤ k * ∑ j, (Real.sin (θ j / 2) ^ 2) ^ 2 := h
        _ = k * ∑ j, Real.sin (θ j / 2) ^ 4 := by
          congr 1
          exact Finset.sum_congr rfl fun j _ => by ring
    have hsum : ∑ j, Real.sin (θ j / 2) ^ 2 * (1 - Real.sin (θ j / 2) ^ 2) =
        halfLevel θ - ∑ j, Real.sin (θ j / 2) ^ 4 := by
      unfold halfLevel
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hsum]
    have h4 : 0 ≤ ∑ j, Real.sin (θ j / 2) ^ 4 := Finset.sum_nonneg fun j _ => by positivity
    have e1 : c ^ 4 * halfLevel θ ^ 2 ≤ c ^ 4 * (k * ∑ j, Real.sin (θ j / 2) ^ 4) :=
      mul_le_mul_of_nonneg_left hcs (by positivity)
    have e2 : 0 ≤ (1 - c ^ 2 * k) * (c ^ 2 * ∑ j, Real.sin (θ j / 2) ^ 4) :=
      mul_nonneg (by linarith) (mul_nonneg (sq_nonneg c) h4)
    nlinarith [e1, e2]

/-- The group speed along an axis: `c cos (θ / 2) / √(1 - c² sin² (θ / 2))`. -/
noncomputable def axisGroupSpeed (c θ : ℝ) : ℝ :=
  c * Real.cos (θ / 2) / Real.sqrt (1 - c ^ 2 * Real.sin (θ / 2) ^ 2)

/-- **GS3.** For `0 ≤ c < 1`, finding 450's angle along an axis has at every `θ` the derivative
`axisGroupSpeed c θ`. -/
theorem axisAngle_hasDerivAt_at (c θ : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    HasDerivAt (axisAngle c) (axisGroupSpeed c θ) θ := by
  have h1 : HasDerivAt (fun θ : ℝ => θ / 2) (1 / 2) θ := by
    simpa using (hasDerivAt_id θ).div_const 2
  have hg : HasDerivAt (fun θ : ℝ => c * Real.sin (θ / 2)) (c * (Real.cos (θ / 2) * (1 / 2))) θ :=
    h1.sin.const_mul c
  have hb : |c * Real.sin (θ / 2)| < 1 := by
    rw [abs_mul, abs_of_nonneg hc0]
    calc c * |Real.sin (θ / 2)| ≤ c * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) hc0
      _ < 1 := by linarith
  have hb2 : (c * Real.sin (θ / 2)) ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one _).mpr hb
  have ha : HasDerivAt Real.arcsin (1 / Real.sqrt (1 - (c * Real.sin (θ / 2)) ^ 2))
      (c * Real.sin (θ / 2)) :=
    Real.hasDerivAt_arcsin (fun h => by rw [h] at hb; norm_num at hb)
      (fun h => by rw [h] at hb; norm_num at hb)
  have hD : 0 < 1 - c ^ 2 * Real.sin (θ / 2) ^ 2 := by rw [← mul_pow]; linarith
  have hsD : Real.sqrt (1 - c ^ 2 * Real.sin (θ / 2) ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hD).ne'
  refine ((ha.comp θ hg).const_mul 2).congr_deriv ?_
  unfold axisGroupSpeed
  rw [mul_pow]
  field_simp

/-- **GS3.** For `0 < c < 1`, at every `θ` with `0 < θ < 2 π` the group speed along an axis is less
than `c`. -/
theorem axis_group_speed_lt (c θ : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (h0 : 0 < θ) (h2 : θ < 2 * π) :
    axisGroupSpeed c θ < c := by
  have hs : 0 < Real.sin (θ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hsl : Real.sin (θ / 2) ^ 2 ≤ 1 := Real.sin_sq_le_one _
  have hc2 : c ^ 2 < 1 := by nlinarith
  have hD : 0 < 1 - c ^ 2 * Real.sin (θ / 2) ^ 2 := by nlinarith
  have hsD := Real.sqrt_pos.mpr hD
  unfold axisGroupSpeed
  rw [div_lt_iff₀ hsD]
  by_cases hcos : Real.cos (θ / 2) ≤ 0
  · calc c * Real.cos (θ / 2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc0.le hcos
      _ < c * Real.sqrt (1 - c ^ 2 * Real.sin (θ / 2) ^ 2) := mul_pos hc0 hsD
  · rw [not_le] at hcos
    have hlt : Real.cos (θ / 2) < Real.sqrt (1 - c ^ 2 * Real.sin (θ / 2) ^ 2) := by
      rw [show Real.cos (θ / 2) = Real.sqrt (Real.cos (θ / 2) ^ 2) from
        (Real.sqrt_sq hcos.le).symm]
      apply Real.sqrt_lt_sqrt (sq_nonneg _)
      rw [Real.cos_sq']
      have := mul_pos (by linarith : (0 : ℝ) < 1 - c ^ 2) (pow_pos hs 2)
      linarith
    exact mul_lt_mul_of_pos_left hlt hc0

/-- **GS3.** At `θ = π`, the shortest light along an axis, the group speed is `0`. -/
theorem axis_group_speed_pi (c : ℝ) : axisGroupSpeed c π = 0 := by
  simp [axisGroupSpeed, Real.cos_pi_div_two]

end Artform.Stages
