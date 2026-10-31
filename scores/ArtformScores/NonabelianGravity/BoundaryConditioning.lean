import ArtformScores.NonabelianGravity.BoundaryCircle

/-! # Kernel-aware conditioning of the actual native spatial boundary symbol -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.BoundarySymbol
open Artform.Scores.NonabelianGravity.Legendre (Point)

noncomputable def boostUnit : Point ℂ := fun i => if i = 22 then 1 else 0

lemma column_norm (z : ℂ) : ‖mixedApply z boostUnit‖ = ‖1 + z‖ / 4 := by
  rw [show boostUnit = (fun i => if i = 22 then 1 else 0) from rfl, column22]
  have ha : ‖-(1 + z) / (4 : ℂ)‖ = ‖1 + z‖ / 4 := by
    rw [norm_div, norm_neg]
    norm_num
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    split_ifs
    · rw [ha]
    · simp only [norm_zero]
      positivity
  · have h := norm_le_pi_norm (fun i : Fin 40 =>
      if i = 10 ∨ i = 15 then -(1 + z) / 4 else (0 : ℂ)) 10
    change ‖-(1 + z) / (4 : ℂ)‖ ≤ _ at h
    rwa [ha] at h

lemma unit_T_ne_zero (z : ℂ) (hz : ‖z‖ = 1) : 10201 + 10589 * z ≠ 0 := by
  intro h
  have hh : (10589 : ℂ) * z = -10201 := by linear_combination h
  have hn := congrArg norm hh
  rw [norm_mul, hz] at hn
  norm_num at hn

lemma kernel_coordinate (n : ℤ) (v : Point ℂ)
    (hv : mixedApply (rotationValue ^ n) v = 0) : v 22 = 0 := by
  have h := left_witness (rotationValue ^ n) (zpow_ne_zero _ rotation_ne_zero) v
  rw [hv, dotProduct_zero] at h
  have hz : ‖rotationValue ^ n‖ = 1 := by rw [norm_zpow, rotation_norm, one_zpow]
  have hp : 1 + rotationValue ^ n ≠ 0 := by
    intro hp
    apply rotation_power_ne_minus_one n
    linear_combination hp
  exact (mul_eq_zero.mp h.symm).resolve_left
    (div_ne_zero (mul_ne_zero (unit_T_ne_zero _ hz) hp) (by norm_num))

lemma boost_orthogonal_to_kernel (n : ℤ) (v : Point ℂ)
    (hv : mixedApply (rotationValue ^ n) v = 0) :
    dotProduct (fun i => star (v i)) boostUnit = 0 := by
  have hk := kernel_coordinate n v hv
  norm_num [dotProduct, boostUnit, Fin.sum_univ_succ, hk]

lemma no_uniform_coordinate_estimate :
    ¬ ∃ C : ℝ, ∀ (n : ℤ) (v : Point ℂ),
      ‖v 22‖ ≤ C * ‖mixedApply (rotationValue ^ n) v‖ := by
  rintro ⟨C, hc⟩
  have hc' (n : ℤ) : 1 ≤ C * (‖1 + rotationValue ^ n‖ / 4) := by
    have h := hc n boostUnit
    change ‖(1 : ℂ)‖ ≤ C * ‖mixedApply (rotationValue ^ n) boostUnit‖ at h
    simpa only [norm_one, column_norm] using h
  let s : Set Circle := {z | (1 : ℝ) ≤ C * (‖(1 : ℂ) + (z : ℂ)‖ / 4)}
  have hs : IsClosed s := isClosed_le continuous_const
    (continuous_const.mul ((continuous_const.add continuous_subtype_val).norm.div_const 4))
  have hr : Set.range (fun n : ℤ => rotation ^ n) ⊆ s := by
    rintro z ⟨n, rfl⟩
    simpa [s, Circle.coe_zpow, rotation_coe] using hc' n
  have hall : Set.univ ⊆ s := by
    rw [← rotation_dense.closure_range]
    exact hs.closure_subset_iff.mpr hr
  have h := hall (Set.mem_univ (Circle.exp Real.pi))
  change 1 ≤ C * (‖(1 : ℂ) + ((Circle.exp Real.pi : Circle) : ℂ)‖ / 4) at h
  rw [Circle.coe_exp, Complex.exp_pi_mul_I] at h
  norm_num at h

end Artform.Scores.NonabelianGravity.BoundarySymbol
