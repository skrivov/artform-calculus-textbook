import ArtformScores.GravityBridge.HeatStatements
import ArtformScores.GravityBridge.Gaussian

/-! # Exact convergent Gaussian gluing keeps its measure and determinant -/

namespace Artform.Scores.GravityBridge

noncomputable section

open MeasureTheory

lemma heat_normalization (h0 h1 : ℝ) (h0p : 0 < h0) (h1p : 0 < h1) :
    (Real.sqrt (2 * Real.pi * h0))⁻¹ * (Real.sqrt (2 * Real.pi * h1))⁻¹ *
      Real.sqrt (Real.pi / ((h0 + h1) / (2 * h0 * h1))) =
        (Real.sqrt (2 * Real.pi * (h0 + h1)))⁻¹ := by
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  simp only [mul_pow, inv_pow]
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  field_simp

lemma heat_kernel_gluing (h0 h1 x y : ℝ) (h0p : 0 < h0) (h1p : 0 < h1) :
    Integrable (fun m : ℝ => heatKernel h0 x m * heatKernel h1 m y) ∧
    (∫ m : ℝ, heatKernel h0 x m * heatKernel h1 m y) = heatKernel (h0 + h1) x y := by
  let a := (h0 + h1) / (2 * h0 * h1)
  let j := x / (2 * h0) + y / (2 * h1)
  let c := x ^ 2 / (2 * h0) + y ^ 2 / (2 * h1)
  have ap : 0 < a := by dsimp [a]; positivity
  have hn0 : h0 ≠ 0 := ne_of_gt h0p
  have hn1 : h1 ≠ 0 := ne_of_gt h1p
  have hH : h0 + h1 ≠ 0 := ne_of_gt (add_pos h0p h1p)
  have hpoly (m : ℝ) :
      -(m - x) ^ 2 / (2 * h0) + -(y - m) ^ 2 / (2 * h1) =
        -gaussianAction a 0 c j 0 1 m := by
    dsimp [gaussianAction, a, j, c]
    field_simp
    ring
  have heff : gaussianEffective a 0 c j 0 1 = (y - x) ^ 2 / (2 * (h0 + h1)) := by
    dsimp [gaussianEffective, a, j, c]
    field_simp
    ring
  have hfun : (fun m : ℝ => heatKernel h0 x m * heatKernel h1 m y) =
      fun m => ((Real.sqrt (2 * Real.pi * h0))⁻¹ * (Real.sqrt (2 * Real.pi * h1))⁻¹) *
        Real.exp (-gaussianAction a 0 c j 0 1 m) := by
    funext m
    dsimp [heatKernel]
    rw [show (Real.sqrt (2 * Real.pi * h0))⁻¹ * Real.exp (-(m - x) ^ 2 / (2 * h0)) *
        ((Real.sqrt (2 * Real.pi * h1))⁻¹ * Real.exp (-(y - m) ^ 2 / (2 * h1))) =
      ((Real.sqrt (2 * Real.pi * h0))⁻¹ * (Real.sqrt (2 * Real.pi * h1))⁻¹) *
        (Real.exp (-(m - x) ^ 2 / (2 * h0)) * Real.exp (-(y - m) ^ 2 / (2 * h1))) by ring]
    rw [← Real.exp_add, hpoly]
  rw [hfun]
  have hg := gaussian_schur_integral a 0 c j 0 1 ap
  constructor
  · exact hg.1.const_mul _
  · rw [integral_const_mul, hg.2, heff]
    dsimp [heatKernel]
    have hc := heat_normalization h0 h1 h0p h1p
    change (Real.sqrt (2 * Real.pi * h0))⁻¹ * (Real.sqrt (2 * Real.pi * h1))⁻¹ *
      (Real.exp (-((y - x) ^ 2 / (2 * (h0 + h1)))) * Real.sqrt (Real.pi / a)) = _
    calc
      _ = ((Real.sqrt (2 * Real.pi * h0))⁻¹ * (Real.sqrt (2 * Real.pi * h1))⁻¹ *
          Real.sqrt (Real.pi / a)) * Real.exp (-((y - x) ^ 2 / (2 * (h0 + h1)))) := by ring
      _ = _ := by rw [hc]; congr 2; ring

lemma midpoint_omission :
    let h : ℝ := 1 / (2 * Real.pi)
    heatKernel h 0 0 * heatKernel h 0 0 = 1 ∧
      heatKernel (h + h) 0 0 = (Real.sqrt 2)⁻¹ ∧
      heatKernel h 0 0 * heatKernel h 0 0 ≠ heatKernel (h + h) 0 0 := by
  dsimp only
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hnorm : 2 * Real.pi * (1 / (2 * Real.pi)) = 1 := by field_simp
  have hnorm2 : 2 * Real.pi * (1 / (2 * Real.pi) + 1 / (2 * Real.pi)) = 2 := by
    field_simp
    norm_num
  have hs : Real.sqrt (2 : ℝ) ≠ 1 := by
    have hsq : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    intro he
    rw [he] at hsq
    norm_num at hsq
  have hk : heatKernel (1 / (2 * Real.pi)) 0 0 = 1 := by
    simp only [heatKernel, hnorm]
    norm_num
  have hk2 : heatKernel (1 / (2 * Real.pi) + 1 / (2 * Real.pi)) 0 0 = (Real.sqrt 2)⁻¹ := by
    simp only [heatKernel, hnorm2]
    norm_num
  rw [hk, hk2]
  refine ⟨by norm_num, rfl, ?_⟩
  simpa only [one_mul] using (show (1 : ℝ) ≠ (Real.sqrt 2)⁻¹ from
    fun he => hs (inv_eq_one.mp he.symm))

/-- **GAC:normalized-gaussian-gluing** (integrated detail and exact normalization). -/
@[ledger "GAC:normalized-gaussian-gluing"]
theorem heatLaw : Statement.heatLaw := by
  exact ⟨heat_normalization, heat_kernel_gluing, midpoint_omission⟩

/-! ## Non-vacuity -/

example : 0 < (1 : ℝ) / (2 * Real.pi) := by positivity

end

end Artform.Scores.GravityBridge
