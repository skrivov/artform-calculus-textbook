import Mathlib.NumberTheory.Niven
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Tactic

/-! # The actual frozen spatial rotation has dense integer powers -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.BoundarySymbol
open scoped Topology
open Real

noncomputable def rotationValue : ℂ := 399 / 401 + (40 / 401) * Complex.I

lemma rotation_norm : ‖rotationValue‖ = 1 := by
  norm_num [rotationValue, Complex.norm_def, Complex.normSq]

lemma rotation_ne_zero : rotationValue ≠ 0 := by
  intro h
  have hn := rotation_norm
  rw [h, norm_zero] at hn
  norm_num at hn

lemma rotation_cos_arg : Real.cos (Complex.arg rotationValue) = 399 / 401 := by
  rw [Complex.cos_arg rotation_ne_zero, rotation_norm]
  norm_num [rotationValue]

lemma rotation_frequency_irrational :
    Irrational (Complex.arg rotationValue / (2 * Real.pi)) := by
  rintro ⟨q, hq⟩
  have hp : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  have ht : Complex.arg rotationValue = ((2 * q : ℚ) : ℝ) * Real.pi := by
    calc
      _ = (Complex.arg rotationValue / (2 * Real.pi)) * (2 * Real.pi) :=
        (div_mul_cancel₀ _ hp).symm
      _ = (q : ℝ) * (2 * Real.pi) := by rw [← hq]
      _ = _ := by push_cast; ring
  have hn := niven ⟨2 * q, ht⟩ ⟨399 / 401, by simpa using rotation_cos_arg⟩
  rw [rotation_cos_arg] at hn
  norm_num at hn

noncomputable def rotation : Circle := Circle.exp (Complex.arg rotationValue)

lemma rotation_coe : (rotation : ℂ) = rotationValue := by
  dsimp only [rotation]
  rw [Circle.coe_exp]
  have h := Complex.norm_mul_exp_arg_mul_I rotationValue
  simpa only [rotation_norm, Complex.ofReal_one, one_mul] using h

lemma rotation_dense : DenseRange (fun n : ℤ => rotation ^ n) := by
  have hd : DenseRange (fun n : ℤ => n •
      (Complex.arg rotationValue : AddCircle (2 * Real.pi))) :=
    AddCircle.denseRange_zsmul_coe_iff.mpr rotation_frequency_irrational
  have he : DenseRange (fun a : AddCircle (2 * Real.pi) =>
      AddCircle.homeomorphCircle' a) := AddCircle.homeomorphCircle'.surjective.denseRange
  have h := he.comp hd AddCircle.homeomorphCircle'.continuous
  convert h using 1
  funext n
  change Circle.exp (Complex.arg rotationValue) ^ n =
    AddCircle.homeomorphCircle' (n • (Complex.arg rotationValue : AddCircle (2 * Real.pi)))
  rw [← AddCircle.coe_zsmul, AddCircle.homeomorphCircle'_apply_mk, Circle.exp_zsmul]

lemma rotation_power_ne_minus_one (n : ℤ) : rotationValue ^ n ≠ -1 := by
  intro h
  by_cases hn : n = 0
  · subst n
    norm_num at h
  have hcircle : rotation ^ n = Circle.exp Real.pi := by
    apply Subtype.ext
    rw [Circle.coe_zpow, rotation_coe, Circle.coe_exp, Complex.exp_pi_mul_I]
    exact h
  have hexp : Circle.exp ((n : ℝ) * Complex.arg rotationValue) = Circle.exp Real.pi := by
    rw [Circle.exp_intCast_mul]
    exact hcircle
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hexp
  apply rotation_frequency_irrational
  refine ⟨(2 * (m : ℚ) + 1) / (2 * (n : ℚ)), ?_⟩
  push_cast
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp
  nlinarith [hm]

end Artform.Scores.NonabelianGravity.BoundarySymbol
