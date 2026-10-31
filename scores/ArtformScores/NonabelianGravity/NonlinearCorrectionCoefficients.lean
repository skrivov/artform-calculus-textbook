import ArtformScores.NonabelianGravity.NonlinearCorrection

/-! # Every ambient second-order coefficient is included, without an isotropic ansatz -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.NonlinearAmbient
open NonlinearDifferential Filter Topology Asymptotics
open scoped Matrix.Norms.Elementwise

lemma coefficient_contact (f b g : ℝ) (w : Env) :
    (fun e : ℝ => (rateCurve f b g e + e ^ 2 • w) - rateCurve f b g e)
      =O[𝓝[≠] 0] (fun e => e ^ 2) := by
  apply IsBigO.of_bound ‖w‖
  filter_upwards [] with e
  simp [norm_smul, mul_comm]

lemma coefficient_curve_tendsto (f b g : ℝ) (w : Env) :
    Tendsto (fun e : ℝ => rateCurve f b g e + e ^ 2 • w) (𝓝[≠] 0) (𝓝 flat) := by
  have h : ContinuousAt (fun e : ℝ => rateCurve f b g e + e ^ 2 • w) 0 :=
    (rate_curve_continuous f b g).add (by fun_prop)
  simpa only [zero_pow (by decide : 2 ≠ 0), zero_smul, add_zero, rate_curve_zero] using
    h.tendsto.mono_left nhdsWithin_le_nhds

lemma all_coefficient_limit (f b g : ℝ) (w : Env) :
    Tendsto (fun e : ℝ => force (rateCurve f b g e + e ^ 2 • w) / e ^ 2) (𝓝[≠] 0)
      (𝓝 (3 * ((100 / 101) * b ^ 2 + (1 / 101) * (g - f) ^ 2))) :=
  arbitrary_correction_limit f b g _ (coefficient_curve_tendsto f b g w)
    (coefficient_contact f b g w)

lemma corrected_force_eventually_nonzero (f b g : ℝ) (u : ℝ → Env)
    (hu : Tendsto u (𝓝[≠] 0) (𝓝 flat))
    (hc : (fun e => u e - rateCurve f b g e) =O[𝓝[≠] 0] (fun e => e ^ 2))
    (hp : 0 < 3 * ((100 / 101) * b ^ 2 + (1 / 101) * (g - f) ^ 2)) :
    ∀ᶠ e in 𝓝[≠] (0 : ℝ), force (u e) ≠ 0 := by
  have hh := (arbitrary_correction_limit f b g u hu hc).eventually
    (eventually_ne_nhds (ne_of_gt hp))
  filter_upwards [hh] with e he
  intro hz
  exact he (by rw [hz, zero_div])

open NonlinearLongHistory in
lemma longer_history_all_local_corrections (t : Fin 3) (u : ℝ → Env)
    (hu : Tendsto u (𝓝[≠] 0) (𝓝 flat))
    (hc : (fun e => u e - rateCurve (frameRate t) (boostRate t) (nextRate t) e)
      =O[𝓝[≠] 0] (fun e => e ^ 2)) :
    Tendsto (fun e : ℝ => force (u e) / e ^ 2) (𝓝[≠] 0) (𝓝 (coefficient t : ℝ)) ∧
      ∀ᶠ e in 𝓝[≠] (0 : ℝ), force (u e) ≠ 0 := by
  have hp : 0 < 3 * ((100 / 101) * (boostRate t : ℝ) ^ 2 +
      (1 / 101) * ((nextRate t : ℝ) - (frameRate t : ℝ)) ^ 2) := by
    have h : (0 : ℝ) < (coefficient t : ℝ) := by exact_mod_cast coefficients_positive t
    simpa only [coefficient, Rat.cast_mul, Rat.cast_pow, Rat.cast_add, Rat.cast_sub,
      Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using h
  refine ⟨?_, corrected_force_eventually_nonzero _ _ _ u hu hc hp⟩
  convert arbitrary_correction_limit (frameRate t) (boostRate t) (nextRate t) u hu hc using 1
  push_cast [NonlinearLongHistory.coefficient]
  rfl

end Artform.Scores.NonabelianGravity.NonlinearAmbient
