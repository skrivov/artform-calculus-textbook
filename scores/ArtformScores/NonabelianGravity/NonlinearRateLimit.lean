import ArtformScores.NonabelianGravity.NonlinearLongHistory

/-! # Exact analytic lapse coefficient for arbitrary isotropic first-order rates -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.NonlinearIsotropic
open Filter Topology

noncomputable def rateForce (f b g e : ℝ) : ℝ :=
  lapseForceAt (1 / 101) (cayleyC (b * e / 2)) (cayleyS (b * e / 2))
    1 (1 + f * e) (1 + g * e)
noncomputable def rateRegular (f b g e : ℝ) : ℝ :=
  3 * (1 + f * e) *
    (2 * (b / 2) ^ 2 / (1 - (b * e / 2) ^ 2) *
      boostCoefficient (cayleyC (b * e / 2)) + (1 / 101) * (g - f) ^ 2)

lemma rate_factor (f b g e : ℝ) (he : 1 - (b * e / 2) ^ 2 ≠ 0) :
    rateForce f b g e = e ^ 2 * rateRegular f b g e := by
  rw [rateForce, force_factorization _ _ _ _ _ (cayley_lorentz _ he)]
  have hc (t : ℝ) (ht : 1 - t ^ 2 ≠ 0) : cayleyC t - 1 = 2 * t ^ 2 / (1 - t ^ 2) := by
    unfold cayleyC
    field_simp [ht]
    ring
  rw [hc _ he]
  dsimp [rateRegular]
  ring

lemma rate_regular_continuous (f b g : ℝ) : ContinuousAt (rateRegular f b g) 0 := by
  unfold rateRegular boostCoefficient cayleyC
  fun_prop (disch := norm_num)

lemma rate_regular_zero (f b g : ℝ) :
    rateRegular f b g 0 = 3 * ((100 / 101) * b ^ 2 + (1 / 101) * (g - f) ^ 2) := by
  norm_num [rateRegular, boostCoefficient, cayleyC]
  ring

lemma rate_force_limit (f b g : ℝ) :
    Tendsto (fun e : ℝ => rateForce f b g e / e ^ 2) (𝓝[≠] 0)
      (𝓝 (3 * ((100 / 101) * b ^ 2 + (1 / 101) * (g - f) ^ 2))) := by
  have hp : ContinuousAt (fun e : ℝ => 1 - (b * e / 2) ^ 2) 0 := by fun_prop
  have hd : ∀ᶠ e in 𝓝 (0 : ℝ), 1 - (b * e / 2) ^ 2 ≠ 0 :=
    hp.eventually_ne (by norm_num)
  have heq : (fun e : ℝ => rateForce f b g e / e ^ 2) =ᶠ[𝓝[≠] 0] rateRegular f b g := by
    filter_upwards [hd.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with e hd he
    have hn : e ≠ 0 := he
    rw [rate_factor f b g e hd]
    field_simp
  have ht : Tendsto (rateRegular f b g) (𝓝[≠] 0) (𝓝 (rateRegular f b g 0)) :=
    (rate_regular_continuous f b g).tendsto.mono_left nhdsWithin_le_nhds
  rw [rate_regular_zero] at ht
  exact ht.congr' heq.symm

open NonlinearLongHistory in
lemma long_history_local_limits (t : Fin 3) :
    Tendsto (fun e : ℝ => rateForce (frameRate t) (boostRate t) (nextRate t) e / e ^ 2)
      (𝓝[≠] 0) (𝓝 (coefficient t : ℝ)) := by
  convert rate_force_limit (frameRate t : ℝ) (boostRate t : ℝ) (nextRate t : ℝ) using 1
  push_cast [NonlinearLongHistory.coefficient]
  rfl

end Artform.Scores.NonabelianGravity.NonlinearIsotropic
