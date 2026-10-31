import ArtformScores.NonabelianGravity.NonlinearIsotropicWitness

/-! # Actual analytic leading lapse force on the prepared rational boost chart -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.NonlinearIsotropic
open Filter Topology

noncomputable def chartParameter (e : ℝ) : ℝ := (-50 / 201) * e
noncomputable def spatialScale (e : ℝ) : ℝ := 1 + (101 / 402) * e
noncomputable def futureScale (e : ℝ) : ℝ := 1 + e

noncomputable def preparedForce (e : ℝ) : ℝ :=
  lapseForceAt (1 / 101) (cayleyC (chartParameter e)) (cayleyS (chartParameter e))
    1 (spatialScale e) (futureScale e)

noncomputable def regularForce (e : ℝ) : ℝ :=
  3 * spatialScale e *
    (2 * (50 / 201) ^ 2 / (1 - chartParameter e ^ 2) *
      boostCoefficient (cayleyC (chartParameter e)) + (1 / 101) * (301 / 402) ^ 2)

lemma force_factor (e : ℝ) (he : 1 - chartParameter e ^ 2 ≠ 0) :
    preparedForce e = e ^ 2 * regularForce e := by
  rw [preparedForce, force_factorization _ _ _ _ _ (cayley_lorentz _ he)]
  have hc : cayleyC (chartParameter e) - 1 =
      2 * chartParameter e ^ 2 / (1 - chartParameter e ^ 2) := by
    unfold cayleyC
    field_simp
    ring
  rw [hc]
  dsimp [regularForce, spatialScale, futureScale, chartParameter]
  field_simp
  ring

lemma regular_force_continuous : ContinuousAt regularForce 0 := by
  unfold regularForce spatialScale chartParameter boostCoefficient cayleyC
  fun_prop (disch := norm_num)

lemma regular_force_zero : regularForce 0 = 40501 / 53868 := by
  norm_num [regularForce, spatialScale, chartParameter, boostCoefficient, cayleyC]

lemma leading_force_limit :
    Tendsto (fun e : ℝ => preparedForce e / e ^ 2) (𝓝[≠] 0) (𝓝 (40501 / 53868)) := by
  have hp : ContinuousAt (fun e : ℝ => 1 - chartParameter e ^ 2) 0 := by
    unfold chartParameter
    fun_prop
  have hd : ∀ᶠ e in 𝓝 (0 : ℝ), 1 - chartParameter e ^ 2 ≠ 0 :=
    hp.eventually_ne (by norm_num [chartParameter])
  have he : ∀ᶠ e : ℝ in 𝓝[≠] 0, e ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with e he
    exact he
  have heq : (fun e : ℝ => preparedForce e / e ^ 2) =ᶠ[𝓝[≠] 0] regularForce := by
    filter_upwards [hd.filter_mono nhdsWithin_le_nhds, he] with e hd he
    rw [force_factor e hd]
    field_simp
  have ht : Tendsto regularForce (𝓝[≠] 0) (𝓝 (regularForce 0)) :=
    regular_force_continuous.tendsto.mono_left nhdsWithin_le_nhds
  rw [regular_force_zero] at ht
  exact ht.congr' heq.symm

end Artform.Scores.NonabelianGravity.NonlinearIsotropic
