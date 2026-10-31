import ArtformScores.NonabelianGravity.NonlinearIsoBinding
import ArtformScores.NonabelianGravity.NonlinearRateLimit
import ArtformScores.NonabelianGravity.NonlinearContact

/-! # Complete criticality and analytic obstruction under arbitrary ambient corrections -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.NonlinearAmbient
open Artform.Scores.GravityBridge.Native.Full40 NonlinearIsotropic NonlinearDifferential
open Filter Topology Asymptotics
open scoped Matrix.Norms.Elementwise

lemma eventually_regular : ∀ᶠ q : Env in 𝓝 flat, Regular q := by
  have hE : ContinuousAt (fun q : Env => q.1.1.det) flat :=
    (smooth_det (n := 1) (fun i j => by fun_prop)).continuousAt
  have hU (k : Fin 4) : ContinuousAt (fun q : Env => (q.2 k).det) flat :=
    (smooth_det (n := 1) (fun i j => by fun_prop)).continuousAt
  have hE' : ∀ᶠ q : Env in 𝓝 flat, q.1.1.det ≠ 0 :=
    hE.eventually_ne (by simp [flat])
  have hU' : ∀ᶠ q : Env in 𝓝 flat, ∀ k, (q.2 k).det ≠ 0 :=
    Filter.eventually_all.mpr (fun k => (hU k).eventually_ne (by simp [flat]))
  filter_upwards [hE', hU'] with q he hu
  exact ⟨he, hu⟩

lemma force_strict_critical : HasStrictFDerivAt force (0 : Env →L[ℝ] ℝ) flat := by
  have hf := (smooth_force_formula flat flat_regular).hasStrictFDerivAt'
    force_formula_critical.2 (by norm_num)
  apply hf.congr_of_eventuallyEq
  filter_upwards [eventually_regular] with q hq
  exact (force_binding q hq).symm

noncomputable def rateCurve (f b g e : ℝ) : Env :=
  iso (cayleyC (b * e / 2)) (cayleyS (b * e / 2)) 1 (1 + f * e) (1 + g * e)

lemma rate_curve_continuous (f b g : ℝ) : ContinuousAt (rateCurve f b g) 0 := by
  have hframe (r : ℝ) : ContinuousAt (fun e : ℝ => frame 1 (1 + r * e)) 0 := by
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    fin_cases i <;> fin_cases j <;> norm_num [frame, Matrix.diagonal] <;> fun_prop
  apply ContinuousAt.prodMk
  · exact (hframe f).prodMk (hframe g)
  · apply continuousAt_pi.mpr
    intro k
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    dsimp [rateCurve, iso, link]
    split_ifs <;> (try dsimp only [cayleyC, cayleyS]) <;> fun_prop (disch := norm_num)

lemma rate_curve_zero (f b g : ℝ) : rateCurve f b g 0 = flat := by
  apply Prod.ext
  · apply Prod.ext <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [rateCurve, iso, flat, frame, Matrix.diagonal, Matrix.one_apply]
  · funext k i j
    fin_cases k <;> fin_cases i <;> fin_cases j <;>
      norm_num [rateCurve, iso, flat, link, cayleyC, cayleyS, Matrix.one_apply]

lemma ambient_rate_force_limit (f b g : ℝ) :
    Tendsto (fun e : ℝ => force (rateCurve f b g e) / e ^ 2) (𝓝[≠] 0)
      (𝓝 (3 * ((100 / 101) * b ^ 2 + (1 / 101) * (g - f) ^ 2))) := by
  have hd : ∀ᶠ e in 𝓝 (0 : ℝ), 1 - (b * e / 2) ^ 2 ≠ 0 :=
    (show ContinuousAt (fun e : ℝ => 1 - (b * e / 2) ^ 2) 0 by fun_prop).eventually_ne
      (by norm_num)
  have ha : ∀ᶠ e in 𝓝 (0 : ℝ), 1 + f * e ≠ 0 :=
    (show ContinuousAt (fun e : ℝ => 1 + f * e) 0 by fun_prop).eventually_ne (by norm_num)
  apply (rate_force_limit f b g).congr'
  filter_upwards [hd.filter_mono nhdsWithin_le_nhds, ha.filter_mono nhdsWithin_le_nhds]
    with e hd ha
  rw [rateCurve, force_iso _ _ _ _ _ one_ne_zero ha (cayley_lorentz _ hd)]
  rfl

lemma arbitrary_correction_limit (f b g : ℝ) (u : ℝ → Env)
    (hu : Tendsto u (𝓝[≠] 0) (𝓝 flat))
    (hcorrection : (fun e => u e - rateCurve f b g e) =O[𝓝[≠] 0] (fun e => e ^ 2)) :
    Tendsto (fun e : ℝ => force (u e) / e ^ 2) (𝓝[≠] 0)
      (𝓝 (3 * ((100 / 101) * b ^ 2 + (1 / 101) * (g - f) ^ 2))) := by
  have hv : Tendsto (rateCurve f b g) (𝓝[≠] 0) (𝓝 flat) := by
    simpa only [rate_curve_zero] using
      (rate_curve_continuous f b g).tendsto.mono_left nhdsWithin_le_nhds
  exact second_order_limit force_strict_critical hu hv hcorrection
    (ambient_rate_force_limit f b g)

lemma prepared_arbitrary_correction_limit (u : ℝ → Env)
    (hu : Tendsto u (𝓝[≠] 0) (𝓝 flat))
    (hc : (fun e => u e - rateCurve (101 / 402) (-100 / 201) 1 e) =O[𝓝[≠] 0]
      (fun e => e ^ 2)) :
    Tendsto (fun e : ℝ => force (u e) / e ^ 2) (𝓝[≠] 0) (𝓝 (40501 / 53868)) := by
  convert arbitrary_correction_limit (101 / 402) (-100 / 201) 1 u hu hc using 1
  norm_num

end Artform.Scores.NonabelianGravity.NonlinearAmbient
