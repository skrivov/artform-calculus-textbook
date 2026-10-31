import ArtformScores.NonabelianGravity.NonlinearCorrectionCoefficients

/-! # All16+24 native second-order parameters enter the actual ambient source -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.NonlinearAmbient
open Artform.Scores.GravityBridge.Native.Full40 NonlinearIsotropic NonlinearDifferential
open Filter Topology Asymptotics
open scoped Matrix.Norms.Elementwise
abbrev Chart := (Mat × Mat) × (Fin 4 → Biv ℝ)

noncomputable def cayleyLink (A : Biv ℝ) : Mat :=
  (1 + (1 / 2 : ℝ) • lie A) * (1 - (1 / 2 : ℝ) • lie A)⁻¹
noncomputable def nativeChart (p : Chart) : Env :=
  ((1 + p.1.1, 1 + p.1.2), fun k => cayleyLink (p.2 k))

lemma lie_zero : lie (0 : Biv ℝ) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [lie]

lemma native_chart_zero : nativeChart 0 = flat := by
  apply Prod.ext
  · simp [nativeChart, flat]
  · funext k
    simp only [nativeChart, flat, cayleyLink, Prod.snd_zero, Pi.zero_apply, lie_zero,
      smul_zero, add_zero, sub_zero, inv_one, mul_one]

lemma smooth_native_chart : ContDiffAt ℝ 1 nativeChart 0 := by
  have hN (k i j : Fin 4) : ContDiffAt ℝ 1
      (fun p : Chart => (1 - (1 / 2 : ℝ) • lie (p.2 k)) i j) 0 := by
    fin_cases i <;> fin_cases j <;> norm_num [lie] <;> fun_prop
  have hP (k i j : Fin 4) : ContDiffAt ℝ 1
      (fun p : Chart => (1 + (1 / 2 : ℝ) • lie (p.2 k)) i j) 0 := by
    fin_cases i <;> fin_cases j <;> norm_num [lie] <;> fun_prop
  have hV (k i j : Fin 4) : ContDiffAt ℝ 1
      (fun p : Chart => (1 - (1 / 2 : ℝ) • lie (p.2 k))⁻¹ i j) 0 := by
    apply smooth_inverse (hN k)
    simp only [Prod.snd_zero, Pi.zero_apply, lie_zero, smul_zero, sub_zero, Matrix.det_one]
    norm_num
  apply ContDiffAt.prodMk
  · apply ContDiffAt.prodMk <;> fun_prop
  · apply contDiffAt_pi.mpr
    intro k
    apply contDiffAt_pi.mpr
    intro i
    apply contDiffAt_pi.mpr
    intro j
    exact smooth_mat_mul (hP k) (hV k) i j

lemma chart_second_order_contact {u v : ℝ → Chart}
    (hu : Tendsto u (𝓝[≠] 0) (𝓝 0)) (hv : Tendsto v (𝓝[≠] 0) (𝓝 0))
    (hd : (fun e => u e - v e) =O[𝓝[≠] 0] (fun e => e ^ 2)) :
    (fun e => nativeChart (u e) - nativeChart (v e)) =O[𝓝[≠] 0] (fun e => e ^ 2) := by
  exact ((smooth_native_chart.hasStrictFDerivAt (by norm_num)).isBigO_sub.comp_tendsto
    (hu.prodMk_nhds hv)).trans hd

noncomputable def boostCoordinates (b : ℝ) (k : Fin 4) : Biv ℝ :=
  fun a => if k ≠ 0 ∧ a.val + 1 = k.val then b else 0

set_option maxHeartbeats 3000000 in
-- This is the full matrix Cayley map, specialized only for the reference curve.
lemma cayley_boost (t : ℝ) (ht : 1 - t ^ 2 ≠ 0) (k : Fin 4) :
    cayleyLink (boostCoordinates (2 * t) k) = link (cayleyC t) (cayleyS t) k := by
  let L := link (cayleyC t) (cayleyS t) k
  have hN : (1 - (1 / 2 : ℝ) • lie (boostCoordinates (2 * t) k)) *
      ((1 / 2 : ℝ) • (1 + L)) = 1 := by
    ext i j
    fin_cases k <;> fin_cases i <;> fin_cases j <;>
      norm_num [L, boostCoordinates, lie, link, cayleyC, cayleyS,
        Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      field_simp [ht] <;> ring
  rw [cayleyLink, Matrix.inv_eq_right_inv hN]
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [L, boostCoordinates, lie, link, cayleyC, cayleyS,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
    field_simp [ht] <;> ring

noncomputable def nativeRate (f b g e : ℝ) : Chart :=
  ((frame 1 (1 + f * e) - 1, frame 1 (1 + g * e) - 1), boostCoordinates (b * e))

lemma native_rate_binding (f b g e : ℝ) (he : 1 - (b * e / 2) ^ 2 ≠ 0) :
    nativeChart (nativeRate f b g e) = rateCurve f b g e := by
  apply Prod.ext
  · simp [nativeChart, nativeRate, rateCurve, iso, add_comm]
  · funext k
    have hb : b * e = 2 * (b * e / 2) := by ring
    change cayleyLink (boostCoordinates (b * e) k) = _
    rw [hb]
    exact cayley_boost (b * e / 2) he k

lemma native_rate_continuous (f b g : ℝ) : ContinuousAt (nativeRate f b g) 0 := by
  have hF (r : ℝ) : ContinuousAt (fun e : ℝ => frame 1 (1 + r * e) - 1) 0 := by
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    fin_cases i <;> fin_cases j <;> norm_num [frame, Matrix.diagonal] <;> fun_prop
  apply ContinuousAt.prodMk
  · exact (hF f).prodMk (hF g)
  · apply continuousAt_pi.mpr
    intro k
    apply continuousAt_pi.mpr
    intro a
    dsimp [nativeRate, boostCoordinates]
    split_ifs <;> fun_prop

lemma native_rate_zero (f b g : ℝ) : nativeRate f b g 0 = 0 := by
  apply Prod.ext
  · apply Prod.ext <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [nativeRate, frame, Matrix.diagonal, Matrix.one_apply]
  · funext k a
    simp [nativeRate, boostCoordinates]

lemma native_all_corrections_limit (f b g : ℝ) (w : Chart) :
    Tendsto (fun e : ℝ => force (nativeChart (nativeRate f b g e + e ^ 2 • w)) / e ^ 2)
      (𝓝[≠] 0) (𝓝 (3 * ((100 / 101) * b ^ 2 + (1 / 101) * (g - f) ^ 2))) := by
  have hv : Tendsto (nativeRate f b g) (𝓝[≠] 0) (𝓝 (0 : Chart)) := by
    simpa only [native_rate_zero] using
      (native_rate_continuous f b g).tendsto.mono_left nhdsWithin_le_nhds
  have hu : Tendsto (fun e : ℝ => nativeRate f b g e + e ^ 2 • w) (𝓝[≠] 0) (𝓝 (0 : Chart)) := by
    have h : ContinuousAt (fun e : ℝ => nativeRate f b g e + e ^ 2 • w) 0 :=
      (native_rate_continuous f b g).add (by fun_prop)
    simpa only [zero_pow (by decide : 2 ≠ 0), zero_smul, add_zero, native_rate_zero] using
      h.tendsto.mono_left nhdsWithin_le_nhds
  have hd : (fun e : ℝ => (nativeRate f b g e + e ^ 2 • w) - nativeRate f b g e)
      =O[𝓝[≠] 0] (fun e => e ^ 2) := by
    apply IsBigO.of_bound ‖w‖
    filter_upwards [] with e
    simp [norm_smul, mul_comm]
  have hc := chart_second_order_contact hu hv hd
  have hden : ∀ᶠ e in 𝓝 (0 : ℝ), 1 - (b * e / 2) ^ 2 ≠ 0 :=
    (show ContinuousAt (fun e : ℝ => 1 - (b * e / 2) ^ 2) 0 by fun_prop).eventually_ne
      (by norm_num)
  have hc' : (fun e : ℝ => nativeChart (nativeRate f b g e + e ^ 2 • w) - rateCurve f b g e)
      =O[𝓝[≠] 0] (fun e => e ^ 2) := by
    refine hc.congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [hden.filter_mono nhdsWithin_le_nhds] with e he
    rw [native_rate_binding f b g e he]
  apply arbitrary_correction_limit f b g _ ?_ hc'
  simpa only [native_chart_zero, Function.comp_def] using!
    smooth_native_chart.continuousAt.tendsto.comp hu

end Artform.Scores.NonabelianGravity.NonlinearAmbient
