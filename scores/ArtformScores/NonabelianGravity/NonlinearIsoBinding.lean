import ArtformScores.NonabelianGravity.NonlinearForceBinding

/-! # Bind the open ambient source to the original exact boost reference -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.NonlinearAmbient
open Artform.Scores.GravityBridge.Native.Full40 NonlinearIsotropic NonlinearDifferential
open Filter Topology
open scoped Matrix.Norms.Elementwise

noncomputable def iso (C S ell a c : ℝ) : Env :=
  ((frame ell a, frame 1 c), link C S)

lemma iso_frames (C S ell a c : ℝ) : frames (iso C S ell a c) = atFrame ell a c := rfl
lemma iso_links (C S ell a c : ℝ) : links (iso C S ell a c) = atLink C S := rfl
lemma iso_inverse (C S ell a c : ℝ) (h : C ^ 2 - S ^ 2 = 1) :
    inverseLinks (iso C S ell a c) = atLink C (-S) := by
  funext t k
  by_cases ht : t = 0
  · simp only [inverseLinks, links, ht, ite_true, iso, atLink]
    exact Matrix.inv_eq_left_inv (link_inverse C S h k)
  · simp [inverseLinks, links, ht, atLink]

lemma iso_metric (ell a : ℝ) (he : ell ≠ 0) (ha : a ≠ 0) :
    metric (frame ell a) = inverseMetric ell a := by
  have hi : (frame ell a)⁻¹ = frame ell⁻¹ a⁻¹ :=
    Matrix.inv_eq_right_inv (frame_inverse ell a he ha)
  rw [metric, hi, ← metric_native]

lemma iso_curvature (C S ell a c : ℝ) (h : C ^ 2 - S ^ 2 = 1) :
    localCurvature (iso C S ell a c) = curvature C S ell a c := by
  simp only [localCurvature, iso_frames, iso_links, iso_inverse _ _ _ _ _ h,
    curvature, ← middle_constructor]

lemma iso_torsion (C S ell a c : ℝ) (he : ell ≠ 0) (ha : a ≠ 0)
    (h : C ^ 2 - S ^ 2 = 1) :
    localTorsion (iso C S ell a c) = torsion (1 / 101) C S ell a c := by
  have hw (r s : Fin 6) : weight (iso C S ell a c) r s =
      (ell * a ^ 3) * (inverseMetric ell a (face r).1 (face s).1 *
        inverseMetric ell a (face r).2 (face s).2 -
        inverseMetric ell a (face r).1 (face s).2 * inverseMetric ell a (face r).2 (face s).1) := by
    simp only [weight, iso, frame_det, iso_metric ell a he ha]
  simp only [localTorsion, hw, tau, iso_frames, iso_inverse _ _ _ _ _ h,
    ← middle_torsion_constructor, NonlinearIsotropic.torsion]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  ring

lemma iso_regular (C S ell a c : ℝ) (he : ell ≠ 0) (ha : a ≠ 0)
    (h : C ^ 2 - S ^ 2 = 1) : Regular (iso C S ell a c) := by
  refine ⟨?_, ?_⟩
  · simp only [iso, frame_det]
    exact mul_ne_zero he (pow_ne_zero 3 ha)
  · intro k
    simp only [iso, link_det C S h k]
    norm_num

lemma iso_lapse_line (C S ell a c s : ℝ) :
    iso C S ell a c + s • lapseDirection = iso C S (ell + s) a c := by
  apply Prod.ext
  · apply Prod.ext
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [iso, frame, lapseDirection, lapse, Matrix.diagonal, add_comm]
    · simp [iso, lapseDirection]
  · simp [iso, lapseDirection]

lemma force_iso (C S ell a c : ℝ) (he : ell ≠ 0) (ha : a ≠ 0)
    (h : C ^ 2 - S ^ 2 = 1) :
    force (iso C S ell a c) = lapseForceAt (1 / 101) C S ell a c := by
  have hq := iso_regular C S ell a c he ha h
  have hd := directional_hasDerivAt (v := lapseDirection)
    ((smooth_action (n := 1) _ hq).differentiableAt (by norm_num))
  have ha0 : ∀ᶠ s in 𝓝 (0 : ℝ), ell + s ≠ 0 :=
    (continuousAt_const.add continuousAt_id).eventually_ne (by simpa using he)
  let K := precedingCurvature (iso C S ell a c) + precedingTorsion (iso C S ell a c) -
    incomingCurvature C S 1 a - incomingTorsion (1 / 101) C S 1 a
  have heq : (fun s : ℝ => action (iso C S ell a c + s • lapseDirection)) =ᶠ[𝓝 0]
      fun s => K + totalAction (1 / 101) C S (ell + s) a c := by
    filter_upwards [ha0] with s hs
    simp only [action]
    rw [preceding_curvature_lapse_line, preceding_torsion_lapse_line]
    simp only [iso_lapse_line, iso_curvature _ _ _ _ _ h, iso_torsion _ _ _ _ _ hs ha h,
      totalAction, incoming_curvature_independent C S (ell + s),
      incoming_torsion_independent (1 / 101) C S (ell + s)]
    dsimp [K]
    ring
  have hl : HasDerivAt (fun s : ℝ => ell + s) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add ell
  have ho : HasDerivAt (fun x => totalAction (1 / 101) C S x a c)
      (lapseForceAt (1 / 101) C S ell a c) (ell + (0 : ℝ)) := by
    simpa using lapse_derivative_at (1 / 101) C S ell a c he ha h
  have hh := (ho.comp 0 hl).const_add K
  have hh' : HasDerivAt (fun s : ℝ => K + totalAction (1 / 101) C S (ell + s) a c)
      (lapseForceAt (1 / 101) C S ell a c) 0 := by simpa using! hh
  exact hd.unique (hh'.congr_of_eventuallyEq heq)

end Artform.Scores.NonabelianGravity.NonlinearAmbient
