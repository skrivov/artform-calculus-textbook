import ArtformScores.NonabelianGravity.NonlinearLocality
import ArtformScores.NonabelianGravity.NonlinearSpatialCritical

/-! # All original lapse-force product contacts, without isotropic restriction -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.NonlinearAmbient
open Artform.Scores.GravityBridge.Native.Full40 NonlinearIsotropic NonlinearDifferential
open Filter Topology
open scoped Matrix.Norms.Elementwise

lemma directional_zero_of_line {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : X → ℝ) (x v : X) (h : ∀ t : ℝ, f (x + t • v) = f x) :
    directional v f x = 0 := by
  by_cases hf : DifferentiableAt ℝ f x
  · exact partial_zero_of_line hf h
  · simp [directional, fderiv_zero_of_not_differentiableAt hf]

lemma average_temporal_directional_zero (q : Env) (r a : Fin 6) (hr : r.val < 3) :
    directional lapseDirection (fun q => average q r a) q = 0 := by
  apply directional_zero_of_line
  intro s
  exact congrFun (average_temporal_line q s r hr) a

lemma reading_directional_zero (q : Env) (r a : Fin 6) :
    directional lapseDirection (fun q => reading q r a) q = 0 := by
  apply directional_zero_of_line
  intro s
  have hu : links (q + s • lapseDirection) = links q := by
    funext t k
    simp [links, lapseDirection]
  simp only [reading, inverseLinks_lapse_line, hu]

lemma tau_flat (r : Fin 6) (i : Fin 4) : tau flat r i = 0 := by
  fin_cases r <;> fin_cases i <;>
    norm_num [tau, cellTorsionFace, frames, inverseLinks, links, flat, face,
      NonlinearIsotropic.shift, Matrix.mul_apply, Matrix.one_apply,
      Fin.sum_univ_succ]

lemma tau_flat_lapse_line (s : ℝ) (r : Fin 6) (i : Fin 4) :
    tau (flat + s • lapseDirection) r i = tau flat r i := by
  rw [tau_flat]
  fin_cases r <;> fin_cases i <;>
    norm_num [tau, cellTorsionFace, frames, inverseLinks, links, flat,
      lapseDirection, lapse, face, NonlinearIsotropic.shift, Matrix.mul_apply, Matrix.one_apply,
      Fin.sum_univ_succ]

lemma tau_flat_directional_zero (r : Fin 6) (i : Fin 4) :
    directional lapseDirection (fun q => tau q r i) flat = 0 :=
  directional_zero_of_line _ _ _ (fun s => tau_flat_lapse_line s r i)

noncomputable def curvatureForce (q : Env) : ℝ :=
  ∑ r : Fin 6, ∑ a : Fin 6, (bivSign a : ℝ) *
    directional lapseDirection (fun q => average q r a) q * reading q r a

noncomputable def torsionForce (q : Env) : ℝ :=
  (1 / 101 : ℝ) * ∑ r : Fin 6, ∑ s : Fin 6, ∑ i : Fin 4, (eta i : ℝ) *
    (directional lapseDirection (fun q => weight q r s) q * (tau q r i * tau q s i) +
      weight q r s *
        (directional lapseDirection (fun q => tau q r i) q * tau q s i +
          tau q r i * directional lapseDirection (fun q => tau q s i) q))

noncomputable def forceFormula (q : Env) : ℝ := curvatureForce q + torsionForce q

lemma curvature_force_critical : Critical curvatureForce flat := by
  unfold curvatureForce
  apply critical_sum
  intro r _
  apply critical_sum
  intro a _
  by_cases hr : r.val < 3
  · have he : (fun q : Env => (bivSign a : ℝ) *
        directional lapseDirection (fun q => average q r a) q * reading q r a) =
        fun _ => 0 := by
      funext q
      rw [average_temporal_directional_zero q r a hr, mul_zero, zero_mul]
    rw [he]
    exact ⟨rfl, hasFDerivAt_const 0 flat⟩
  · have hd : ContDiffAt ℝ 1
        (directional lapseDirection (fun q => average q r a)) flat :=
      smooth_partial (by simpa only [average] using! smooth_average (n := 2) flat flat_regular r a)
    exact critical_mul_left ((differentiableAt_const (bivSign a : ℝ)).fun_mul
      (hd.differentiableAt (by norm_num))) (reading_spatial_critical r a (by omega))

lemma torsion_force_critical : Critical torsionForce flat := by
  have hT (r : Fin 6) (i : Fin 4) : DifferentiableAt ℝ (fun q => tau q r i) flat :=
    (smooth_tau (n := 1) flat flat_regular r i).differentiableAt (by norm_num)
  have hDT (r : Fin 6) (i : Fin 4) : DifferentiableAt ℝ
      (directional lapseDirection (fun q => tau q r i)) flat :=
    (smooth_partial (n := 1) (smooth_tau (n := 2) flat flat_regular r i)).differentiableAt
      (by norm_num)
  have hW (r s : Fin 6) : DifferentiableAt ℝ (fun q => weight q r s) flat :=
    (smooth_weight (n := 1) flat flat_regular r s).differentiableAt (by norm_num)
  have hDW (r s : Fin 6) : DifferentiableAt ℝ
      (directional lapseDirection (fun q => weight q r s)) flat :=
    (smooth_partial (n := 1) (smooth_weight (n := 2) flat flat_regular r s)).differentiableAt
      (by norm_num)
  unfold torsionForce
  apply critical_mul_left (differentiableAt_const (1 / 101 : ℝ))
  apply critical_sum
  intro r _
  apply critical_sum
  intro s _
  apply critical_sum
  intro i _
  apply critical_mul_left (differentiableAt_const (eta i : ℝ))
  apply critical_add
  · exact critical_mul_left (hDW r s)
      (critical_product (hT r i) (hT s i) (tau_flat r i) (tau_flat s i))
  · apply critical_mul_left (hW r s)
    apply critical_add
    · exact critical_product (hDT r i) (hT s i) (tau_flat_directional_zero r i) (tau_flat s i)
    · exact critical_product (hT r i) (hDT s i) (tau_flat r i) (tau_flat_directional_zero s i)

lemma force_formula_critical : Critical forceFormula flat :=
  critical_add curvature_force_critical torsion_force_critical

end Artform.Scores.NonabelianGravity.NonlinearAmbient
