import ArtformScores.NonabelianGravity.NonlinearActionSmooth

/-! # The critical formula is the derivative of the original action -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.NonlinearAmbient
open Artform.Scores.GravityBridge.Native.Full40 NonlinearIsotropic NonlinearDifferential
open Filter Topology
open scoped Matrix.Norms.Elementwise

lemma directional_add {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f g : X → ℝ} {x v : X}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    directional v (fun q => f q + g q) x = directional v f x + directional v g x := by
  exact (directional_hasDerivAt (v := v) (hf.fun_add hg)).unique
    ((directional_hasDerivAt (v := v) hf).add (directional_hasDerivAt (v := v) hg))

lemma directional_sum {X α : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [Fintype α] {f : α → X → ℝ} {x v : X}
    (hf : ∀ a, DifferentiableAt ℝ (f a) x) :
    directional v (fun q => ∑ a, f a q) x = ∑ a, directional v (f a) x := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ)
    (fun a _ => directional_hasDerivAt (v := v) (hf a))
  exact (directional_hasDerivAt (v := v)
    (DifferentiableAt.fun_sum (fun a _ => hf a))).unique hd

lemma directional_const_mul {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : X → ℝ} {x v : X} (c : ℝ) (hf : DifferentiableAt ℝ f x) :
    directional v (fun q => c * f q) x = c * directional v f x := by
  have h := partial_mul (v := v) (differentiableAt_const c) hf
  simpa [directional] using! h

lemma curvature_force_binding (q : Env) (hq : Regular q) :
    directional lapseDirection localCurvature q = curvatureForce q := by
  have ha (r a : Fin 6) : DifferentiableAt ℝ (fun q => average q r a) q :=
    (smooth_average (n := 1) q hq r a).differentiableAt (by norm_num)
  have hr (r a : Fin 6) : DifferentiableAt ℝ (fun q => reading q r a) q :=
    (smooth_reading (n := 1) q hq r a).differentiableAt (by norm_num)
  change directional lapseDirection
    (fun q => ∑ r : Fin 6, ∑ a : Fin 6, (bivSign a : ℝ) * average q r a * reading q r a) q = _
  rw [directional_sum (fun r => DifferentiableAt.fun_sum
    (fun a _ => ((differentiableAt_const _).fun_mul (ha r a)).fun_mul (hr r a)))]
  apply Finset.sum_congr rfl
  intro r _
  rw [directional_sum (fun a => ((differentiableAt_const _).fun_mul (ha r a)).fun_mul (hr r a))]
  apply Finset.sum_congr rfl
  intro a _
  rw [partial_mul ((differentiableAt_const _).fun_mul (ha r a)) (hr r a),
    directional_const_mul _ (ha r a), reading_directional_zero]
  ring

lemma torsion_force_binding (q : Env) (hq : Regular q) :
    directional lapseDirection localTorsion q = torsionForce q := by
  have ht (r : Fin 6) (i : Fin 4) : DifferentiableAt ℝ (fun q => tau q r i) q :=
    (smooth_tau (n := 1) q hq r i).differentiableAt (by norm_num)
  have hw (r s : Fin 6) : DifferentiableAt ℝ (fun q => weight q r s) q :=
    (smooth_weight (n := 1) q hq r s).differentiableAt (by norm_num)
  have he : localTorsion = fun q => (1 / 101 : ℝ) *
      ∑ r : Fin 6, ∑ s : Fin 6, ∑ i : Fin 4,
        (eta i : ℝ) * (weight q r s * (tau q r i * tau q s i)) := by
    funext q
    simp only [localTorsion, etaPair, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, directional_const_mul]
  · unfold torsionForce
    congr 1
    rw [directional_sum]
    · apply Finset.sum_congr rfl
      intro r _
      rw [directional_sum]
      · apply Finset.sum_congr rfl
        intro s _
        rw [directional_sum]
        · apply Finset.sum_congr rfl
          intro i _
          rw [directional_const_mul, partial_mul (hw r s) ((ht r i).fun_mul (ht s i)),
            partial_mul (ht r i) (ht s i)]
          exact (hw r s).fun_mul ((ht r i).fun_mul (ht s i))
        · intro i
          exact (differentiableAt_const _).fun_mul ((hw r s).fun_mul ((ht r i).fun_mul (ht s i)))
      · intro s
        exact DifferentiableAt.fun_sum (fun i _ => (differentiableAt_const _).fun_mul
          ((hw r s).fun_mul ((ht r i).fun_mul (ht s i))))
    · intro r
      exact DifferentiableAt.fun_sum (fun s _ => DifferentiableAt.fun_sum
        (fun i _ => (differentiableAt_const _).fun_mul
          ((hw r s).fun_mul ((ht r i).fun_mul (ht s i)))))
  · exact DifferentiableAt.fun_sum (fun r _ => DifferentiableAt.fun_sum
      (fun s _ => DifferentiableAt.fun_sum (fun i _ => (differentiableAt_const _).fun_mul
        ((hw r s).fun_mul ((ht r i).fun_mul (ht s i))))))

lemma force_binding (q : Env) (hq : Regular q) : force q = forceFormula q := by
  have hs := (smooth_action (n := 1) q hq).differentiableAt (by norm_num)
  -- Use the derivative along the actual lapse line, retaining both incident cells.
  have hline : (fun s : ℝ => action (q + s • lapseDirection)) = fun s =>
      precedingCurvature q + precedingTorsion q +
        localCurvature (q + s • lapseDirection) + localTorsion (q + s • lapseDirection) := by
    funext s
    simp only [action, preceding_curvature_lapse_line, preceding_torsion_lapse_line]
  have hc : DifferentiableAt ℝ localCurvature q := by
    unfold localCurvature
    exact DifferentiableAt.fun_sum (fun r _ => (smooth_cell_curvature (n := 1)
      (smooth_frames q) (smooth_links q) (smooth_inverse_links q hq) r).differentiableAt
        (by norm_num))
  have ht : DifferentiableAt ℝ localTorsion q := by
    have hw := smooth_weight (n := 1) q hq
    have hT := smooth_tau (n := 1) q hq
    have h : ContDiffAt ℝ 1 localTorsion q := by unfold localTorsion etaPair; fun_prop
    exact h.differentiableAt (by norm_num)
  have h := directional_hasDerivAt (v := lapseDirection) hs
  rw [hline] at h
  have hh := ((directional_hasDerivAt (v := lapseDirection) hc).const_add
    (precedingCurvature q + precedingTorsion q)).add
      (directional_hasDerivAt (v := lapseDirection) ht)
  have he := h.unique hh
  change force q = _ at he
  rw [curvature_force_binding q hq, torsion_force_binding q hq] at he
  exact he

end Artform.Scores.NonabelianGravity.NonlinearAmbient
