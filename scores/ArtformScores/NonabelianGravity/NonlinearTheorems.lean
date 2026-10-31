import ArtformScores.NonabelianGravity.NonlinearStatements

/-! # Exact nonlinear source theorem registration and nonvacuity -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity
open NonlinearIsotropic

@[ledger "NGB:native-isotropic-lapse-constraint"]
theorem nativeIsotropicLapseConstraint : Statement.nativeIsotropicLapseConstraint := by
  exact ⟨frame_det, frame_inverse, metric_native,
    fun C S h k => ⟨link_inverse C S h k, link_lorentz C S h k, link_det C S h k⟩,
    action_difference, lapse_derivative_at, zero_force_iff, prepared_linear_match,
    prepared_frame_tangent, prepared_future_tangent, prepared_link_tangent,
    leading_force_limit, explicit_nonlinear_rejected⟩

example : (40501 / 53868 : ℝ) > 0 := by norm_num

example : preparedMiddle 22 ≠ 0 := by norm_num [preparedMiddle]

example : deriv (fun (N : ℝ) => totalAction (1 / 101) (161605 / 161603) (-804 / 161603)
    N (40301 / 40200) (101 / 100)) 1 ≠ 0 := explicit_nonlinear_rejected 1 one_ne_zero

end Artform.Scores.NonabelianGravity
