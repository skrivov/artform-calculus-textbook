import ArtformScores.NonabelianGravity.NonlinearIsotropicCurvature
import ArtformScores.NonabelianGravity.NonlinearIsotropicIncoming
import ArtformScores.NonabelianGravity.NonlinearIsotropicTorsion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! # Exact two-cell native lapse action and its real first variation -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.NonlinearIsotropic
variable {K : Type*} [Field K] [CharZero K]

def totalAction (κ C S ell a c : K) : K :=
  incomingCurvature C S ell a + incomingTorsion κ C S ell a +
    curvature C S ell a c + torsion κ C S ell a c

lemma action_difference (κ C S ell a c : K) (he : ell ≠ 0) (ha : a ≠ 0)
    (h : C ^ 2 - S ^ 2 = 1) :
    totalAction κ C S ell a c - totalAction κ C S 1 a c =
      (ell - 1) * a * closedLapse C S - 3 * κ * a *
        ((c - a) ^ 2 / ell - (c - a) ^ 2 + 2 * (ell - 1) * (C - 1)) := by
  simp only [totalAction, incoming_curvature_independent C S ell,
    incoming_torsion_independent κ C S ell, torsion_closed κ C S ell a c he ha h,
    torsion_closed κ C S 1 a c one_ne_zero ha h, div_one, mul_one]
  have hc := curvature_closed_difference C S ell a c h
  linear_combination hc

def lapseForce (κ C S a c : K) : K :=
  a * closedLapse C S + 3 * κ * a * ((c - a) ^ 2 - 2 * (C - 1))

def lapseForceAt (κ C S ell a c : K) : K :=
  a * closedLapse C S + 3 * κ * a * ((c - a) ^ 2 / ell ^ 2 - 2 * (C - 1))

lemma lapse_derivative_at (κ C S ell₀ a c : ℝ) (he₀ : ell₀ ≠ 0)
    (ha : a ≠ 0) (h : C ^ 2 - S ^ 2 = 1) :
    HasDerivAt (fun ell => totalAction κ C S ell a c)
      (lapseForceAt κ C S ell₀ a c) ell₀ := by
  let model := fun ell : ℝ => totalAction κ C S 1 a c + (ell - 1) * (a * closedLapse C S) -
    3 * κ * a * ((c - a) ^ 2 / ell - (c - a) ^ 2 + 2 * (ell - 1) * (C - 1))
  have hi := hasDerivAt_id ell₀
  have h₁ := (hi.sub_const 1).mul_const (a * closedLapse C S)
  have h₂ := (((hasDerivAt_const ell₀ ((c - a) ^ 2)).div hi he₀).sub_const
    ((c - a) ^ 2)).add (((hi.sub_const 1).const_mul 2).mul_const (C - 1))
  have hm : HasDerivAt model (lapseForceAt κ C S ell₀ a c) ell₀ := by
    convert ((hasDerivAt_const ell₀ (totalAction κ C S 1 a c)).add h₁).sub
      (h₂.const_mul (3 * κ * a)) using 1 <;> (try funext ell) <;> simp [model, lapseForceAt]
    ring
  apply hm.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds he₀] with ell he
  have hd := action_difference κ C S ell a c he ha h
  dsimp [model]
  linear_combination hd

lemma lapse_derivative (κ C S a c : ℝ) (ha : a ≠ 0) (h : C ^ 2 - S ^ 2 = 1) :
    HasDerivAt (fun ell => totalAction κ C S ell a c) (lapseForce κ C S a c) 1 := by
  simpa only [lapseForceAt, lapseForce, one_pow, div_one] using
    lapse_derivative_at κ C S 1 a c one_ne_zero ha h

end Artform.Scores.NonabelianGravity.NonlinearIsotropic
