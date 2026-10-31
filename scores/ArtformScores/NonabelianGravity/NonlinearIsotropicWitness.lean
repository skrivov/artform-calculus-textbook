import ArtformScores.NonabelianGravity.NonlinearIsotropicConstraint
import ArtformScores.NonabelianGravity.NonlinearIsotropicLinks
import ArtformScores.NonabelianGravity.LegendreGluing

/-! # A complete linearized history and its explicit nonlinear isotropic test -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.NonlinearIsotropic
open Legendre

def preparedFinal : Point ℚ := fun i => if i = 5 ∨ i = 10 ∨ i = 15 then 1 else 0

def preparedMiddle : Point ℚ := fun i =>
  if i = 5 ∨ i = 10 ∨ i = 15 then 101 / 402
  else if i = 22 ∨ i = 29 ∨ i = 36 then -100 / 201 else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Every40-component original affine momentum equation, with both cells retained.
lemma prepared_linear_match : post 0 preparedMiddle - pre preparedMiddle preparedFinal = 0 := by
  rw [matching_iff]
  decide +kernel

noncomputable def cayleyC (t : ℝ) : ℝ := (1 + t ^ 2) / (1 - t ^ 2)
noncomputable def cayleyS (t : ℝ) : ℝ := 2 * t / (1 - t ^ 2)

lemma cayley_lorentz (t : ℝ) (ht : 1 - t ^ 2 ≠ 0) :
    cayleyC t ^ 2 - cayleyS t ^ 2 = 1 := by
  dsimp [cayleyC, cayleyS]
  field_simp
  ring

lemma cayleyC_derivative : HasDerivAt cayleyC 0 0 := by
  have hs := (hasDerivAt_id (0 : ℝ)).pow 2
  have hc := hasDerivAt_const (0 : ℝ) (1 : ℝ)
  convert (hc.add hs).div (hc.sub hs) (by norm_num) using 1 <;>
    (try funext t) <;> norm_num [cayleyC]

lemma cayleyS_derivative : HasDerivAt cayleyS 2 0 := by
  have hi := hasDerivAt_id (0 : ℝ)
  have hd := (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (hi.pow 2)
  convert (hi.const_mul 2).div hd (by norm_num) using 1 <;>
    (try funext t) <;> norm_num [cayleyS]

lemma prepared_boost_tangent :
    HasDerivAt (fun e : ℝ => cayleyS ((-50 / 201) * e)) (-100 / 201) 0 := by
  have hi := (hasDerivAt_id (0 : ℝ)).const_mul (-50 / 201)
  have ho : HasDerivAt cayleyS 2 ((-50 / 201) * id (0 : ℝ)) := by
    simpa using cayleyS_derivative
  convert ho.comp 0 hi using 1 <;> (try funext e) <;> norm_num [Function.comp_def, neg_mul]

lemma prepared_frame_tangent (i j : Fin 4) :
    HasDerivAt (fun e : ℝ => frame 1 (1 + (101 / 402) * e) i j)
      ((fieldPoint preparedMiddle).1 i j : ℝ) 0 := by
  have hs : HasDerivAt (fun e : ℝ => 1 + (101 / 402) * e) (101 / 402) 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).const_mul (101 / 402)).const_add 1 using 1 <;>
      norm_num [add_comm]
  fin_cases i <;> fin_cases j <;>
    norm_num [frame, Matrix.diagonal, fieldPoint, frameSlot, preparedMiddle] <;>
    first | simpa using hs | exact hasDerivAt_const (0 : ℝ) (0 : ℝ) |
      exact hasDerivAt_const (0 : ℝ) (1 : ℝ)

lemma prepared_future_tangent (i j : Fin 4) :
    HasDerivAt (fun e : ℝ => frame 1 (1 + e) i j)
      ((fieldPoint preparedFinal).1 i j : ℝ) 0 := by
  have hs : HasDerivAt (fun e : ℝ => 1 + e) 1 0 := by
    simpa [add_comm] using (hasDerivAt_id (0 : ℝ)).const_add 1
  fin_cases i <;> fin_cases j <;>
    norm_num [frame, Matrix.diagonal, fieldPoint, frameSlot, preparedFinal] <;>
    first | simpa using hs | exact hasDerivAt_const (0 : ℝ) (0 : ℝ) |
      exact hasDerivAt_const (0 : ℝ) (1 : ℝ)

lemma prepared_link_tangent (k i j : Fin 4) :
    HasDerivAt (fun e : ℝ =>
      link (cayleyC ((-50 / 201) * e)) (cayleyS ((-50 / 201) * e)) k i j)
      ((Artform.Scores.GravityBridge.Native.Full40.lie
        ((fieldPoint preparedMiddle).2 k)) i j : ℝ) 0 := by
  have hi := (hasDerivAt_id (0 : ℝ)).const_mul (-50 / 201)
  have ho : HasDerivAt cayleyC 0 ((-50 / 201) * id (0 : ℝ)) := by
    simpa using cayleyC_derivative
  have hc : HasDerivAt (fun e : ℝ => cayleyC ((-50 / 201) * e)) 0 0 := by
    convert ho.comp 0 hi using 1 <;> (try funext e) <;> norm_num [Function.comp_def, neg_mul]
  have hs := prepared_boost_tangent
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [link, fieldPoint, connectionSlot, preparedMiddle,
      Artform.Scores.GravityBridge.Native.Full40.lie] <;>
    first
    | simpa only [neg_div, neg_mul] using hc
    | simpa only [neg_div, neg_mul] using hs
    | exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
    | exact hasDerivAt_const (0 : ℝ) (1 : ℝ)

lemma explicit_curve_values :
    cayleyC ((-50 / 201) * (1 / 100)) = 161605 / 161603 ∧
    cayleyS ((-50 / 201) * (1 / 100)) = -804 / 161603 := by
  norm_num [cayleyC, cayleyS]

lemma explicit_nonlinear_rejected (ell : ℝ) (he : ell ≠ 0) :
    deriv (fun N => totalAction (1 / 101) (161605 / 161603) (-804 / 161603)
      N (40301 / 40200) (101 / 100)) ell ≠ 0 := by
  apply lapse_derivative_nonzero _ _ _ _ _ he <;> norm_num

lemma explicit_links_legal (k : Fin 4) :
    link (161605 / 161603 : ℝ) (804 / 161603) k *
      link (161605 / 161603) (-804 / 161603) k = 1 ∧
    (link (161605 / 161603 : ℝ) (-804 / 161603) k).transpose *
      Matrix.diagonal (fun i => (Artform.Scores.GravityBridge.Native.Full40.eta i : ℝ)) *
      link (161605 / 161603) (-804 / 161603) k =
      Matrix.diagonal (fun i => (Artform.Scores.GravityBridge.Native.Full40.eta i : ℝ)) ∧
    (link (161605 / 161603 : ℝ) (-804 / 161603) k).det = 1 := by
  have h : (161605 / 161603 : ℝ) ^ 2 - (-804 / 161603) ^ 2 = 1 := by norm_num
  constructor
  · simpa only [neg_div, neg_neg] using link_inverse _ _ h k
  · exact ⟨link_lorentz _ _ h k, link_det _ _ h k⟩

end Artform.Scores.NonabelianGravity.NonlinearIsotropic
