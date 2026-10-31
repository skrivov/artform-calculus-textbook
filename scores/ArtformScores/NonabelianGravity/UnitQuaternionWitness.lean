import ArtformScores.NonabelianGravity.QuaternionForm

/-! # A nonzero tangent in the actual unit-quaternion domain

The Cayley curve has unit norm at every real parameter and derivative `2i`
at zero. No identification of an arbitrary group with a physical gauge group
is used. Unit quaternions supply the concrete compact SU(2) model here.
-/
set_option autoImplicit false
noncomputable section
namespace Artform.Scores.NonabelianGravity.Maurer

def cayley (t : ℝ) : H := (1+t • imaginaryI)*(1-t • imaginaryI)⁻¹
lemma cayley_denominator (t : ℝ) : (1-t • imaginaryI : H) ≠ 0 := by
  intro he
  have hr := congrArg (fun q : H => q.re) he
  norm_num [imaginaryI] at hr
lemma cayley_norm (t : ℝ) : Quaternion.normSq (cayley t)=1 := by
  have hn : Quaternion.normSq (1-t • imaginaryI : H) ≠ 0 :=
    Quaternion.normSq_ne_zero.mpr (cayley_denominator t)
  have he : Quaternion.normSq (1+t • imaginaryI : H)=
      Quaternion.normSq (1-t • imaginaryI : H) := by
    simp [Quaternion.normSq_def',imaginaryI]
  rw [cayley,map_mul,Quaternion.normSq_inv,he,mul_inv_cancel₀ hn]
lemma cayley_zero : cayley 0=1 := by simp [cayley]
lemma cayley_derivative : HasDerivAt cayley (2 • imaginaryI) 0 := by
  have hp : HasDerivAt (fun t : ℝ => 1+t • imaginaryI) imaginaryI 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const imaginaryI).const_add 1
  have hm : HasDerivAt (fun t : ℝ => 1-t • imaginaryI) (-imaginaryI) 0 := by
    convert (hasDerivAt_const (0:ℝ) (1:H)).sub
      ((hasDerivAt_id (0:ℝ)).smul_const imaginaryI) using 1
    · rfl
    · simp
  have hi := (hasFDerivAt_inv' (𝕜:=ℝ) (cayley_denominator 0)).comp_hasDerivAt 0 hm
  have hi' : HasDerivAt (fun t : ℝ => (1-t • imaginaryI)⁻¹) imaginaryI 0 := by
    convert hi using 1
    · rfl
    · simp
  convert hp.mul hi' using 1
  · rfl
  · simp [two_smul]

/-! ## Non-vacuity -/
example : Quaternion.normSq (cayley 0)=1 ∧ (2 • imaginaryI : H) ≠ 0 := by
  refine ⟨cayley_norm 0,?_⟩
  intro he
  have hi := congrArg (fun q : H => q.imI) he
  norm_num [imaginaryI] at hi
end Artform.Scores.NonabelianGravity.Maurer
