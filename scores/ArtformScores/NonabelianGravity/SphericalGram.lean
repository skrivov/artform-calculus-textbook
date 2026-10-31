import ArtformScores.NonabelianGravity.SphericalFixture

/-! # Corrected quaternion normal Gram: gauge and branch signs

The pair24 uses the specified face1 transport. Neither simultaneous
conjugation nor independent choices of axis signs change its determinant.
These identities do not supply a reconstruction theorem.
-/
set_option autoImplicit false
noncomputable section
namespace Artform.Scores.NonabelianGravity.Orthant.TransportGram
open Maurer

def corrected (n : Fin 4 → H) (u : Hˣ) : Matrix (Fin 4) (Fin 4) ℝ := fun i j =>
  if (i=1 ∧ j=3) ∨ (i=3 ∧ j=1) then pairing (n 1) (adjoint u (n 3))
  else pairing (n i) (n j)
lemma corrected_gauge (h u : Hˣ) (n : Fin 4 → H) :
    corrected (fun i => adjoint h (n i)) (h*u*h⁻¹)=corrected n u := by
  have he : ∀ x, adjoint (h*u*h⁻¹) (adjoint h x)=adjoint h (adjoint u x) := by
    intro x
    simp [adjoint,mul_assoc]
  funext i j
  simp only [corrected,he,pairing_adjoint]

def sign (b : Bool) : ℤ := if b then -1 else 1
lemma sign_square (b : Bool) : (sign b : ℝ)*(sign b : ℝ)=1 := by
  cases b <;> norm_num [sign]
def signed (b : Fin 4 → Bool) (n : Fin 4 → H) : Fin 4 → H := fun i => sign (b i) • n i
lemma corrected_sign (b : Fin 4 → Bool) (n : Fin 4 → H) (u : Hˣ) :
    corrected (signed b n) u=
      Matrix.diagonal (fun i => (sign (b i):ℝ))*corrected n u*
        Matrix.diagonal (fun i => (sign (b i):ℝ)) := by
  funext i j
  simp only [corrected,signed,adjoint_zsmul,pairing_zsmul_left,pairing_zsmul_right]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal_mul,Matrix.mul_diagonal,corrected] <;> ring
lemma corrected_sign_det (b : Fin 4 → Bool) (n : Fin 4 → H) (u : Hˣ) :
    (corrected (signed b n) u).det=(corrected n u).det := by
  let D : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal (fun i => (sign (b i):ℝ))
  have hd : D.det*D.det=1 := by
    simp only [D,Matrix.det_diagonal,← Finset.prod_mul_distrib,sign_square,Finset.prod_const_one]
  rw [corrected_sign,Matrix.det_mul,Matrix.det_mul]
  change D.det*(corrected n u).det*D.det=(corrected n u).det
  calc
    _ = (D.det*D.det)*(corrected n u).det := by ring
    _ = _ := by rw [hd,one_mul]

/-! ## Non-vacuity -/
example (n : Fin 4 → H) (u : Hˣ) : corrected (signed (fun _ => false) n) u=corrected n u := by
  have he : signed (fun _ => false) n=n := by
    funext i
    simp [signed,sign]
  rw [he]
end Artform.Scores.NonabelianGravity.Orthant.TransportGram
