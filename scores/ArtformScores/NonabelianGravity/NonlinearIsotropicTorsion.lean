import ArtformScores.NonabelianGravity.NonlinearIsotropicSource

/-! # Original determinant and both inverse metric factors in the isotropic cell -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.NonlinearIsotropic
open Artform.Scores.GravityBridge.Native.Full40
variable {K : Type*} [Field K]

def torsionFace (C S ell a c : K) (f : Fin 6) : Vec K :=
  let k := (face f).1
  let l := (face f).2
  fun i => (link C (-S) k * atFrame ell a c (shift k)) i l - frame ell a i l -
    (link C (-S) l * atFrame ell a c (shift l)) i k + frame ell a i k

def inverseMetric (ell a : K) : Frame K :=
  Matrix.diagonal ![-1 / ell ^ 2, 1 / a ^ 2, 1 / a ^ 2, 1 / a ^ 2]

def torsion (κ C S ell a c : K) : K :=
  κ * (ell * a ^ 3) * ∑ r : Fin 6, ∑ s : Fin 6,
    (inverseMetric ell a (face r).1 (face s).1 *
      inverseMetric ell a (face r).2 (face s).2 -
     inverseMetric ell a (face r).1 (face s).2 *
      inverseMetric ell a (face r).2 (face s).1) *
    etaPair (torsionFace C S ell a c r) (torsionFace C S ell a c s)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
-- Every pair of original forward torsions and both full inverse metric factors.
lemma torsion_raw (κ C S ell a c : K) (he : ell ≠ 0) (ha : a ≠ 0) :
    torsion κ C S ell a c =
      -3 * κ * a / ell * (-(ell * (1 - C)) ^ 2 + (c - a + ell * S) ^ 2) := by
  norm_num [torsion, inverseMetric, torsionFace, frame, atFrame, link, shift,
    face, etaPair, eta, Matrix.mul_apply, Matrix.diagonal, Fin.sum_univ_succ]
  field_simp
  ring

lemma torsion_closed (κ C S ell a c : K) (he : ell ≠ 0) (ha : a ≠ 0)
    (h : C ^ 2 - S ^ 2 = 1) :
    torsion κ C S ell a c = -3 * κ * a *
      ((c - a) ^ 2 / ell + 2 * (c - a) * S + 2 * ell * (C - 1)) := by
  rw [torsion_raw κ C S ell a c he ha]
  have hs : S ^ 2 - (1 - C) ^ 2 = 2 * (C - 1) := by linear_combination -h
  calc
    _ = -3 * κ * a * ((c - a) ^ 2 / ell + 2 * (c - a) * S +
        ell * (S ^ 2 - (1 - C) ^ 2)) := by field_simp; ring
    _ = _ := by rw [hs]; ring

lemma frame_det (ell a : K) : (frame ell a).det = ell * a ^ 3 := by
  simp [frame, Matrix.det_diagonal, Fin.prod_univ_succ, pow_succ, mul_assoc]

lemma frame_inverse (ell a : K) (he : ell ≠ 0) (ha : a ≠ 0) :
    frame ell a * frame ell⁻¹ a⁻¹ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [frame, Matrix.mul_apply, Matrix.diagonal, he, ha]

lemma metric_native (ell a : K) : inverseMetric ell a =
    frame ell⁻¹ a⁻¹ * Matrix.diagonal (fun i => (eta i : K)) *
      (frame ell⁻¹ a⁻¹).transpose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [inverseMetric, frame, eta, Matrix.mul_apply, Matrix.diagonal,
      Matrix.transpose_apply, pow_two, div_eq_mul_inv]

def cellTorsionFace (E : ℕ → Frame K) (V : ℕ → Fin 4 → Frame K) (f : Fin 6) : Vec K :=
  let k := (face f).1
  let l := (face f).2
  fun i => (V 0 k * E (shift k)) i l - E 0 i l - (V 0 l * E (shift l)) i k + E 0 i k

lemma middle_torsion_constructor (C S ell a c : K) (f : Fin 6) :
    torsionFace C S ell a c f =
      cellTorsionFace (atFrame ell a c) (atLink C (-S)) f := rfl

def incomingTorsion (κ C S ell a : K) : K :=
  κ * ∑ r : Fin 6, ∑ s : Fin 6,
    (inverseMetric (1 : K) 1 (face r).1 (face s).1 *
      inverseMetric (1 : K) 1 (face r).2 (face s).2 -
     inverseMetric (1 : K) 1 (face r).1 (face s).2 *
      inverseMetric (1 : K) 1 (face r).2 (face s).1) *
    etaPair (cellTorsionFace (incomingFrame ell a) (incomingLink C (-S)) r)
      (cellTorsionFace (incomingFrame ell a) (incomingLink C (-S)) s)

lemma incoming_torsion_face_independent (C S ell a : K) (f : Fin 6) :
    cellTorsionFace (incomingFrame ell a) (incomingLink C S) f =
      cellTorsionFace (incomingFrame 1 a) (incomingLink C S) f := by
  funext i
  fin_cases f <;> fin_cases i <;>
    norm_num [cellTorsionFace, incomingFrame, incomingLink, frame, link, shift,
      face, Matrix.mul_apply, Matrix.diagonal, Fin.sum_univ_succ]

lemma incoming_torsion_independent (κ C S ell a : K) :
    incomingTorsion κ C S ell a = incomingTorsion κ C S 1 a := by
  simp only [incomingTorsion, incoming_torsion_face_independent]

end Artform.Scores.NonabelianGravity.NonlinearIsotropic
