import ArtformScores.NonabelianGravity.SphericalOrthant
import ArtformScores.NonabelianGravity.DipoleErasure
import ArtformScores.NonabelianGravity.QuaternionForm

/-! # Unit-quaternion lifts of actual orthant face loops, and collapse

This binds the rational loop matrices to concrete quaternion conjugations.
The erasing link lift is a Gauss-admitted independent connection choice.
It is not asserted to be a reconstructed two-cell Levi-Civita gluing.
-/
set_option autoImplicit false
noncomputable section
namespace Artform.Scores.NonabelianGravity.Orthant
abbrev H := Maurer.H
def radius : ℝ := Real.sqrt (1/2)
lemma radius_sq : radius*radius=1/2 := by
  have he := Real.sq_sqrt (show (0:ℝ) ≤ 1/2 by norm_num)
  simpa [radius,pow_two] using he
lemma radius_pos : 0 < radius := Real.sqrt_pos.mpr (by norm_num)

def faceValue : Fin 4 → H :=
  ![⟨radius,radius,0,0⟩,⟨radius,0,radius,0⟩,
    ⟨radius,0,0,radius⟩,⟨radius,0,-radius,0⟩]
def faceInverse : Fin 4 → H :=
  ![⟨radius,-radius,0,0⟩,⟨radius,0,-radius,0⟩,
    ⟨radius,0,0,-radius⟩,⟨radius,0,radius,0⟩]
def face (f : Fin 4) : Hˣ where
  val := faceValue f
  inv := faceInverse f
  val_inv := by fin_cases f <;> ext <;> simp [faceValue,faceInverse] <;> nlinarith [radius_sq]
  inv_val := by fin_cases f <;> ext <;> simp [faceValue,faceInverse] <;> nlinarith [radius_sq]

lemma face_norm : ∀ f, Quaternion.normSq (face f : H)=1 := by
  intro f
  fin_cases f <;> simp [face,faceValue,Quaternion.normSq_def'] <;> nlinarith [radius_sq]
lemma face_re : ∀ f, (face f : H).re=radius := by intro f; fin_cases f <;> rfl
lemma face_noncentral : ∀ f, (face f : H).re^2<1 := by
  intro f
  rw [face_re]
  nlinarith [radius_sq]
lemma face_not_one : ∀ f, face f ≠ 1 := by
  intro f he
  have hr := face_noncentral f
  rw [he] at hr
  norm_num at hr

def vector (v : V3) : H := ⟨0,(v 0:ℝ),(v 1:ℝ),(v 2:ℝ)⟩
def axis (i : Fin 3) : H := vector (fun j => if j=i then 1 else 0)
lemma face_action : ∀ (f : Fin 4) (j : Fin 3),
    (face f : H)*axis j*(↑(face f)⁻¹ : H)=vector (fun i => rotation f i j) := by
  intro f j
  fin_cases f <;> fin_cases j <;> ext <;>
    norm_num [face,faceValue,faceInverse,axis,vector,rotation] <;> nlinarith [radius_sq]
lemma face_normal : ∀ f,
    (face f : H)=⟨radius,radius*(normal f 0:ℝ),radius*(normal f 1:ℝ),
      radius*(normal f 2:ℝ)⟩ := by
  intro f
  fin_cases f <;> ext <;> simp [face,faceValue,normal]
lemma face_closed : Dipole.closedTuple face := by
  have hr4 : radius*radius*radius*radius=1/4 := by
    calc
      _ = (radius*radius)*(radius*radius) := by ring
      _ = 1/4 := by rw [radius_sq]; norm_num
  apply Units.ext
  ext <;> norm_num [Dipole.closedTuple,face,faceValue] <;> nlinarith [radius_sq,hr4]

def fixture : Dipole.State Hˣ := Dipole.erasingLift face
lemma fixture_gauss : Dipole.Gauss fixture := Dipole.erasingLift_gauss face face_closed
lemma fixture_nontrivial : Dipole.NontrivialFaces fixture := face_not_one
lemma fixture_unit : ∀ e,
    Quaternion.normSq (fixture.U e : H)=1 ∧ Quaternion.normSq (fixture.P e : H)=1 := by
  intro e
  constructor
  · fin_cases e
    · change Quaternion.normSq (faceInverse 0)=1
      simp [faceInverse,Quaternion.normSq_def']
      nlinarith [radius_sq]
    all_goals norm_num [fixture,Dipole.erasingLift]
  · exact face_norm e
lemma collapsed_gauss : Dipole.Gauss (Dipole.kick false fixture) :=
  (Dipole.kick_gauss false fixture).mpr fixture_gauss
lemma collapsed_face : (Dipole.kick false fixture).P 0=1 :=
  congrFun (Dipole.erasingLift_kick face) 0
lemma collapsed_gauge : ∀ h : Dipole.canvas.V → Hˣ,
    (Dipole.gauge h (Dipole.kick false fixture)).P 0=1 := Dipole.erased_gauge face
lemma collapsed_guard : ¬ Dipole.NontrivialFaces (Dipole.kick false fixture) := by
  intro hh
  exact hh 0 collapsed_face

/-! ## Non-vacuity -/
example : Dipole.Gauss fixture ∧ Dipole.NontrivialFaces fixture ∧ gram.det ≠ 0 :=
  ⟨fixture_gauss,fixture_nontrivial,by rw [gram_nondegenerate]; norm_num⟩
end Artform.Scores.NonabelianGravity.Orthant
