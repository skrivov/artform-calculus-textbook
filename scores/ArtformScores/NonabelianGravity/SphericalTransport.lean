import ArtformScores.NonabelianGravity.SphericalGluing
import ArtformScores.NonabelianGravity.SphericalFixture

/-! # Quaternion lifts of the matched cell-sector transport

These realize the specified seam/stem matrices between the source and
target frames. Their interpretation is cellwise and one-sided. No smooth
global connection at the doubled orthant's singular strata is asserted.
-/
set_option autoImplicit false
noncomputable section
namespace Artform.Scores.NonabelianGravity.Orthant.Gluing

def basisUnit (j : Fin 3) : Hˣ where
  val := axis j
  inv := -axis j
  val_inv := by fin_cases j <;> ext <;> norm_num [axis,vector]
  inv_val := by fin_cases j <;> ext <;> norm_num [axis,vector]
def link : Fin 4 → Hˣ := ![basisUnit 0,basisUnit 1,basisUnit 2,basisUnit 1]
lemma link_norm : ∀ f, Quaternion.normSq (link f : H)=1 := by
  intro f
  fin_cases f <;> norm_num [link,basisUnit,axis,vector,Quaternion.normSq_def']
lemma link_action : ∀ (f : Fin 4) (j : Fin 3),
    (link f : H)*axis j*(↑(link f)⁻¹ : H)=vector (fun i => linkRotation f i j) := by
  intro f j
  fin_cases f <;> fin_cases j <;> ext <;>
    norm_num [link,basisUnit,axis,vector,linkRotation]

def fixture : Dipole.State Hˣ := ⟨link,face⟩
lemma fixture_outgoing : ∀ e, Dipole.outgoing fixture e=(face e)⁻¹ := by
  intro e
  fin_cases e <;> apply Units.ext <;> ext <;>
    norm_num [Dipole.outgoing,fixture,link,basisUnit,axis,vector,face,faceValue,faceInverse]
lemma fixture_gauss : Dipole.Gauss fixture := by
  have hi := congrArg Inv.inv face_closed
  simp only [mul_inv_rev,inv_one] at hi
  funext v
  fin_cases v
  · simpa [Dipole.defect,fixture_outgoing,mul_assoc] using hi
  · exact face_closed
lemma fixture_unit : ∀ e,
    Quaternion.normSq (fixture.U e : H)=1 ∧ Quaternion.normSq (fixture.P e : H)=1 :=
  fun e => ⟨link_norm e,face_norm e⟩

def sourceFace (f : Fin 4) : Hˣ := Dipole.outgoing fixture (sourceLabel f)
def sourceNormal (f : Fin 4) : V3 := -normal (sourceLabel f)
def sourceRotation (f : Fin 4) : Matrix (Fin 3) (Fin 3) ℚ :=
  (rotation (sourceLabel f)).transpose
def sourceGram : Matrix (Fin 4) (Fin 4) ℚ := fun i j =>
  if (i=1 ∧ j=3) ∨ (i=3 ∧ j=1) then
    dot3 (sourceNormal 1) ((sourceRotation 0).mulVec (sourceNormal 3))
  else dot3 (sourceNormal i) (sourceNormal j)
def sourceConvexity : Fin 4 → ℚ :=
  ![dot3 (cross (sourceNormal 0) (sourceNormal 1)) (sourceNormal 2),
    dot3 (cross (sourceNormal 0) (sourceNormal 2)) (sourceNormal 3),
    dot3 (cross (sourceNormal 1) (sourceNormal 0))
      ((sourceRotation 0).mulVec (sourceNormal 3)),
    dot3 (cross (sourceNormal 2) (sourceNormal 1))
      ((sourceRotation 2).transpose.mulVec (sourceNormal 3))]
lemma source_gram_identity : sourceGram=1 := by decide +kernel
lemma source_convexity_positive : ∀ f, sourceConvexity f=1 := by decide +kernel
lemma source_face_normal : ∀ f, (sourceFace f : H)=
    ⟨radius,radius*(sourceNormal f 0:ℝ),radius*(sourceNormal f 1:ℝ),
      radius*(sourceNormal f 2:ℝ)⟩ := by
  intro f
  simp only [sourceFace,fixture_outgoing]
  fin_cases f <;> ext <;>
    norm_num [face,faceValue,faceInverse,sourceLabel,sourceNormal,normal]
lemma source_face_action : ∀ (f : Fin 4) (j : Fin 3),
    (sourceFace f : H)*axis j*(↑(sourceFace f)⁻¹ : H)=
      vector (fun i => sourceRotation f i j) := by
  intro f j
  simp only [sourceFace,fixture_outgoing,inv_inv]
  fin_cases f <;> fin_cases j <;> ext <;>
    norm_num [face,faceValue,faceInverse,sourceLabel,sourceRotation,rotation,axis,vector] <;>
    nlinarith [radius_sq]

/-- Equality is at the SO(3) action level, independent of central lift signs. -/
def SeamAdmitted (s : Dipole.State Hˣ) : Prop := ∀ f j,
  (s.U f : H)*axis j*(↑(s.U f)⁻¹ : H)=vector (fun i => linkRotation f i j)
lemma fixture_seam : SeamAdmitted fixture := link_action
lemma erasing_not_seam : ¬ SeamAdmitted Orthant.fixture := by
  intro hh
  have he := congrArg (fun q : H => q.imJ) (hh 0 1)
  norm_num [Orthant.fixture,Dipole.erasingLift,face,faceValue,faceInverse,
    axis,vector,linkRotation] at he

/-! ## Non-vacuity -/
example : Dipole.Gauss fixture ∧ SeamAdmitted fixture ∧ sourceGram=1 :=
  ⟨fixture_gauss,fixture_seam,source_gram_identity⟩
end Artform.Scores.NonabelianGravity.Orthant.Gluing
