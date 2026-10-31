import ArtformScores.NonabelianGravity.SphericalTransport
import ArtformScores.NonabelianGravity.SphericalGram
import ArtformScores.NonabelianGravity.DipoleConnection

/-! # Actual matched-sector kick and independent-connection drift

The kick has a negative corrected Gram determinant, even though all face
holonomies remain noncentral. The drift keeps every intrinsic flux but
changes a mixed gauge-invariant trace and violates the fixed seam law.
-/
set_option autoImplicit false
noncomputable section
namespace Artform.Scores.NonabelianGravity.Orthant.Gluing

def postValue : Fin 4 → H :=
  ![⟨0,0,-radius,-radius⟩,⟨0,radius,0,radius⟩,
    ⟨radius,0,0,radius⟩,⟨radius,0,-radius,0⟩]
def postFace (f : Fin 4) : Hˣ where
  val := postValue f
  inv := Star.star (postValue f)
  val_inv := by fin_cases f <;> ext <;> simp [postValue] <;> nlinarith [radius_sq]
  inv_val := by fin_cases f <;> ext <;> simp [postValue] <;> nlinarith [radius_sq]
def kicked : Dipole.State Hˣ := Dipole.kick false fixture
lemma kicked_P : kicked.P=postFace := by
  funext f
  fin_cases f <;> apply Units.ext <;> ext <;>
    norm_num [kicked,Dipole.kick,Dipole.factor,Dipole.holonomy,fixture,link,basisUnit,
      axis,vector,face,faceValue,postFace,postValue]
lemma kicked_gauss : Dipole.Gauss kicked := (Dipole.kick_gauss false fixture).mpr fixture_gauss
lemma kicked_unit : ∀ f, Quaternion.normSq (kicked.P f : H)=1 := by
  intro f
  rw [kicked_P]
  fin_cases f <;> norm_num [postFace,postValue,Quaternion.normSq_def'] <;>
    nlinarith [radius_sq]
lemma kicked_noncentral : ∀ f, (kicked.P f : H).re^2<1 := by
  intro f
  rw [kicked_P]
  fin_cases f
  · change (0:ℝ)^2<1
    norm_num
  · change (0:ℝ)^2<1
    norm_num
  all_goals change radius^2<1; nlinarith [radius_sq]
def postNormal : Fin 4 → H :=
  ![⟨0,0,-radius,-radius⟩,⟨0,radius,0,radius⟩,axis 2,-axis 1]
def postCos : Fin 4 → ℝ := ![0,0,radius,radius]
def postSin : Fin 4 → ℝ := ![1,1,radius,radius]
lemma post_normal_binding : ∀ f, (kicked.P f : H)=
    ⟨postCos f,postSin f*(postNormal f).imI,postSin f*(postNormal f).imJ,
      postSin f*(postNormal f).imK⟩ := by
  intro f
  rw [kicked_P]
  fin_cases f <;> ext <;> simp [postFace,postValue,postCos,postSin,postNormal,axis,vector]
lemma post_normal_unit : ∀ f,
    (postNormal f).re=0 ∧ Quaternion.normSq (postNormal f)=1 ∧ 0 < postSin f := by
  intro f
  fin_cases f <;> simp [postNormal,postSin,axis,vector,Quaternion.normSq_def'] <;>
    nlinarith [radius_sq,radius_pos]

def postGram : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1,-1/2,-radius,radius;-1/2,1,radius,-radius;
    -radius,radius,1,0;radius,-radius,0,1]
lemma post_gram_binding : TransportGram.corrected postNormal (kicked.P 0)=postGram := by
  have hr3 : radius*(radius*radius)=radius/2 := by rw [radius_sq]; ring
  rw [kicked_P]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [TransportGram.corrected,postNormal,postFace,postValue,postGram,
      Maurer.pairing,Maurer.traceH,Maurer.adjoint,axis,vector] <;> nlinarith [radius_sq,hr3]
lemma post_gram_det : postGram.det= -1/4 := by
  rw [Matrix.det_succ_row_zero]
  norm_num [postGram,Fin.sum_univ_succ,Matrix.det_fin_three,Matrix.submatrix,Fin.succAbove]
  nlinarith [radius_sq]
lemma post_sign_gauge_det (b : Fin 4 → Bool) (h : Hˣ) :
    (TransportGram.corrected
      (fun i => Maurer.adjoint h (TransportGram.signed b postNormal i))
      (h*kicked.P 0*h⁻¹)).det= -1/4 := by
  rw [TransportGram.corrected_gauge,TransportGram.corrected_sign_det,
    post_gram_binding,post_gram_det]
def secondConvexity (n : Fin 4 → H) : ℝ :=
  (n 0).imJ*(n 2).imK*(n 3).imI-(n 0).imK*(n 2).imJ*(n 3).imI+
    (n 0).imK*(n 2).imI*(n 3).imJ-(n 0).imI*(n 2).imK*(n 3).imJ+
    (n 0).imI*(n 2).imJ*(n 3).imK-(n 0).imJ*(n 2).imI*(n 3).imK
lemma post_second_convexity : secondConvexity postNormal=0 := by
  norm_num [secondConvexity,postNormal,axis,vector]

def drifted : Dipole.State Hˣ := Dipole.driftOne false 0 fixture
def IntrinsicMatched (s : Dipole.State Hˣ) : Prop :=
  s.P=face ∧ (∀ e, Dipole.outgoing s e=(face e)⁻¹) ∧
    ∀ e, Quaternion.normSq (s.U e : H)=1
def UnitGauge (h : Dipole.canvas.V → Hˣ) : Prop := ∀ v, Quaternion.normSq (h v : H)=1
def IndependentAdmitted (s : Dipole.State Hˣ) : Prop :=
  ∃ h t, UnitGauge h ∧ IntrinsicMatched t ∧ Dipole.gauge h t=s
lemma fixture_intrinsic : IntrinsicMatched fixture := ⟨rfl,fixture_outgoing,link_norm⟩
lemma fixture_independent : IndependentAdmitted fixture :=
  ⟨1,fixture,fun _ => by norm_num,fixture_intrinsic,Dipole.gauge_one fixture⟩
lemma intrinsic_drift (b : Bool) (e : Dipole.canvas.E) (s : Dipole.State Hˣ)
    (hs : IntrinsicMatched s) : IntrinsicMatched (Dipole.driftOne b e s) := by
  refine ⟨hs.1,fun f => ?_,fun f => ?_⟩
  · rw [Dipole.driftOne_outgoing]
    exact hs.2.1 f
  · by_cases hf : f=e
    · subst f
      have hp : Quaternion.normSq (s.P e : H)=1 := by rw [hs.1]; exact face_norm e
      cases b <;>
        simp [Dipole.driftOne,map_mul,hp,hs.2.2 e]
    · simpa [Dipole.driftOne,hf] using hs.2.2 f
lemma independent_drift (b : Bool) (e : Dipole.canvas.E) (s : Dipole.State Hˣ)
    (hs : IndependentAdmitted s) : IndependentAdmitted (Dipole.driftOne b e s) := by
  obtain ⟨h,t,hh,ht,rfl⟩ := hs
  exact ⟨h,Dipole.driftOne b e t,hh,intrinsic_drift b e t ht,
    (Dipole.driftOne_gauge b e h t).symm⟩
lemma independent_gauge (h : Dipole.canvas.V → Hˣ) (s : Dipole.State Hˣ)
    (hh : UnitGauge h) (hs : IndependentAdmitted s) : IndependentAdmitted (Dipole.gauge h s) := by
  obtain ⟨k,t,hk,ht,rfl⟩ := hs
  refine ⟨h*k,t,?_,ht,Dipole.gauge_mul h k t⟩
  intro v
  change Quaternion.normSq ((h v : H)*(k v : H))=1
  rw [map_mul,hh v,hk v,one_mul]
lemma independent_gauss (s : Dipole.State Hˣ) (hs : IndependentAdmitted s) : Dipole.Gauss s := by
  obtain ⟨h,t,hh,ht,rfl⟩ := hs
  have hi := congrArg Inv.inv face_closed
  simp only [mul_inv_rev,inv_one] at hi
  have hg : Dipole.Gauss t := by
    funext v
    fin_cases v
    · simpa [Dipole.defect,ht.2.1,mul_assoc] using hi
    · simpa [Dipole.defect,ht.1,Dipole.closedTuple] using face_closed
  funext v
  rw [Dipole.defect_gauge]
  simp [congrFun hg v]
lemma independent_unit (s : Dipole.State Hˣ) (hs : IndependentAdmitted s) : ∀ e,
    Quaternion.normSq (s.U e : H)=1 ∧ Quaternion.normSq (s.P e : H)=1 := by
  obtain ⟨h,t,hh,ht,rfl⟩ := hs
  have hi : ∀ v, Quaternion.normSq (↑((h v)⁻¹) : H)=1 := by
    intro v
    rw [Units.val_inv_eq_inv_val,Quaternion.normSq_inv,hh v,inv_one]
  intro e
  have hp : Quaternion.normSq (t.P e : H)=1 := by rw [ht.1]; exact face_norm e
  constructor
  · change Quaternion.normSq ((h 1 : H)*(t.U e : H)*(↑((h 0)⁻¹) : H))=1
    rw [map_mul,map_mul,hh 1,ht.2.2 e,hi 0,one_mul,one_mul]
  · change Quaternion.normSq ((h 1 : H)*(t.P e : H)*(↑((h 1)⁻¹) : H))=1
    rw [map_mul,map_mul,hh 1,hp,hi 1,one_mul,one_mul]
lemma drifted_intrinsic : drifted.P=fixture.P ∧
    ∀ e, Dipole.outgoing drifted e=Dipole.outgoing fixture e :=
  ⟨rfl,fun e => Dipole.driftOne_outgoing false 0 e fixture⟩
lemma drifted_gauss : Dipole.Gauss drifted := by
  change Dipole.defect (Dipole.driftOne false 0 fixture)=1
  rw [Dipole.driftOne_defect]
  exact fixture_gauss
lemma drifted_unit : ∀ e,
    Quaternion.normSq (drifted.U e : H)=1 ∧ Quaternion.normSq (drifted.P e : H)=1 := by
  intro e
  constructor
  · by_cases he : e=0
    · subst e
      change Quaternion.normSq ((face 0 : H)*(link 0 : H))=1
      rw [map_mul,face_norm,link_norm,one_mul]
    · simpa [drifted,Dipole.driftOne,fixture,he] using link_norm e
  · exact face_norm e
def mixedTrace (s : Dipole.State Hˣ) : ℝ := ((s.P 1*s.U 0*(s.U 1)⁻¹ : Hˣ) : H).re
lemma mixedTrace_gauge (h : Dipole.canvas.V → Hˣ) (s : Dipole.State Hˣ) :
    mixedTrace (Dipole.gauge h s)=mixedTrace s := by
  have he : (Dipole.gauge h s).P 1*(Dipole.gauge h s).U 0*((Dipole.gauge h s).U 1)⁻¹=
      h 1*(s.P 1*s.U 0*(s.U 1)⁻¹)*(h 1)⁻¹ := by simp [Dipole.gauge,mul_assoc]
  unfold mixedTrace
  rw [he]
  have ht := Maurer.trace_adjoint (h 1) (↑(s.P 1*s.U 0*(s.U 1)⁻¹) : H)
  exact neg_injective ht
lemma mixedTrace_fixture : mixedTrace fixture=0 := by
  norm_num [mixedTrace,fixture,link,basisUnit,axis,vector,face,faceValue]
lemma mixedTrace_drifted : mixedTrace drifted= -1/2 := by
  norm_num [mixedTrace,drifted,Dipole.driftOne,fixture,link,basisUnit,axis,vector,face,faceValue]
  nlinarith [radius_sq]
lemma drifted_not_gauge : ¬ ∃ h, Dipole.gauge h fixture=drifted := by
  rintro ⟨h,hh⟩
  have he := mixedTrace_gauge h fixture
  rw [hh,mixedTrace_fixture,mixedTrace_drifted] at he
  norm_num at he
lemma drifted_not_seam : ¬ SeamAdmitted drifted := by
  intro hh
  have he := congrArg (fun q : H => q.imJ) (hh 0 1)
  norm_num [drifted,Dipole.driftOne,fixture,link,basisUnit,axis,vector,
    linkRotation,face,faceValue,faceInverse] at he

/-! ## Non-vacuity -/
example : Dipole.Gauss fixture ∧ SeamAdmitted fixture ∧ Dipole.Gauss kicked ∧
    Dipole.Gauss drifted := ⟨fixture_gauss,fixture_seam,kicked_gauss,drifted_gauss⟩
end Artform.Scores.NonabelianGravity.Orthant.Gluing
