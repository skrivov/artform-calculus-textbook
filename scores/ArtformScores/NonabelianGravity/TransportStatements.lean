import ArtformScores.NonabelianGravity.TransportControls
import ArtformScores.Meta.Ledger

/-! # Literal matched-sector transport and update submissions

The geometry is an explicit doubled orthant with cell-sector seam data.
No smooth global connection or native gravitational dynamics is asserted.
-/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.Statement
open Orthant

/-- **NGB:matched-orthant-transport** (paired metrics, sector frames and flux holonomies). -/
@[ledger "NGB:matched-orthant-transport"]
def matchedOrthantTransport : Prop :=
  (∀ v, Gluing.sourceLabel (Gluing.sourceLabel v)=v ∧
    Gluing.sourceVertex (Gluing.sourceLabel v)=vertex v) ∧
  (∀ f v, v≠f → Gluing.sourceLabel v ≠ Gluing.sourceLabel f) ∧
  (∀ f, Gluing.targetFaceGram f=1 ∧ Gluing.sourceFaceGram f=Gluing.targetFaceGram f) ∧
  (∀ (f : Fin 4) (x : V4), x f=0 → (Gluing.seam f).mulVec x=x) ∧
  (∀ f, (Gluing.seam f).mulVec (vertex f)= -vertex f ∧
    Gluing.sourceLoop f=(loop (Gluing.sourceLabel f)).transpose ∧
    (Gluing.basedSeam f).mulVec (vertex 3)=vertex 3 ∧
    (Gluing.linkRotation f).transpose*Gluing.linkRotation f=1 ∧
    (Gluing.linkRotation f).det=1) ∧
  (∀ (f : Fin 4) (i j : Fin 3),
    -(Gluing.basedSeam f i.castSucc j.castSucc)=Gluing.linkRotation f i j) ∧
  (∀ (f : Fin 4) (j : Fin 3),
    (Gluing.link f : H)*axis j*(↑(Gluing.link f)⁻¹ : H)=
      vector (fun i => Gluing.linkRotation f i j)) ∧
  (∀ e, Dipole.outgoing Gluing.fixture e=(face e)⁻¹ ∧
    Quaternion.normSq (Gluing.fixture.U e : H)=1 ∧
    Quaternion.normSq (Gluing.fixture.P e : H)=1) ∧
  Dipole.Gauss Gluing.fixture ∧ Gluing.SeamAdmitted Gluing.fixture ∧
  Gluing.sourceGram=1 ∧ (∀ f, Gluing.sourceConvexity f=1) ∧
  (∀ f, (Gluing.sourceFace f : H)=
    ⟨radius,radius*(Gluing.sourceNormal f 0:ℝ),radius*(Gluing.sourceNormal f 1:ℝ),
      radius*(Gluing.sourceNormal f 2:ℝ)⟩) ∧
  (∀ (f : Fin 4) (j : Fin 3),
    (Gluing.sourceFace f : H)*axis j*(↑(Gluing.sourceFace f)⁻¹ : H)=
      vector (fun i => Gluing.sourceRotation f i j)) ∧
  ¬ Gluing.SeamAdmitted Orthant.fixture

/-- **NGB:matched-score-separation** (kick sector escape and independent drift comparison). -/
@[ledger "NGB:matched-score-separation"]
def matchedScoreSeparation : Prop :=
  (∀ (G : Type) [Group G] (b : Bool) (e : Dipole.canvas.E) (s : Dipole.State G),
    (Dipole.driftOne b e s).P=s.P ∧
    (∀ f, Dipole.outgoing (Dipole.driftOne b e s) f=Dipole.outgoing s f) ∧
    Dipole.defect (Dipole.driftOne b e s)=Dipole.defect s ∧
    Dipole.driftOne (!b) e (Dipole.driftOne b e s)=s ∧
    ∀ h, Dipole.driftOne b e (Dipole.gauge h s)=Dipole.gauge h (Dipole.driftOne b e s)) ∧
  Gluing.kicked.P=Gluing.postFace ∧ Dipole.Gauss Gluing.kicked ∧
  (∀ f, Quaternion.normSq (Gluing.kicked.P f : H)=1 ∧ (Gluing.kicked.P f : H).re^2<1) ∧
  (∀ f, (Gluing.kicked.P f : H)=
    ⟨Gluing.postCos f,Gluing.postSin f*(Gluing.postNormal f).imI,
      Gluing.postSin f*(Gluing.postNormal f).imJ,Gluing.postSin f*(Gluing.postNormal f).imK⟩ ∧
    (Gluing.postNormal f).re=0 ∧ Quaternion.normSq (Gluing.postNormal f)=1 ∧
      0 < Gluing.postSin f) ∧
  TransportGram.corrected Gluing.postNormal (Gluing.kicked.P 0)=Gluing.postGram ∧
  Gluing.postGram.det= -1/4 ∧
  (∀ (b : Fin 4 → Bool) (h : Hˣ),
    (TransportGram.corrected
      (fun i => Maurer.adjoint h (TransportGram.signed b Gluing.postNormal i))
      (h*Gluing.kicked.P 0*h⁻¹)).det= -1/4) ∧
  Gluing.secondConvexity Gluing.postNormal=0 ∧
  Gluing.IntrinsicMatched Gluing.fixture ∧ Gluing.IndependentAdmitted Gluing.fixture ∧
  (∀ s, Gluing.IndependentAdmitted s → Dipole.Gauss s ∧
    ∀ e, Quaternion.normSq (s.U e : H)=1 ∧ Quaternion.normSq (s.P e : H)=1) ∧
  (∀ (b : Bool) (e : Dipole.canvas.E) (s : Dipole.State Hˣ),
    Gluing.IndependentAdmitted s → Gluing.IndependentAdmitted (Dipole.driftOne b e s)) ∧
  (∀ (h : Dipole.canvas.V → Hˣ) (s : Dipole.State Hˣ),
    Gluing.UnitGauge h → Gluing.IndependentAdmitted s →
      Gluing.IndependentAdmitted (Dipole.gauge h s)) ∧
  Gluing.drifted.P=Gluing.fixture.P ∧
  (∀ e, Dipole.outgoing Gluing.drifted e=Dipole.outgoing Gluing.fixture e) ∧
  Dipole.Gauss Gluing.drifted ∧
  (∀ e, Quaternion.normSq (Gluing.drifted.U e : H)=1 ∧
    Quaternion.normSq (Gluing.drifted.P e : H)=1) ∧
  (∀ (h : Dipole.canvas.V → Hˣ) (s : Dipole.State Hˣ),
    Gluing.mixedTrace (Dipole.gauge h s)=Gluing.mixedTrace s) ∧
  Gluing.mixedTrace Gluing.fixture=0 ∧ Gluing.mixedTrace Gluing.drifted= -1/2 ∧
  (¬ ∃ h, Dipole.gauge h Gluing.fixture=Gluing.drifted) ∧ ¬ Gluing.SeamAdmitted Gluing.drifted
end Artform.Scores.NonabelianGravity.Statement
