import ArtformScores.NonabelianGravity.SphericalFixture
import ArtformScores.Meta.Ledger

/-! # Literal dipole admission diagnostic submissions

These are a complete group-carrier construction and a one-cell geometric
counterexample. They do not certify matched two-cell transport or dynamics.
-/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.Statement

/-- **NGB:dipole-oriented-score** (complete first-digon map and free-link obstruction). -/
@[ledger "NGB:dipole-oriented-score"]
def dipoleOrientedScore : Prop :=
  (∀ v a, a ∈ Dipole.star v ↔ Dipole.endpoint a=v) ∧
  (∀ v, (Dipole.star v).Nodup ∧ (Dipole.star v).length=4) ∧
  ∀ (G : Type) [Group G],
    (∀ (s : Dipole.State G) v, Dipole.defect s v=
      ((Dipole.star v).map (fun a => if a.2 then s.P a.1 else Dipole.outgoing s a.1)).prod) ∧
    (∀ (b : Bool) (s : Dipole.State G),
      Dipole.kick (!b) (Dipole.kick b s)=s ∧ Dipole.defect (Dipole.kick b s)=Dipole.defect s ∧
      ∀ h, Dipole.kick b (Dipole.gauge h s)=Dipole.gauge h (Dipole.kick b s)) ∧
    (∀ P : Dipole.canvas.E → G, Dipole.closedTuple P →
      Dipole.Gauss (Dipole.erasingLift P) ∧
      (Dipole.kick false (Dipole.erasingLift P)).P=![1,P 1*P 0,P 2,P 3] ∧
      ∀ h, (Dipole.gauge h (Dipole.kick false (Dipole.erasingLift P))).P 0=1) ∧
    (∀ A : Set (Dipole.canvas.E → G),
      (∃ P ∈ A, Dipole.closedTuple P) → (∀ P ∈ A, P 0 ≠ 1) →
      ¬ (∀ s : Dipole.State G, Dipole.Gauss s → s.P ∈ A → (Dipole.kick false s).P ∈ A)) ∧
    ∀ (P : Dipole.canvas.E → G) (b : Bool), Dipole.closedTuple P →
      Dipole.Gauss (Dipole.identityLift P) ∧
      Dipole.kick b (Dipole.identityLift P)=Dipole.identityLift P

/-- **NGB:spherical-face-collapse** (orthant matrices, quaternion lifts and a collapsed face). -/
@[ledger "NGB:spherical-face-collapse"]
def sphericalFaceCollapse : Prop :=
  Orthant.vertexGram=1 ∧ Orthant.dot4 Orthant.interior Orthant.interior=1 ∧
  (∀ i, 0 < Orthant.interior i) ∧
  (∀ s t, s≠t → Orthant.edge s t*Orthant.edge t s=1 ∧
    (Orthant.edge t s).mulVec (Orthant.vertex s)=Orthant.vertex t) ∧
  (∀ (f : Fin 4) (i j : Fin 3),
    Orthant.loop f i.castSucc j.castSucc=Orthant.rotation f i j) ∧
  (∀ f, (Orthant.loop f).mulVec (Orthant.vertex 3)=Orthant.vertex 3 ∧
    (Orthant.rotation f).transpose*Orthant.rotation f=1 ∧ (Orthant.rotation f).det=1) ∧
  Orthant.loop 3*Orthant.loop 2*Orthant.loop 1*Orthant.loop 0=1 ∧
  Orthant.gram=1 ∧ Orthant.gram.det=1 ∧ (∀ i, Orthant.convexity i=1) ∧
  (∀ (f : Fin 4) (j : Fin 3),
    (Orthant.face f : Orthant.H)*Orthant.axis j*(↑(Orthant.face f)⁻¹ : Orthant.H)=
      Orthant.vector (fun i => Orthant.rotation f i j)) ∧
  (∀ f, (Orthant.face f : Orthant.H)=
    ⟨Orthant.radius,Orthant.radius*(Orthant.normal f 0:ℝ),
      Orthant.radius*(Orthant.normal f 1:ℝ),Orthant.radius*(Orthant.normal f 2:ℝ)⟩) ∧
  Dipole.closedTuple Orthant.face ∧ (∀ f, (Orthant.face f : Orthant.H).re^2<1) ∧
  (∀ e, Quaternion.normSq (Orthant.fixture.U e : Orthant.H)=1 ∧
    Quaternion.normSq (Orthant.fixture.P e : Orthant.H)=1) ∧
  Dipole.Gauss Orthant.fixture ∧ Dipole.NontrivialFaces Orthant.fixture ∧
  Dipole.Gauss (Dipole.kick false Orthant.fixture) ∧
  (Dipole.kick false Orthant.fixture).P 0=1 ∧
  ∀ h, (Dipole.gauge h (Dipole.kick false Orthant.fixture)).P 0=1
end Artform.Scores.NonabelianGravity.Statement
