import ArtformScores.NonabelianGravity.DipoleStatements

/-! # Checked proofs of the dipole admission diagnostic -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity

/-- **NGB:dipole-oriented-score** (complete oriented digon and quantified obstruction). -/
@[ledger "NGB:dipole-oriented-score"]
theorem dipoleOrientedScore : Statement.dipoleOrientedScore := by
  refine ⟨Dipole.star_complete,fun v => ⟨Dipole.star_nodup v,Dipole.star_valence v⟩,?_⟩
  intro G inst
  exact ⟨Dipole.defect_star,fun b s =>
    ⟨Dipole.kick_inverse b s,Dipole.kick_defect b s,fun h => Dipole.kick_gauge b h s⟩,
    fun P hP => ⟨Dipole.erasingLift_gauss P hP,Dipole.erasingLift_kick P,Dipole.erased_gauge P⟩,
    Dipole.no_saturated_domain,fun P b hP =>
      ⟨Dipole.identityLift_gauss P hP,Dipole.identityLift_kick b P⟩⟩

/-- **NGB:spherical-face-collapse** (actual orthant endpoint geometry and face collapse). -/
@[ledger "NGB:spherical-face-collapse"]
theorem sphericalFaceCollapse : Statement.sphericalFaceCollapse :=
  ⟨Orthant.vertexGram_identity,Orthant.interior_admitted.1,Orthant.interior_admitted.2,
    fun s t h => ⟨Orthant.edge_inverse s t h,Orthant.edge_endpoint s t h⟩,
    Orthant.loop_restriction,fun f => ⟨Orthant.loop_base f,Orthant.rotation_special_orthogonal f⟩,
    Orthant.loop_closure,Orthant.gram_identity,Orthant.gram_nondegenerate,
    Orthant.convexity_positive,
    Orthant.face_action,Orthant.face_normal,Orthant.face_closed,Orthant.face_noncentral,
    Orthant.fixture_unit,Orthant.fixture_gauss,Orthant.fixture_nontrivial,
    Orthant.collapsed_gauss,Orthant.collapsed_face,Orthant.collapsed_gauge⟩

/-! ## Non-vacuity -/
example : Dipole.Gauss Orthant.fixture ∧ Dipole.NontrivialFaces Orthant.fixture ∧
    Dipole.Gauss (Dipole.kick false Orthant.fixture) ∧ (Dipole.kick false Orthant.fixture).P 0=1 :=
  ⟨Orthant.fixture_gauss,Orthant.fixture_nontrivial,Orthant.collapsed_gauss,Orthant.collapsed_face⟩
example : Dipole.Gauss (Dipole.identityLift Orthant.face) ∧
    Dipole.kick false (Dipole.identityLift Orthant.face)=Dipole.identityLift Orthant.face :=
  ⟨Dipole.identityLift_gauss _ Orthant.face_closed,Dipole.identityLift_kick _ _⟩
end Artform.Scores.NonabelianGravity
