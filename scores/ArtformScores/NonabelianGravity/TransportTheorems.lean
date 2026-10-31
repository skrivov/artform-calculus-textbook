import ArtformScores.NonabelianGravity.TransportStatements

/-! # Checked proofs of the matched cell-sector diagnostic -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity
open Orthant

/-- **NGB:matched-orthant-transport** (actual paired metric and prescribed seam data). -/
@[ledger "NGB:matched-orthant-transport"]
theorem matchedOrthantTransport : Statement.matchedOrthantTransport :=
  ⟨fun v => ⟨Gluing.sourceLabel_inverse v,Gluing.paired_vertices v⟩,
    Gluing.face_pairing,Gluing.face_metrics,Gluing.seam_tangents,
    fun f => ⟨Gluing.seam_normal f,Gluing.source_loop_inverse f,Gluing.based_seam_base f,
      Gluing.link_rotation_orthogonal f⟩,
    Gluing.based_seam_frame,Gluing.link_action,
    fun e => ⟨Gluing.fixture_outgoing e,Gluing.fixture_unit e⟩,
    Gluing.fixture_gauss,Gluing.fixture_seam,Gluing.source_gram_identity,
    Gluing.source_convexity_positive,Gluing.source_face_normal,Gluing.source_face_action,
    Gluing.erasing_not_seam⟩

/-- **NGB:matched-score-separation** (complete kick escape and intrinsic-data drift). -/
@[ledger "NGB:matched-score-separation"]
theorem matchedScoreSeparation : Statement.matchedScoreSeparation := by
  refine ⟨?_,Gluing.kicked_P,Gluing.kicked_gauss,
    fun f => ⟨Gluing.kicked_unit f,Gluing.kicked_noncentral f⟩,
    fun f => ⟨Gluing.post_normal_binding f,Gluing.post_normal_unit f⟩,
    Gluing.post_gram_binding,Gluing.post_gram_det,Gluing.post_sign_gauge_det,
    Gluing.post_second_convexity,Gluing.fixture_intrinsic,Gluing.fixture_independent,
    fun s hs => ⟨Gluing.independent_gauss s hs,Gluing.independent_unit s hs⟩,
    Gluing.independent_drift,Gluing.independent_gauge,
    Gluing.drifted_intrinsic.1,Gluing.drifted_intrinsic.2,
    Gluing.drifted_gauss,Gluing.drifted_unit,Gluing.mixedTrace_gauge,Gluing.mixedTrace_fixture,
    Gluing.mixedTrace_drifted,Gluing.drifted_not_gauge,Gluing.drifted_not_seam⟩
  intro G inst b e s
  exact ⟨rfl,fun f => Dipole.driftOne_outgoing b e f s,Dipole.driftOne_defect b e s,
    Dipole.driftOne_inverse b e s,fun h => Dipole.driftOne_gauge b e h s⟩

/-! ## Non-vacuity -/
example : Dipole.Gauss Gluing.fixture ∧ Gluing.SeamAdmitted Gluing.fixture ∧
    Gluing.sourceFaceGram 0=Gluing.targetFaceGram 0 :=
  ⟨Gluing.fixture_gauss,Gluing.fixture_seam,(Gluing.face_metrics 0).2⟩
example : Dipole.Gauss Gluing.drifted ∧
    ¬ ∃ h, Dipole.gauge h Gluing.fixture=Gluing.drifted :=
  ⟨Gluing.drifted_gauss,Gluing.drifted_not_gauge⟩
end Artform.Scores.NonabelianGravity
