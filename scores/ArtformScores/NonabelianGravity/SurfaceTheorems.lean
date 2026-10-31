import ArtformScores.NonabelianGravity.SurfaceStatements

/-! # Checked identification with known genus-two presentation operations -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity

/-- **NGB:surface-orbit-dictionary** (full orbit-set coverage and both inverse orders). -/
@[ledger "NGB:surface-orbit-dictionary"]
theorem surfaceOrbitDictionary : Statement.surfaceOrbitDictionary := by
  intro G _
  exact ⟨Surface.pack_gauss,fun s hs => ⟨Surface.normalize_tree s,
    Surface.normalize_relation s hs,Surface.normalize_covers s hs⟩,
    Surface.pack_orbit_iff,Surface.from_to_surface,Surface.to_from_surface⟩

/-- **NGB:surface-face-twists** (exact standard substitutions in both orientations). -/
@[ledger "NGB:surface-face-twists"]
theorem surfaceFaceTwists : Statement.surfaceFaceTwists := by
  refine ⟨?_,Surface.surface_witness_moves⟩
  intro G _ f backward c
  exact ⟨Surface.surfaceRelator_generators c,Surface.pack_twist f backward c,
    Surface.twist_relator f backward c,Surface.generators_twist f backward c,
    Surface.toSurface_kick f backward⟩

/-! ## Non-vacuity -/
example : Gauss (Surface.pack Surface.surfaceWitness.val) :=
  (Surface.pack_gauss _).mpr Surface.surfaceWitness.property
example : Surface.twistOrbits 0 false
      (Quotient.mk (Surface.conjugacySetoid Surface.S3) Surface.surfaceWitness) ≠
    Quotient.mk (Surface.conjugacySetoid Surface.S3) Surface.surfaceWitness :=
  Surface.surface_witness_moves
end Artform.Scores.NonabelianGravity
