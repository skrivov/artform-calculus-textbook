import ArtformScores.NonabelianGravity.SurfaceCoordinates

/-! # The explicit full Gauss-orbit and surface-presentation-orbit bijection

All gauge functions are retained. Tree fixing leaves precisely simultaneous
conjugation of four generators; it imposes no physical gauge selection.
-/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.Surface
variable (G : Type) [Group G]
abbrev Presentation := {c : Coordinates G // relator c=1}
def conjugacySetoid : Setoid (Presentation G) where
  r c d := ∃ h, conjugate h c.val=d.val
  iseqv :=
    { refl c := ⟨1,conjugate_one c.val⟩
      symm := by
        rintro c d ⟨h,he⟩
        refine ⟨h⁻¹,?_⟩
        rw [← he,← conjugate_mul]
        simpa using conjugate_one c.val
      trans := by
        rintro c d e ⟨h,hh⟩ ⟨k,hk⟩
        exact ⟨k*h,by rw [conjugate_mul,hh,hk]⟩ }
abbrev PresentationOrbits := Quotient (conjugacySetoid G)
variable {G}

def toGauss (c : Presentation G) : Admitted G := ⟨pack c.val,(pack_gauss _).mpr c.property⟩
def toPresentation (s : Admitted G) : Presentation G :=
  ⟨coordinates (normalize s.val),normalize_relation s.val s.property⟩

lemma toGauss_respects (c d : Presentation G) (hcd : (conjugacySetoid G).r c d) :
    (gaugeSetoid G).r (toGauss c) (toGauss d) := by
  obtain ⟨h,he⟩ := (pack_orbit_iff c.val d.val).mpr hcd
  exact ⟨h,he⟩

lemma toPresentation_respects (s t : Admitted G) (hst : (gaugeSetoid G).r s t) :
    (conjugacySetoid G).r (toPresentation s) (toPresentation t) := by
  obtain ⟨h,hh⟩ := hst
  apply (pack_orbit_iff _ _).mp
  change ∃ k, gauge k (pack (coordinates (normalize s.val)))=
    pack (coordinates (normalize t.val))
  rw [normalize_covers _ s.property,normalize_covers _ t.property]
  refine ⟨treeGauge t.val*h*(treeGauge s.val)⁻¹,?_⟩
  unfold normalize
  rw [← gauge_mul]
  have he : treeGauge t.val*h*(treeGauge s.val)⁻¹*treeGauge s.val=treeGauge t.val*h := by group
  rw [he,gauge_mul,hh]

def fromSurface : PresentationOrbits G → GaugeReduced G :=
  Quotient.map toGauss toGauss_respects
def toSurface : GaugeReduced G → PresentationOrbits G :=
  Quotient.map toPresentation toPresentation_respects

lemma treeGauge_pack (c : Coordinates G) : treeGauge (pack c)=1 := by
  funext v
  fin_cases v <;> simp [treeGauge,pack]
lemma normalize_pack (c : Coordinates G) : normalize (pack c)=pack c := by
  rw [normalize,treeGauge_pack,gauge_one]

lemma to_from_surface (c : PresentationOrbits G) : toSurface (fromSurface c)=c := by
  induction c using Quotient.inductionOn with
  | h c =>
    apply congrArg (Quotient.mk (conjugacySetoid G))
    apply Subtype.ext
    exact (congrArg coordinates (normalize_pack c.val)).trans (coordinates_pack c.val)

lemma from_to_surface (s : GaugeReduced G) : fromSurface (toSurface s)=s := by
  induction s using Quotient.inductionOn with
  | h s =>
    apply Quotient.sound
    refine ⟨(treeGauge s.val)⁻¹,?_⟩
    change gauge (treeGauge s.val)⁻¹ (pack (coordinates (normalize s.val)))=s.val
    rw [normalize_covers _ s.property,normalize,← gauge_mul]
    simpa using gauge_one s.val

def orbitEquiv : GaugeReduced G ≃ PresentationOrbits G where
  toFun := toSurface
  invFun := fromSurface
  left_inv := from_to_surface
  right_inv := to_from_surface

/-! ## Non-vacuity -/
example : Nonempty (Presentation G) := ⟨⟨⟨1,1,1,1⟩,by simp [relator]⟩⟩
example (s : GaugeReduced G) : fromSurface (orbitEquiv s)=s := from_to_surface s
end Artform.Scores.NonabelianGravity.Surface
