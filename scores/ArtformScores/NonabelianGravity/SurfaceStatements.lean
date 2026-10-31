import ArtformScores.NonabelianGravity.SurfaceTwists
import ArtformScores.Meta.Ledger

/-! # Literal presentation-orbit identification submissions

These identify known surface-group substitutions in the score model. No
novelty, smoothness, symplectic quotient or gravitational law is asserted.
-/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.Statement

/-- **NGB:surface-orbit-dictionary** (complete Gauss and presentation orbit sets). -/
@[ledger "NGB:surface-orbit-dictionary"]
def surfaceOrbitDictionary : Prop :=
  ∀ (G : Type) [Group G],
    (∀ c : Surface.Coordinates G, Gauss (Surface.pack c) ↔ Surface.relator c=1) ∧
    (∀ s : State G, Gauss s → Surface.TreeFixed (Surface.normalize s) ∧
      Surface.relator (Surface.coordinates (Surface.normalize s))=1 ∧
      Surface.pack (Surface.coordinates (Surface.normalize s))=Surface.normalize s) ∧
    (∀ c d : Surface.Coordinates G, (∃ h, gauge h (Surface.pack c)=Surface.pack d) ↔
      ∃ h, Surface.conjugate h c=d) ∧
    (∀ s : GaugeReduced G, Surface.fromSurface (Surface.toSurface s)=s) ∧
    ∀ c : Surface.PresentationOrbits G, Surface.toSurface (Surface.fromSurface c)=c

/-- **NGB:surface-face-twists** (the actual kicks give standard handle substitutions). -/
@[ledger "NGB:surface-face-twists"]
def surfaceFaceTwists : Prop :=
  (∀ (G : Type) [Group G] (f : canvas.F) (backward : Bool) (c : Surface.Coordinates G),
    Surface.surfaceRelator (Surface.generators c)=Surface.relator c ∧
    Surface.pack (Surface.twist f backward c)=kick f backward (Surface.pack c) ∧
    Surface.relator (Surface.twist f backward c)=Surface.relator c ∧
    Surface.generators (Surface.twist f backward c)=
      Surface.standardTwist f backward (Surface.generators c) ∧
    ∀ s : GaugeReduced G, Surface.toSurface (runPhysical [.face f backward] s)=
      Surface.twistOrbits f backward (Surface.toSurface s)) ∧
  Surface.twistOrbits 0 false
      (Quotient.mk (Surface.conjugacySetoid Surface.S3) Surface.surfaceWitness) ≠
    Quotient.mk (Surface.conjugacySetoid Surface.S3) Surface.surfaceWitness
end Artform.Scores.NonabelianGravity.Statement
