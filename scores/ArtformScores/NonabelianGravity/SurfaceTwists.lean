import ArtformScores.NonabelianGravity.SurfaceQuotient

/-! # The actual face kicks are standard genus-two presentation substitutions

The topological name Dehn twist is supplied by the cited surface literature.
Lean checks the exact substitution and the full orbit-set intertwining;
it does not construct a surface diffeomorphism or a symplectic isomorphism.
-/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.Surface
variable {G : Type} [Group G]

def twist (f : canvas.F) (backward : Bool) (c : Coordinates G) : Coordinates G :=
  if f=0 then {c with x:=driftFactor backward c.a*c.x}
  else {c with z:=driftFactor backward c.b*c.z}
lemma pack_twist (f : canvas.F) (backward : Bool) (c : Coordinates G) :
    pack (twist f backward c)=kick f backward (pack c) := by
  apply State.ext
  · funext e
    fin_cases f <;> fin_cases e <;> simp [pack,twist,kick]
  · funext e
    fin_cases f <;> cases backward <;> fin_cases e <;>
      simp [pack,twist,kick,leftFactor,rightFactor,multiplier,driftFactor,
        holonomy_left,holonomy_right] <;> group
lemma twist_relator (f : canvas.F) (backward : Bool) (c : Coordinates G) :
    relator (twist f backward c)=relator c := by
  fin_cases f <;> cases backward <;> simp [twist,relator,driftFactor] <;> group
lemma twist_conjugate (f : canvas.F) (backward : Bool) (h : G) (c : Coordinates G) :
    twist f backward (conjugate h c)=conjugate h (twist f backward c) := by
  fin_cases f <;> cases backward <;> ext <;> simp [twist,conjugate,driftFactor,mul_assoc]

@[ext] structure Generators (G : Type) where
  A1 : G
  B1 : G
  A2 : G
  B2 : G
def generators (c : Coordinates G) : Generators G := ⟨c.x⁻¹,c.a⁻¹,c.z⁻¹,c.b⁻¹⟩
def surfaceRelator (p : Generators G) : G :=
  (p.A1*p.B1*p.A1⁻¹*p.B1⁻¹)*(p.A2*p.B2*p.A2⁻¹*p.B2⁻¹)
lemma surfaceRelator_generators (c : Coordinates G) : surfaceRelator (generators c)=relator c := by
  simp [surfaceRelator,generators,relator]
def standardTwist (f : canvas.F) (backward : Bool) (p : Generators G) : Generators G :=
  if f=0 then {p with A1:=p.A1*driftFactor backward p.B1}
  else {p with A2:=p.A2*driftFactor backward p.B2}
lemma generators_twist (f : canvas.F) (backward : Bool) (c : Coordinates G) :
    generators (twist f backward c)=standardTwist f backward (generators c) := by
  fin_cases f <;> cases backward <;> ext <;> simp [twist,standardTwist,generators,driftFactor]

def twistPresentation (f : canvas.F) (backward : Bool) (c : Presentation G) : Presentation G :=
  ⟨twist f backward c.val,by rw [twist_relator,c.property]⟩
lemma twistPresentation_respects (f : canvas.F) (backward : Bool) (c d : Presentation G)
    (hcd : (conjugacySetoid G).r c d) :
    (conjugacySetoid G).r (twistPresentation f backward c) (twistPresentation f backward d) := by
  obtain ⟨h,he⟩ := hcd
  refine ⟨h,?_⟩
  change conjugate h (twist f backward c.val)=twist f backward d.val
  rw [← twist_conjugate,he]
def twistOrbits (f : canvas.F) (backward : Bool) : PresentationOrbits G → PresentationOrbits G :=
  Quotient.map (twistPresentation f backward) (twistPresentation_respects f backward)

lemma fromSurface_twist (f : canvas.F) (backward : Bool) (c : PresentationOrbits G) :
    fromSurface (twistOrbits f backward c)=runPhysical [.face f backward] (fromSurface c) := by
  induction c using Quotient.inductionOn with
  | h c =>
    apply congrArg (Quotient.mk (gaugeSetoid G))
    apply Subtype.ext
    exact pack_twist f backward c.val

lemma toSurface_kick (f : canvas.F) (backward : Bool) (s : GaugeReduced G) :
    toSurface (runPhysical [.face f backward] s)=twistOrbits f backward (toSurface s) := by
  apply Function.LeftInverse.injective to_from_surface
  rw [from_to_surface,fromSurface_twist,from_to_surface]

/-! ## Non-vacuity -/
abbrev S3 := ClassicalNonabelian.S3
def surfaceWitness : Presentation S3 :=
  ⟨⟨ClassicalNonabelian.reflection,ClassicalNonabelian.rotation,1,1⟩,by simp [relator]⟩
lemma surface_witness_moves :
    twistOrbits 0 false (Quotient.mk (conjugacySetoid S3) surfaceWitness) ≠
      Quotient.mk (conjugacySetoid S3) surfaceWitness := by
  intro he
  obtain ⟨h,hh⟩ := Quotient.eq.mp he
  have hx := congrArg Coordinates.x hh
  have hr : ClassicalNonabelian.reflection ≠ (1 : S3) := by decide +kernel
  apply hr
  simpa [conjugate,twistPresentation,twist,surfaceWitness,driftFactor,mul_assoc] using
    congrArg (fun y => h⁻¹*y*h) hx
example : relator surfaceWitness.val=1 := surfaceWitness.property
end Artform.Scores.NonabelianGravity.Surface
