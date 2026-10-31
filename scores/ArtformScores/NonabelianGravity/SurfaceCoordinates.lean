import ArtformScores.NonabelianGravity.Descent

/-! # Exact genus-two presentation coordinates for the complete Gauss carrier

This is a set-level group dictionary, not a new smooth or symplectic reduction
theorem. The remaining relation is the standard product of two commutators.
-/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.Surface

@[ext] structure Coordinates (G : Type) where
  a : G
  b : G
  x : G
  z : G

variable {G : Type} [Group G]
def relator (c : Coordinates G) : G :=
  (c.x⁻¹*c.a⁻¹*c.x*c.a)*(c.z⁻¹*c.b⁻¹*c.z*c.b)
def pack (c : Coordinates G) : State G :=
  ⟨![1,1,1,c.a,1,1,c.b],
    ![c.x,c.a⁻¹*c.x*c.a*c.z⁻¹,c.a⁻¹*c.x*c.a,c.x,c.b⁻¹*c.z*c.b,c.b⁻¹*c.z*c.b,c.z]⟩
def coordinates (s : State G) : Coordinates G := ⟨s.U 3,s.U 6,s.P 0,s.P 6⟩
lemma coordinates_pack (c : Coordinates G) : coordinates (pack c)=c := by cases c; rfl

lemma pack_defect (c : Coordinates G) (v : canvas.V) :
    defect (pack c) v=if v=1 then (relator c)⁻¹ else 1 := by
  fin_cases v <;> simp [defect,outgoing,pack,relator] <;> group
lemma pack_gauss (c : Coordinates G) : Gauss (pack c) ↔ relator c=1 := by
  constructor
  · intro hg
    have he := congrFun hg 1
    simpa [pack_defect] using he
  · intro hr
    funext v
    simp [pack_defect,hr]

def TreeFixed (s : State G) : Prop :=
  s.U 0=1 ∧ s.U 1=1 ∧ s.U 2=1 ∧ s.U 4=1 ∧ s.U 5=1
def treeGauge (s : State G) : canvas.V → G :=
  ![1,(s.U 0)⁻¹,(s.U 0)⁻¹*(s.U 4)⁻¹,
    (s.U 0)⁻¹*(s.U 1)⁻¹*(s.U 2)⁻¹,(s.U 0)⁻¹*(s.U 1)⁻¹,
    (s.U 0)⁻¹*(s.U 4)⁻¹*(s.U 5)⁻¹]
def normalize (s : State G) : State G := gauge (treeGauge s) s
lemma normalize_tree (s : State G) : TreeFixed (normalize s) := by
  simp [TreeFixed,normalize,gauge,treeGauge,canvas,mul_assoc]

lemma solve_right (a b : G) (h : a * b = 1) : b=a⁻¹ := by
  have he := congrArg (fun z => a⁻¹*z) h
  simpa [mul_assoc] using he

lemma pack_coordinates (s : State G) (ht : TreeFixed s) (hg : Gauss s) :
    pack (coordinates s)=s := by
  obtain ⟨h0,h1,h2,h4,h5⟩ := ht
  have hv (v : canvas.V) : defect s v=1 := congrFun hg v
  have hp3 : s.P 3=s.P 0 := by
    have he := hv 0
    simp only [defect,outgoing,h0,inv_one,one_mul,mul_one] at he
    simpa using solve_right _ _ he
  have hp5 : s.P 5=(s.U 6)⁻¹*s.P 6*s.U 6 := by
    have he := hv 5
    simp only [defect] at he
    simpa [outgoing,mul_assoc] using solve_right _ _ he
  have hp4 : s.P 4=(s.U 6)⁻¹*s.P 6*s.U 6 := by
    have he := hv 2
    simp only [defect,outgoing,h5,inv_one,one_mul,mul_one] at he
    simpa [hp5] using solve_right _ _ he
  have hp2 : s.P 2=(s.U 3)⁻¹*s.P 0*s.U 3 := by
    have he := hv 3
    simp only [defect,outgoing] at he
    simpa [hp3,mul_assoc] using solve_right _ _ he
  have hp1 : s.P 1=(s.U 3)⁻¹*s.P 0*s.U 3*(s.P 6)⁻¹ := by
    have he := hv 4
    simp only [defect,outgoing,h2,inv_one,one_mul,mul_one] at he
    change (s.P 2)⁻¹*s.P 1*s.P 6=1 at he
    have hh := solve_right _ _ (show (s.P 2)⁻¹*(s.P 1*s.P 6)=1 by
      simpa only [mul_assoc] using he)
    have hx := congrArg (fun z => z*(s.P 6)⁻¹) hh
    simpa [hp2,mul_assoc] using hx
  apply State.ext
  · funext e
    fin_cases e <;> simp [pack,coordinates,h0,h1,h2,h4,h5]
  · funext e
    fin_cases e <;> simp [pack,coordinates,hp1,hp2,hp3,hp4,hp5]

lemma normalize_covers (s : State G) (hg : Gauss s) :
    pack (coordinates (normalize s))=normalize s :=
  pack_coordinates _ (normalize_tree s) ((gauss_gauge _ _).mpr hg)
lemma normalize_relation (s : State G) (hg : Gauss s) :
    relator (coordinates (normalize s))=1 := by
  apply (pack_gauss _).mp
  rw [normalize_covers s hg]
  exact (gauss_gauge _ _).mpr hg

def conjugate (h : G) (c : Coordinates G) : Coordinates G :=
  ⟨h*c.a*h⁻¹,h*c.b*h⁻¹,h*c.x*h⁻¹,h*c.z*h⁻¹⟩
lemma pack_conjugate (h : G) (c : Coordinates G) :
    pack (conjugate h c)=gauge (fun _ => h) (pack c) := by
  apply State.ext <;> funext e <;> fin_cases e <;>
    simp [pack,conjugate,gauge,mul_assoc]
lemma conjugate_one (c : Coordinates G) : conjugate 1 c=c := by
  ext <;> simp [conjugate]
lemma conjugate_mul (h k : G) (c : Coordinates G) :
    conjugate (h*k) c=conjugate h (conjugate k c) := by
  ext <;> simp [conjugate,mul_assoc]
lemma relator_conjugate (h : G) (c : Coordinates G) :
    relator (conjugate h c)=h*relator c*h⁻¹ := by simp [relator,conjugate,mul_assoc]

lemma residual_gauge (c d : Coordinates G) (h : canvas.V → G)
    (he : gauge h (pack c) = pack d) : h=(fun _ => h 0) := by
  have hu (e : canvas.E) := congrArg (fun s : State G => s.U e) he
  have h1 : h 1=h 0 := by
    have hh := hu 0
    apply mul_inv_eq_one.mp
    simpa [gauge,pack,canvas] using hh
  have h4 : h 4=h 1 := by
    have hh := hu 1
    apply mul_inv_eq_one.mp
    simpa [gauge,pack,canvas] using hh
  have h3 : h 3=h 4 := by
    have hh := hu 2
    apply mul_inv_eq_one.mp
    simpa [gauge,pack,canvas] using hh
  have h2 : h 2=h 1 := by
    have hh := hu 4
    apply mul_inv_eq_one.mp
    simpa [gauge,pack,canvas] using hh
  have h5 : h 5=h 2 := by
    have hh := hu 5
    apply mul_inv_eq_one.mp
    simpa [gauge,pack,canvas] using hh
  funext v
  fin_cases v <;> simp [h1,h2,h3,h4,h5]

lemma pack_orbit_iff (c d : Coordinates G) :
    (∃ h, gauge h (pack c)=pack d) ↔ ∃ h, conjugate h c=d := by
  constructor
  · rintro ⟨h,he⟩
    have hh := residual_gauge c d h he
    refine ⟨h 0,?_⟩
    rw [hh,← pack_conjugate] at he
    have hx := congrArg coordinates he
    simpa only [coordinates_pack] using hx
  · rintro ⟨h,he⟩
    exact ⟨fun _ => h,by rw [← pack_conjugate,he]⟩

/-! ## Non-vacuity -/
example : relator (Coordinates.mk (1:G) 1 1 1)=1 := by simp [relator]
example (s : State G) (hg : Gauss s) : ∃ c, relator c=1 ∧ ∃ h, gauge h s=pack c :=
  ⟨coordinates (normalize s),normalize_relation s hg,treeGauge s,(normalize_covers s hg).symm⟩
end Artform.Scores.NonabelianGravity.Surface
