import ArtformScores.NonabelianGravity.Dipole

/-! # A universal free-link face-collapse control

The link choice here is permitted on the full group carrier. Additional
geometric transport or gluing restrictions may exclude it. The conclusion
does not assert that a matched Regge or Levi-Civita domain admits this lift.
-/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.Dipole
variable {G : Type} [Group G]

def closedTuple (P : canvas.E → G) : Prop := P 3*P 2*P 1*P 0=1
def erasingLift (P : canvas.E → G) : State G := ⟨![(P 0)⁻¹,1,1,1],P⟩
lemma erasingLift_gauss (P : canvas.E → G) (hP : closedTuple P) : Gauss (erasingLift P) := by
  have hi := congrArg Inv.inv hP
  simp only [closedTuple] at hP
  simp only [mul_inv_rev,inv_one] at hi
  funext v
  fin_cases v
  · simpa [defect,outgoing,erasingLift,mul_assoc] using hi
  · simpa [defect,erasingLift,mul_assoc] using hP
lemma erasingLift_kick (P : canvas.E → G) :
    (kick false (erasingLift P)).P=![1,P 1*P 0,P 2,P 3] := by
  funext e
  fin_cases e <;> simp [kick,factor,holonomy,erasingLift]
lemma erased_gauge (P : canvas.E → G) (h : canvas.V → G) :
    (gauge h (kick false (erasingLift P))).P 0=1 := by
  simp [gauge,erasingLift_kick]

/-- A necessary face guard; this predicate is not a reconstructed-cell definition. -/
def NontrivialFaces (s : State G) : Prop := ∀ e, s.P e ≠ 1
lemma no_invariant_domain (P : canvas.E → G) (D : Set (State G))
    (hstart : erasingLift P ∈ D) (hguard : ∀ s ∈ D, s.P 0 ≠ 1) :
    ¬ (∀ s ∈ D, kick false s ∈ D) := by
  intro hinv
  have he := hguard _ (hinv _ hstart)
  exact he (congrFun (erasingLift_kick P) 0)

/-- A target-tuple restriction alone cannot protect a face while keeping every link lift. -/
lemma no_saturated_domain (A : Set (canvas.E → G))
    (hstart : ∃ P ∈ A, closedTuple P) (hguard : ∀ P ∈ A, P 0 ≠ 1) :
    ¬ (∀ s : State G, Gauss s → s.P ∈ A → (kick false s).P ∈ A) := by
  rintro hinv
  obtain ⟨P,hP,hclosed⟩ := hstart
  have he := hguard _ (hinv (erasingLift P) (erasingLift_gauss P hclosed) hP)
  exact he (congrFun (erasingLift_kick P) 0)

/-- A restricted positive control: identity links make this kick stationary. -/
def identityLift (P : canvas.E → G) : State G := ⟨1,P⟩
lemma identityLift_gauss (P : canvas.E → G) (hP : closedTuple P) : Gauss (identityLift P) := by
  have hi := congrArg Inv.inv hP
  simp only [mul_inv_rev,inv_one] at hi
  funext v
  fin_cases v
  · simpa [defect,outgoing,identityLift,mul_assoc] using hi
  · simpa [closedTuple,defect,identityLift,mul_assoc] using hP
lemma identityLift_kick (b : Bool) (P : canvas.E → G) : kick b (identityLift P)=identityLift P := by
  apply State.ext
  · rfl
  · funext e
    cases b <;> fin_cases e <;> simp [kick,factor,holonomy,identityLift]

/-! ## Non-vacuity -/
example (a : G) : Gauss (erasingLift ![a,a⁻¹,1,1]) := by
  apply erasingLift_gauss
  simp [closedTuple]
end Artform.Scores.NonabelianGravity.Dipole
