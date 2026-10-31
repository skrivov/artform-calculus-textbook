import ArtformScores.NonabelianGravity.Geometry

/-! # NGB: exact dictionary to the Alekseev-Malkin-Meinrenken double

Only the group-valued dictionary is asserted here. A differential two-form,
its quasi-Hamiltonian axioms and symplectic reduction are separate duties.
-/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity
variable {G : Type} [Group G]

def doubleA (U _P : G) : G := U
def doubleB (U P : G) : G := U⁻¹*P
def doubleTarget (a b : G) : G := a*b
def doubleSource (a b : G) : G := a⁻¹*b⁻¹
lemma double_endpoints (U P : G) :
    doubleTarget (doubleA U P) (doubleB U P)=P ∧
    doubleSource (doubleA U P) (doubleB U P)=U⁻¹*P⁻¹*U := by
  constructor <;> simp [doubleTarget,doubleSource,doubleA,doubleB,mul_assoc]
lemma double_covariance (U P ht hs : G) :
    doubleA (ht*U*hs⁻¹) (ht*P*ht⁻¹)=ht*doubleA U P*hs⁻¹ ∧
    doubleB (ht*U*hs⁻¹) (ht*P*ht⁻¹)=hs*doubleB U P*ht⁻¹ := by
  constructor <;> simp [doubleA,doubleB,mul_assoc]
lemma double_inverse (a b : G) :
    doubleA a (a*b)=a ∧ doubleB a (a*b)=b := by
  simp [doubleA,doubleB]
lemma double_drift (U P : G) :
    doubleA (P*U) P=doubleA U P*doubleB U P*doubleA U P ∧
    doubleB (P*U) P=(doubleA U P)⁻¹ := by
  constructor <;> simp [doubleA,doubleB,mul_assoc]

/-! ## Non-vacuity -/
example (s : State G) (e : canvas.E) :
    doubleSource (doubleA (s.U e) (s.P e)) (doubleB (s.U e) (s.P e))=outgoing s e :=
  (double_endpoints _ _).2
end Artform.Scores.NonabelianGravity
