import ArtformScores.GravityBridge.ConstraintDefs

/-! # Exact variation, constraints and relational momentum matching -/

namespace Artform.Scores.GravityBridge.Statement

/-- **GAC:singular-action** (singular discrete quadratic action and variational gluing). -/
@[ledger "GAC:singular-action"]
def singularActionLaw : Prop :=
  (∀ (x y dx dy : SingularConfig) (e : ℚ),
    singularAction (x + e • dx) (y + e • dy) = singularAction x y +
      e * (-boundaryPair (preMomentum x y) dx + boundaryPair (postMomentum x y) dy) +
        e ^ 2 * (dy.1 - dx.1) ^ 2 / 2) ∧
  (∀ x p y q : SingularConfig, singularRelation (x, p) (y, q) ↔
    p.2 = 0 ∧ q.2 = 0 ∧ q.1 = p.1 ∧ y.1 = x.1 + p.1) ∧
  (∀ x y z : SingularConfig, cornerStationary x y z ↔ x.1 - 2 * y.1 + z.1 = 0) ∧
  (∀ (x y z d : SingularConfig) (e : ℚ),
    singularAction x (y + e • d) + singularAction (y + e • d) z =
      singularAction x y + singularAction y z +
        e * (2 * y.1 - x.1 - z.1) * d.1 + e ^ 2 * d.1 ^ 2) ∧
  (∀ x y z : SingularConfig,
    (∃ px py pz, singularRelation (x, px) (y, py) ∧ singularRelation (y, py) (z, pz)) ↔
      cornerStationary x y z)

end Artform.Scores.GravityBridge.Statement
