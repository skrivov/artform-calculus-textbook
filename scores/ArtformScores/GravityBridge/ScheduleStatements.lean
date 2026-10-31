import ArtformScores.GravityBridge.ScheduleDefs

/-! # Schedule defects and endpoint terms -/

namespace Artform.Scores.GravityBridge.Statement

/-- **GAC:schedule-boundary** (schedule defects and endpoint terms). -/
@[ledger "GAC:schedule-boundary"]
def scheduleLaw : Prop :=
  (∀ (a b : ℚ) (x : ℚ × ℚ),
    scheduleMove b (scheduleKick a x) - scheduleKick a (scheduleMove b x) =
      (a * b * x.1, -a * b * x.2)) ∧
  (∀ a b : ℚ,
    (∀ x, scheduleMove b (scheduleKick a x) = scheduleKick a (scheduleMove b x)) ↔ a * b = 0) ∧
  (∀ (a b : ℚ) (x y : ℚ × ℚ),
    (scheduleMove b (scheduleKick a x)).1 * (scheduleMove b (scheduleKick a y)).2 -
      (scheduleMove b (scheduleKick a x)).2 * (scheduleMove b (scheduleKick a y)).1 =
        x.1 * y.2 - x.2 * y.1 ∧
    (scheduleKick a (scheduleMove b x)).1 * (scheduleKick a (scheduleMove b y)).2 -
      (scheduleKick a (scheduleMove b x)).2 * (scheduleKick a (scheduleMove b y)).1 =
        x.1 * y.2 - x.2 * y.1) ∧
  (∀ (a b : ℚ) (x u : ℚ × ℚ),
    boundaryPotential (scheduleMove b (scheduleKick a x)) (scheduleMove b (scheduleKick a u)) -
      boundaryPotential x u = kmDerivative a b x u ∧
    boundaryPotential (scheduleKick a (scheduleMove b x)) (scheduleKick a (scheduleMove b u)) -
      boundaryPotential x u = mkDerivative a b x u) ∧
  (∀ (a b : ℚ) (x u : ℚ × ℚ) (e : ℚ),
    kmPrimitive a b (x + e • u) =
      kmPrimitive a b x + e * kmDerivative a b x u + e ^ 2 * kmPrimitive a b u ∧
    mkPrimitive a b (x + e • u) =
      mkPrimitive a b x + e * mkDerivative a b x u + e ^ 2 * mkPrimitive a b u) ∧
  (∀ (K X : Type*) [Field K] [AddCommGroup X] [Module K X]
    (N : Submodule K X) (F G : X →ₗ[K] X),
    N.mkQ.comp F = N.mkQ.comp G ↔ LinearMap.range (F - G) ≤ N)

end Artform.Scores.GravityBridge.Statement
