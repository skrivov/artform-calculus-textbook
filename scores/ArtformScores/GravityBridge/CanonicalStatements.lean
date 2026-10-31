import ArtformScores.GravityBridge.CanonicalDefs

/-! # Canonical composition and nonlinear intersection test -/

namespace Artform.Scores.GravityBridge.Statement

/-- **GAC:canonical-composition** (canonical composition and nonlinear intersection test). -/
@[ledger "GAC:canonical-composition"]
def canonicalLaw : Prop :=
  (∀ (K X Y Z : Type*) [Field K] [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module K Y] [AddCommGroup Z] [Module K Z] [FiniteDimensional K Y]
    (BX : LinearMap.BilinForm K X) (BY : LinearMap.BilinForm K Y)
    (BZ : LinearMap.BilinForm K Z), BY.Nondegenerate →
    ∀ (R : Submodule K (X × Y)) (S : Submodule K (Y × Z)),
      CanonicalLinear BX BY R → CanonicalLinear BY BZ S →
        CanonicalLinear BX BZ (linearRelationCompose R S)) ∧
  (phaseForm.IsAlt ∧ phaseForm.Nondegenerate ∧
    CanonicalLinear phaseForm phaseForm singularLinearRelation) ∧
  Function.Injective quadraticCotangent ∧
  (∀ a : Plane, Function.Injective (quadraticTangent a) ∧ ∀ u v : Plane,
    -areaForm (quadraticTangent a u).1 (quadraticTangent a v).1 +
      areaForm (quadraticTangent a u).2 (quadraticTangent a v).2 = 0) ∧
  (∀ (a u : Plane) (e : ℝ),
    quadraticCotangent (a + e • u) = quadraticCotangent a + e • quadraticTangent a u +
      e ^ 2 • (((u.1 ^ 2, 0), (0, 2 * u.1 * u.2)) : Plane × Plane)) ∧
  (∀ z : Plane, (∃ y : Plane, y.1 = 0 ∧ cotangentRelation y z) ↔ z = 0) ∧
  (∀ p : ℝ, (quadraticTangent (0, p) (1, 0)).1.1 = 0 ∧
    (quadraticTangent (0, p) (1, 0)).2.1 = 1 ∧
    ¬ ∃ e : ℝ, e ≠ 0 ∧ (quadraticCotangent ((0, p) + e • (1, 0))).1.1 = 0)

end Artform.Scores.GravityBridge.Statement
