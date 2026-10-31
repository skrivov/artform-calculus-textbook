import ArtformScores.GravityBridge.Native.Retrospective.FirstContactDefs
/-! # The full signed inverse in the first connection contact -/
namespace Artform.Scores.GravityBridge.Native.Retrospective.Statement
open Matrix
/-- **GAC2:full-inverse-first-contact**
(the full signed inverse in the first connection contact). -/
@[ledger "GAC2:full-inverse-first-contact"]
def firstContactLaw : Prop :=
    (∀ (z : ℚ),
    polynomialInverse (1 / 101) *ᵥ connectionSource z =
    (-101 / 103 : ℚ) • connectionSource z) ∧
    (∀ (z : ℚ),
    (-2 / 101 : ℚ) • (polynomialInverse (1 / 101) *ᵥ connectionSource z) =
      (2 / 103 : ℚ) • connectionSource z) ∧
    (∀ (z : ℚ),
    (-2 / 101 : ℚ) • (polynomialInverse (1 / 101) *ᵥ connectionSource z) -
      curvatureOnlyPreparation (1 / 101) z = (-4 / 10403 : ℚ) • connectionSource z) ∧
    (∀ (z : ℚ),
    (-2 / 101 : ℚ) • (polynomialInverse (1 / 101) *ᵥ connectionSource z) =
      curvatureOnlyPreparation (1 / 101) z ↔ z = 0)
end Artform.Scores.GravityBridge.Native.Retrospective.Statement
