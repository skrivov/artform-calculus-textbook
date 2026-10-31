import ArtformScores.NonabelianGravity.LegendreSchur
import ArtformScores.Meta.Ledger

/-! # Literal native-boundary score and composition claims -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.Statement
open Legendre

/-- **NGB:native-legendre-score** (the complete cut Taylor action). -/
@[ledger "NGB:native-legendre-score"]
def nativeLegendreScore : Prop :=
  (∀ u v : Point ℚ, cellQuadratic u v = matrixAction u v ∧
    linearCell u v = u 22 + u 29 + u 36 - (v 22 + v 29 + v 36)) ∧
  (∀ u v du dv : Point ℝ,
    HasDerivAt (fun e : ℝ => cutAction (u + e • du) (v + e • dv))
      (pair (post u v) dv - pair (pre u v) du) 0) ∧
  Matrix.rank mixed = 24 ∧
  (∀ a b : Phase ℚ, NativeRelation a b ↔ ScoreRelation a b) ∧
  unit25 ≠ 0 ∧ NativeRelation ((0 : Point ℚ), flatMomentum) (unit25, flatMomentum)

/-- **NGB:native-boundary-composition** (source-compatible stationary elimination). -/
@[ledger "NGB:native-boundary-composition"]
def nativeBoundaryComposition : Prop :=
  middleH * middleInverse = activeProjector ∧
  middleInverse * middleH = activeProjector ∧
  middleInverse.transpose = middleInverse ∧ Matrix.rank middleH = 36 ∧
  (∀ x y z j : Point ℚ, post x y - pre y z = j ↔
    activeProjector.mulVec j = j ∧
      activeProjector.mulVec y = middleInverse.mulVec (residual x z j)) ∧
  (∀ x y z j : Point ℚ, post x y - pre y z = j →
    twoCellAction x y z j = effectiveAction x z j) ∧
  composedMixed = -(mixed * middleInverse * mixed) ∧
  Matrix.rank mixed = 24 ∧ Matrix.rank composedMixed = 18 ∧
  effectiveAction 0 0 unit25 = -9595 / 39964 ∧
  post (0 : Point ℚ) 0 - pre 0 0 = 0 ∧
  (¬ ∃ y : Point ℚ, post 0 y - pre y 0 = unit0) ∧
  NativeRelation ((0 : Point ℚ), flatMomentum) (unit25, flatMomentum) ∧
  (¬ ∃ b : Phase ℚ, NativeRelation (unit25, flatMomentum) b)

end Artform.Scores.NonabelianGravity.Statement
