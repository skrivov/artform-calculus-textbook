import ArtformScores.NonabelianGravity.HistorySample
import ArtformScores.Meta.Ledger

/-! # Literal complete native history compatibility claim -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.Statement
open HistoryElimination Legendre

/-- **NGB:native-complete-history** (all finite lengths, complete source guards and solutions). -/
@[ledger "NGB:native-complete-history"]
def nativeCompleteHistory : Prop :=
  (∀ n : ℕ, Nonempty (Certificate (historyMatrix n))) ∧
  (∀ (n : ℕ) (x z : Point ℚ) (j y : Vector n),
    NativeMatch x z j y ↔ (historyMatrix n).mulVec y = sourceResidual x z j) ∧
  (∀ (n : ℕ) (c : Certificate (historyMatrix n)) (x z : Point ℚ) (j : Vector n),
    (∃ y, NativeMatch x z j y) ↔ Compatible c (sourceResidual x z j)) ∧
  (∀ (n : ℕ) (c : Certificate (historyMatrix n)) (x z : Point ℚ) (j free : Vector n),
    Compatible c (sourceResidual x z j) →
      NativeMatch x z j (solution c (sourceResidual x z j) free)) ∧
  (∀ (n : ℕ) (c : Certificate (historyMatrix n)) (x z : Point ℚ) (j y : Vector n),
    NativeMatch x z j y → y = solution c (sourceResidual x z j) (c.backward.mulVec y)) ∧
  sampleBackward * sampleForward = 1 ∧
  sampleForward * sampleBackward = 1 ∧
  sampleForward.transpose * historyMatrix 2 * sampleForward = Matrix.diagonal sampleDiagonal ∧
  Fintype.card {i : Index 2 // sampleDiagonal i ≠ 0} = 66 ∧
  (∀ n : ℕ, NativeMatch (n := n) 0 0 0 0) ∧
  (¬ ∃ y, NativeMatch 0 0 incompatibleSource y)

end Artform.Scores.NonabelianGravity.Statement
