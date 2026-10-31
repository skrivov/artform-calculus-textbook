import ArtformScores.GravityBridge.TwoCellDefs

/-! # Two-cell source and endpoint reduction -/

namespace Artform.Scores.GravityBridge.Statement

/-- **GAC:two-cell-torsion** (two-cell source and endpoint reduction). -/
@[ledger "GAC:two-cell-torsion"]
def twoCellLaw : Prop :=
  (∀ a m b j : ℚ,
    twoCellTorsion a m b j = twoCellEffective a b j +
      2 * Native.kappa * (m - twoCellMiddle a b j) ^ 2) ∧
  (∀ a m b j : ℚ,
    2 * Native.kappa * (m - a) - 2 * Native.kappa * (b - m) = j ↔
      m = twoCellMiddle a b j) ∧
  (∀ a b j : ℚ,
    2 * Native.kappa * (twoCellMiddle a b j - a) = Native.kappa * (b - a) + j / 2 ∧
    2 * Native.kappa * (b - twoCellMiddle a b j) = Native.kappa * (b - a) - j / 2) ∧
  (∀ a m b j : ℚ,
    twoCellEffective a b j ≤ twoCellTorsion a m b j ∧
    (twoCellTorsion a m b j = twoCellEffective a b j ↔ m = twoCellMiddle a b j))

end Artform.Scores.GravityBridge.Statement
