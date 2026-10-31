import ArtformScores.GravityBridge.Native.CoordinateSymbol.ForcedRowDefs

/-! # Native unit-row forcing with zero initial four-jet -/

namespace Artform.Scores.GravityBridge.Native.CoordinateSymbol.Statement

open Matrix

/-- **GAC2:native-forced-row-zero-four-jet**
(native unit-row forcing with zero initial four-jet). -/
@[ledger "GAC2:native-forced-row-zero-four-jet"]
def forcedRowLaw : Prop :=
    (∀ (l t : ℝ),
    HasDerivAt (fun s => forcedRowJet l s 0) (forcedRowJet l t 1) t ∧
    HasDerivAt (fun s => forcedRowJet l s 1) (forcedRowJet l t 2) t ∧
    HasDerivAt (fun s => forcedRowJet l s 2) (forcedRowJet l t 3) t ∧
    HasDerivAt (fun s => forcedRowJet l s 3) (forcedRowJet l t 4) t) ∧
    (∀ (l : ℝ) (_hl : l ^ 2 = 2),
    forcedRowJet l 0 0 = 0 ∧ forcedRowJet l 0 1 = 0 ∧
    forcedRowJet l 0 2 = 0 ∧ forcedRowJet l 0 3 = 0) ∧
    (∀ (l t : ℝ) (_hl : l ^ 2 = 2),
    (-(1 / 101 : ℝ) * (9999 / 9991)) *
      (forcedRowJet l t 4 - forcedRowJet l t 2 - 2 * forcedRowJet l t 0) = 1)

end Artform.Scores.GravityBridge.Native.CoordinateSymbol.Statement
