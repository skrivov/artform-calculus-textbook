import ArtformScores.GravityBridge.Native.NativeDetailTests.RetuningDefs

/-! # One coarse scalar rescaling fails two original stationary tests -/

namespace Artform.Scores.GravityBridge.Native.NativeDetailTests.Statement

open Matrix CurvedSubdivision Full40 MeasureTheory Set Filter
open scoped ENNReal

/-- **GAC2:native-coarse-scalar-retuning**
(one coarse scalar rescaling fails two original stationary tests). -/
@[ledger "GAC2:native-coarse-scalar-retuning"]
def retuningLaw : Prop :=
    (stationaryValue 1 (5 / 4) (3 / 4) < -(45 / 32 : ℝ) ∧
      -(80 / 27 : ℝ) < stationaryValue 1 (5 / 3) (4 / 3)) ∧
    (¬ ∃ beta : ℝ,
      stationaryValue 1 (5 / 4) (3 / 4) = -beta * (15 / 8) ∧
      stationaryValue 1 (5 / 3) (4 / 3) = -beta * (40 / 9)) ∧
    ((5 / 4 : ℚ) ^ 2 - (3 / 4) ^ 2 = 1 ∧ (5 / 3 : ℚ) ^ 2 - (4 / 3) ^ 2 = 1 ∧
    (17 / 8 : ℚ) ^ 2 - (15 / 8) ^ 2 = 1 ∧ (41 / 9 : ℚ) ^ 2 - (40 / 9) ^ 2 = 1)

end Artform.Scores.GravityBridge.Native.NativeDetailTests.Statement
