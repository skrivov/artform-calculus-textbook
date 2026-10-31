import ArtformScores.GravityBridge.Native.GreenComposition.SourceBoundary
import ArtformScores.GravityBridge.Native.Retrospective.BlockPrograms

/-! # Matched exact programs for all three native component outputs -/

namespace Artform.Scores.GravityBridge.Native.GreenComposition

open scoped BigOperators
open Matrix Retrospective



def literalBoundaryProgram : List ScalarGate := [
  .add (.input 0) (.input 1), .scale (1 / 2) (.slot 0), .scale (101 / 4) (.input 2),
  .add (.slot 1) (.slot 2), .add (.slot 3) (.neg (.input 0)), .scale (2 / 101) (.slot 4),
  .add (.input 1) (.neg (.slot 3)), .scale (2 / 101) (.slot 6)]

def reusedBoundaryProgram : List ScalarGate := [
  .add (.input 1) (.neg (.input 0)), .scale (1 / 101) (.slot 0), .scale (1 / 2) (.input 2),
  .add (.slot 1) (.slot 2), .add (.slot 1) (.neg (.slot 2)), .scale (101 / 2) (.slot 3),
  .add (.input 0) (.slot 5)]

end Artform.Scores.GravityBridge.Native.GreenComposition
