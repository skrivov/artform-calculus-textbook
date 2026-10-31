import ArtformScores.GravityBridge.Native.R7Blocks.CompleteDefs

/-! # Complete bounded graph defect with its own propagator -/

namespace Artform.Scores.GravityBridge.Native.R7Blocks.Statement


/-- **GAC2:complete-graph-riccati**
(complete bounded graph defect with its own propagator). -/
@[ledger "GAC2:complete-graph-riccati"]
def completeLaw : Prop :=
  ∀ (Y Z : Type) [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z],
    (∀ (A11 : Y →L[ℝ] Y) (A12 : Z →L[ℝ] Y)
    (A21 : Y →L[ℝ] Z) (A22 : Z →L[ℝ] Z) (K : Y →L[ℝ] Z) (y : Y),
    blockAction A11 A12 A21 A22 (graphMap K y) =
      graphMap K (ownDataAction A11 A12 K y) + (0, blockDefect A11 A12 A21 A22 K y)) ∧
    (∀ (A11 : Y →L[ℝ] Y) (A12 : Z →L[ℝ] Y)
    (A21 : Y →L[ℝ] Z) (A22 : Z →L[ℝ] Z) (K : Y →L[ℝ] Z),
    Set.MapsTo (blockAction A11 A12 A21 A22) (Set.range (graphMap K))
      (Set.range (graphMap K)) ↔ blockDefect A11 A12 A21 A22 K = 0) ∧
    (∀ (A11 : Y →L[ℝ] Y) (A12 : Z →L[ℝ] Y)
    (A21 : Y →L[ℝ] Z) (A22 : Z →L[ℝ] Z) (K : Y →L[ℝ] Z),
    blockDefect A11 A12 A21 A22 K =
      A21 + A22.comp K - K.comp A11 - (K.comp A12).comp K)

end Artform.Scores.GravityBridge.Native.R7Blocks.Statement
