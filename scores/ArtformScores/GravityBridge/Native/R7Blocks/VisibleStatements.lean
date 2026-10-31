import ArtformScores.GravityBridge.Native.R7Blocks.VisibleDefs

/-! # Artform visible closure and complete image invariance -/

namespace Artform.Scores.GravityBridge.Native.R7Blocks.Statement


/-- **GAC2:visible-closure-image-gap**
(artform visible closure and complete image invariance). -/
@[ledger "GAC2:visible-closure-image-gap"]
def visibleLaw : Prop :=
  ∀ (Y Z : Type) [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z],
    (∀ (A11 : Y →L[ℝ] Y) (A12 : Z →L[ℝ] Y)
    (A21 : Y →L[ℝ] Z) (A22 : Z →L[ℝ] Z) (K : Y →L[ℝ] Z) (y : Y),
    (blockRealization K).visible (blockAction A11 A12 A21 A22) y =
      ownDataAction A11 A12 K y) ∧
    (∀ (A11 : Y →L[ℝ] Y) (A12 : Z →L[ℝ] Y)
    (A21 : Y →L[ℝ] Z) (A22 : Z →L[ℝ] Z) (K : Y →L[ℝ] Z),
    linearDefect (graphMap K) (ContinuousLinearMap.fst ℝ Y Z)
      (blockAction A11 A12 A21 A22) =
      (0 : Y →L[ℝ] Y).prod (blockDefect A11 A12 A21 A22 K)) ∧
    (∀ (A11 : Y →L[ℝ] Y) (A12 : Z →L[ℝ] Y)
    (A21 : Y →L[ℝ] Z) (A22 : Z →L[ℝ] Z) (K : Y →L[ℝ] Z),
    (blockRealization K).Intertwines (blockAction A11 A12 A21 A22) ↔
      blockDefect A11 A12 A21 A22 K = 0) ∧
    (∀ (A11 : Y →L[ℝ] Y) (A12 : Z →L[ℝ] Y)
    (A21 : Y →L[ℝ] Z) (A22 : Z →L[ℝ] Z) (y : Y) (phi : Z →L[ℝ] ℝ)
    (_hsource : phi (A21 y) = 36 / 505),
    ¬ (blockRealization (0 : Y →L[ℝ] Z)).Invariant (blockAction A11 A12 A21 A22))

end Artform.Scores.GravityBridge.Native.R7Blocks.Statement
